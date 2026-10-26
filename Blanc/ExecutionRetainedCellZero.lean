import Blanc.ExecutionCellProvenance
import Blanc.Lift.TargetLogEvents

/-!
Zero preservation from actual settlement-retained writes. The observed account
is independent of the current frame's storage target or code image.
-/

namespace Blanc

open Jaune

private theorem Exec.cont_cell_zero
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm} {out : Execution}
    (step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
    (next : Exec pc' sevm post out)
    (hsg : sevm.benvStat.rules.stateGas = none) {owner : Adr} {key : B256}
    (bounds : ∀ w, Exec.Deriv.successfulSstore? ⟨pc, sevm, pre, out, .cont step next⟩ =
      some w → w.owner = owner → w.key = key →
      w.value.toNat ≤ ((pre.getStor owner).get key).toNat)
    (zero : (pre.getStor owner).get key = 0) :
    (post.getStor owner).get key = 0 := by
  by_cases matching : sevm.currentTarget = owner ∧
      Ninst.At sevm.code pc (.reg .sstore) ∧ pre.stack.head? = some key
  · obtain ⟨target, decoded, head⟩ := matching
    have nstep : Ninst.step ⟨pc, sevm, pre⟩ (.reg .sstore) = .cont pc' post := by
      rw [← Evm.step_next decoded]
      exact step
    have actual : Ninst.Run sevm pre (.reg .sstore) post := by
      refine ⟨.none, trivial, pc, ?_⟩
      unfold Ninst.StepRun
      rw [nstep]
      exact ⟨rfl, rfl⟩
    obtain ⟨written, value, popped⟩ := of_run_sstore actual
    have writtenEq : written = key := by
      rw [popped] at head
      exact Option.some.inj head
    let node : Exec.Deriv := ⟨pc, sevm, pre, out, .cont step next⟩
    let w : Exec.StorageWrite := ⟨node, sevm.currentTarget, written, value⟩
    have get : Evm.getInst ⟨pc, sevm, pre⟩ = some (.next (.reg .sstore)) := decoded
    have stack : pre.stack = written :: value :: post.stack := popped
    have found : Exec.Deriv.successfulSstore? node = some w := by
      simp only [node, w, Exec.Deriv.successfulSstore?, get, stack]
    have bound := bounds w found target writtenEq
    have effect := sstore_getStor_set (xs := []) actual ⟨post.stack, popped⟩
    rw [target] at effect
    rw [effect, Stor.get_set_ite, ite_eq_left writtenEq]
    apply B256.toNat_inj
    rw [B256.toNat_zero]
    exact Nat.eq_zero_of_le_zero (by simpa only [zero, B256.toNat_zero] using bound)
  · rw [Evm.step_cont_getStor_get_noStateGas hsg step
      (fun target decoded head => matching ⟨target, decoded, head⟩)]
    exact zero

/-- A protected cell initially zero remains zero when every actual retained
write to that cell is non-increasing at its own prefix. Complete settlement
discards failed child writes. No lifted code image or current-target equality
is required for the surrounding frames. -/
theorem Exec.cell_zero_of_retained_nonInc_noStateGas
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (hsg : sevm.benvStat.rules.stateGas = none) {owner : Adr} {key : B256}
    (hcode : (pre.getCode owner).toList ≠ [])
    (bounds : ∀ m ∈ Exec.retainedNodes run, ∀ w,
      Exec.Deriv.successfulSstore? m = some w → w.owner = owner → w.key = key →
      w.value.toNat ≤ ((m.devm.getStor owner).get key).toNat)
    (zero : (pre.getStor owner).get key = 0) :
    ((Execution.committedPost out committed).getStor owner).get key = 0 := by
  induction run with
  | @halt pc sevm pre out step =>
      have noWrite : Exec.Deriv.successfulSstore?
          ⟨pc, sevm, pre, out, .halt step⟩ = none := rfl
      have cell := (Exec.storageReplay_committedPost_noStateGas
        (.halt step) committed hsg).2 owner hcode key
      simpa only [Exec.retainedStorageWrites,
        Exec.retainedNodes_eq_of_commits _ committed, Exec.retainedNodesOfCommits,
        List.filterMap_cons, noWrite, List.filterMap_nil,
        Exec.StorageWrite.replayCell, List.foldl_nil, zero] using cell
  | @cont pc sevm pre pc' post out step next ih =>
      have code := Exec.Deriv.ParentStep.codePreserve (.cont step next) owner hcode
      have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
      have nextBounds : ∀ m ∈ Exec.retainedNodes next, ∀ w,
          Exec.Deriv.successfulSstore? m = some w → w.owner = owner → w.key = key →
          w.value.toNat ≤ ((m.devm.getStor owner).get key).toNat := by
        intro m member
        apply bounds m
        simpa only [Exec.retainedNodes_eq_of_commits _ committed,
          Exec.retainedNodesOfCommits, List.mem_cons] using Or.inr member
      apply ih committed hsg nextCode nextBounds
      apply Exec.cont_cell_zero step next hsg
      · intro w found own hit
        apply bounds _ ?_ w found own hit
        simp only [Exec.retainedNodes_eq_of_commits _ committed,
          Exec.retainedNodesOfCommits, List.mem_cons, true_or]
      · exact zero
  | doneErr step enter resume =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre frame resume pc' settled post out step enter resumed next ih =>
      have code := Exec.Deriv.ParentStep.codePreserve
        (.doneOk step enter resumed next) owner hcode
      have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
      apply ih committed hsg nextCode
      · intro m member
        apply bounds m
        simpa only [Exec.retainedNodes_eq_of_commits _ committed,
          Exec.retainedNodesOfCommits, List.mem_cons] using Or.inr member
      · rw [Evm.step_doneOk_getStor_eq step enter resumed owner
          (State.Protected.of_code_ne_nil hcode)]
        exact zero
  | runErr step enter child resume ih =>
      simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre frame resume pc' childEvm raw post out step enter child
      resumed next childIH nextIH =>
      have code := Exec.Deriv.ParentStep.codePreserve
        (.runOk step enter child resumed next) owner hcode
      have nextCode : (post.getCode owner).toList ≠ [] := by rw [code]; exact hcode
      have childCode : (childEvm.dyna.getCode owner).toList ≠ [] := by
        rw [(Evm.step_spawn_child step enter).2.1 owner]
        exact hcode
      have childSg := Evm.step_spawn_child_fork_noStateGas step enter hsg
      obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
      have nonempty : pre.getCode owner ≠ .empty := by
        intro empty
        apply hcode
        rw [empty]
        exact ByteArray.toList_empty
      have seam := Xinst.spawn_run_getStor_noStateGas hsg spawn enter child resumed nonempty
      by_cases settles : frame.settlementCommits raw = true
      · have childCommitted := Frame.raw_commits_of_settlementCommits settles
        have childBounds : ∀ m ∈ Exec.retainedNodes child, ∀ w,
            Exec.Deriv.successfulSstore? m = some w → w.owner = owner → w.key = key →
            w.value.toNat ≤ ((m.devm.getStor owner).get key).toNat := by
          intro m member
          apply bounds m
          rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles]
          exact List.mem_cons_of_mem _ (List.mem_append_left _ member)
        have childZero := childIH childCommitted childSg childCode childBounds
          (by rw [Evm.step_spawn_enter_getStor_noStateGas hsg step enter hcode]; exact zero)
        apply nextIH committed hsg nextCode
        · intro m member
          apply bounds m
          rw [Exec.retainedNodes_runOk_of_settlementCommits _ _ _ _ _ committed settles]
          exact List.mem_cons_of_mem _ (List.mem_append_right _ member)
        · rw [seam.1 settles key]
          exact childZero
      · apply nextIH committed hsg nextCode
        · intro m member
          apply bounds m
          rw [Exec.retainedNodes_runOk_of_not_settlementCommits _ _ _ _ _ committed settles]
          exact List.mem_cons_of_mem _ member
        · rw [seam.2 settles key]
          exact zero

end Blanc
