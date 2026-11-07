import Blanc.Lift.Usdc.EntryChain
import Blanc.Lift.Usdc.HistoryFamilyProxy
import Blanc.Lift.Usdc.ProxySstoreH
import Blanc.Lift.Usdc.ProxyReachH
import Blanc.ExecutionModelAccounting
import Blanc.Lift.CursorSourceRunReturn
import Blanc.ExecutionWholeFrameAccountingIn

/-!
# What the proxy's frames keep, on historical forks

The pieces `EntryTarget` assembles. No `CoveredFork`: upgrade and rescue frames ran on historical forks.
-/

namespace Blanc.Lift

open Jaune Blanc

variable {P : Sevm → Devm → Ninst → Devm → Prop}

/-- `CursorOK.state_post_of_silent` from `rules.stateGas = none` alone. -/
theorem CursorOK.state_post_of_silentH {code : ByteArray} {c : Cert} (checked : Cert.check code c = true)
    {S : List Nat} (hS : SilentSet c.prog S = true) {post : Devm} :
    ∀ (n : Nat) {F : Exec.Deriv} {κ : Cursor}, κ.K.length = n → CursorOK code c F κ →
      F.exn = .ok post → F.sevm.benvStat.rules.stateGas = none → κ.f.silentIn S = true →
      (∀ s ∈ κ.K.map Cont.f, s.silentIn S = true) → post.state = F.devm.state := by
  intro n
  induction n with
  | zero =>
      intro F κ hn placed success hsg hf hK
      rcases placed.sourceRunReturnH checked success hsg with halted | ⟨cont, tail, -, -, hKe, -⟩
      · simp only [SFunc.silentIn, Bool.and_eq_true] at hf
        exact SFunc.RunP.state_of_silent StepIn.toRun hS hf.1 hf.2 halted
      · rw [hKe] at hn
        cases hn
  | succ n ih =>
      intro F κ hn placed success hsg hf hK
      simp only [SFunc.silentIn, Bool.and_eq_true] at hf
      rcases placed.sourceRunReturnH checked success hsg with halted |
          ⟨cont, tail, state, run, hKe, -, -, returned, placedC⟩
      · exact SFunc.RunP.state_of_silent StepIn.toRun hS hf.1 hf.2 halted
      · have h1 := SFunc.RunP.state_of_silent StepIn.toRun hS hf.1 hf.2 returned
        rw [hKe] at hn hK
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hn
        simp only [List.map_cons, List.mem_cons, forall_eq_or_imp] at hK
        exact (ih hn placedC rfl hsg hK.1 hK.2).trans h1

/-- `silent_after_exec` from `rules.stateGas = none` alone. -/
theorem silent_after_execH {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {E S : List Nat} (hE : ExecFreeSet c.prog E = true) (hS : SilentSet c.prog S = true)
    (hall : ∀ f ∈ c.prog, f.contsIn E S = true)
    (hx : ∀ f ∈ c.prog, f.nodesSatisfy (ExecSilent S) = true)
    {R : Exec.Deriv} {post : Devm} (hpc : R.pc = 0) (hcode : R.sevm.code = code)
    (hsg : R.sevm.benvStat.rules.stateGas = none) (success : R.exn = .ok post)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix R N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    ∀ N', Exec.Deriv.ParentStep N' N → post.state = N'.devm.state ∧
      ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas hc hpc hcode hsg chain
  obtain ⟨g, hf, hg⟩ := ok.nodesSatisfy_exec (Reach.nodesSatisfy hx reach).1 hat
  have hK : ∀ s ∈ κ.K.map Cont.f, s.silentIn S = true := by
    have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
    have start : (Cursor.start c).conf R.devm = ⟨R.devm, (Cursor.start c).f, []⟩ := by
      cases c <;> rfl
    rw [start] at reach
    exact Reach.conts_silent hE hall reach hT (Cursor.start_contsIn hall)
  intro N' edge
  have hsevmN : N.sevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have hsgN : N.sevm.benvStat.rules.stateGas = none := by rw [hsevmN]; exact hsg
  obtain ⟨κ₁, hs, -, ok₁⟩ := cursor_stepS_noStateGas hc ok edge hsgN
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hf hK
  subst hf
  cases hs with
  | next habs =>
    have hchain : Exec.Deriv.ParentPrefix R N' := chain.snoc edge
    have hsevmN' : N'.sevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hchain
    have hsgN' : N'.sevm.benvStat.rules.stateGas = none := by rw [hsevmN']; exact hsg
    have success' : N'.exn = .ok post := (Exec.Deriv.ParentPrefix.exn_eq hchain).trans success
    simp only [ExecSilent] at hg
    refine ⟨CursorOK.state_post_of_silentH hc hS _ rfl ok₁ success' hsgN' hg hK,
      fun M hM y => noExec_after_of_cursorH hc hchain hM hsg ok₁ (ExecFreeSet.of_silentSet hS)
        (SFunc.execFreeIn_of_silentIn hg) (fun s hs => SFunc.execFreeIn_of_silentIn (hK s hs)) y⟩

/-- **A same-frame edge out of a node that decodes no external instruction keeps a cell its `SSTORE`,
if any, does not name.** -/
theorem parentStep_cell_of_noExec {next node : Exec.Deriv} (edge : Exec.Deriv.ParentStep next node)
    (noExec : ∀ x, ¬ Ninst.At node.sevm.code node.pc (.exec x)) {ca : Adr} {k : B256}
    (protection : State.Protected node.devm.state ca)
    (target : node.sevm.currentTarget = ca)
    (noWrite : Ninst.At node.sevm.code node.pc (.reg .sstore) →
      ∀ key rest, node.devm.stack = key :: rest → key ≠ k) :
    (next.devm.getStor ca).get k = (node.devm.getStor ca).get k := by
  rcases decoded : node.sevm.code.getInst node.pc with _ | instruction
  · exact (Cursor.parentStep_false_of_none edge decoded).elim
  cases instruction with
  | last l => exact (Cursor.parentStep_false_of_linst edge decoded).elim
  | jump j =>
      have run : Jinst.run ⟨node.pc, node.sevm, node.devm⟩ j = .ok ⟨next.pc, next.devm⟩ :=
        Cursor.parentStep_jinst edge decoded
      have frame := Jinst.run_instructionFrame ⟨node.pc, node.sevm, node.devm⟩ j
      rw [run] at frame
      exact congrArg (fun s => Stor.get s k) (frame.getStor ca).symm
  | next i =>
      have hat : Ninst.At node.sevm.code node.pc i := decoded
      by_cases store : i = .reg .sstore
      · subst store
        obtain ⟨-, run⟩ := Cursor.parentStep_ninst edge hat
        obtain ⟨key, value, pop⟩ := of_run_sstore run
        have update := sstore_getStor_set run (pref_of_split pop)
        rw [target] at update
        rw [update]
        have stack : node.devm.stack = key :: value :: _ := pop
        exact Stor.get_set_ne _ (noWrite hat key _ stack) _
      · cases edge with
        | cont hstep tail =>
            rename_i pc pc' sevm pre post out
            have nstep := (Evm.step_next hat).symm.trans hstep
            have nrun : Ninst.StepRun pc sevm pre i .none (.ok post) := by
              unfold Ninst.StepRun
              rw [nstep]
              exact ⟨rfl, rfl⟩
            exact congrArg (fun s => Stor.get s k)
              (Ninst.none_getStor_eq_of_ne_sstore nrun store ca protection)
        | doneOk hstep _ _ _ =>
            obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
            exact (noExec x hx).elim
        | runOk hstep _ _ _ _ =>
            obtain ⟨x, hx, -⟩ := Evm.step_spawn_inv hstep
            exact (noExec x hx).elim

end Blanc.Lift

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc.Proxy Blanc.ExecutionAccountingReplay

theorem proxy_size_ne_zero : Proxy.code.size ≠ 0 := by decide +kernel

theorem proxy_size_ne_delegation : Proxy.code.size ≠ eoaDelegatedCodeLength := by decide +kernel

/-- The proxy's code semantics. -/
abbrev entrySem : CodeSem := CodeSem.ofBytes Proxy.code proxy_size_ne_zero proxy_size_ne_delegation

/-- A chain frame: a proxy frame on a historical fork. -/
abbrev EntryGood (T : Adr) : Exec.Frame → Prop := CodeFrame T HistFork Proxy.code

variable {T : Adr} {Allowed : Exec.Frame → Prop}

/-- **A rescue frame is no chain link**: its re-entrant frames are. -/
def entryKeep (F : Exec.Frame) : Bool := decide (Blanc.Sevm.selector F.sevm ≠ rescueSelector)

local notation "Ca" => viewCarrier T ledgerView (EntryGood T) Allowed entryKeep

theorem ledgerView_congr {w w' : StorWords} (h : ∀ k, k ≠ implSlot → k ≠ adminSlot → w k = w' k) :
    ledgerView w = ledgerView w' := by
  funext k
  unfold ledgerView
  by_cases hk : k = implSlot ∨ k = adminSlot
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right fun c => (hk c).elim, ite_eq_right fun c => (hk c).elim]
    exact h k (fun e => hk (.inl e)) (fun e => hk (.inr e))

theorem entry_ofStateGet {s s' : State} (h : ∀ k, (s.getStor T).get k = (s'.getStor T).get k) :
    (Ca).ofState s = (Ca).ofState s' :=
  congrArg ledgerView (funext h)

/-- **The proxy's tail** on a historical fork. -/
theorem proxy_tailH {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    ∀ N', Exec.Deriv.ParentStep N' N → post.state = N'.devm.state ∧
      ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) :=
  silent_after_execH Proxy.cert_check proxy_execFree proxy_silentSet proxy_contsIn proxy_execSilent
    (R := ⟨0, sevm, pre, .ok post, run⟩) rfl codeEq hsg rfl chain hat

/-- A proxy frame's `SSTORE` names one of the proxy's two slots. -/
theorem proxy_store_slots {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N)
    (hat : Ninst.At N.sevm.code N.pc (.reg .sstore)) {key : B256} {rest : List B256}
    (stack : N.devm.stack = key :: rest) : key = implSlot ∨ key = adminSlot := by
  rcases proxy_sstoreNodeH run codeEq hsg bal chain hat with ⟨r, h⟩ | ⟨r, h, -⟩
  · rw [stack] at h
    exact .inr (List.cons.inj h).1
  · rw [stack] at h
    exact .inl (List.cons.inj h).1

/-- A cell other than the proxy's two slots holds from a successful proxy frame's entry to any node
decoding an external instruction. -/
theorem proxy_cell_to_exec {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (codeEq : sevm.code = Proxy.code) (target : sevm.currentTarget = T)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none)
    (rootCode : (pre.getCode T).toList ≠ []) {k : B256} (hi : k ≠ implSlot) (ha : k ≠ adminSlot) :
    ∀ {A N : Exec.Deriv}, Exec.Deriv.ParentPrefix A N →
      Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ A →
      (∃ x, Ninst.At N.sevm.code N.pc (.exec x)) →
      (N.devm.getStor T).get k = (A.devm.getStor T).get k := by
  intro A N chain
  induction chain with
  | refl => intro _ _; rfl
  | @step root next tail head rest ih =>
      intro fromRoot exec
      rw [ih (fromRoot.snoc head) exec]
      have noExec : ∀ x, ¬ Ninst.At root.sevm.code root.pc (.exec x) := by
        intro x hat
        obtain ⟨y, hy⟩ := exec
        exact (proxy_tailH run codeEq hsg fromRoot hat next head).2 _ rest y hy
      have sevmEq := Blanc.Exec.Deriv.ParentPrefix.sevm_eq fromRoot
      have codeKept := (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode fromRoot).2 T rootCode
      refine parentStep_cell_of_noExec head noExec
        (State.Protected.of_code_ne_nil (by
          change (root.devm.getCode T).toList ≠ []
          rw [codeKept]
          exact rootCode))
        (by rw [sevmEq]; exact target) fun hat key tail stack => ?_
      rcases proxy_store_slots run codeEq hsg bal fromRoot hat stack with e | e
      · rw [e]; exact hi.symm
      · rw [e]; exact ha.symm

/-- A successful proxy frame that decodes no external instruction keeps every cell apart from the
proxy's two slots. -/
theorem proxy_cell_of_noExec {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (codeEq : sevm.code = Proxy.code)
    (hsg : sevm.benvStat.rules.stateGas = none) (bal : sevm.benvStat.rules.bal = none)
    (rootCode : (pre.getCode T).toList ≠ [])
    (noExec : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x))
    {k : B256} (hi : k ≠ implSlot) (ha : k ≠ adminSlot) :
    (post.getStor T).get k = (pre.getStor T).get k := by
  refine frame_cellInv (Exec.Frame.ofRun run committed) hsg rootCode k
    (Inv := fun v => v = (pre.getStor T).get k) rfl ?_
  intro m member w found _ key _
  have chain := write_onChain run (by
    rw [Exec.rawFrameDescendants_eq_nil_of_noExec run noExec]
    exact fun _ h => absurd h List.not_mem_nil) member found
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  rcases proxy_store_slots run codeEq hsg bal chain decoded stack with e | e
  · exact (hi (key.symm.trans e)).elim
  · exact (ha (key.symm.trans e)).elim

end Blanc.Lift.Usdc
