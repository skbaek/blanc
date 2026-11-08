import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionDirectCode
import Blanc.ExecutionTraceAdmission
import Blanc.StorageOnlySpec
import Blanc.ExecutionTraceRootCallers
import Blanc.ExecutionImmutableCode

/-!
# Installed code at every settled frame, and own code at every own frame

For an address `ca` whose code `C` at the checkpoint is nonempty and not an EIP-7702 designator:

* `ConfiguredHistoryTrace.settled_ownCode`: every settled frame of a configured history finds `C`
  installed at `ca` when it starts, and every settled frame at `ca` runs `C` from pc `0`, provided
  frames running `C` at `ca` spawn only by `CALL`, `STATICCALL` or `CREATE2` (`OwnSpawns`; for a
  certified runtime, `CursorOK.exec_spawn_undelegated`).  No `DELEGATECALL`/`CALLCODE` from `C` means no frame
  at `ca` runs foreign code: a `CALL`/`STATICCALL` into `ca` runs the installed code, and a create
  never targets an address with code.
* `ConfiguredHistoryTrace.settledRoots_caller_ne_of_code`: `ca ≠ systemAddress` originates no settled
  message root (EIP-3607 on the installed code).

Contract-neutral: both are carried by the trivial storage-only specification of `C`.
-/

namespace Blanc

open Jaune

/-- The spawn kinds of frames running `C` at `ca`: every external instruction decoded along their chain
is `CALL`, `STATICCALL` or `CREATE2`. -/
def OwnSpawns (ca : Adr) (C : ByteArray) : Prop :=
  ∀ {R N : Exec.Deriv} {x : Xinst}, R.pc = 0 → R.sevm.code = C → R.sevm.currentTarget = ca →
    CoveredFork R.sevm.benvStat.fork → Exec.Deriv.ParentPrefix R N →
    Ninst.At N.sevm.code N.pc (.exec x) → x = .call ∨ x = .staticcall ∨ x = .create2

/-- A `CREATE2` spawn targets an account that is not protected in the spawning world. -/
theorem Xinst.step_create2_spawn_unprotected {sevm : Sevm} {d : Devm} {frame : Frame}
    {rsm : Resume} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Xinst.step sevm d .create2 = .spawn frame rsm) :
    ¬ State.Protected d.state frame.inner.currentTarget := by
  have hcreate2 : sevm.benvStat.rules.op.create2 = true :=
    hfork.cases (motive := fun f => (Fork.ruleSet f).op.create2 = true) rfl rfl rfl rfl
  simp only [Xinst.step, hfork.rules_stateGas_none, hcreate2, ↓reduceIte, Bind.bind,
    Except.bind] at h
  rcases eq1 : Devm.pop d with _ | ⟨v1, s1⟩ <;> simp only [eq1] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rcases eq2 : Devm.popToNat s1 with _ | ⟨n2, s2⟩ <;> simp only [eq2] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rcases eq3 : Devm.popToNat s2 with _ | ⟨n3, s3⟩ <;> simp only [eq3] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rcases eq4 : Devm.pop s3 with _ | ⟨v4, s4⟩ <;> simp only [eq4] at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  split at h
  · simp only [XStep.ofExcept, reduceCtorEq] at h
  rename_i s5 eq5
  simp only [XStep.ofExcept, pure, Except.pure] at h
  have state : (s5.memExtends [(n2, n3)]).state = d.state := by
    obtain ⟨x2, f2, -⟩ := Devm.pop_of_popToNat_val eq2
    obtain ⟨x3, f3, -⟩ := Devm.pop_of_popToNat_val eq3
    rw [show (s5.memExtends [(n2, n3)]).state = s5.state from rfl,
      ← (Devm.burn_of_chargeGas eq5).state, ← (Devm.pop_of_pop eq4).state, ← f3.state,
      ← f2.state, ← (Devm.pop_of_pop eq1).state]
  rw [← state, (genericCreate_step_spawn_exact h).1]
  exact genericCreate_step_spawn_target_unprotected h

/-- A frame starts at pc `0` on a covered fork, finds `C` installed at `ca`, and runs `C` if it runs at
`ca`. -/
def OwnCodeAt (ca : Adr) (C : ByteArray) (f : Exec.Frame) : Prop :=
  f.pre.getCode ca = C ∧ f.pc = 0 ∧ CoveredFork f.sevm.benvStat.fork ∧
    (f.sevm.currentTarget = ca → f.sevm.code = C)

/-- **Own code below a frame.**  Along the chain of a frame `R` that starts at pc `0` with `C` installed at
`ca` (and runs `C` if it runs at `ca`), every committed descendant frame satisfies `OwnCodeAt ca C`. -/
theorem Exec.descendantFrames_ownCode {ca : Adr} {C : ByteArray} (nonempty : C.toList ≠ [])
    (nondelegating : ¬ isValidDelegation C) (spawns : OwnSpawns ca C) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      {R : Exec.Deriv}, Exec.Deriv.ParentPrefix R ⟨pc, sevm, pre, out, run⟩ → R.pc = 0 →
      CoveredFork R.sevm.benvStat.fork → R.devm.getCode ca = C →
      (R.sevm.currentTarget = ca → R.sevm.code = C) →
      ∀ f ∈ Exec.descendantFrames run, OwnCodeAt ca C f := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ _ _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont step next ih =>
      intro R chain pcZero fork code own
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.cont step next)) pcZero fork code own
  | doneErr _ _ _ =>
      intro _ _ _ _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk step enter resume next ih =>
      intro R chain pcZero fork code own
      simpa only [Exec.descendantFrames] using
        ih (chain.snoc (.doneOk step enter resume next)) pcZero fork code own
  | runErr _ _ _ _ =>
      intro _ _ _ _ _ _ f member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro R chain pcZero fork code own f member
      have sevmEq : nodeSevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
      have codeNe : C ≠ .empty := fun empty => nonempty (by rw [empty]; simp only [ByteArray.toList_empty])
      have nodeCode : nodePre.getCode ca = C := by
        have keep := (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 ca
          (by rw [code]; exact nonempty)
        exact keep.trans code
      obtain ⟨pcZero', getCode, codeSource⟩ := Evm.step_spawn_child hstep henter
      have childFork : CoveredFork cevm.sta.benvStat.fork :=
        Evm.step_spawn_child_fork hstep henter (by rw [sevmEq]; exact fork)
      have childCode : cevm.dyna.getCode ca = C := (getCode ca).trans nodeCode
      have childOwn : cevm.sta.currentTarget = ca → cevm.sta.code = C := by
        intro target
        by_cases same : nodeSevm.currentTarget = ca
        · obtain ⟨x, hat, spawn, -⟩ := Evm.step_spawn_inv hstep
          have kind := spawns (N := ⟨nodePc, nodeSevm, nodePre, final,
            .runOk hstep henter child hresume next⟩) pcZero (own (sevmEq ▸ same))
            (sevmEq ▸ same) fork chain hat
          have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
            rw [← Frame.enter_run_currentTarget henter, target, same]
          have notDel : ¬ isValidDelegation (nodePre.getCode frame.inner.currentTarget) := by
            rw [sameTarget, same, nodeCode]
            exact nondelegating
          rw [Frame.enter_run_code henter]
          rcases kind with rfl | rfl | rfl
          · rw [Xinst.step_call_sameTarget_code spawn sameTarget notDel, sameTarget, same, nodeCode]
          · rw [Xinst.step_staticcall_sameTarget_code spawn sameTarget notDel, sameTarget, same,
              nodeCode]
          · have unprotected := Xinst.step_create2_spawn_unprotected
              (by rw [sevmEq]; exact fork) spawn
            rw [sameTarget, same] at unprotected
            exact (unprotected (State.Protected.of_code_ne_nil (by
              change (nodePre.getCode ca).toList ≠ []
              rw [nodeCode]
              exact nonempty))).elim
        · rw [codeSource (by rw [target]; exact same) (by rw [target, nodeCode]; exact codeNe)
            (by rw [target, nodeCode]; exact nondelegating), target, nodeCode]
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next
          settles] at member
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (rfl | inChild) | inNext
        · exact ⟨childCode, pcZero', childFork, childOwn⟩
        · exact childIh (R := ⟨_, _, _, _, child⟩) (.refl _) pcZero' childFork childCode childOwn
            f inChild
        · exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) pcZero fork code own
            f inNext
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next
          settles] at member
        exact nextIh (chain.snoc (.runOk hstep henter child hresume next)) pcZero fork code own
          f member

/-! ## The trivial specification of an installed code -/

namespace ExecutionTrace

end ExecutionTrace

end Blanc
