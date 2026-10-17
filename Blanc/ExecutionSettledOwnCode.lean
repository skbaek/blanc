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
  simp only [Xinst.step, hfork.rules_stateGas_none, Bind.bind, Except.bind] at h
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

/-- The code semantics of an installed code with no run content. -/
private def ownSem (C : ByteArray) (nonempty : C.toList ≠ [])
    (nondelegating : ¬ isValidDelegation C) : CodeSem where
  image := some C.toList
  Run := fun _ _ _ => True
  correct := fun _ _ => trivial
  ne_nil := by
    intro l image
    exact (Option.some.inj image) ▸ nonempty
  not_delegation := by
    intro actual image
    exact ExecutionTrace.bytes_eq_of_image image ▸ nondelegating

private def ownSpec (C : ByteArray) (nonempty : C.toList ≠ [])
    (nondelegating : ¬ isValidDelegation C) : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly (ownSem C nonempty nondelegating) (fun _ => True)

private theorem ownSpec_preserves (C : ByteArray) (nonempty : C.toList ≠ [])
    (nondelegating : ¬ isValidDelegation C) (ca : Adr) :
    (ownSpec C nonempty nondelegating).PreservesAdmitted ca (fun _ _ => True) := by
  intro sevm pre post fork run admitted image wf inv
  exact ⟨trivial, trivial⟩

open ExecutionAccountingReplay in
/-- The ladder observing every settled frame with `OwnCodeAt ca C`. -/
private def ownLadder {ca : Adr} {C : ByteArray} (nonempty : C.toList ≠ [])
    (nondelegating : ¬ isValidDelegation C) (spawns : OwnSpawns ca C) :
    AccountingLadderAdmitted (ownSpec C nonempty nondelegating) ca (fun _ _ => True) where
  carrier :=
    { Snap := Unit
      Step := Exec.Frame
      Tag := Unit
      Replay := fun _ steps _ => ∀ f ∈ steps, OwnCodeAt ca C f
      ofState := fun _ => ()
      frameEntry := fun _ _ => ()
      nil := fun _ f member => (List.not_mem_nil member).elim
      readsStorage := false
      silent := fun _ _ => rfl
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim⟩
      entry_eq_ofState := fun _ _ _ _ => rfl }
  append := fun left right f member => (List.mem_append.mp member).elim (left f) (right f)
  tag := fun _ _ => ()
  preserves := ownSpec_preserves C nonempty nondelegating ca
  view :=
    { O := Exec.Frame
      obs := id
      obs_nil := rfl
      obs_append := fun _ _ => rfl
      frameObs := fun f => [f]
      credit := by
        intros
        exact ⟨[], fun f member => (List.not_mem_nil member).elim, rfl⟩ }
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed _ ready _ fork bound
    obtain ⟨installed, -⟩ := Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have pcZero : pc = 0 := by
      have := congrArg Evm.pc evmEq
      simpa only [initEvm] using this
    have code : pre.getCode ca = C := ExecutionTrace.bytes_eq_of_image installed.1
    have own : sevm.currentTarget = ca → sevm.code = C := fun target =>
      ExecutionTrace.bytes_eq_of_image (installed.2 target).1
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    intro f member
    rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact ⟨code, pcZero, fork, own⟩
    · exact Exec.descendantFrames_ownCode nonempty nondelegating spawns run
        (R := ⟨pc, sevm, pre, out, run⟩) (.refl _) pcZero fork code own f deeper

namespace ExecutionTrace

/-- **Installed code at every settled frame, own code at every own frame.**  If `C` is installed at `ca`
at the checkpoint, is nonempty and is no designator, and frames running `C` at `ca` spawn only by `CALL`,
`STATICCALL` or `CREATE2`, then every settled frame of the history finds `C` at `ca` when it starts, and
every settled frame starts at pc `0` on a covered fork and, if it runs at `ca`, runs `C`. -/
theorem ConfiguredHistoryTrace.settled_ownCode {ca : Adr} {C : ByteArray}
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) (spawns : OwnSpawns ca C)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : checkpoint.state.getCode ca = C) :
    ∀ f ∈ trace.settledFrames, OwnCodeAt ca C f := by
  have admitted : trace.FrameAdmitted ca (fun _ _ => True) :=
    (trace.frameAdmitted_iff_rawFrames ca _).2 fun _ _ _ => trivial
  have inv : (ownSpec C nonempty nondelegating).StateInv ca checkpoint.state := by
    refine ⟨?_, trivial, trivial⟩
    change some (checkpoint.state.getCode ca).toList = some C.toList
    rw [installed]
  obtain ⟨steps, replay, observed⟩ :=
    (ownLadder nonempty nondelegating spawns).configuredHistory trace admitted inv
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  intro f member
  exact replay f (observed ▸ member)

/-- **An installed code originates no settled root.**  If `C` is installed at `ca` at the checkpoint, is
nonempty and is no designator, and `ca ≠ systemAddress`, then `ca` is the caller of no settled message
root (EIP-3607). -/
theorem ConfiguredHistoryTrace.settledRoots_caller_ne_of_code {ca : Adr} {C : ByteArray}
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : checkpoint.state.getCode ca = C) (notSystem : ca ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ ca := by
  have admitted : trace.FrameAdmitted ca (fun _ _ => True) :=
    (trace.frameAdmitted_iff_rawFrames ca _).2 fun _ _ _ => trivial
  have inv : (ownSpec C nonempty nondelegating).StateInv ca checkpoint.state := by
    refine ⟨?_, trivial, trivial⟩
    change some (checkpoint.state.getCode ca).toList = some C.toList
    rw [installed]
  exact trace.settledRoots_caller_ne (ownSpec_preserves C nonempty nondelegating ca) admitted
    inv notSystem

end ExecutionTrace

end Blanc
