import Blanc.ExecutionInOwnCode
import Blanc.ExecutionWholeFrameAccountingIn
import Blanc.ExecutionStagedSstoreAttribution
import Blanc.ExecutionMidHistoryInFacts

/-!
# Own code at the settled frames of a mid history

`ConfiguredHistoryTraceIn.settled_ownCodeIn` over a `MidHistoryTraceIn`: from a mid history's start with `C`
installed at `a`, every settled frame sees `C` at `a`, starts at pc `0` under the selected domain, and runs `C` if
it runs at `a`, when frames running `C` at `a` spawn only by `CALL`, `STATICCALL` or `CREATE2`.

`MidHistoryTraceIn.rawFrames_closed`: its raw frames contain every frame they enter.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune Blanc.ExecutionAccountingReplay

/-- The ladder observing `OwnCodeAtIn` at every settled frame. -/
def ownCodeLadderIn {F : Fork → Prop} (sem : CodeSem) (a : Adr) {C : ByteArray}
    (hsgF : ∀ {f}, F f → (Fork.ruleSet f).stateGas = none)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) (image : sem.image = some C.toList)
    (spawns : OwnSpawnsIn a C) :
    AccountingLadderAdmittedIn F (ContractSpecSem.ofStorageOnly sem (fun _ => True)) a (fun _ _ => True) where
  carrier :=
    { Snap := Unit
      Step := Exec.Frame
      Tag := Unit
      Replay := fun _ steps _ => ∀ f ∈ steps, OwnCodeAtIn F a C f
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
  preserves := fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩
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
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    obtain ⟨installed, -⟩ := Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    have hpc : pc = 0 := congrArg (fun e : Evm => e.pc) evmEq
    subst hpc
    have hsg : sevm.benvStat.rules.stateGas = none := hsgF fork
    have codeOf : ∀ {x : ByteArray}, some x.toList = sem.image → x = C := fun {x} h => by
      rw [image] at h
      apply ByteArray.ext
      apply Array.toList_inj.mp
      simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj h
    have rootCode : pre.getCode a = C := codeOf installed.1
    have rootTarget : sevm.currentTarget = a → sevm.code = C := fun target =>
      codeOf (installed.2 target).1
    have below := Exec.descendantFrames_ownCodeIn (F := F) nonempty nondelegating spawns run
      (R := ⟨0, sevm, pre, out, run⟩) (.refl _) rfl fork hsg rootCode rootTarget
    refine ⟨Exec.committedFrames run, ?_, by
      change Exec.committedFrames run = (Exec.committedFrames run).flatMap fun f => [f]
      rw [List.flatMap_singleton']⟩
    intro f member
    rw [Exec.committedFrames, dite_eq_left committed] at member
    rcases List.mem_cons.mp member with rfl | deeper
    · exact ⟨rootCode, rfl, fork, hsg, rootTarget⟩
    · exact below f deeper

/-- **Own code at every settled frame of a mid history.** -/
theorem MidHistoryTraceIn.settled_ownCodeIn {F : Fork → Prop} (sem : CodeSem) (a : Adr) {C : ByteArray}
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (hsgF : ∀ {f}, F f → (Fork.ruleSet f).stateGas = none)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C) (spawns : OwnSpawnsIn a C)
    (trace : MidHistoryTraceIn F cfg start future) (capabilities : BodyStageCapabilities F)
    (installed : some (start.state.getCode a).toList = sem.image)
    (K : InstalledRuntimeSafety C) (image : sem.image = some C.toList) :
    ∀ f ∈ trace.settledFrames, OwnCodeAtIn F a C f := by
  have startInv : (ContractSpecSem.ofStorageOnly sem (fun _ => True)).StateInv a start.state :=
    ⟨installed, trivial, trivial⟩
  obtain ⟨steps, replay, observed⟩ :=
    (ownCodeLadderIn sem a hsgF nonempty nondelegating image spawns).midHistoryIn trace
      ((trace.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial) capabilities
      (trace.rewardCreditsFunded capabilities) startInv K image
  change steps = trace.settledFrames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  intro f member
  exact replay f (observed ▸ member)

/-- The raw frames of a mid history contain every frame they enter. -/
theorem MidHistoryTraceIn.rawFrames_closed {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future) :
    RawFramesClosed trace.rawFrames := by
  induction trace with
  | tail block cut =>
    exact RawFramesClosed.append cut.after.rawFrames_closed block.bodyTrace.requests.rawFrames_closed
  | step prior block ih => exact RawFramesClosed.append ih block.bodyTrace.rawFrames_closed

end ExecutionTrace

end Blanc
