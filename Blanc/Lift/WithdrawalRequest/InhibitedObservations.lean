import Blanc.Lift.WithdrawalRequest.InhibitedHistory
import Blanc.Lift.WithdrawalRequest.BalanceHistory
import Blanc.ExecutionAccountingMidHistoryIn

/-!
Before activation, the deployed inhibitor rules out every committed nonstatic
target frame. The accounting carrier below carries the initial-storage invariant
through the same retained execution whose observations it proves empty.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune Blanc.WithdrawalRequest Blanc.ExecutionTrace ExecutionAccountingReplay

/-- A conditional replay carries INIT and rules out every observed target frame.
Keeping the premise inside the relation lets the common accounting traversal
thread it through foreign calls, rollback, settlement and block boundaries. -/
private def inhibitedReplay (pre : Stor) (frames : List Exec.Frame) (post : Stor) : Prop :=
  RepresentsStorage pre.get initial → RepresentsStorage post.get initial ∧ frames = []

private theorem inhibitedReplay_append {pre mid post : Stor} {left right : List Exec.Frame}
    (first : inhibitedReplay pre left mid) (second : inhibitedReplay mid right post) :
    inhibitedReplay pre (left ++ right) post := by
  intro initialStorage
  obtain ⟨midStorage, emptyLeft⟩ := first initialStorage
  obtain ⟨postStorage, emptyRight⟩ := second midStorage
  exact ⟨postStorage, by rw [emptyLeft, emptyRight]; rfl⟩

private def inhibitedCarrier : ReplayCarrier withdrawalRequestPredeployAddress where
  Snap := Stor
  Step := Exec.Frame
  Tag := Unit
  Replay := inhibitedReplay
  ofState state := state.getStor withdrawalRequestPredeployAddress
  frameEntry _ state := state.getStor withdrawalRequestPredeployAddress
  nil := fun _ initialStorage => ⟨initialStorage, rfl⟩
  readsStorage := true
  silent := fun storage _ => storage rfl
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_⟩
    rw [storage]
    exact fun initialStorage => ⟨initialStorage, rfl⟩
  entry_eq_ofState := by
    intro _ _ callerNe _ transfer bound
    exact benvAfterTransfer_getStor_eq_of_safe transfer bound
      (fun transfers _ => Or.inl (callerNe transfers))

private def inhibitedObservation : ReplayObservation inhibitedCarrier where
  O := Exec.Frame
  obs frames := frames
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := balanceFrameObservation
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change inhibitedReplay (pre.getStor withdrawalRequestPredeployAddress) []
      (post.getStor withdrawalRequestPredeployAddress)
    rw [storage]
    exact fun initialStorage => ⟨initialStorage, rfl⟩

private theorem inhibitedTargetHandler {F : Fork → Prop}
    (neutral : ∀ {f : Fork}, F f → NeutralFork f)
    {sevm : Sevm} {pre post : Devm}
    (code : inhibitedSem.Run sevm pre post)
    (target : sevm.currentTarget = withdrawalRequestPredeployAddress) :
    Exec.CoreAccountingIn F withdrawalRequestPredeployAddress inhibitedSem inhibitedEntry
      inhibitedCarrier inhibitedObservation 0 sevm pre (.ok post) := by
  intro run committed fork _ admitted
  have frames : Exec.committedFrames run = [Exec.Frame.ofRun run committed] := by
    rw [Exec.committedFrames, dite_eq_left committed, canonical_descendants run code]
  refine ⟨?_, ?_⟩
  · intro static
    change (Exec.committedFrames run).flatMap balanceFrameObservation = []
    rw [frames]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply ite_eq_right
    intro observed
    have impossible : sevm.isStatic = false := observed.2
    rw [static] at impossible
    cases impossible
  · intro _
    refine ⟨(Exec.committedFrames run).flatMap balanceFrameObservation, ?_, rfl⟩
    intro initialStorage
    have entry := admitted.root target
    have inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max := by
      rw [target]
      exact initialStorage.excess
    exact False.elim (exec_user_inhibited_no_okH code (neutral fork).stateGas
      (neutral fork).bal entry.1.1 entry.2 inhibited run)

private theorem inhibited_coreAccounting {F : Fork → Prop}
    (neutral : ∀ {f : Fork}, F f → NeutralFork f) :
    Exec.Fa (Exec.WknSem withdrawalRequestPredeployAddress inhibitedSem
      (fun pc sevm pre out _ => Exec.CoreAccountingIn F withdrawalRequestPredeployAddress
        inhibitedSem inhibitedEntry inhibitedCarrier inhibitedObservation pc sevm pre out)) := by
  apply Exec.coreAccountingIn F withdrawalRequestPredeployAddress inhibitedSem inhibitedEntry
    inhibitedCarrier inhibitedObservation inhibitedReplay_append (fun _ _ => ())
  · intro _ _ _
    rfl
  · exact balanceFrameObservation_foreign
  · exact fun fork => (neutral fork).stateGas
  · intro sevm pre post semantic target _
    exact inhibitedTargetHandler neutral semantic target

private def inhibitedLadder {F : Fork → Prop}
    (neutral : ∀ {f : Fork}, F f → NeutralFork f) :
    AccountingLadderAdmittedIn F inhibitedSpec withdrawalRequestPredeployAddress
      inhibitedEntry where
  carrier := inhibitedCarrier
  append := inhibitedReplay_append
  tag := fun _ _ => ()
  preserves := inhibitedSpec_preservesIn neutral
  view := inhibitedObservation
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (inhibited_coreAccounting neutral pc sevm pre out run installed run committed fork
      installed admitted).2 entryBound

/-- The actual remainder of the deployment block and following preactivation
blocks preserve INIT and contain no committed nonstatic EIP-7002 target frame.
The two results are produced by one replay of this exact retained history. -/
theorem inhibited_mid_history_observations {F : Fork → Prop}
    (neutral : ∀ {f : Fork}, F f → NeutralFork f)
    (capabilities : BodyStageCapabilities F)
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future)
    (callers : trace.FrameAdmitted withdrawalRequestPredeployAddress
      (fun sevm _ => sevm.caller ≠ systemAddress))
    (installed : start.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (initialStorage : RepresentsStorage
      (start.state.getStor withdrawalRequestPredeployAddress).get initial) :
    RepresentsStorage (future.state.getStor withdrawalRequestPredeployAddress).get initial ∧
      trace.settledFrames.flatMap balanceFrameObservation = [] := by
  have startInv : inhibitedSpec.StateInv withdrawalRequestPredeployAddress start.state :=
    ⟨by rw [installed]; rfl, trivial, initialStorage⟩
  obtain ⟨frames, replay, observed⟩ := (inhibitedLadder neutral).midHistoryIn trace
    (inhibited_mid_admitted trace callers) capabilities (trace.rewardCreditsFunded capabilities)
    startInv inhibitedInstalledCert rfl
  obtain ⟨finalStorage, empty⟩ := replay initialStorage
  exact ⟨finalStorage, observed.symm.trans empty⟩

end Blanc.Lift.WithdrawalRequest
