import Blanc.Lift.WithdrawalRequest.Semantics
import Blanc.ExecutionAccountingSignedBalance
import Blanc.ExecutionAccountingCore
import Blanc.ExecutionAccountingAdmission

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionAccountingReplay

def balanceFrameObservation (frame : Exec.Frame) : List Exec.Frame :=
  if frame.sevm.currentTarget = withdrawalRequestPredeployAddress ∧
      frame.sevm.isStatic = false then [frame] else []

def balanceObservation : ReplayObservation (signedBalanceCarrier withdrawalRequestPredeployAddress)
    where
  O := Exec.Frame
  obs steps := steps.flatMap SignedBalanceCredit.frames
  obs_nil := rfl
  obs_append := fun _ _ => List.flatMap_append
  frameObs := balanceFrameObservation
  credit := by
    intro _ pre post amount _ balance _
    refine ⟨[.incidental amount], ?_, rfl⟩
    change ((pre.bal withdrawalRequestPredeployAddress).toNat : Int) +
      (([SignedBalanceCredit.incidental amount].map SignedBalanceCredit.amount).sum : Int) =
      ((post.bal withdrawalRequestPredeployAddress).toNat : Int)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      SignedBalanceCredit.amount, Nat.add_zero]
    rw [balance, Int.natCast_add]

theorem balanceFrameObservation_foreign (frame : Exec.Frame)
    (foreign : frame.sevm.currentTarget ≠ withdrawalRequestPredeployAddress) :
    balanceFrameObservation frame = [] := by
  exact ite_eq_right (fun condition => foreign condition.1)

theorem canonical_descendants {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (code : sevm.code = Blanc.withdrawalRequestCode) : Exec.descendantFrames run = [] := by
  have free : SpawnFreeReach sevm.code := by
    rw [code]
    exact Blanc.withdrawalRequestCode_spawnFreeReach
  have raw := Exec.rawFrameDescendants_eq_nil_of_reach run (noPushBefore_zero _ _) free
  cases frames : Exec.descendantFrames run with
  | nil => rfl
  | cons frame rest =>
    have member := Exec.mem_rawFrameDescendants_of_mem_descendantFrames run frame
      (by rw [frames]; exact List.mem_cons_self)
    rw [raw] at member
    cases member

private theorem balanceTargetHandler {sevm : Sevm} {pre post : Devm}
    (semantic : balanceSem.Run sevm pre post)
    (target : sevm.currentTarget = withdrawalRequestPredeployAddress) :
    Exec.CoreAccounting withdrawalRequestPredeployAddress balanceSem balanceEntryCondition
      (signedBalanceCarrier withdrawalRequestPredeployAddress) balanceObservation
      0 sevm pre (.ok post) := by
  intro run committed fork installed admitted
  have effect := semantic.2 fork (admitted.root target)
  have preserved := effect.preserves.1 withdrawalRequestPredeployAddress
  have balance : post.state.bal withdrawalRequestPredeployAddress =
      pre.state.bal withdrawalRequestPredeployAddress := preserved
  have frames : Exec.committedFrames run = [Exec.Frame.ofRun run committed] := by
    rw [Exec.committedFrames, dite_eq_left committed, canonical_descendants run semantic.1]
  refine ⟨?_, ?_⟩
  · intro static
    rw [frames]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change balanceFrameObservation (Exec.Frame.ofRun run committed) = []
    apply ite_eq_right
    intro condition
    have impossible : sevm.isStatic = false := condition.2
    rw [static] at impossible
    cases impossible
  · intro _
    cases static : sevm.isStatic with
    | false =>
      refine ⟨[.message (Exec.Frame.ofRun run committed)], ?_, ?_⟩
      · change signedBalanceEntry withdrawalRequestPredeployAddress sevm pre.state +
          (([SignedBalanceCredit.message (Exec.Frame.ofRun run committed)].map
            SignedBalanceCredit.amount).sum : Int) =
          ((post.state.bal withdrawalRequestPredeployAddress).toNat : Int)
        rw [signedBalanceEntry, ite_eq_left target, balance]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          SignedBalanceCredit.amount, Exec.Frame.ofRun, Nat.add_zero]
        omega
      · rw [frames]
        change [Exec.Frame.ofRun run committed] =
          balanceFrameObservation (Exec.Frame.ofRun run committed) ++ []
        rw [balanceFrameObservation, ite_eq_left ⟨target, static⟩, List.append_nil]
    | true =>
      have value := (effect.static_getter static).2.2.1
      refine ⟨[], ?_, ?_⟩
      · change signedBalanceEntry withdrawalRequestPredeployAddress sevm pre.state + 0 =
          ((post.state.bal withdrawalRequestPredeployAddress).toNat : Int)
        rw [signedBalanceEntry, ite_eq_left target, value, balance]
        change ((pre.state.bal withdrawalRequestPredeployAddress).toNat : Int) - 0 + 0 = _
        omega
      · rw [frames]
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        change [] = balanceFrameObservation (Exec.Frame.ofRun run committed)
        symm
        apply ite_eq_right
        intro condition
        have impossible : sevm.isStatic = false := condition.2
        rw [static] at impossible
        cases impossible

/-- Actual foreign executions use the common accounting engine; canonical target roots
    supply their exact message-value credit. -/
theorem balance_coreAccounting :
    Exec.Fa (Exec.WknSem withdrawalRequestPredeployAddress balanceSem
      (fun pc sevm pre out _ =>
        Exec.CoreAccounting withdrawalRequestPredeployAddress balanceSem balanceEntryCondition
          (signedBalanceCarrier withdrawalRequestPredeployAddress) balanceObservation
          pc sevm pre out)) := by
  apply Exec.coreAccounting withdrawalRequestPredeployAddress balanceSem balanceEntryCondition
    (signedBalanceCarrier withdrawalRequestPredeployAddress) balanceObservation
    signedBalanceCarrier_append (fun _ _ => ())
  · intro sevm state foreign
    exact ite_eq_right foreign
  · exact balanceFrameObservation_foreign
  · intro sevm pre post semantic target _
    exact balanceTargetHandler semantic target

def balanceLadder : AccountingLadderAdmitted balanceSpec withdrawalRequestPredeployAddress
    balanceEntryCondition where
  carrier := signedBalanceCarrier withdrawalRequestPredeployAddress
  append := signedBalanceCarrier_append
  tag := fun _ _ => ()
  preserves := balanceSpec_preserves
  view := balanceObservation
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
      bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (balance_coreAccounting pc sevm pre out run installed run committed fork installed
      admitted).2 entryBound

/-- The retained history accounts for every balance increment, with message credits
    observed as exactly the actual committed nonstatic target frames. -/
theorem history_balance_replay {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    ∃ steps : List SignedBalanceCredit,
      ((checkpoint.state.bal withdrawalRequestPredeployAddress).toNat : Int) +
          ((steps.map SignedBalanceCredit.amount).sum : Int) =
        ((future.state.bal withdrawalRequestPredeployAddress).toNat : Int) ∧
      steps.flatMap SignedBalanceCredit.frames =
        trace.settledFrames.flatMap balanceFrameObservation := by
  apply balanceLadder.configuredHistory trace (history_balanceEntryCondition trace)
  refine ⟨?_, trivial, trivial⟩
  change some (checkpoint.state.getCode withdrawalRequestPredeployAddress).toList =
    some Blanc.withdrawalRequestCode.toList
  rw [code]

theorem history_balance_nondecreasing {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat ≤
      (future.state.bal withdrawalRequestPredeployAddress).toNat := by
  obtain ⟨steps, replay, _⟩ := history_balance_replay trace code
  omega

theorem history_message_values_bound {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat +
        ((trace.settledFrames.flatMap balanceFrameObservation).map
          (fun frame => frame.sevm.value.toNat)).sum ≤
      (future.state.bal withdrawalRequestPredeployAddress).toNat := by
  obtain ⟨steps, replay, observed⟩ := history_balance_replay trace code
  have bound := signedBalanceCredit_frames_sum_le steps
  rw [observed] at bound
  omega

/-- Submission tags select committed user frames with the canonical 56-byte input. -/
abbrev submissionPaymentFrame (frame : Exec.Frame) : Prop :=
  (frame.sevm.currentTarget = withdrawalRequestPredeployAddress ∧ frame.sevm.isStatic = false) ∧
    frame.sevm.caller ≠ systemAddress ∧ frame.sevm.data.length = 56

def submissionFramePayments (frame : Exec.Frame) : List (Exec.Frame × Nat) :=
  if submissionPaymentFrame frame then [(frame, frame.sevm.value.toNat)] else []

def submissionCreditPayments : SignedBalanceCredit → List (Exec.Frame × Nat)
  | credit@(.message frame) =>
    if submissionPaymentFrame frame then [(frame, credit.amount)] else []
  | .incidental _ => []

private theorem submissionCreditPayments_factor (credit : SignedBalanceCredit) :
    submissionCreditPayments credit =
      (SignedBalanceCredit.frames credit).flatMap submissionFramePayments := by
  cases credit with
  | message frame =>
    simp only [submissionCreditPayments, SignedBalanceCredit.frames, SignedBalanceCredit.amount,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, submissionFramePayments]
  | incidental amount => rfl

private theorem submissionFramePayments_observed (frame : Exec.Frame) :
    (balanceFrameObservation frame).flatMap submissionFramePayments =
      submissionFramePayments frame := by
  by_cases observed : frame.sevm.currentTarget = withdrawalRequestPredeployAddress ∧
      frame.sevm.isStatic = false
  · rw [balanceFrameObservation, ite_eq_left observed]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  · have other : ¬ submissionPaymentFrame frame := fun submission => observed submission.1
    rw [balanceFrameObservation, ite_eq_right observed, List.flatMap_nil,
      submissionFramePayments, ite_eq_right other]

/-- Every retained submission is paired with a message credit of exactly its actual value.
    Incidental credits are absent from this ordered payment projection. -/
theorem history_submission_payments {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    ∃ steps : List SignedBalanceCredit,
      ((checkpoint.state.bal withdrawalRequestPredeployAddress).toNat : Int) +
          ((steps.map SignedBalanceCredit.amount).sum : Int) =
        ((future.state.bal withdrawalRequestPredeployAddress).toNat : Int) ∧
      steps.flatMap submissionCreditPayments =
        trace.settledFrames.flatMap submissionFramePayments := by
  obtain ⟨steps, replay, observed⟩ := history_balance_replay trace code
  refine ⟨steps, replay, ?_⟩
  calc
    steps.flatMap submissionCreditPayments =
        (steps.flatMap SignedBalanceCredit.frames).flatMap submissionFramePayments := by
      rw [List.flatMap_assoc]
      apply congrArg (fun projection => steps.flatMap projection)
      funext credit
      exact submissionCreditPayments_factor credit
    _ = (trace.settledFrames.flatMap balanceFrameObservation).flatMap
        submissionFramePayments := congrArg (fun frames => frames.flatMap submissionFramePayments)
          observed
    _ = trace.settledFrames.flatMap submissionFramePayments := by
      rw [List.flatMap_assoc]
      apply congrArg (fun projection => trace.settledFrames.flatMap projection)
      funext frame
      exact submissionFramePayments_observed frame

/-- Canonical code preservation is inherited from the ordinary retained-history ladder. -/
theorem history_canonical_code {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (code : checkpoint.state.getCode withdrawalRequestPredeployAddress =
      Blanc.withdrawalRequestCode) :
    future.state.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode := by
  have initial : balanceSpec.StateInv withdrawalRequestPredeployAddress checkpoint.state := by
    refine ⟨?_, trivial, trivial⟩
    change some (checkpoint.state.getCode withdrawalRequestPredeployAddress).toList =
      some Blanc.withdrawalRequestCode.toList
    rw [code]
  have final := trace.stateInv_admitted_sem balanceSpec_preserves
    (history_balanceEntryCondition trace) initial
  exact code_eq_of_image final.code

end Blanc.Lift.WithdrawalRequest
