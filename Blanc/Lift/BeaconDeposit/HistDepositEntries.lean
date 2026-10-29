import Blanc.Lift.BeaconDeposit.HistCommittedHistory
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionImmutableCode

/-! Deposit-entry invariants from the exact historical settlement-retained replay. -/

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

private def depositEntryInv (storage : Stor) : Prop := ∃ history, SolInv storage history

/-- Observe exactly the successful target frames contributing a deposit node.
The inherited observation is identity on the actual retained frame list. -/
private def depositEntryObservation (ca : Adr) :
    ReplayObservation (entryCarrierIn HistFork ca beaconSem beaconFrameEntryRules depositEntryInv) :=
  { entryObservationIn HistFork ca beaconSem beaconFrameEntryRules depositEntryInv with
    frameObs := fun frame =>
      if frame.sevm.currentTarget = ca ∧ Sevm.selector frame.sevm = BeaconDeposit.depositSelector
      then [frame] else [] }

private theorem beaconEntry_coreIn (ca : Adr) :
    Exec.Fa (Exec.WknSem ca beaconSem
      (fun pc s d e _ => Exec.CoreAccountingIn HistFork ca beaconSem beaconFrameEntryRules
        (entryCarrierIn HistFork ca beaconSem beaconFrameEntryRules depositEntryInv)
        (depositEntryObservation ca) pc s d e)) := by
  apply Exec.coreAccountingIn HistFork ca beaconSem beaconFrameEntryRules
    (entryCarrierIn HistFork ca beaconSem beaconFrameEntryRules depositEntryInv)
    (depositEntryObservation ca)
    (EntryReplayIn.append HistFork ca beaconSem beaconFrameEntryRules depositEntryInv)
    (fun _ _ => ())
  · intro sevm state foreign
    rfl
  · intro frame foreign
    change (if frame.sevm.currentTarget = ca ∧
      Sevm.selector frame.sevm = BeaconDeposit.depositSelector then [frame] else []) = []
    rw [ite_eq_right (fun selected => foreign selected.1)]
  · exact fun fork => fork.stateGas_none
  · intro sevm pre post hcode target deeper run committed fork installed admitted
    obtain ⟨⟨stack, memory⟩, calldata, nodeleg, warm⟩ := admitted.root target
    have descendants := Exec.staticOnly_descendantFrames_flatMap_eq_nilIn
      (F := HistFork) ca beaconSem beaconFrameEntryRules (depositEntryObservation ca).frameObs
      ⟨0, sevm, pre, .ok post, run⟩ target installed.1 fork
      (fun chain instruction => parentPrefix_exec_staticcallH
        (root := ⟨0, sevm, pre, .ok post, run⟩) rfl hcode fork.stateGas_none chain instruction)
      (fun child childCommitted childFork depth childAt childAdmitted static =>
        (deeper _ _ _ _ child depth childAt
          child childCommitted childFork childAt childAdmitted).1 static)
      run (.refl _) (by
        intro frameRoot member selected
        exact admitted frameRoot (List.mem_cons_of_mem _ member) selected)
    have observed : (Exec.committedFrames run).flatMap (depositEntryObservation ca).frameObs =
        (depositEntryObservation ca).frameObs (Exec.Frame.ofRun run committed) := by
      simp only [Exec.committedFrames, dite_eq_left committed, List.flatMap_cons,
        descendants, List.append_nil]
    refine ⟨?_, fun _ => ⟨(depositEntryObservation ca).frameObs
      (Exec.Frame.ofRun run committed), ?_, observed.symm⟩⟩
    · intro static
      rw [observed]
      change (if sevm.currentTarget = ca ∧ Sevm.selector sevm = BeaconDeposit.depositSelector
        then [Exec.Frame.ofRun run committed] else []) = []
      have notSelected : ¬ (sevm.currentTarget = ca ∧
          Sevm.selector sevm = BeaconDeposit.depositSelector) := by
        intro selected
        have empty := frameAccepted_eq_nil_of_staticH hcode fork.stateGas_none fork.bal_none
          calldata stack memory static run
        simp only [frameAccepted, ite_eq_left selected.2, List.cons_ne_nil] at empty
      rw [ite_eq_right notSelected]
    · intro ⟨history, invariant⟩
      have sha : ShaReadyRules sevm pre :=
        ⟨nodeleg, warm, isPrecomp_two_hist fork, fork.stateGas_none, fork.bal_none⟩
      have postInvariant := frame_solInvH_of_rules hcode fork.stateGas_none fork.bal_none
        calldata stack memory sha (by rw [target]; exact invariant) run
      rw [target] at postInvariant
      refine ⟨⟨_, postInvariant⟩, ?_⟩
      intro frame member
      change frame ∈ (if sevm.currentTarget = ca ∧
        Sevm.selector sevm = BeaconDeposit.depositSelector
        then [Exec.Frame.ofRun run committed] else []) at member
      split at member
      · rw [List.mem_singleton] at member
        subst frame
        exact ⟨rfl, fork, installed, admitted.root target, ⟨history, invariant⟩⟩
      · exact False.elim (List.not_mem_nil member)

private def beaconEntryLadderIn (ca : Adr) :
    AccountingLadderAdmittedIn HistFork beaconSpec ca beaconFrameEntryRules where
  carrier := entryCarrierIn HistFork ca beaconSem beaconFrameEntryRules depositEntryInv
  append := EntryReplayIn.append HistFork ca beaconSem beaconFrameEntryRules depositEntryInv
  tag := fun _ _ => ()
  preserves := beaconSpec_preservesAdmittedIn_of_rules ca
  view := depositEntryObservation ca
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ :=
      Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (beaconEntry_coreIn ca pc sevm pre out run installed
      run committed fork installed admitted).2 entryBound

/-- The exact transaction replay derives the invariant at each retained deposit entry.
No per-frame invariant is supplied, and opaque target descendants are handled statically. -/
theorem transactionListIn_deposit_entryGood_of_rules
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntryRules)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat) :
    ∀ frame ∈ trace.settledFrames, frame.sevm.currentTarget = ca →
      Sevm.selector frame.sevm = BeaconDeposit.depositSelector →
      EntryGoodIn HistFork ca beaconSem beaconFrameEntryRules
        (fun storage => ∃ history, SolInv storage history) frame := by
  have initial : beaconSpec.StateInv ca benv.state :=
    ⟨by rw [installed]; rfl, trivial, ⟨initialHistory, invariant⟩⟩
  obtain ⟨frames, replay, observed⟩ :=
    (beaconEntryLadderIn ca).transactionListIn trace
      ((trace.freshFrameAdmitted ca).and admitted) initial notCreated sumNof fork
      fork.stateGas_none beaconInstalledCertH rfl blockIndex
  have good := (replay ⟨initialHistory, invariant⟩).2
  change frames = trace.settledFrames.flatMap (depositEntryObservation ca).frameObs at observed
  intro frame member target selected
  apply good frame
  rw [observed]
  apply List.mem_flatMap.mpr
  refine ⟨frame, member, ?_⟩
  change frame ∈ (if frame.sevm.currentTarget = ca ∧
    Sevm.selector frame.sevm = BeaconDeposit.depositSelector then [frame] else [])
  rw [ite_eq_left ⟨target, selected⟩]
  exact List.mem_singleton.mpr rfl

/-- A derived successful target entry produces its actual one-event log suffix. -/
theorem depositEntry_log_appendH_of_rules {ca : Adr} {frame : Exec.Frame}
    (good : EntryGoodIn HistFork ca beaconSem beaconFrameEntryRules
      (fun storage => ∃ history, SolInv storage history) frame)
    (target : frame.sevm.currentTarget = ca)
    (selected : Sevm.selector frame.sevm = BeaconDeposit.depositSelector) :
    ∃ log : Log, log.address = ca ∧ frame.post.logs = frame.pre.logs ++ [log] := by
  rcases frame with ⟨pc, sevm, pre, out, run, committed⟩
  cases out with
  | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    rcases good with ⟨pcZero, fork, installed, ⟨⟨stack, memory⟩, calldata, nodeleg, warm⟩,
      history, invariant⟩
    change pc = 0 at pcZero
    subst pc
    have hcode : sevm.code = code := bytes_eq_of_image (installed.2 target).1
    have sha : ShaReadyRules sevm pre :=
      ⟨nodeleg, warm, isPrecomp_two_hist fork, fork.stateGas_none, fork.bal_none⟩
    have invariantTarget : SolInv (Devm.getStor pre sevm.currentTarget) history := by
      rw [target]
      exact invariant
    obtain ⟨_, s', event, _, _, _, _, _, logs⟩ :=
      (deposit_frame_refinesH_of_rules hcode fork.stateGas_none fork.bal_none calldata
        stack memory sha invariantTarget run).1 selected
    refine ⟨BeaconDeposit.depositEventLog ca event, rfl, ?_⟩
    rw [target] at logs
    exact logs

/-- Every node extracted from the same retained transaction suffix has an actual
single-event append at its producing frame, using the derived entry invariant. -/
theorem transactionListIn_node_frame_log_of_rules
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntryRules)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames)
    {node : B256} (accepted : node ∈ committedFrameNodes ca frame) :
    ∃ log : Log, log.address = ca ∧ frame.post.logs = frame.pre.logs ++ [log] := by
  by_cases target : frame.sevm.currentTarget = ca
  · by_cases selected : Sevm.selector frame.sevm = BeaconDeposit.depositSelector
    · exact depositEntry_log_appendH_of_rules
        (transactionListIn_deposit_entryGood_of_rules trace admitted installed invariant notCreated
          sumNof fork blockIndex frame member target selected) target selected
    · simp only [committedFrameNodes, ite_eq_left target, frameAccepted,
        ite_eq_right selected, List.not_mem_nil] at accepted
  · simp only [committedFrameNodes, ite_eq_right target, List.not_mem_nil] at accepted

/-- Compatibility form retaining the original entry witness on the same actual roots. -/
theorem transactionListIn_deposit_entryGood
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat) :
    ∀ frame ∈ trace.settledFrames, frame.sevm.currentTarget = ca →
      Sevm.selector frame.sevm = BeaconDeposit.depositSelector →
      EntryGoodIn HistFork ca beaconSem beaconFrameEntry
        (fun storage => ∃ history, SolInv storage history) frame := by
  intro frame member target selected
  obtain ⟨pc, fork, atCode, _, invariant⟩ := transactionListIn_deposit_entryGood_of_rules
    trace (transactionListIn_beaconEntry_toRules trace admitted) installed invariant
    notCreated sumNof fork blockIndex frame member target selected
  have original := (trace.frameAdmitted_iff_rawFrames ca beaconFrameEntry).mp
    ((trace.freshFrameAdmitted ca).and admitted) _
    (trace.mem_rawFrames_of_mem_settledFrames frame member) target
  exact ⟨pc, fork, atCode, original, invariant⟩

/-- Compatibility form for the original entry witness. -/
theorem depositEntry_log_appendH {ca : Adr} {frame : Exec.Frame}
    (good : EntryGoodIn HistFork ca beaconSem beaconFrameEntry
      (fun storage => ∃ history, SolInv storage history) frame)
    (target : frame.sevm.currentTarget = ca)
    (selected : Sevm.selector frame.sevm = BeaconDeposit.depositSelector) :
    ∃ log : Log, log.address = ca ∧ frame.post.logs = frame.pre.logs ++ [log] := by
  rcases good with ⟨pc, fork, installed, entry, invariant⟩
  exact depositEntry_log_appendH_of_rules
    ⟨pc, fork, installed, beaconFrameEntry_toRules entry, invariant⟩ target selected

/-- Compatibility form for the original transaction admission. -/
theorem transactionListIn_node_frame_log
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {initialHistory : List B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : benv.state.getCode ca = code)
    (invariant : SolInv (benv.state.getStor ca) initialHistory)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (fork : HistFork benv.stat.fork) (blockIndex : Nat)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames)
    {node : B256} (accepted : node ∈ committedFrameNodes ca frame) :
    ∃ log : Log, log.address = ca ∧ frame.post.logs = frame.pre.logs ++ [log] :=
  transactionListIn_node_frame_log_of_rules trace
    (transactionListIn_beaconEntry_toRules trace admitted) installed invariant
    notCreated sumNof fork blockIndex member accepted

end Blanc.Lift.BeaconDeposit
