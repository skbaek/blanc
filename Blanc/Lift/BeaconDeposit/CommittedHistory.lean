import Blanc.Lift.BeaconDeposit.CommittedExec
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionAccountingCore

namespace Blanc.Lift.BeaconDeposit

open Jaune Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

private theorem target_replay {ca : Adr} {sevm : Sevm} {pre post : Devm}
    (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true)
    (hcode : sevm.code = code) (target : sevm.currentTarget = ca)
    (fork : CoveredFork sevm.benvStat.fork)
    (admitted : Exec.FrameAdmitted ca beaconFrameEntry run)
    (nodes : (Exec.committedFrames run).flatMap (committedFrameNodes ca) =
      frameAccepted sevm) :
    (sevm.isStatic = true →
      (Exec.committedFrames run).flatMap (committedFrameNodes ca) = []) ∧
    (sum pre.state.bal < 2 ^ 256 → ∃ steps,
      (depositCarrier ca).Replay ((depositCarrier ca).frameEntry sevm pre.state) steps
        ((depositCarrier ca).ofState (Execution.committedPost (.ok post) committed).state) ∧
      (depositObservation ca).obs steps =
        (Exec.committedFrames run).flatMap (committedFrameNodes ca)) := by
  obtain ⟨⟨stack, memory⟩, calldata, nodeleg, warm⟩ := admitted.root target
  refine ⟨?_, ?_⟩
  · intro static
    rw [nodes]
    exact frameAccepted_eq_nil_of_static hcode fork calldata stack memory static run
  · intro _
    refine ⟨frameAccepted sevm, ?_, nodes.symm⟩
    change DepositReplay (Devm.getStor pre ca) (frameAccepted sevm) (Devm.getStor post ca)
    intro history invariant
    have sha : ShaReady sevm pre := ⟨nodeleg, warm, isPrecomp_two fork, fork⟩
    rw [← target] at invariant ⊢
    exact frame_solInv hcode fork calldata stack memory sha invariant run

private theorem beacon_core (ca : Adr) :
    Exec.Fa (Exec.WknSem ca beaconSem
      (fun pc s d e _ => Blanc.Exec.CoreAccounting ca beaconSem beaconFrameEntry
        (depositCarrier ca) (depositObservation ca) pc s d e)) := by
  apply Blanc.Exec.coreAccounting ca beaconSem beaconFrameEntry
    (depositCarrier ca) (depositObservation ca) DepositReplay.append (fun _ _ => ())
  · intro sevm state foreign
    rfl
  · intro frame foreign
    change committedFrameNodes ca frame = []
    simp only [committedFrameNodes, ite_eq_right foreign]
  · intro sevm pre post hcode target deeper run committed fork installed admitted
    apply target_replay run committed hcode target fork admitted
    apply target_committedFrameNodes run committed hcode target installed fork admitted
    intro pc s d out child childCommitted childFork depth childAt childAdmitted static
    exact (deeper pc s d out child depth childAt
      child childCommitted childFork childAt childAdmitted).1 static

private def beaconAccountingLadder (ca : Adr) :
    AccountingLadderAdmitted beaconSpec ca beaconFrameEntry where
  carrier := depositCarrier ca
  append := DepositReplay.append
  tag := fun _ _ => ()
  preserves := beaconSpec_preservesAdmitted ca
  view := depositObservation ca
  root := by
    intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed
      admitted ready _ fork bound
    obtain ⟨installed, entryBound⟩ :=
      Blanc.Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
    exact (beacon_core ca pc sevm pre out run installed
      run committed fork installed admitted).2 entryBound

/-- Every actual configured history extends precisely the initial history by
its ordered settlement-retained deposit nodes. Frame chaining is derived by
the replay of the interpreter and wrappers, rather than supplied separately. -/
theorem configuredHistory_solInv {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    SolInv (future.state.getStor ca) (initialHistory ++ committedNodes ca trace) := by
  have initial : beaconSpec.StateInv ca checkpoint.state :=
    ⟨by rw [installed]; rfl, trivial, ⟨initialHistory, invariant⟩⟩
  obtain ⟨nodes, replay, observed⟩ :=
    (beaconAccountingLadder ca).configuredHistory trace
      ((trace.freshFrameAdmitted ca).and admitted) initial
  change DepositReplay (checkpoint.state.getStor ca) nodes (future.state.getStor ca) at replay
  change nodes = committedNodes ca trace at observed
  rw [observed] at replay
  exact replay initialHistory invariant

/-- The final deployed count word is the length of the same exact history. -/
theorem configuredHistory_count {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    (future.state.getStor ca).get solCountSlot =
      Nat.toB256 (initialHistory ++ committedNodes ca trace).length ∧
      (initialHistory ++ committedNodes ca trace).length < 2 ^ 32 :=
  solCount_eq_of_solInv (configuredHistory_solInv trace admitted installed invariant)

/-- The final mixed root belongs to the same exact extracted node sequence. -/
theorem configuredHistory_root {ca : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca beaconEntry)
    (installed : checkpoint.state.getCode ca = code)
    (invariant : SolInv (checkpoint.state.getStor ca) initialHistory) :
    BeaconDeposit.Acc.root Bytes.sha256 (solAcc (future.state.getStor ca)) =
      BeaconDeposit.mixedRootOf Bytes.sha256 (initialHistory ++ committedNodes ca trace) :=
  BeaconDeposit.root_correct _ _ _
    (configuredHistory_solInv trace admitted installed invariant).2

/-- A deployed warm count read after the configured history returns precisely
the little-endian length of its initial history and committed deposits. -/
theorem configuredHistory_count_view {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (sevm : Sevm) (base : Devm) (G : Nat)
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted sevm.currentTarget beaconEntry)
    (installed : checkpoint.state.getCode sevm.currentTarget = code)
    (invariant : SolInv (checkpoint.state.getStor sevm.currentTarget) initialHistory)
    (state : base.state = future.state)
    (hcode : sevm.code = code)
    (dataLength : 4 ≤ sevm.data.length) (dataBound : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0)
    (selector : Sevm.selector sevm = BeaconDeposit.getDepositCountSelector)
    (fork : CoveredFork sevm.benvStat.fork)
    (warm : (⟨sevm.currentTarget, countSlot⟩ : Adr × B256) ∈ base.accessedStorageKeys) :
    ∃ memory, Nonempty (Exec 0 sevm
      (base.setMach ⟨[], Mem.empty, G + countGasWarm, base.stateGas⟩)
      (.ok ((base.setMach ⟨[Sevm.selector sevm], memory, G, base.stateGas⟩).withOutput
        (BeaconDeposit.abiDynamicBytesReturn (BeaconDeposit.le64
          (initialHistory ++ committedNodes sevm.currentTarget trace).length))))) := by
  apply get_deposit_count_warm_exec_history sevm base (future.state.getStor sevm.currentTarget)
    (initialHistory ++ committedNodes sevm.currentTarget trace) G hcode dataLength dataBound
    value selector fork warm
  · exact congrArg (fun world : State => world.getStor sevm.currentTarget) state
  · exact configuredHistory_solInv trace admitted installed invariant

/-- A deployed root read after the configured history returns the mixed root
of its initial history followed by its exact committed deposits. -/
theorem configuredHistory_root_view {cfg : ChainConfig}
    {checkpoint future : BlockChain} {initialHistory : List B256}
    (sevm : Sevm) (base : Devm) (G : Nat)
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted sevm.currentTarget beaconEntry)
    (installed : checkpoint.state.getCode sevm.currentTarget = code)
    (invariant : SolInv (checkpoint.state.getStor sevm.currentTarget) initialHistory)
    (state : base.state = future.state)
    (hcode : sevm.code = code)
    (dataLength : 4 ≤ sevm.data.length) (dataBound : sevm.data.length < 2 ^ 256)
    (value : sevm.value = 0)
    (selector : Sevm.selector sevm = BeaconDeposit.getDepositRootSelector)
    (fork : CoveredFork sevm.benvStat.fork)
    (nodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (warm : (2 : Adr) ∈ base.accessedAddresses)
    (depth : sevm.depth ≠ 0)
    (bound : G + rootViewGas sevm base
      (initialHistory ++ committedNodes sevm.currentTarget trace).length + 6000 < 2 ^ 256) :
    ∃ post, Nonempty (Exec 0 sevm
      (base.setMach ⟨[], Mem.empty, G + rootViewGas sevm base
        (initialHistory ++ committedNodes sevm.currentTarget trace).length, base.stateGas⟩)
      (.ok post)) ∧ post.gasLeft = G ∧
      post.output = (BeaconDeposit.mixedRootOf Bytes.sha256
        (initialHistory ++ committedNodes sevm.currentTarget trace)).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor base a) ∧ post.logs = base.logs := by
  apply get_deposit_root_exec_mixedRoot sevm base (future.state.getStor sevm.currentTarget)
    (initialHistory ++ committedNodes sevm.currentTarget trace) G hcode dataLength dataBound
    value selector fork
  · exact congrArg (fun world : State => world.getStor sevm.currentTarget) state
  · exact configuredHistory_solInv trace admitted installed invariant
  · exact nodeleg
  · exact warm
  · exact isPrecomp_two fork
  · exact depth
  · exact bound

end Blanc.Lift.BeaconDeposit
