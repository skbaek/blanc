import Blanc.Composition.ConsolidationRequestDrainInput
import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk
import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk
import Blanc.Composition.ConsolidationRequestPublicStorage
import Blanc.Lift.StaticOnlyFramesIn
import Blanc.ExecutionModelAccounting
import Blanc.ConcreteRunKept
import Blanc.TransactionForwardH
import Blanc.BlockForward
import Blanc.Lift.WithdrawalRequest.AmsterdamSystem
import Blanc.Lift.RequestSystem.CoveredCall
import Blanc.Lift.RequestSystem.Effects
import Blanc.ExecutionKeptConfigured
import Blanc.KeptCreateAvoid
import Blanc.SyntheticBpo2Envelope
import Blanc.Lift.WalkCost
import Blanc.StorageRefund
import Blanc.ExecutionKeptPreCalls

/-! A closed coded-SYSTEM history for the EIP-7251 FIFO exclusion.
The initial header is independent of the world; subsequent commitments are
constructed from the actual body outputs. -/

namespace Blanc.Composition.ConsolidationRequestDrainControl

open Jaune Blanc Blanc.Lift
open Blanc.Composition.ConsolidationRequestDrainInput
open Blanc.Lift.WithdrawalRequest.FloodTx (txD senderE txD_recoveredSender txD_intrinsic)

private theorem no_descendants {sevm : Sevm} {pre : Devm} {out : Execution}
    (code : sevm.code = beaconRootsCode ∨ sevm.code = historyStorageCode ∨
      sevm.code = withdrawalRequestCode ∨ sevm.code = consolidationRequestCode)
    (fork : CoveredFork sevm.benvStat.fork) (run : Exec 0 sevm pre out) :
    Exec.descendantFrames run = [] := by
  obtain ⟨c, checked, closed⟩ : ∃ c : Cert, Cert.check sevm.code c = true ∧
      ∀ f ∈ c.prog, f.execsSatisfy (fun _ => false) = true := by
    rcases code with code | code | code | code <;> rw [code]
    · exact ⟨SystemExecution.BeaconRoots.cert, SystemExecution.BeaconRoots.cert_check, by decide +kernel⟩
    · exact ⟨SystemExecution.HistoryStorage.cert, SystemExecution.HistoryStorage.cert_check, by decide +kernel⟩
    · exact ⟨WithdrawalRequest.cert, WithdrawalRequest.cert_check, by decide +kernel⟩
    · exact ⟨SystemExecution.ConsolidationRequest.cert, SystemExecution.ConsolidationRequest.cert_check, by decide +kernel⟩
  apply Exec.descendantFrames_eq_nil_of_noExec run
  intro node chain x inst
  obtain ⟨cursor, reachable, ok⟩ := cursor_of_parentPrefix_noStateGas
    checked rfl rfl fork.rules_stateGas_none chain
  have allowed := ok.execsSatisfy (cursor.execsSatisfy_of_reachable closed reachable) inst
  cases allowed

private def senderAcct (nonce : UInt64) : Acct :=
  { Acct.nil with nonce := nonce, bal := (2 ^ 100 : Nat).toB256 }
private def contracts : State :=
  ((((State.setPresent .empty systemAddress { Acct.nil with nonce := 1, code := callerCode }).setPresent
    beaconRootsAddress { Acct.nil with nonce := 1, code := beaconRootsCode }).setPresent
    historyStorageAddress { Acct.nil with nonce := 1, code := historyStorageCode }).setPresent
    withdrawalRequestPredeployAddress { Acct.nil with nonce := 1, code := withdrawalRequestCode }).setPresent
    consolidationRequestPredeployAddress
      { Acct.nil with nonce := 1, code := consolidationRequestCode, stor := Stor.empty.set 0 B256.max }
private def initial : State :=
  (contracts.setPresent senderE (senderAcct 2)).setPresent subSender (senderAcct 0)
private def parentHeader : Header :=
  { SyntheticBpo2Envelope.checkpointHeader .empty with gasLimit := 2 ^ 22, gasUsed := 2 ^ 21 }
private def parentBlock : Block :=
  { header := parentHeader, txs := [], wds := [], ommers := [] }
private def start : BlockChain := ⟨[parentBlock], initial, 1⟩
private def templateA : Header := { parentHeader with number := 1, timestamp := 1 }
private def inputA : Benv := initBenv .prague start
  (BlockForward.commitHeader Fork.prague.ruleSet parentBlock templateA initial .init)

private theorem initial_installed : SystemCodeInstalled initial := by
  intro p member
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> kernel_rfl
private theorem initial_system : initial.getCode systemAddress = callerCode := by kernel_rfl
private theorem initial_storage : initial.getStor consolidationRequestPredeployAddress =
    Stor.empty.set 0 B256.max := by kernel_rfl

private def beaconA : State := (SystemExecution.BeaconRoots.systemPost inputA).state
private def historyEnvA : Benv := inputA.withState beaconA
private def historyA : State := (SystemExecution.HistoryStorage.systemPost historyEnvA).state
private theorem beacon_callA :
    processUncheckedSystemTransaction inputA beaconRootsAddress inputA.stat.parentBeaconBlockRoot.toBytes =
      .ok (beaconA, systemCallOutput (SystemExecution.BeaconRoots.systemPost inputA)) :=
  (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputA) CoveredFork.prague (initial_installed _ List.mem_cons_self)).1
private theorem history_installedA : historyEnvA.state.getCode historyStorageAddress = historyStorageCode := by
  have foreign := (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputA) CoveredFork.prague (initial_installed _ List.mem_cons_self)).2.2
    historyStorageAddress (by decide)
  exact (congrArg Acct.code foreign).trans
    (initial_installed _ (List.mem_cons_of_mem _ List.mem_cons_self))
private theorem lastA : historyEnvA.stat.blockHashes.getLast? = some parentHeader.hash := rfl
private theorem history_callA :
    processUncheckedSystemTransaction historyEnvA historyStorageAddress parentHeader.hash.toBytes =
      .ok (historyA, systemCallOutput (SystemExecution.HistoryStorage.systemPost historyEnvA)) :=
  (SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnvA) (lastHash := parentHeader.hash) CoveredFork.prague history_installedA lastA).1
private theorem beacon_codesA (a : Adr) : beaconA.getCode a = initial.getCode a := by
  have effect := (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputA) CoveredFork.prague (initial_installed _ List.mem_cons_self)).2.1
  change (SystemExecution.BeaconRoots.systemPost inputA).state.getCode a = _
  rw [effect, State.getCode_setStorVal, State.getCode_setStorVal]
  rfl
private theorem history_codesA (a : Adr) : historyA.getCode a = initial.getCode a := by
  have effect := (SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnvA) (lastHash := parentHeader.hash) CoveredFork.prague history_installedA lastA).2.1
  change (SystemExecution.HistoryStorage.systemPost historyEnvA).state.getCode a = _
  rw [effect, State.getCode_setStorVal]
  exact beacon_codesA a
private theorem history_otherA {a : Adr}
    (notR : beaconRootsAddress ≠ a) (notH : historyStorageAddress ≠ a) :
    historyA.get a = initial.get a := by
  have afterR := (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputA) CoveredFork.prague (initial_installed _ List.mem_cons_self)).2.2 a notR
  have afterH := (SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnvA) (lastHash := parentHeader.hash) CoveredFork.prague history_installedA lastA).2.2 a notH
  exact afterH.trans afterR

private def txEnvA : Benv := inputA.withState historyA
private abbrev wPath := WithdrawalRequest.Amsterdam.sysPath
private def withdrawalA : State := RequestSystem.sysState wPath.shape historyA withdrawalRequestPredeployAddress
private def withdrawalOutA : MsgCallOutput :=
  systemCallOutput (wPath.coveredPost txEnvA withdrawalRequestPredeployAddress)
private def requestEnvA : Benv := txEnvA.withState withdrawalA
private def stateA : State := RequestSystem.sysState cSysShape withdrawalA consolidationRequestPredeployAddress
private theorem withdrawal_installedA : txEnvA.state.getCode withdrawalRequestPredeployAddress =
    withdrawalRequestCode := (history_codesA _).trans
  (initial_installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
private theorem withdrawal_codesA (a : Adr) : withdrawalA.getCode a = initial.getCode a :=
  (RequestSystem.sysState_getCode wPath.shape historyA withdrawalRequestPredeployAddress a).trans
    (history_codesA a)
private theorem withdrawal_otherA {a : Adr} (notW : withdrawalRequestPredeployAddress ≠ a) :
    withdrawalA.get a = historyA.get a := by
  rw [State.get_eq_getD, State.get_eq_getD, withdrawalA,
    RequestSystem.sysState_getElem_ne wPath.shape historyA notW]
private theorem consolidation_installedA : requestEnvA.state.getCode consolidationRequestPredeployAddress =
    consolidationRequestCode := (withdrawal_codesA _).trans
  (initial_installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
private theorem withdrawal_callA : processCheckedSystemTransaction txEnvA withdrawalRequestPredeployAddress [] =
    .ok (withdrawalA, withdrawalOutA) := by
  exact (wPath.covered_call_spec WithdrawalRequest.Amsterdam.sysMemory CoveredFork.prague
    (by
      change (withdrawalRequestPredeployAddress, withdrawalRequestCode) ∈ systemContracts
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) withdrawal_installedA
    (B := 1000000) (by decide +kernel) (by decide)).1
private theorem history_storageW_A : historyA.getStor withdrawalRequestPredeployAddress = Stor.empty :=
  (congrArg Acct.stor (history_otherA (by decide) (by decide))).trans (by kernel_rfl)
private theorem withdrawal_output_empty {benv : Benv}
    (storage : benv.state.getStor withdrawalRequestPredeployAddress = Stor.empty) :
    (systemCallOutput (wPath.coveredPost benv withdrawalRequestPredeployAddress)).returnData = [] := by
  let s := initSevm (wPath.coveredMsg benv withdrawalRequestPredeployAddress)
  let b := initDevm (wPath.coveredMsg benv withdrawalRequestPredeployAddress)
  have count : wPath.count s b = 0 := by
    change RequestSystem.drainCount 16 ((benv.state.getStor withdrawalRequestPredeployAddress).get 2)
      ((benv.state.getStor withdrawalRequestPredeployAddress).get 3) = 0
    rw [storage]
    rfl
  change (wPath.coveredPost benv withdrawalRequestPredeployAddress).output = []
  change (wPath.framePostOn b (RequestSystem.coveredStores s)
    (systemTransactionGas - wPath.coveredCost benv withdrawalRequestPredeployAddress)).output = []
  rw [RequestSystem.SysPath.framePostOn, RequestSystem.chargedRetPost_output]
  change ((wPath.drain s b).memory.read 0 (wPath.shape.len.word * wPath.count s b).toNat).1 = []
  rw [count]
  rfl
private theorem withdrawal_outputA : withdrawalOutA.returnData = [] :=
  withdrawal_output_empty history_storageW_A
private theorem withdrawal_storageC_A : withdrawalA.getStor consolidationRequestPredeployAddress =
    Stor.empty.set 0 B256.max :=
  (RequestSystem.sysState_getStor_other wPath.shape historyA (by decide)).trans
    ((congrArg Acct.stor (history_otherA (by decide) (by decide))).trans initial_storage)
private theorem stateA_storage : stateA.getStor consolidationRequestPredeployAddress = Stor.empty := by
  rw [stateA, BuilderRequest.Delivery.sysState_getStor, withdrawal_storageC_A]
  kernel_rfl
private theorem stateA_senderE : stateA.get senderE = senderAcct 2 := by
  rw [State.get_eq_getD, stateA, RequestSystem.sysState_getElem_ne cSysShape withdrawalA (by decide),
    ← State.get_eq_getD, withdrawal_otherA (by decide), history_otherA (by decide) (by decide)]
  kernel_rfl
private theorem stateA_subSender : stateA.get subSender = senderAcct 0 := by
  rw [State.get_eq_getD, stateA, RequestSystem.sysState_getElem_ne cSysShape withdrawalA (by decide),
    ← State.get_eq_getD, withdrawal_otherA (by decide), history_otherA (by decide) (by decide)]
  kernel_rfl
private theorem stateA_system : stateA.getCode systemAddress = callerCode :=
  (RequestSystem.sysState_getCode cSysShape withdrawalA consolidationRequestPredeployAddress systemAddress).trans
    ((withdrawal_codesA systemAddress).trans initial_system)
private theorem stateA_installed : SystemCodeInstalled stateA := by
  intro p member
  exact (RequestSystem.sysState_getCode cSysShape withdrawalA consolidationRequestPredeployAddress p.1).trans
    ((withdrawal_codesA p.1).trans (initial_installed p member))

private theorem bodyA : ∃ out, applyBody inputA [] [] [] = .ok (stateA, out) ∧
    out.blockGasUsed = 0 ∧ out.requests = [] := by
  obtain ⟨outC, cRun, cError, cGas, cData⟩ := ConsolidationRequest.system_call_ok
    (benv := requestEnvA) CoveredFork.prague consolidation_installedA
  have cEmpty : outC.returnData = [] := by
    rw [cData]
    change ConsolidationRequest.drained (withdrawalA.getStor consolidationRequestPredeployAddress).get = []
    rw [withdrawal_storageC_A]
    rfl
  have txRun : applyTransactions ([] : List (Nat × Tx))
      ((inputA.withState beaconA).withState historyA) .init = .ok (txEnvA, .init) := rfl
  have parse : parseDepositRequests BlockOutput.init = .ok [] := rfl
  have body := BlockForward.applyBody_forward (benv := inputA) (txs := []) (ommers := [])
    CoveredFork.prague beacon_callA lastA history_callA rfl txRun parse withdrawal_callA cRun
  refine ⟨BlockForward.requestsOutput .init withdrawalOutA.returnData outC.returnData, body, rfl, ?_⟩
  rw [withdrawal_outputA, cEmpty]
  rfl

private theorem caller_prefix (s : Sevm) (b : Devm) :
    let sta : Sevm := { s with code := callerCode, benvStat := { s.benvStat with fork := .prague } }
    ConcreteRun.stepN 7 ⟨0, sta, b.setMach ⟨[], .empty, 1027576, b.stateGas⟩⟩ =
      some ⟨27, sta, b.setMach
        ⟨[(1027561 : Nat).toB256, consolidationRequestPredeployAddress.toBytes.toB256,
          0, 0, 0, 0, 0], .empty, 1027561, b.stateGas⟩⟩ := by
  have closed :
      (fun (s : Sevm) (b : Devm) =>
        let sta : Sevm := { s with code := callerCode, benvStat := { s.benvStat with fork := .prague } }
        ConcreteRun.stepN 7 ⟨0, sta, b.setMach ⟨[], .empty, 1027576, b.stateGas⟩⟩) =
      (fun (s : Sevm) (b : Devm) =>
        let sta : Sevm := { s with code := callerCode, benvStat := { s.benvStat with fork := .prague } }
        some (⟨27, sta, b.setMach
          ⟨[(1027561 : Nat).toB256, consolidationRequestPredeployAddress.toBytes.toB256,
            0, 0, 0, 0, 0], .empty, 1027561, b.stateGas⟩⟩ : Evm)) := by
    kernel_rfl
  exact congrFun (congrFun closed s) b

private theorem caller_exec {sevm : Sevm} {base : Devm}
    (hcode : sevm.code = callerCode) (hfork : sevm.benvStat.fork = .prague)
    (hsys : sevm.currentTarget = systemAddress) (hstatic : sevm.isStatic = false)
    (depth : sevm.depth ≠ 0)
    (hstack : base.stack = []) (hmem : base.memory = .empty) (hgas : base.gasLeft = 1027576)
    (herr : base.error = none) (href : 0 ≤ base.refundCounter)
    (installed : base.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    (horig : ∀ k, getOrigStorVal sevm consolidationRequestPredeployAddress k =
      base.getStorVal consolidationRequestPredeployAddress k) :
    let msg := callerChildMsg sevm base 1027561 consolidationRequestCode
    let child := consolidationChildPost msg
    let post := callerPost base 1027561 child
    ∃ run : Exec 0 sevm base (.ok post), ∃ f : Exec.Frame,
      Exec.keptAt consolidationRequestPredeployAddress run = [f] ∧
      f.sevm.caller = systemAddress ∧ f.sevm.currentTarget = consolidationRequestPredeployAddress ∧
      f.pc = 0 ∧ f.sevm.code = consolidationRequestCode ∧ f.pre.state = base.state ∧
      f.post.state = RequestSystem.sysState cSysShape base.state consolidationRequestPredeployAddress ∧
      post.error = none ∧ 0 ≤ post.refundCounter ∧
      post.state = RequestSystem.sysState cSysShape base.state consolidationRequestPredeployAddress ∧
      post.logs = base.logs ∧ post.output = base.output := by
  intro msg child post
  have fork : CoveredFork sevm.benvStat.fork := by rw [hfork]; exact CoveredFork.prague
  have affordable : accessCost consolidationRequestPredeployAddress base.accessedAddresses ≤ 1027561 :=
    (accessCost_le (x := consolidationRequestPredeployAddress) (a := base.accessedAddresses)).trans (by decide)
  have forwarded : 120000 ≤ SystemWordWriter.forwardedGas base consolidationRequestPredeployAddress 1027561 := by
    have bound := accessCost_le (x := consolidationRequestPredeployAddress) (a := base.accessedAddresses)
    change _ ≤ 2600 at bound
    unfold SystemWordWriter.forwardedGas except64th
    omega
  have facts := consolidation_child_exec fork hsys hstatic horig forwarded
  change exec (initEvm msg) = .ok child ∧ child.error = none ∧ 0 ≤ child.refundCounter ∧
    child.state = RequestSystem.sysState cSysShape base.state consolidationRequestPredeployAddress ∧
    child.logs = [] at facts
  obtain ⟨childRun⟩ := (exec_iff_exec_eq 0 (initSevm msg) (initDevm msg) (.ok child)).mpr facts.1
  have enter : (Frame.ofCall msg).enter = .run (initEvm msg) := by
    apply Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
    change sevm.benvStat.rules.isPrecomp consolidationRequestPredeployAddress = false
    unfold BenvStat.rules
    rw [hfork]
    decide
  have settle : (Frame.ofCall msg).settle (.ok child) = .ok child := by
    rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
    simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, facts.2.1,
      Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
      Devm.recordTouch_of_not_touchedSweep (show msg.benv.stat.rules.settle.touchedSweep = false from by
        change sevm.benvStat.rules.settle.touchedSweep = false
        unfold BenvStat.rules
        rw [hfork]
        rfl)]
  have resume : Resume.run (.call (callerParent base 1027561) 0 0)
      ((Frame.ofCall msg).settle (.ok child)) = .ok post := by
    rw [settle, Resume.run_call_ok (by rw [facts.2.1]; rfl) (by change 0 < 1024; decide)]
    rfl
  let callState := base.setMach
    ⟨[(1027561 : Nat).toB256, consolidationRequestPredeployAddress.toBytes.toB256,
      0, 0, 0, 0, 0], .empty, 1027561, base.stateGas⟩
  have callAt : Ninst.At sevm.code 27 (.exec .call) := by rw [hcode]; rfl
  have stopAt : sevm.code.getInst 28 = some (.last .stop) := by rw [hcode]; rfl
  have step : Evm.step ⟨27, sevm, callState⟩ =
      .spawn (Frame.ofCall msg) (.call (callerParent base 1027561) 0 0) 28 := by
    rw [Evm.step_next callAt]
    have nondelegated : getDelegatedCodeAddress consolidationRequestCode = none := by
      unfold getDelegatedCodeAddress
      apply ite_eq_right
      exact (systemContracts_facts _ ConsolidationRequest.member).2.1
    have spawned := caller_call_spawn fork depth (show (1027561 : Nat) < 2 ^ 256 from by decide)
      affordable installed nondelegated
    simp only [Ninst.step_exec, callState, spawned, XStep.toStep]
    rfl
  let tail : Exec 28 sevm post (.ok post) := .halt (Evm.step_last stopAt)
  let run : Exec 27 sevm callState (.ok post) := .runOk step enter childRun resume tail
  have staEq : { sevm with code := callerCode, benvStat := { sevm.benvStat with fork := .prague } } = sevm := by
    rw [← hcode, ← hfork]
  have pre := caller_prefix sevm base
  dsimp only at pre
  rw [staEq] at pre
  have baseEq : base.setMach ⟨[], .empty, 1027576, base.stateGas⟩ = base := by
    rw [← hgas]
    exact (St.self (d := base) hstack hmem).symm
  rw [baseEq] at pre
  have rawCommit : Execution.commits (.ok child) = true := by
    change child.error.isNone = true
    rw [facts.2.1]
    rfl
  have committed : Frame.settlementCommits (Frame.ofCall msg) (.ok child) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits rawCommit
  have kept : Exec.keptAt consolidationRequestPredeployAddress run =
      [Exec.Frame.ofRun (pc := (initEvm msg).pc) (sevm := (initEvm msg).sta)
        (pre := (initEvm msg).dyna) childRun (Frame.raw_commits_of_settlementCommits committed)] := by
    rw [show Exec.keptAt consolidationRequestPredeployAddress run =
      Exec.Frame.ofRun (pc := (initEvm msg).pc) (sevm := (initEvm msg).sta)
        (pre := (initEvm msg).dyna) childRun (Frame.raw_commits_of_settlementCommits committed) :: Exec.keptAt consolidationRequestPredeployAddress tail from
        by
          simpa only [run] using (Exec.keptAt_settled_here (a := consolidationRequestPredeployAddress)
            (childEvm := initEvm msg) step enter childRun resume tail committed rfl)]
    simp only [tail, Exec.keptAt.eq_def]
  have final := callerPost_facts base 1027561 child
  refine ⟨ConcreteRun.Exec.ofStepN 7 pre run, Exec.Frame.ofRun (pc := (initEvm msg).pc) (sevm := (initEvm msg).sta)
        (pre := (initEvm msg).dyna) childRun (Frame.raw_commits_of_settlementCommits committed),
    ?_, hsys, rfl, rfl, rfl, rfl, facts.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ConcreteRun.Exec.keptAt_ofStepN consolidationRequestPredeployAddress 7 pre run).trans kept
  · exact final.2.2.2.1.trans herr
  · rw [show post.refundCounter = base.refundCounter + child.refundCounter from final.2.2.1]
    exact add_nonneg href facts.2.2.1
  · exact final.1.trans facts.2.2.2.1
  · exact final.2.1.trans (by rw [facts.2.2.2.2, List.append_nil])
  · exact final.2.2.2.2


private def config : ChainConfig := ChainConfig.single 1 .prague
private noncomputable def outputA : BlockOutput := Classical.choose bodyA
private theorem outputA_facts : applyBody inputA [] [] [] = .ok (stateA, outputA) ∧
    outputA.blockGasUsed = 0 ∧ outputA.requests = [] := Classical.choose_spec bodyA
private noncomputable def headerA : Header :=
  BlockForward.commitHeader Fork.prague.ruleSet parentBlock templateA stateA outputA
private noncomputable def blockA : Block := { header := headerA, txs := [], wds := [], ommers := [] }
private noncomputable def chainA : BlockChain := ⟨appendBlock start.blocks blockA, stateA, 1⟩
private noncomputable def runA : BodyRun := Classical.choose (exists_bodyRoots outputA_facts.1)
private theorem rootsA : BodyRoots inputA [] [] [] stateA outputA runA :=
  Classical.choose_spec (exists_bodyRoots outputA_facts.1)
private noncomputable def keptA : KeptBlock := ⟨start, blockA, .prague, outputA, runA⟩
private theorem inputA_headerA : initBenv .prague start headerA = inputA := by
  simpa only [headerA, inputA] using BlockForward.initBenv_commitHeader_body_eq .prague start
    Fork.prague.ruleSet parentBlock templateA stateA initial outputA BlockOutput.init
private theorem headerA_valid : validateHeader Fork.prague.ruleSet start headerA = .ok () := by
  apply BlockForward.commitHeader_ok CoveredFork.prague rfl rfl rfl
  · exact BlockForward.calculateBaseFeePerGas_unit (by decide) (by decide) (by decide) (by decide)
  · rfl
  · rw [outputA_facts.2.1]
    exact Nat.zero_le _
  · decide
  · rfl
  · rfl
private theorem stepA : KeptStep config keptA chainA := by
  have selected : config.forkAt blockA.header.number blockA.header.timestamp = .ok .prague :=
    ChainConfig.single_forkAt 1 .prague _ _
  refine ⟨?_, selected, Or.inl CoveredFork.prague, ?_⟩
  · apply BlockForward.stateTransitionUsing_forward rfl selected CoveredFork.prague headerA_valid rfl
    · change applyBody (initBenv .prague start headerA) [] [] [] = .ok (stateA, outputA)
      rw [inputA_headerA]
      exact outputA_facts.1
    all_goals rfl
  · change BodyRoots (initBenv .prague start headerA) [] [] [] stateA outputA runA
    rw [inputA_headerA]
    exact rootsA
private theorem activation_history : KeptHistory config start [keptA] chainA :=
  KeptHistory.step KeptHistory.refl stepA
private theorem stateA_storageW : stateA.getStor withdrawalRequestPredeployAddress = Stor.empty := by
  rw [stateA, RequestSystem.sysState_getStor_other cSysShape withdrawalA
    (by decide : consolidationRequestPredeployAddress ≠ withdrawalRequestPredeployAddress),
    withdrawalA, BuilderRequest.Delivery.sysState_getStor, history_storageW_A]
  kernel_rfl
private def templateB : Header := { parentHeader with number := 2, timestamp := 2 }
private noncomputable def inputB : Benv := initBenv .prague chainA
  (BlockForward.commitHeader Fork.prague.ruleSet blockA templateB stateA .init)

private noncomputable def beaconB : State := (SystemExecution.BeaconRoots.systemPost inputB).state
private noncomputable def historyEnvB : Benv := inputB.withState beaconB
private noncomputable def historyB : State := (SystemExecution.HistoryStorage.systemPost historyEnvB).state
private theorem beacon_callB :
    processUncheckedSystemTransaction inputB beaconRootsAddress inputB.stat.parentBeaconBlockRoot.toBytes =
      .ok (beaconB, systemCallOutput (SystemExecution.BeaconRoots.systemPost inputB)) :=
  (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputB) CoveredFork.prague (stateA_installed _ List.mem_cons_self)).1
private theorem history_installedB : historyEnvB.state.getCode historyStorageAddress = historyStorageCode := by
  have foreign := (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputB) CoveredFork.prague (stateA_installed _ List.mem_cons_self)).2.2
    historyStorageAddress (by decide)
  exact (congrArg Acct.code foreign).trans
    (stateA_installed _ (List.mem_cons_of_mem _ List.mem_cons_self))
private theorem lastB : historyEnvB.stat.blockHashes.getLast? = some headerA.hash := rfl
private theorem history_callB :
    processUncheckedSystemTransaction historyEnvB historyStorageAddress headerA.hash.toBytes =
      .ok (historyB, systemCallOutput (SystemExecution.HistoryStorage.systemPost historyEnvB)) :=
  (SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnvB) (lastHash := headerA.hash) CoveredFork.prague history_installedB lastB).1
private theorem history_codesB (a : Adr) : historyB.getCode a = stateA.getCode a := by
  have afterR := (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputB) CoveredFork.prague (stateA_installed _ List.mem_cons_self)).2.1
  have afterH := (SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnvB) (lastHash := headerA.hash) CoveredFork.prague history_installedB lastB).2.1
  change (SystemExecution.HistoryStorage.systemPost historyEnvB).state.getCode a = _
  rw [afterH, State.getCode_setStorVal]
  change (SystemExecution.BeaconRoots.systemPost inputB).state.getCode a = _
  rw [afterR, State.getCode_setStorVal, State.getCode_setStorVal]
  rfl
private theorem history_otherB {a : Adr}
    (notR : beaconRootsAddress ≠ a) (notH : historyStorageAddress ≠ a) :
    historyB.get a = stateA.get a := by
  have afterR := (SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := inputB) CoveredFork.prague (stateA_installed _ List.mem_cons_self)).2.2 a notR
  have afterH := (SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnvB) (lastHash := headerA.hash) CoveredFork.prague history_installedB lastB).2.2 a notH
  exact afterH.trans afterR
private theorem history_storageC_B : historyB.getStor consolidationRequestPredeployAddress = Stor.empty :=
  (congrArg Acct.stor (history_otherB (by decide) (by decide))).trans stateA_storage
private theorem history_storageW_B : historyB.getStor withdrawalRequestPredeployAddress = Stor.empty :=
  (congrArg Acct.stor (history_otherB (by decide) (by decide))).trans stateA_storageW
private theorem history_senderE_B : historyB.get senderE = senderAcct 2 :=
  (history_otherB (by decide) (by decide)).trans stateA_senderE
private theorem history_subSender_B : historyB.get subSender = senderAcct 0 :=
  (history_otherB (by decide) (by decide)).trans stateA_subSender
private theorem history_systemB : historyB.getCode systemAddress = callerCode :=
  (history_codesB _).trans stateA_system
private theorem history_installed_allB : SystemCodeInstalled historyB :=
  fun p member => (history_codesB _).trans (stateA_installed p member)
private noncomputable def txEnvB : Benv := inputB.withState historyB

open Blanc.Lift.ConsolidationRequest
open Blanc.ExecutionTrace

private theorem submission_gas_bound (sevm : Sevm) (b : Devm) :
    submissionGas sevm b Mem.empty 1 ≤ 150000 := by
  have word : (Mem.empty.write 0 (sourceWord sevm).toBytes).size = 32 := by
    rw [Mem.size_write_of_length (len := 32) (B256.length_toBytes _) (by decide)]
    rfl
  have length : (sevm.data.sliceD 0 96 0).length = 96 := List.length_sliceD _ _ _ _
  have copied : (copyMemory sevm Mem.empty).size = 128 := by
    rw [copyMemory, Mem.size_write_of_length length (by decide), word]
    rfl
  have source : sourceGas Mem.empty ≤ 6 := by decide
  have copy : ConsolidationRequest.copyGas (Mem.empty.write 0 (sourceWord sevm).toBytes) ≤ 21 := by
    unfold ConsolidationRequest.copyGas
    rw [word]
    decide
  have logged : log0Gas (copyMemory sevm Mem.empty) 116 ≤ 1303 := by
    unfold log0Gas
    rw [copied]
    decide
  rw [← Blanc.Composition.ConsolidationRequestPublic.submissionCharge_eq]
  unfold Blanc.Composition.ConsolidationRequestPublic.submissionCharge
    Blanc.Composition.ConsolidationRequestPublic.submissionReads
    Blanc.Composition.ConsolidationRequestPublic.submissionStores recordWritesGas
  dsimp only
  xcost [source, copy, logged]
private theorem submission_exec {sevm : Sevm} {base : Devm}
    (code : sevm.code = consolidationRequestCode) (fork : sevm.benvStat.fork = .prague)
    (caller : sevm.caller ≠ systemAddress) (data : sevm.data.length = 96)
    (value : 1 ≤ sevm.value.toNat) (dynamic : sevm.isStatic = false)
    (stack : base.stack = []) (memory : base.memory = Mem.empty) (gas : base.gasLeft = 1026040)
    (error : base.error = none) (refund : 0 ≤ base.refundCounter)
    (zero : base.getStorVal sevm.currentTarget 0 = 0)
    (original : ∀ k, getOrigStorVal sevm sevm.currentTarget k = 0) :
    ∃ post, Nonempty (Exec 0 sevm base (.ok post)) ∧ post.error = none ∧
      0 ≤ post.refundCounter ∧ post.accountsToDelete = base.accountsToDelete ∧
      ConsolidationRequest.SubmissionEffects sevm base post ∧
      (∀ a, post.state.getCode a = base.state.getCode a) ∧
      (∀ a, sevm.currentTarget ≠ a → post.state.get a = base.state.get a) := by
  let slack := 1026040 - submissionGas sevm base Mem.empty 1
  have cost := submission_gas_bound sevm base
  have slackEnough : gCallStipend < slack := by unfold slack; change 2300 < _; omega
  have enough : submissionGas sevm base Mem.empty 1 ≤ 1026040 := by omega
  have charge : slack + submissionGas sevm base Mem.empty 1 = 1026040 := Nat.sub_add_cancel enough
  have covered : CoveredFork sevm.benvStat.fork := by rw [fork]; exact .prague
  obtain ⟨run⟩ := exec_submission_witness (b := base) (M := Mem.empty) (G := slack)
    code covered caller data value dynamic slackEnough zero
  rw [charge, ← gas, ← St.self stack memory] at run
  let post := submissionPost sevm (afterSload sevm base 0) Mem.empty slack
  refine ⟨post, ⟨run⟩, ?_, ?_, ?_, submissionPost_effects data Mem.wf_empty slack, ?_, ?_⟩
  · have logError : ∀ d l, (Devm.addLog d l).error = d.error := fun _ _ => rfl
    simp only [post, submissionPost, St_error, submissionBase, afterSstore_error, logged,
      logError, recordsWritten, recordStore, tailRead, afterSload_error, countStore, error]
  · have writes (d : Devm) (key value : B256) :
        d.refundCounter ≤ (afterSstore sevm d key value).refundCounter :=
      afterSstore_refundCounter_ge_of_safe sevm d key value
        (Or.inr (Or.inl (actualOrigStorVal_eq_zero_of_raw (original key))))
    let b := afterSload sevm base 0
    let key := submissionKey (tailWord sevm b)
    let d0 := tailRead sevm b
    let d1 := afterSstore sevm d0 key sevm.caller.toB256
    let d2 := afterSstore sevm d1 (1 + key) (Sevm.dataWord sevm 0)
    let d3 := afterSstore sevm d2 (1 + (1 + key)) (Sevm.dataWord sevm 32)
    let d4 := afterSstore sevm d3 (1 + (1 + (1 + key))) (Sevm.dataWord sevm 64)
    have count := writes (afterSload sevm b 1) 1 (1 + countWord sevm b)
    rw [afterSload_refundCounter] at count
    have start : 0 ≤ d0.refundCounter := by
      change 0 ≤ (tailRead sevm b).refundCounter
      rw [tailRead, afterSload_refundCounter]
      have initial : 0 ≤ b.refundCounter := by
        simpa only [b, afterSload_refundCounter] using refund
      exact initial.trans count
    have record : 0 ≤ d4.refundCounter :=
      (((start.trans (writes d0 key sevm.caller.toB256)).trans
        (writes d1 (1 + key) (Sevm.dataWord sevm 0))).trans
        (writes d2 (1 + (1 + key)) (Sevm.dataWord sevm 32))).trans
        (writes d3 (1 + (1 + (1 + key))) (Sevm.dataWord sevm 64))
    have machRefund : ∀ d : Devm,
        (St d [] (submissionMemory sevm Mem.empty) slack).refundCounter = d.refundCounter := fun _ => rfl
    dsimp only [post]
    have recordIdentity : recordsWritten sevm (afterSload sevm base 0) = d4 := rfl
    rw [submissionPost, machRefund, submissionBase, logged, recordIdentity]
    have tail := writes (d4.addLog (submissionLog sevm Mem.empty)) 3 (1 + tailWord sevm b)
    have logRefund : ∀ (d : Devm) l, (d.addLog l).refundCounter = d.refundCounter := fun _ _ => rfl
    rw [logRefund] at tail
    exact record.trans tail
  · have mach : ∀ d : Devm,
        (St d [] (submissionMemory sevm Mem.empty) slack).accountsToDelete = d.accountsToDelete := fun _ => rfl
    have logDelete : ∀ d l, (Devm.addLog d l).accountsToDelete = d.accountsToDelete := fun _ _ => rfl
    simp only [post, submissionPost, mach, submissionBase, afterSstore_accountsToDelete,
      logged, logDelete, recordsWritten, recordStore, tailRead, afterSload_accountsToDelete,
      countStore]
  · intro a
    dsimp only [post]
    rw [submissionPost, St_state, submissionBase_state]
    simp only [State.getCode_setStorVal]
  · intro a away
    dsimp only [post]
    rw [submissionPost, St_state, submissionBase_state]
    simp only [State.get_setStorVal_ne _ _ _ away]

private theorem submission_message_run {benv : Benv} {debit : State} {msg : Msg} {after : Benv}
    (fork : benv.stat.fork = .prague)
    (code : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode)
    (storage : benv.state.getStor consolidationRequestPredeployAddress = Stor.empty)
    (debited : (benv.state.incrNonce subSender).subBal subSender (2 ^ 21 : Nat).toB256 = some debit)
    (prepared : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction txSub 0 subSender 2 22536 []) txSub = .ok msg)
    (transferred : msg.benvAfterTransfer = .ok after) :
    ∃ post, Nonempty (Exec 0 (initSevm (msg.withBenv after)) (initDevm (msg.withBenv after)) (.ok post)) ∧
      post.error = none ∧ 0 ≤ post.refundCounter ∧ post.accountsToDelete = .emptyWithCapacity ∧
      ConsolidationRequest.SubmissionEffects (initSevm (msg.withBenv after))
        (initDevm (msg.withBenv after)) post ∧
      (∀ a, post.state.getCode a = after.state.getCode a) ∧
      (∀ a, consolidationRequestPredeployAddress ≠ a → post.state.get a = after.state.get a) := by
  have prepare := prepareMessage_call (benv := { benv.beginTransaction with state := debit })
    (tenv := transactionTenv benv.beginTransaction txSub 0 subSender 2 22536 []) (tx := txSub) rfl
  rw [prepare] at prepared
  cases prepared
  have debitCode : debit.getCode consolidationRequestPredeployAddress = consolidationRequestCode := by
    rw [State.subBal_getCode debited]
    change ((benv.state.incrNonce subSender).get consolidationRequestPredeployAddress).code = _
    rw [State.incrNonce_get_code]
    exact code
  have debitStorage : debit.getStor consolidationRequestPredeployAddress = Stor.empty := by
    obtain ⟨_, same⟩ := State.of_subBal debited
    rw [same]
    change (((benv.state.incrNonce subSender).setBal subSender _).get
      consolidationRequestPredeployAddress).stor = _
    rw [State.setBal_get_ne (by decide : subSender ≠ consolidationRequestPredeployAddress),
      State.incrNonce_get_stor, ite_eq_right (by
        rintro ⟨same, _⟩
        exact subSender_distinct.2.2.2.2.2.2 same)]
    exact storage
  have stat := benvAfterTransfer_stat transferred
  let m := (callMessage { benv.beginTransaction with state := debit }
    (transactionTenv benv.beginTransaction txSub 0 subSender 2 22536 []) txSub
      consolidationRequestPredeployAddress).withBenv after
  have fork' : (initSevm m).benvStat.fork = .prague := by
    change after.stat.fork = .prague
    rw [stat]
    exact fork
  have current : Devm.getStor (initDevm m) consolidationRequestPredeployAddress = Stor.empty := by
    have preserved :=  benvAfterTransfer_ok_getStor transferred consolidationRequestPredeployAddress
      (Or.inr (Or.inr (by
        change (debit.getCode consolidationRequestPredeployAddress).size ≠ 0
        rw [debitCode, ByteArray.size_eq_length_toList]
        exact fun h => ConsolidationRequest.linked.runnable.1 (List.length_eq_zero_iff.mp h))))
    exact preserved.trans debitStorage
  have original : ∀ k, getOrigStorVal (initSevm m) consolidationRequestPredeployAddress k = 0 := by
    intro k
    change (after.stat.origState.getStor consolidationRequestPredeployAddress).get k = 0
    rw [stat]
    change (benv.state.getStor consolidationRequestPredeployAddress).get k = 0
    rw [storage]
    rfl
  have slot0 : (initDevm m).getStorVal (initSevm m).currentTarget 0 = 0 := by
    change (Devm.getStor (initDevm m) consolidationRequestPredeployAddress).get 0 = 0
    rw [current]
    rfl
  obtain ⟨post, run, error, refund, deletes, effects, codes, foreign⟩ := submission_exec (base := initDevm m)
    (sevm := initSevm m) debitCode fork' subSender_distinct.2.2.1 payload96_length
    (by change 1 ≤ (1 : B256).toNat; decide) rfl rfl rfl rfl rfl
    (by change (0 : Int) ≤ 0; omega) slot0 original
  exact ⟨post, run, error, refund, deletes, effects, codes, foreign⟩

private noncomputable def subDebit : State :=
  (txEnvB.state.incrNonce subSender).setBal subSender
    ((2 ^ 100 : Nat).toB256 - (2 ^ 21 : Nat).toB256)
private theorem sub_debit :
    (txEnvB.state.incrNonce subSender).subBal subSender (2 ^ 21 : Nat).toB256 = some subDebit := by
  have balance : txEnvB.state.bal subSender = (2 ^ 100 : Nat).toB256 := by
    change (historyB.get subSender).bal = _
    rw [history_subSender_B]
    rfl
  have affordable : (2 ^ 21 : Nat).toB256 ≤ txEnvB.state.bal subSender := by
    rw [balance]
    decide
  simpa only [balance, subDebit] using subBal_incrNonce_of_le affordable
private noncomputable def subMsg : Msg :=
  callMessage { txEnvB.beginTransaction with state := subDebit }
    (transactionTenv txEnvB.beginTransaction txSub 0 subSender 2 22536 []) txSub
      consolidationRequestPredeployAddress
private theorem sub_prepared :
    prepareMessage { txEnvB.beginTransaction with state := subDebit }
      (transactionTenv txEnvB.beginTransaction txSub 0 subSender 2 22536 []) txSub = .ok subMsg :=
  prepareMessage_call rfl
private theorem sub_after_exists : ∃ after, subMsg.benvAfterTransfer = .ok after := by
  have affordable : ¬ subMsg.benv.state.bal subMsg.caller < subMsg.value := by
    change ¬ subDebit.bal subSender < (1 : B256)
    unfold subDebit State.bal
    rw [State.setBal_get_self, Acct.clearIfEmpty_bal]
    change ¬ ((2 ^ 100 : Nat).toB256 - (2 ^ 21 : Nat).toB256) < (1 : B256)
    decide
  obtain ⟨_, _, transferred⟩ := Msg.benvAfterTransfer_of_affordable subMsg rfl affordable
    (by change (1 : B256) ≠ 0; decide)
  exact ⟨_, transferred⟩
private noncomputable def subAfter : Benv := Classical.choose sub_after_exists
private theorem sub_transferred : subMsg.benvAfterTransfer = .ok subAfter :=
  Classical.choose_spec sub_after_exists
private theorem sub_code : subMsg.code = consolidationRequestCode := by
  change subDebit.getCode consolidationRequestPredeployAddress = _
  rw [subDebit, State.setBal_getCode]
  change ((txEnvB.state.incrNonce subSender).get consolidationRequestPredeployAddress).code = _
  rw [State.incrNonce_get_code]
  exact history_installed_allB _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
private theorem sub_runtime_exists :
    ∃ post, Nonempty (Exec 0 (initSevm (subMsg.withBenv subAfter))
      (initDevm (subMsg.withBenv subAfter)) (.ok post)) ∧
      post.error = none ∧ 0 ≤ post.refundCounter ∧ post.accountsToDelete = .emptyWithCapacity ∧
      ConsolidationRequest.SubmissionEffects (initSevm (subMsg.withBenv subAfter))
        (initDevm (subMsg.withBenv subAfter)) post ∧
      (∀ a, post.state.getCode a = subAfter.state.getCode a) ∧
      (∀ a, consolidationRequestPredeployAddress ≠ a → post.state.get a = subAfter.state.get a) :=
  submission_message_run rfl
    (history_installed_allB _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
    history_storageC_B sub_debit sub_prepared sub_transferred
private noncomputable def subPost : Devm := Classical.choose sub_runtime_exists
private theorem sub_facts :
    Nonempty (Exec 0 (initSevm (subMsg.withBenv subAfter))
      (initDevm (subMsg.withBenv subAfter)) (.ok subPost)) ∧
      subPost.error = none ∧ 0 ≤ subPost.refundCounter ∧ subPost.accountsToDelete = .emptyWithCapacity ∧
      ConsolidationRequest.SubmissionEffects (initSevm (subMsg.withBenv subAfter))
        (initDevm (subMsg.withBenv subAfter)) subPost ∧
      (∀ a, subPost.state.getCode a = subAfter.state.getCode a) ∧
      (∀ a, consolidationRequestPredeployAddress ≠ a → subPost.state.get a = subAfter.state.get a) := Classical.choose_spec sub_runtime_exists
private noncomputable def subRun : Exec (initEvm (subMsg.withBenv subAfter)).pc
    (initEvm (subMsg.withBenv subAfter)).sta (initEvm (subMsg.withBenv subAfter)).dyna
    (.ok subPost) := Classical.choice sub_facts.1
private theorem sub_exec : exec (initEvm (subMsg.withBenv subAfter)) = .ok subPost :=
  (exec_iff_exec_eq _ _ _ _).mp ⟨subRun⟩
private theorem sub_nodelegated : getDelegatedCodeAddress subMsg.code = none := by
  rw [sub_code]
  obtain ⟨_, nondelegating, _⟩ := systemContracts_facts _ ConsolidationRequest.member
  unfold getDelegatedCodeAddress
  exact ite_eq_right nondelegating
private noncomputable def subMessageOut : MsgCallOutput :=
  { gasLeft := subPost.gasLeft, refundCounter := ((0 + subPost.refundCounter.toNat : Nat) : Int)
    logs := subPost.logs, accountsToDelete := subPost.accountsToDelete
    error := none, returnData := subPost.output, touchedAccounts := subPost.meta.touchedAccounts }
private theorem sub_message : processMessageCall subMsg = .ok (subPost.state, subMessageOut) := by
  apply processMessageCall_call_of_message rfl rfl rfl sub_nodelegated
  · exact processMessage_call_of_exec sub_transferred rfl
      (by change pragueRules.isPrecomp consolidationRequestPredeployAddress = false; decide)
      sub_exec sub_facts.2.1 rfl
  · exact sub_facts.2.1
  · exact Int.toNat?_eq_some_of_nonneg sub_facts.2.2.1

private theorem sub_valid : validateTransaction txEnvB.stat.rules txSub 0 = .ok (22536, 24840) :=
  validateTransaction_ok_of_facts rfl (txSub_intrinsic 0) (by decide) (by decide) rfl rfl
private theorem sub_sender : txEnvB.beginTransaction.state.get subSender = senderAcct 0 :=
  history_subSender_B
private theorem sub_checked : checkTransaction txEnvB.beginTransaction
    (transactionPreludeBout .init txSub 0) txSub = .ok (subSender, 2, [], 0) := by
  apply checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
  · exact checkTransactionGasLimits_ok_of_room rfl
      (by change 2 ^ 20 ≤ 2 ^ 22; decide) (by change 0 ≤ _; exact Nat.zero_le _)
  · exact checkTransactionChainId_two rfl rfl
  · exact txSub_recoveredSender
  · exact checkTransactionGasFee_two (benv := txEnvB.beginTransaction) (tx := txSub)
      (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by change 1 ≤ 8; decide) (by decide)
  · exact checkTransactionBlobData_two rfl _
  · exact checkTransactionReceiver_two rfl
  · exact checkTransactionAuthorizationList_two rfl
  · rw [sub_sender]
    exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl
private theorem sub_transaction_debit :
    (txEnvB.state.incrNonce subSender).subBal subSender
      (txSub.gas * 2 + transactionBlobGasFee txEnvB txSub).toB256 = some subDebit := by
  rw [transactionBlobGasFee_two (show txSub.type = .two 1 1 8
    (some consolidationRequestPredeployAddress) [] from rfl), Nat.add_zero]
  exact sub_debit
private theorem sub_transaction_message : transactionMessage txEnvB .init txSub 0 = .ok (subSender, subMsg) := by
  have valid : validateTransaction txEnvB.beginTransaction.stat.rules txSub 0 = .ok (22536, 24840) := sub_valid
  have deb : (txEnvB.beginTransaction.state.incrNonce subSender).subBal subSender
      (txSub.gas * 2 + transactionBlobGasFee txEnvB.beginTransaction txSub).toB256 = some subDebit :=
    sub_transaction_debit
  have tenv : transactionTenvAt txEnvB.beginTransaction txSub 0 subSender 2 22536 [] =
      transactionTenv txEnvB.beginTransaction txSub 0 subSender 2 22536 [] := rfl
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none txSub rfl]
  simp only [valid, sub_checked, deb, Except.mapError, bind, Except.bind, Option.toExcept]
  rw [tenv, sub_prepared]

private theorem sub_enter : (Frame.ofCall subMsg).enter = .run (initEvm (subMsg.withBenv subAfter)) := by
  apply Frame.enter_run_of_nonprecompile sub_transferred rfl
  change subAfter.stat.rules.isPrecomp consolidationRequestPredeployAddress = false
  rw [benvAfterTransfer_stat sub_transferred]
  change pragueRules.isPrecomp consolidationRequestPredeployAddress = false
  decide
private theorem sub_resolved : messageCallExecutionMessage subMsg = subMsg := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  have nd : subMsg.benv.stat.rules.delegatedCodeAddress subMsg.code = none := by
    unfold ForkRules.delegatedCodeAddress
    rw [sub_nodelegated]
    split <;> rfl
  rw [nd]
private theorem sub_entry : messageEntry subMsg =
    some (Frame.ofCall subMsg, initEvm (subMsg.withBenv subAfter)) := by
  unfold messageEntry legacyEntry
  change (match messageCallDelegation subMsg with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none) = _
  have delegated : messageCallDelegation subMsg = .ok (subMsg, 0) := rfl
  rw [delegated]
  change enteredFrame (Frame.ofCall (messageCallExecutionMessage subMsg)) = _
  rw [sub_resolved]
  unfold enteredFrame
  rw [sub_enter]
private noncomputable def subRoot : Root :=
  ⟨Frame.ofCall subMsg, initEvm (subMsg.withBenv subAfter), .ok subPost, subRun⟩
private theorem sub_commits : Execution.commits (.ok subPost : Execution) = true := by
  change subPost.error.isNone = true
  rw [sub_facts.2.1]
  rfl
private noncomputable def subFrame : Exec.Frame :=
  Exec.Frame.ofRun (pc := (initEvm (subMsg.withBenv subAfter)).pc)
    (sevm := (initEvm (subMsg.withBenv subAfter)).sta)
    (pre := (initEvm (subMsg.withBenv subAfter)).dyna) subRun sub_commits
private theorem sub_root_retained : Root.keptAt consolidationRequestPredeployAddress subRoot = [subFrame] := by
  have settles : Frame.settlementCommits (Frame.ofCall subMsg) (.ok subPost) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits sub_commits
  dsimp only [subRoot, Root.keptAt]
  rw [dite_eq_left settles, ite_eq_left (show (initEvm (subMsg.withBenv subAfter)).sta.currentTarget =
    consolidationRequestPredeployAddress from rfl)]
  rfl
private theorem sub_message_roots : MessageRoots subMsg subPost.state subMessageOut [subRoot] := by
  refine ⟨sub_message, ?_⟩
  rw [sub_entry]
  rfl
private theorem sub_transaction_roots : ∃ st bout,
    TransactionRoots txEnvB .init txSub 0 st bout subSender [subRoot] ∧
    bout.blockGasUsed ≤ 2 ^ 20 ∧ bout.receiptKeys = [BLT.toBytes (.bytes (0 : Nat).toBytes)] ∧
    bout.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? =
      some (makeReceipt txSub none bout.cumulativeGasUsed subPost.logs) ∧
    ∃ refund tip, st = (subPost.state.addBal subSender refund).addBal 0 tip := by
  have refund : Int.toNat? subMessageOut.refundCounter = some subPost.refundCounter.toNat := by
    change Int.toNat? ((0 + subPost.refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (i := (subPost.refundCounter.toNat : Int)) (by omega)
  obtain ⟨bout, process, _, gas, keys, receipt⟩ := processTransaction_of_stages_receipts
    (bout := .init) (index := 0) rfl rfl rfl rfl sub_valid sub_checked sub_transaction_debit
      sub_prepared sub_message refund
  have emptyList : subMessageOut.accountsToDelete.toList = [] := by
    rw [show subMessageOut.accountsToDelete = .emptyWithCapacity from sub_facts.2.2.2.1]
    exact Std.HashSet.toList_emptyWithCapacity
  rw [emptyList, List.foldl_nil] at process
  refine ⟨_, bout, ⟨process, subMsg, subPost.state, subMessageOut,
    sub_transaction_message, sub_message_roots⟩, ?_, keys, receipt, _, _, rfl⟩
  rw [gas, show BlockOutput.init.blockGasUsed = 0 from rfl, Nat.zero_add]
  exact txGasUsed_le (gas := txSub.gas) (floor := 24840) (left := subMessageOut.gasLeft)
    (refund := subPost.refundCounter.toNat) (by decide)

private noncomputable def subState : State := Classical.choose sub_transaction_roots
private noncomputable def subOut : BlockOutput := Classical.choose (Classical.choose_spec sub_transaction_roots)
private theorem sub_roots : TransactionRoots txEnvB .init txSub 0 subState subOut subSender [subRoot] :=
  (Classical.choose_spec (Classical.choose_spec sub_transaction_roots)).1
private theorem sub_gas : subOut.blockGasUsed ≤ 2 ^ 20 :=
  (Classical.choose_spec (Classical.choose_spec sub_transaction_roots)).2.1
private theorem sub_world : ∃ refund tip,
    subState = (subPost.state.addBal subSender refund).addBal 0 tip :=
  (Classical.choose_spec (Classical.choose_spec sub_transaction_roots)).2.2.2.2
private theorem sub_after_other {a : Adr}
    (notSub : subSender ≠ a) (notC : consolidationRequestPredeployAddress ≠ a) :
    subAfter.state.get a = historyB.get a := by
  obtain ⟨mid, debit, after⟩ := of_benvAfterTransfer (msg := subMsg) rfl
    (by change (1 : B256) ≠ 0; decide) sub_transferred
  obtain ⟨_, middle⟩ := State.of_subBal debit
  rw [after]
  change (mid.addBal consolidationRequestPredeployAddress (1 : B256)).get a = _
  rw [State.addBal, State.setBal_get_ne notC, middle]
  change (subDebit.setBal subSender _).get a = _
  rw [State.setBal_get_ne notSub, subDebit, State.setBal_get_ne notSub]
  unfold State.incrNonce
  rw [State.setAccount_get_ne _ notSub]
  rfl
private theorem sub_state_other {a : Adr}
    (notSub : subSender ≠ a) (notC : consolidationRequestPredeployAddress ≠ a) (notZero : (0 : Adr) ≠ a) :
    subState.get a = historyB.get a := by
  obtain ⟨refund, tip, world⟩ := sub_world
  rw [world, State.addBal, State.setBal_get_ne notZero, State.addBal, State.setBal_get_ne notSub]
  exact (sub_facts.2.2.2.2.2.2 a notC).trans (sub_after_other notSub notC)
private theorem sub_state_senderE : subState.get senderE = senderAcct 2 :=
  (sub_state_other (by decide) (by decide) (by decide)).trans history_senderE_B
private theorem sub_state_storageW : subState.getStor withdrawalRequestPredeployAddress = Stor.empty :=
  (congrArg Acct.stor (sub_state_other (by decide) (by decide) (by decide))).trans history_storageW_B
private theorem sub_state_codes (a : Adr) : subState.getCode a = historyB.getCode a := by
  obtain ⟨refund, tip, world⟩ := sub_world
  rw [world, State.addBal_getCode, State.addBal_getCode, sub_facts.2.2.2.2.2.1 a,
    benvAfterTransfer_ok_getCode sub_transferred a]
  change subDebit.getCode a = _
  rw [subDebit, State.setBal_getCode]
  change ((txEnvB.state.incrNonce subSender).get a).code = _
  rw [State.incrNonce_get_code]
  rfl
private theorem sub_state_installed : SystemCodeInstalled subState :=
  fun p member => (sub_state_codes _).trans (history_installed_allB p member)
private theorem sub_state_system : subState.getCode systemAddress = callerCode :=
  (sub_state_codes _).trans history_systemB
private noncomputable def submittedStor : Stor :=
  ConsolidationRequest.submittedStorage (initSevm (subMsg.withBenv subAfter)) Stor.empty
private theorem sub_state_storageC : subState.getStor consolidationRequestPredeployAddress = submittedStor := by
  obtain ⟨refund, tip, world⟩ := sub_world
  rw [world]
  change (((subPost.state.addBal subSender refund).addBal 0 tip).get
    consolidationRequestPredeployAddress).stor = _
  rw [State.addBal, State.setBal_get_ne (by decide : (0 : Adr) ≠ consolidationRequestPredeployAddress),
    State.addBal, State.setBal_get_ne subSender_distinct.2.2.2.2.2.2]
  have effects := sub_facts.2.2.2.2.1.storage
  change subPost.getStor consolidationRequestPredeployAddress =
    ConsolidationRequest.submittedStorage (initSevm (subMsg.withBenv subAfter))
      (subAfter.state.getStor consolidationRequestPredeployAddress) at effects
  have current : subAfter.state.getStor consolidationRequestPredeployAddress = Stor.empty := by
    have protectedStore := benvAfterTransfer_ok_getStor sub_transferred consolidationRequestPredeployAddress
      (Or.inr (Or.inr (by
        change subMsg.code.size ≠ 0
        rw [sub_code, ByteArray.size_eq_length_toList]
        exact fun h => ConsolidationRequest.linked.runnable.1 (List.length_eq_zero_iff.mp h))))
    rw [protectedStore]
    change (subDebit.get consolidationRequestPredeployAddress).stor = _
    rw [subDebit, State.setBal_get_ne subSender_distinct.2.2.2.2.2.2,
      State.incrNonce_get_stor, ite_eq_right (by
        rintro ⟨same, _⟩
        exact subSender_distinct.2.2.2.2.2.2 same)]
    exact history_storageC_B
  rw [current] at effects
  exact effects
private theorem submitted_meta :
    (submittedStor.get 0, submittedStor.get 1, submittedStor.get 2, submittedStor.get 3) =
      (0, 1, 0, 1) := by
  obtain ⟨_, _, _, _, excess, count, head, tail⟩ :=
    ConsolidationRequest.submittedStorage_record (initSevm (subMsg.withBenv subAfter))
      (s := Stor.empty) (by change (0 : Nat) < 2 ^ 253; decide)
  change ((ConsolidationRequest.submittedStorage _ Stor.empty).get 0,
    (ConsolidationRequest.submittedStorage _ Stor.empty).get 1,
    (ConsolidationRequest.submittedStorage _ Stor.empty).get 2,
    (ConsolidationRequest.submittedStorage _ Stor.empty).get 3) = _
  rw [excess, count, head, tail]
  rfl
private noncomputable def drainEnv : Benv := txEnvB.withState subState

private noncomputable def drainDebit : State :=
  (drainEnv.state.incrNonce senderE).setBal senderE
    ((2 ^ 100 : Nat).toB256 - (2 ^ 21 : Nat).toB256)
private theorem drain_debit :
    (drainEnv.state.incrNonce senderE).subBal senderE (2 ^ 21 : Nat).toB256 = some drainDebit := by
  have balance : drainEnv.state.bal senderE = (2 ^ 100 : Nat).toB256 := by
    change (subState.get senderE).bal = _
    rw [sub_state_senderE]
    rfl
  have affordable : (2 ^ 21 : Nat).toB256 ≤ drainEnv.state.bal senderE := by
    rw [balance]
    decide
  simpa only [balance, drainDebit] using subBal_incrNonce_of_le affordable
private noncomputable def drainMsg : Msg :=
  callMessage { drainEnv.beginTransaction with state := drainDebit }
    (transactionTenv drainEnv.beginTransaction txD 1 senderE 2 21000 []) txD systemAddress
private noncomputable def drainBase : Devm := initDevm drainMsg
private noncomputable def drainSevm : Sevm := initSevm drainMsg
private noncomputable def drainChildMsg : Msg :=
  callerChildMsg drainSevm drainBase 1027561 consolidationRequestCode
private noncomputable def drainPost : Devm :=
  callerPost drainBase 1027561 (consolidationChildPost drainChildMsg)
private theorem drain_code (a : Adr) : drainDebit.getCode a = subState.getCode a := by
  rw [drainDebit, State.setBal_getCode]
  change ((drainEnv.state.incrNonce senderE).get a).code = _
  rw [State.incrNonce_get_code]
  rfl
private theorem drain_storageC : drainDebit.getStor consolidationRequestPredeployAddress =
    subState.getStor consolidationRequestPredeployAddress := by
  change (((drainEnv.state.incrNonce senderE).setBal senderE _).get
    consolidationRequestPredeployAddress).stor = _
  rw [State.setBal_get_ne (by decide : senderE ≠ consolidationRequestPredeployAddress),
    State.incrNonce_get_stor, ite_eq_right (by
      rintro ⟨same, _⟩
      exact (by decide : senderE ≠ consolidationRequestPredeployAddress) same)]
  rfl
private theorem drain_runtime_exists :
    ∃ run : Exec 0 drainSevm drainBase (.ok drainPost), ∃ f : Exec.Frame,
      Exec.keptAt consolidationRequestPredeployAddress run = [f] ∧
      f.sevm.caller = systemAddress ∧ f.sevm.currentTarget = consolidationRequestPredeployAddress ∧
      f.pc = 0 ∧ f.sevm.code = consolidationRequestCode ∧ f.pre.state = drainBase.state ∧
      f.post.state = RequestSystem.sysState cSysShape drainBase.state consolidationRequestPredeployAddress ∧
      drainPost.error = none ∧ 0 ≤ drainPost.refundCounter ∧
      drainPost.state = RequestSystem.sysState cSysShape drainBase.state consolidationRequestPredeployAddress ∧
      drainPost.logs = drainBase.logs ∧ drainPost.output = drainBase.output := by
  apply caller_exec (sevm := drainSevm) (base := drainBase)
  · exact (drain_code systemAddress).trans sub_state_system
  · rfl
  · rfl
  · rfl
  · change (1024 : Nat) ≠ 0
    decide
  · rfl
  · rfl
  · rfl
  · rfl
  · change (0 : Int) ≤ 0
    omega
  · exact (drain_code consolidationRequestPredeployAddress).trans
      (sub_state_installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
  · intro k
    change (subState.getStor consolidationRequestPredeployAddress).get k =
      (drainDebit.getStor consolidationRequestPredeployAddress).get k
    rw [drain_storageC]
private noncomputable def drainRun : Exec (initEvm drainMsg).pc (initEvm drainMsg).sta
    (initEvm drainMsg).dyna (.ok drainPost) := Classical.choose drain_runtime_exists
private noncomputable def drainChildFrame : Exec.Frame :=
  Classical.choose (Classical.choose_spec drain_runtime_exists)
private theorem drain_facts :
      Exec.keptAt consolidationRequestPredeployAddress drainRun = [drainChildFrame] ∧
      drainChildFrame.sevm.caller = systemAddress ∧ drainChildFrame.sevm.currentTarget = consolidationRequestPredeployAddress ∧
      drainChildFrame.pc = 0 ∧ drainChildFrame.sevm.code = consolidationRequestCode ∧ drainChildFrame.pre.state = drainBase.state ∧
      drainChildFrame.post.state = RequestSystem.sysState cSysShape drainBase.state consolidationRequestPredeployAddress ∧
      drainPost.error = none ∧ 0 ≤ drainPost.refundCounter ∧
      drainPost.state = RequestSystem.sysState cSysShape drainBase.state consolidationRequestPredeployAddress ∧
      drainPost.logs = drainBase.logs ∧ drainPost.output = drainBase.output :=
  Classical.choose_spec (Classical.choose_spec drain_runtime_exists)
private theorem drain_exec : exec (initEvm drainMsg) = .ok drainPost :=
  (exec_iff_exec_eq _ _ _ _).mp ⟨drainRun⟩

private theorem drain_post_facts : drainPost.error = none ∧ 0 ≤ drainPost.refundCounter ∧
    drainPost.state = RequestSystem.sysState cSysShape drainBase.state consolidationRequestPredeployAddress ∧
    drainPost.logs = [] ∧ drainPost.output = [] := by
  obtain ⟨_, _, _, _, _, _, _, error, refund, state, logs, output⟩ := drain_facts
  exact ⟨error, refund, state, logs.trans rfl, output.trans rfl⟩
private theorem drain_prepared :
    prepareMessage { drainEnv.beginTransaction with state := drainDebit }
      (transactionTenv drainEnv.beginTransaction txD 1 senderE 2 21000 []) txD = .ok drainMsg :=
  prepareMessage_call rfl
private theorem drain_nodelegated : getDelegatedCodeAddress drainMsg.code = none := by
  change getDelegatedCodeAddress (drainDebit.getCode systemAddress) = none
  rw [drain_code, sub_state_system]
  exact callerCode_undelegated
private noncomputable def drainMessageOut : MsgCallOutput :=
  { gasLeft := drainPost.gasLeft, refundCounter := ((0 + drainPost.refundCounter.toNat : Nat) : Int)
    logs := drainPost.logs, accountsToDelete := drainPost.accountsToDelete
    error := none, returnData := drainPost.output, touchedAccounts := drainPost.meta.touchedAccounts }
private theorem drain_message : processMessageCall drainMsg = .ok (drainPost.state, drainMessageOut) := by
  apply processMessageCall_call_of_message rfl rfl rfl drain_nodelegated
  · exact processMessage_call_of_exec (Msg.benvAfterTransfer_of_value_zero rfl) rfl
      (by change pragueRules.isPrecomp systemAddress = false; decide)
      drain_exec drain_post_facts.1 rfl
  · exact drain_post_facts.1
  · exact Int.toNat?_eq_some_of_nonneg drain_post_facts.2.1
private theorem drain_valid : validateTransaction drainEnv.stat.rules txD 0 = .ok (21000, 21000) :=
  validateTransaction_ok_of_facts rfl (txD_intrinsic rfl rfl rfl rfl rfl 0)
    (by decide) (by decide) rfl rfl
private theorem drain_sender : drainEnv.beginTransaction.state.get senderE = senderAcct 2 :=
  sub_state_senderE
private theorem drain_checked : checkTransaction drainEnv.beginTransaction
    (transactionPreludeBout subOut txD 1) txD = .ok (senderE, 2, [], 0) := by
  apply checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
  · apply checkTransactionGasLimits_ok_of_room rfl
    · change 2 ^ 20 ≤ 2 ^ 22 - subOut.blockGasUsed
      have := sub_gas
      omega
    · change 0 ≤ _
      exact Nat.zero_le _
  · exact checkTransactionChainId_two rfl rfl
  · exact txD_recoveredSender
  · exact checkTransactionGasFee_two (benv := drainEnv.beginTransaction) (tx := txD)
      (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by change 1 ≤ 8; decide) (by decide)
  · exact checkTransactionBlobData_two rfl _
  · exact checkTransactionReceiver_two rfl
  · exact checkTransactionAuthorizationList_two rfl
  · rw [drain_sender]
    exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl
private theorem drain_transaction_debit :
    (drainEnv.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee drainEnv txD).toB256 = some drainDebit := by
  rw [transactionBlobGasFee_two (show txD.type = .two 1 1 8 (some systemAddress) [] from rfl), Nat.add_zero]
  exact drain_debit
private theorem drain_transaction_message :
    transactionMessage drainEnv subOut txD 1 = .ok (senderE, drainMsg) := by
  have valid : validateTransaction drainEnv.beginTransaction.stat.rules txD 0 = .ok (21000, 21000) := drain_valid
  have deb : (drainEnv.beginTransaction.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee drainEnv.beginTransaction txD).toB256 = some drainDebit :=
    drain_transaction_debit
  have tenv : transactionTenvAt drainEnv.beginTransaction txD 1 senderE 2 21000 [] =
      transactionTenv drainEnv.beginTransaction txD 1 senderE 2 21000 [] := rfl
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none txD rfl]
  simp only [valid, drain_checked, deb, Except.mapError, bind, Except.bind, Option.toExcept]
  rw [tenv, drain_prepared]
private theorem drain_enter : (Frame.ofCall drainMsg).enter = .run (initEvm drainMsg) :=
  Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
    (by change pragueRules.isPrecomp systemAddress = false; decide)
private theorem drain_resolved : messageCallExecutionMessage drainMsg = drainMsg := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  have nd : drainMsg.benv.stat.rules.delegatedCodeAddress drainMsg.code = none := by
    unfold ForkRules.delegatedCodeAddress
    rw [drain_nodelegated]
    split <;> rfl
  rw [nd]
private theorem drain_entry : messageEntry drainMsg = some (Frame.ofCall drainMsg, initEvm drainMsg) := by
  unfold messageEntry legacyEntry
  change (match messageCallDelegation drainMsg with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none) = _
  have delegated : messageCallDelegation drainMsg = .ok (drainMsg, 0) := rfl
  rw [delegated]
  change enteredFrame (Frame.ofCall (messageCallExecutionMessage drainMsg)) = _
  rw [drain_resolved]
  unfold enteredFrame
  rw [drain_enter]
private noncomputable def drainRoot : Root := ⟨Frame.ofCall drainMsg, initEvm drainMsg, .ok drainPost, drainRun⟩
private theorem drain_commits : Execution.commits (.ok drainPost : Execution) = true := by
  change drainPost.error.isNone = true
  rw [drain_post_facts.1]
  rfl
private theorem drain_root_retained : Root.keptAt consolidationRequestPredeployAddress drainRoot = [drainChildFrame] := by
  have settles : Frame.settlementCommits (Frame.ofCall drainMsg) (.ok drainPost) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits drain_commits
  dsimp only [drainRoot, Root.keptAt]
  rw [dite_eq_left settles, ite_eq_right (show (initEvm drainMsg).sta.currentTarget ≠
    consolidationRequestPredeployAddress from by change systemAddress ≠ consolidationRequestPredeployAddress; decide)]
  exact drain_facts.1
private theorem drain_message_roots : MessageRoots drainMsg drainPost.state drainMessageOut [drainRoot] := by
  refine ⟨drain_message, ?_⟩
  rw [drain_entry]
  rfl
private theorem drain_transaction_roots : ∃ st bout,
    TransactionRoots drainEnv subOut txD 1 st bout senderE [drainRoot] ∧
    bout.blockGasUsed ≤ 2 ^ 21 ∧
    bout.receiptKeys = subOut.receiptKeys ++ [BLT.toBytes (.bytes (1 : Nat).toBytes)] ∧
    bout.receiptsTrie[BLT.toBytes (.bytes (1 : Nat).toBytes)]? =
      some (makeReceipt txD none bout.cumulativeGasUsed []) ∧
    ∃ refund tip, st = drainPost.accountsToDelete.toList.foldl destroyAccount
      ((drainPost.state.addBal senderE refund).addBal 0 tip) := by
  have refund : Int.toNat? drainMessageOut.refundCounter = some drainPost.refundCounter.toNat := by
    change Int.toNat? ((0 + drainPost.refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (i := (drainPost.refundCounter.toNat : Int)) (by omega)
  obtain ⟨bout, process, _, gas, keys, receipt⟩ := processTransaction_of_stages_receipts
    (bout := subOut) (index := 1) rfl rfl rfl rfl drain_valid drain_checked drain_transaction_debit
      drain_prepared drain_message refund
  refine ⟨_, bout, ⟨process, drainMsg, drainPost.state, drainMessageOut,
    drain_transaction_message, drain_message_roots⟩, ?_, keys, ?_, _, _, rfl⟩
  · rw [gas]
    have used := txGasUsed_le (gas := txD.gas) (floor := 21000) (left := drainMessageOut.gasLeft)
      (refund := drainPost.refundCounter.toNat) (by decide)
    change subOut.blockGasUsed + txGasUsed txD.gas 21000 drainMessageOut.gasLeft
      drainPost.refundCounter.toNat ≤ 2 ^ 21
    exact (Nat.add_le_add sub_gas used).trans (by decide)
  · simpa only [drainMessageOut, drain_post_facts.2.2.2.1] using receipt

private noncomputable def drainState : State := Classical.choose drain_transaction_roots
private noncomputable def drainOut : BlockOutput := Classical.choose (Classical.choose_spec drain_transaction_roots)
private theorem drain_roots : TransactionRoots drainEnv subOut txD 1 drainState drainOut senderE [drainRoot] :=
  (Classical.choose_spec (Classical.choose_spec drain_transaction_roots)).1
private theorem drain_gas : drainOut.blockGasUsed ≤ 2 ^ 21 :=
  (Classical.choose_spec (Classical.choose_spec drain_transaction_roots)).2.1
private theorem drain_world : ∃ refund tip,
    drainState = drainPost.accountsToDelete.toList.foldl destroyAccount
      ((drainPost.state.addBal senderE refund).addBal 0 tip) :=
  (Classical.choose_spec (Classical.choose_spec drain_transaction_roots)).2.2.2.2
private theorem drain_post_codes (a : Adr) : drainPost.state.getCode a = subState.getCode a := by
  rw [drain_post_facts.2.2.1, RequestSystem.sysState_getCode]
  exact drain_code a
private theorem drain_state_protected {a : Adr}
    (nonempty : (subState.getCode a).toList ≠ []) (nondelegating : ¬ isValidDelegation (subState.getCode a)) :
    drainState.getCode a = subState.getCode a ∧ drainState.getStor a = drainPost.state.getStor a := by
  have code : drainMsg.benv.state.getCode a = subState.getCode a := drain_code a
  have notDeleted : a ∉ drainPost.accountsToDelete :=
    drain_message_roots.not_deleted (by rw [code]; exact nonempty)
      (by rw [code]; exact nondelegating) AdrSet.not_mem_empty AdrSet.not_mem_empty rfl
  have notListed : ∀ x ∈ drainPost.accountsToDelete.toList, x ≠ a :=
    fun x member same => notDeleted (same ▸ Std.HashSet.mem_toList.mp member)
  have postCode : (drainPost.state.getCode a).toList ≠ [] := by
    rw [drain_post_codes]
    exact nonempty
  obtain ⟨refund, tip, world⟩ := drain_world
  have settled := settled_getCode_getStor_of_code_nonempty (rules := pragueRules) (touched := [])
    (st := drainPost.state) (s := senderE) (c := 0) (w := a) (r := refund) (f := tip) notListed postCode
  rw [sweepTouchedAccounts_of_not_touchedSweep (show pragueRules.settle.touchedSweep = false from rfl)] at settled
  rw [world]
  exact ⟨settled.1.trans (drain_post_codes a), settled.2⟩
private theorem drain_state_installed : SystemCodeInstalled drainState := by
  intro p member
  obtain ⟨_, nondelegating, nonempty⟩ := systemContracts_facts p member
  exact (drain_state_protected (by rw [sub_state_installed p member]; exact nonempty)
    (by rw [sub_state_installed p member]; exact nondelegating)).1.trans (sub_state_installed p member)
private theorem drain_state_system : drainState.getCode systemAddress = callerCode :=
  (drain_state_protected (by rw [sub_state_system]; exact callerCode_runtime.1)
    (by rw [sub_state_system]; exact callerCode_runtime.2)).1.trans sub_state_system
private theorem drain_state_storageW : drainState.getStor withdrawalRequestPredeployAddress = Stor.empty := by
  have installed := sub_state_installed _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  obtain ⟨_, nondelegating, nonempty⟩ := systemContracts_facts _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  rw [(drain_state_protected (by rw [installed]; exact nonempty)
    (by rw [installed]; exact nondelegating)).2, drain_post_facts.2.2.1,
    RequestSystem.sysState_getStor_other cSysShape drainBase.state
      (by decide : consolidationRequestPredeployAddress ≠ withdrawalRequestPredeployAddress)]
  change (((drainEnv.state.incrNonce senderE).setBal senderE _).get withdrawalRequestPredeployAddress).stor = _
  rw [State.setBal_get_ne (by decide : senderE ≠ withdrawalRequestPredeployAddress),
    State.incrNonce_get_stor, ite_eq_right (by
      rintro ⟨same, _⟩
      exact (by decide : senderE ≠ withdrawalRequestPredeployAddress) same)]
  exact sub_state_storageW
private noncomputable def clearedStor : Stor := BuilderRequest.Delivery.drainStor cSysShape submittedStor
private theorem drain_state_storageC : drainState.getStor consolidationRequestPredeployAddress = clearedStor := by
  have installed := sub_state_installed _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  obtain ⟨_, nondelegating, nonempty⟩ := systemContracts_facts _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  rw [(drain_state_protected (by rw [installed]; exact nonempty)
    (by rw [installed]; exact nondelegating)).2, drain_post_facts.2.2.1,
    BuilderRequest.Delivery.sysState_getStor]
  change BuilderRequest.Delivery.drainStor cSysShape (drainDebit.getStor consolidationRequestPredeployAddress) = _
  rw [drain_storageC, sub_state_storageC]
  rfl
private theorem cleared_shape : clearedStor =
    ((((submittedStor.set 2 0).set 3 0).set 0 0).set 1 0) := by
  have excess := congrArg Prod.fst submitted_meta
  have count := congrArg (fun x => x.2.1) submitted_meta
  have head := congrArg (fun x => x.2.2.1) submitted_meta
  have tail := congrArg (fun x => x.2.2.2) submitted_meta
  dsimp only at excess count head tail
  unfold clearedStor BuilderRequest.Delivery.drainStor
  rw [excess, count, head, tail]
  rfl
private theorem cleared_queue : clearedStor.get 2 = 0 ∧ clearedStor.get 3 = 0 := by
  rw [cleared_shape]
  constructor
  · rw [Stor.get_set_ne _ (by decide : (1 : B256) ≠ 2),
      Stor.get_set_ne _ (by decide : (0 : B256) ≠ 2),
      Stor.get_set_ne _ (by decide : (3 : B256) ≠ 2), Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3),
      Stor.get_set_ne _ (by decide : (0 : B256) ≠ 3), Stor.get_set_self]

private theorem tx_rootsB : TransactionsRoots [(0, txSub), (1, txD)] txEnvB .init
    (txEnvB.withState drainState) drainOut [(subSender, txSub), (senderE, txD)] [subRoot, drainRoot] := by
  simpa only [Benv.withState, List.append_nil, List.singleton_append] using
    TransactionsRoots.cons sub_roots (TransactionsRoots.cons drain_roots (TransactionsRoots.nil _ _))
private theorem sub_logs : subPost.logs =
    [⟨consolidationRequestPredeployAddress, [], subSender.toBytes ++ payload96⟩] := by
  have logs := sub_facts.2.2.2.2.1.logs
  have empty : (initDevm (subMsg.withBenv subAfter)).logs = [] := by
    apply Lift.initDevm_logs
    change subAfter.stat.rules.stateGas = none
    rw [benvAfterTransfer_stat sub_transferred]
    rfl
  rw [empty, List.nil_append] at logs
  exact logs
private theorem depositsB : parseDepositRequests drainOut = .ok [] := by
  have subInfo := Classical.choose_spec (Classical.choose_spec sub_transaction_roots)
  have drainInfo := Classical.choose_spec (Classical.choose_spec drain_transaction_roots)
  have first : drainOut.receiptsTrie[BLT.toBytes (.bytes (0 : Nat).toBytes)]? =
      some (makeReceipt txSub none subOut.cumulativeGasUsed subPost.logs) := by
    obtain ⟨entry, inserted⟩ := processTransaction_receiptsTrie drain_roots.1
    rw [inserted, Std.TreeMap.getElem?_insert]
    simp only [Std.compare_eq_iff_eq, receiptKey_ne, ite_false]
    exact subInfo.2.2.2.1
  have subKeys : subOut.receiptKeys = [BLT.toBytes (.bytes (0 : Nat).toBytes)] := subInfo.2.2.1
  have drainKeys : drainOut.receiptKeys = subOut.receiptKeys ++ [BLT.toBytes (.bytes (1 : Nat).toBytes)] :=
    drainInfo.2.2.1
  apply BlockForward.parseDepositRequests_of_no_deposit_logs
  intro key member
  rw [drainKeys, subKeys] at member
  change key ∈ [BLT.toBytes (.bytes (0 : Nat).toBytes), BLT.toBytes (.bytes (1 : Nat).toBytes)] at member
  rcases List.mem_cons.mp member with same | same
  · subst key
    refine ⟨_, first, ?_⟩
    change ∀ log ∈ subPost.logs, log.address ≠ depositContractAddress
    rw [sub_logs]
    intro log member
    obtain rfl := List.mem_singleton.mp member
    decide
  · obtain rfl := List.mem_singleton.mp same
    refine ⟨_, drainInfo.2.2.2.1, ?_⟩
    intro log member
    change log ∈ ([] : List Log) at member
    cases member
private noncomputable def txFinalB : Benv := txEnvB.withState drainState
private noncomputable def withdrawalB : State :=
  RequestSystem.sysState wPath.shape drainState withdrawalRequestPredeployAddress
private noncomputable def withdrawalOutB : MsgCallOutput :=
  systemCallOutput (wPath.coveredPost txFinalB withdrawalRequestPredeployAddress)
private noncomputable def requestEnvB : Benv := txFinalB.withState withdrawalB
private noncomputable def stateB : State :=
  RequestSystem.sysState cSysShape withdrawalB consolidationRequestPredeployAddress
private theorem withdrawal_installedB : txFinalB.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode :=
  drain_state_installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
private theorem withdrawal_callB : processCheckedSystemTransaction txFinalB withdrawalRequestPredeployAddress [] =
    .ok (withdrawalB, withdrawalOutB) :=
  (wPath.covered_call_spec WithdrawalRequest.Amsterdam.sysMemory CoveredFork.prague
    (by
      change (withdrawalRequestPredeployAddress, withdrawalRequestCode) ∈ systemContracts
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) withdrawal_installedB
    (B := 1000000) (by decide +kernel) (by decide)).1
private theorem withdrawal_outputB : withdrawalOutB.returnData = [] :=
  withdrawal_output_empty drain_state_storageW
private theorem withdrawal_storageC_B : withdrawalB.getStor consolidationRequestPredeployAddress = clearedStor :=
  (RequestSystem.sysState_getStor_other wPath.shape drainState (by decide)).trans drain_state_storageC
private theorem consolidation_installedB : requestEnvB.state.getCode consolidationRequestPredeployAddress =
    consolidationRequestCode :=
  (RequestSystem.sysState_getCode wPath.shape drainState withdrawalRequestPredeployAddress
    consolidationRequestPredeployAddress).trans
      (drain_state_installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
private theorem bodyB : ∃ out, applyBody inputB [Sum.inr txSub, Sum.inr txD] [] [] = .ok (stateB, out) ∧
    out.blockGasUsed ≤ 2 ^ 21 ∧ out.requests = [] := by
  obtain ⟨outC, cRun, cError, cGas, cData⟩ := ConsolidationRequest.system_call_ok
    (benv := requestEnvB) CoveredFork.prague consolidation_installedB
  have cEmpty : outC.returnData = [] := by
    rw [cData]
    change ConsolidationRequest.drained (withdrawalB.getStor consolidationRequestPredeployAddress).get = []
    rw [withdrawal_storageC_B]
    unfold ConsolidationRequest.drained
    rw [cleared_queue.1, cleared_queue.2]
    rfl
  have body := BlockForward.applyBody_forward (benv := inputB)
    (txs := [Sum.inr txSub, Sum.inr txD]) (ommers := []) CoveredFork.prague
      beacon_callB lastB history_callB rfl tx_rootsB.run depositsB withdrawal_callB cRun
  refine ⟨BlockForward.requestsOutput drainOut withdrawalOutB.returnData outC.returnData, body, drain_gas, ?_⟩
  rw [withdrawal_outputB, cEmpty]
  change drainOut.requests ++ [] ++ [] = []
  rw [tx_rootsB.requests_eq]
  rfl

private noncomputable def outputB : BlockOutput := Classical.choose bodyB
private theorem outputB_facts : applyBody inputB [Sum.inr txSub, Sum.inr txD] [] [] = .ok (stateB, outputB) ∧
    outputB.blockGasUsed ≤ 2 ^ 21 ∧ outputB.requests = [] := Classical.choose_spec bodyB
private noncomputable def headerB : Header :=
  BlockForward.commitHeader Fork.prague.ruleSet blockA templateB stateB outputB
private noncomputable def blockB : Block :=
  { header := headerB, txs := [Sum.inr txSub, Sum.inr txD], wds := [], ommers := [] }
private noncomputable def chainB : BlockChain := ⟨appendBlock chainA.blocks blockB, stateB, 1⟩
private noncomputable def runB : BodyRun := Classical.choose (exists_bodyRoots outputB_facts.1)
private theorem rootsB : BodyRoots inputB [Sum.inr txSub, Sum.inr txD] [] [] stateB outputB runB :=
  Classical.choose_spec (exists_bodyRoots outputB_facts.1)
private noncomputable def keptB : KeptBlock := ⟨chainA, blockB, .prague, outputB, runB⟩
private theorem inputB_headerB : initBenv .prague chainA headerB = inputB := by
  simpa only [headerB, inputB] using BlockForward.initBenv_commitHeader_body_eq .prague chainA
    Fork.prague.ruleSet blockA templateB stateB stateA outputB BlockOutput.init
private theorem headerB_valid : validateHeader Fork.prague.ruleSet chainA headerB = .ok () := by
  apply BlockForward.commitHeader_ok CoveredFork.prague rfl rfl rfl
  · change calculateBaseFeePerGas (2 ^ 22) (2 ^ 22) outputA.blockGasUsed 1 = .ok 1
    rw [outputA_facts.2.1]
    exact BlockForward.calculateBaseFeePerGas_unit (by decide) (by decide) (by decide) (by decide)
  · rfl
  · exact outputB_facts.2.1.trans (by decide)
  · decide
  · rfl
  · rfl
private theorem stepB : KeptStep config keptB chainB := by
  have selected : config.forkAt blockB.header.number blockB.header.timestamp = .ok .prague :=
    ChainConfig.single_forkAt 1 .prague _ _
  refine ⟨?_, selected, Or.inl CoveredFork.prague, ?_⟩
  · apply BlockForward.stateTransitionUsing_forward rfl selected CoveredFork.prague headerB_valid rfl
    · change applyBody (initBenv .prague chainA headerB) [Sum.inr txSub, Sum.inr txD] [] [] = .ok (stateB, outputB)
      rw [inputB_headerB]
      exact outputB_facts.1
    all_goals rfl
  · change BodyRoots (initBenv .prague chainA headerB) [Sum.inr txSub, Sum.inr txD] [] [] stateB outputB runB
    rw [inputB_headerB]
    exact rootsB
private theorem historyAB : KeptHistory config start [keptA, keptB] chainB := by
  simpa only [List.singleton_append] using KeptHistory.step activation_history stepB
private theorem stateB_installed : SystemCodeInstalled stateB := by
  intro p member
  exact (RequestSystem.sysState_getCode cSysShape withdrawalB consolidationRequestPredeployAddress p.1).trans
    ((RequestSystem.sysState_getCode wPath.shape drainState withdrawalRequestPredeployAddress p.1).trans
      (drain_state_installed p member))
private theorem stateB_system : stateB.getCode systemAddress = callerCode :=
  (RequestSystem.sysState_getCode cSysShape withdrawalB consolidationRequestPredeployAddress systemAddress).trans
    ((RequestSystem.sysState_getCode wPath.shape drainState withdrawalRequestPredeployAddress systemAddress).trans
      drain_state_system)
private theorem stateB_queue : (stateB.getStor consolidationRequestPredeployAddress).get 2 = 0 ∧
    (stateB.getStor consolidationRequestPredeployAddress).get 3 = 0 := by
  rw [stateB, BuilderRequest.Delivery.sysState_getStor, withdrawal_storageC_B]
  have emptyShape {s : Stor} (head : s.get 2 = 0) (tail : s.get 3 = 0) :
      BuilderRequest.Delivery.drainStor cSysShape s =
        ((((s.set 2 0).set 3 0).set 0 (cSysShape.next (s.get 0) (s.get 1))).set 1 0) := by
    unfold BuilderRequest.Delivery.drainStor
    rw [head, tail]
    rfl
  rw [emptyShape cleared_queue.1 cleared_queue.2]
  constructor
  · rw [Stor.get_set_ne _ (by decide : (1 : B256) ≠ 2),
      Stor.get_set_ne _ (by decide : (0 : B256) ≠ 2),
      Stor.get_set_ne _ (by decide : (3 : B256) ≠ 2), Stor.get_set_self]
  · rw [Stor.get_set_ne _ (by decide : (1 : B256) ≠ 3),
      Stor.get_set_ne _ (by decide : (0 : B256) ≠ 3), Stor.get_set_self]
private theorem final_queue_empty : ConsolidationRequestPublic.remainingQueue stateB = [] := by
  unfold ConsolidationRequestPublic.remainingQueue ConsolidationRequestPublic.storedQueue
  rw [stateB_queue.1, stateB_queue.2]
  rfl

private theorem system_C_callers {benv : Benv} {p : Adr × ByteArray} {data : Bytes}
    {post : State} {out : MsgCallOutput} {rs : List Root}
    (member : p ∈ systemContracts) (installed : benv.state.getCode p.1 = p.2)
    (fork : CoveredFork benv.stat.fork)
    (roots : MessageRoots (systemTransactionMessage benv p.1 data) post out rs) :
    ∀ f ∈ rs.flatMap (Root.keptAt consolidationRequestPredeployAddress), f.sevm.caller = systemAddress := by
  have shape : p.2 = beaconRootsCode ∨ p.2 = historyStorageCode ∨ p.2 = withdrawalRequestCode ∨
      p.2 = consolidationRequestCode := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl rfl))
    · exact .inr (.inr (.inr rfl))
  obtain ⟨_, nondelegating, nonempty⟩ := systemContracts_facts p member
  intro f memberF
  obtain ⟨r, memberR, memberF⟩ := List.mem_flatMap.mp memberF
  have machine := roots.entry_machine memberR
  have route := roots.entry_routing memberR
  have entryCode := roots.entry_call_code memberR rfl rfl rfl
  have code : r.evm.sta.code = p.2 :=
    (entryCode.1 (by change (benv.state.getCode p.1).toList ≠ []; rw [installed]; exact nonempty)
      (by change ¬ isValidDelegation (benv.state.getCode p.1); rw [installed]; exact nondelegating)).trans installed
  rcases r with ⟨frame, ⟨pc, sta, pre⟩, raw, run⟩
  dsimp only at machine route code memberF
  obtain rfl := machine.1
  have alternative : sta.code = beaconRootsCode ∨ sta.code = historyStorageCode ∨
      sta.code = withdrawalRequestCode ∨ sta.code = consolidationRequestCode := by
    rcases shape with same | same | same | same
    · exact .inl (code.trans same)
    · exact .inr (.inl (code.trans same))
    · exact .inr (.inr (.inl (code.trans same)))
    · exact .inr (.inr (.inr (code.trans same)))
  have covered : CoveredFork sta.benvStat.fork := by
    rw [route.2.2.1]
    exact fork
  have below := no_descendants alternative covered run
  unfold Root.keptAt at memberF
  split at memberF
  · split at memberF
    · obtain rfl := List.mem_singleton.mp memberF
      exact route.1
    · have descendant := Exec.mem_descendantFrames_of_mem_keptAt run memberF
      rw [below] at descendant
      cases descendant
  · cases memberF

private theorem pre_outputA : runA.preState = historyA ∧ runA.preBal = {} := by
  apply PreRoots.output_of_calls (beacon := beaconA) (beaconBal := {}) rootsA.pre
  · unfold beaconRootsCall
    simp only [show inputA.stat.rules.sys.beaconRoots = true from rfl, ite_true,
      Except.mapError, beacon_callA, bind, Except.bind]
    rfl
  · change historyStorageCall inputA.stat.rules historyEnvA {} = .ok (historyA, {})
    unfold historyStorageCall
    simp only [show inputA.stat.rules.sys.historyStorage = true from rfl, ite_true,
      lastA, Option.toExcept, Except.mapError, history_callA, bind, Except.bind]
    rfl
private theorem pre_outputB : runB.preState = historyB ∧ runB.preBal = {} := by
  apply PreRoots.output_of_calls (beacon := beaconB) (beaconBal := {}) rootsB.pre
  · unfold beaconRootsCall
    simp only [show inputB.stat.rules.sys.beaconRoots = true from rfl, ite_true,
      Except.mapError, beacon_callB, bind, Except.bind]
    rfl
  · change historyStorageCall inputB.stat.rules historyEnvB {} = .ok (historyB, {})
    unfold historyStorageCall
    simp only [show inputB.stat.rules.sys.historyStorage = true from rfl, ite_true,
      lastB, Option.toExcept, Except.mapError, history_callB, bind, Except.bind]
    rfl
private theorem tx_outputA : runA.senders = [] ∧ runA.txRoots = [] ∧
    runA.txEnv = txEnvA := by
  obtain ⟨decoded, decode, transactions⟩ := rootsA.transactions
  change Except.ok ([] : List Tx) = .ok decoded at decode
  obtain rfl := Except.ok.inj decode
  rw [pre_outputA.1, pre_outputA.2] at transactions
  change TransactionsRoots [] txEnvA .init runA.txEnv runA.txOut runA.senders runA.txRoots at transactions
  have same := transactions.unique (TransactionsRoots.nil txEnvA .init)
  exact ⟨same.2.2.1, same.2.2.2, same.1⟩
private theorem tx_outputB : runB.senders = [(subSender, txSub), (senderE, txD)] ∧
    runB.txRoots = [subRoot, drainRoot] ∧ runB.txEnv = txFinalB ∧ runB.txOut = drainOut := by
  obtain ⟨decoded, decode, transactions⟩ := rootsB.transactions
  change Except.ok [txSub, txD] = .ok decoded at decode
  obtain rfl := Except.ok.inj decode
  rw [pre_outputB.1, pre_outputB.2] at transactions
  change TransactionsRoots [(0, txSub), (1, txD)] txEnvB .init runB.txEnv runB.txOut runB.senders runB.txRoots at transactions
  have same := transactions.unique tx_rootsB
  exact ⟨same.2.2.1, same.2.2.2, same.1, same.2.1⟩

private theorem pre_C_packet {benv : Benv} {st : State} {bal : BalBuilder} {rs : List Root}
    (roots : PreRoots benv st bal rs) (fork : benv.stat.fork = .prague)
    (codes : SystemCodeInstalled benv.state) (system : benv.state.getCode systemAddress = callerCode) :
    (∀ f ∈ rs.flatMap (Root.keptAt consolidationRequestPredeployAddress), f.sevm.caller = systemAddress) ∧
      NoCreateAt systemAddress rs := by
  have rules : benv.stat.rules = pragueRules := by unfold BenvStat.rules; rw [fork]; rfl
  have covered : CoveredFork benv.stat.fork := by rw [fork]; exact .prague
  have avoid := roots.noCreateAt_of_code (by rw [rules]; rfl) systemAddress
    (by rw [system]; exact callerCode_runtime.1) (by rw [system]; exact callerCode_runtime.2)
    (by decide) (by decide)
  obtain ⟨beacon, beaconBal, br, hr, _, first, _, second, rfl⟩ := roots
  have initialH : benv.state.getCode historyStorageAddress = historyStorageCode :=
    codes (historyStorageAddress, historyStorageCode) (List.mem_cons_of_mem _ List.mem_cons_self)
  have factsH := systemContracts_facts (historyStorageAddress, historyStorageCode)
    (List.mem_cons_of_mem _ List.mem_cons_self)
  have historyCode : beacon.getCode historyStorageAddress = historyStorageCode :=
    (first.chain (a := historyStorageAddress) (by rw [initialH]; exact factsH.2.2) (by rw [initialH]; exact factsH.2.1)).2.trans initialH
  rw [PreCall, ite_eq_left (show benv.stat.rules.sys.beaconRoots = true from by rw [rules]; rfl)] at first
  rw [PreCall, ite_eq_left (show benv.stat.rules.sys.historyStorage = true from by rw [rules]; rfl)] at second
  obtain ⟨outB, rootB⟩ := first
  obtain ⟨outH, rootH⟩ := second
  refine ⟨?_, avoid⟩
  intro f member
  rw [List.flatMap_append, List.mem_append] at member
  rcases member with member | member
  · exact system_C_callers (benv := benv) (p := (beaconRootsAddress, beaconRootsCode)) List.mem_cons_self
      (codes (beaconRootsAddress, beaconRootsCode) List.mem_cons_self) covered rootB f member
  · exact system_C_callers (benv := benv.withState beacon) (p := (historyStorageAddress, historyStorageCode))
      (List.mem_cons_of_mem _ List.mem_cons_self) historyCode covered rootH f member

private theorem request_C_packet {benv : Benv} {bout : BlockOutput} {st : State}
    {out : BlockOutput} {steps : List RequestStep}
    (pass : RequestPass benv bout st out steps) (fork : benv.stat.fork = .prague)
    (codes : SystemCodeInstalled benv.state) (system : benv.state.getCode systemAddress = callerCode) :
    (∀ f ∈ (requestRootsOf steps).flatMap (Root.keptAt consolidationRequestPredeployAddress),
      f.sevm.caller = systemAddress) ∧ NoCreateAt systemAddress (requestRootsOf steps) := by
  have rules : benv.stat.rules = pragueRules := by unfold BenvStat.rules; rw [fork]; rfl
  have covered : CoveredFork benv.stat.fork := by rw [fork]; exact .prague
  unfold RequestPass at pass
  rw [ite_eq_left (show benv.stat.rules.header.requestsHash = true from by rw [rules]; rfl)] at pass
  obtain ⟨deposits, acc, bal, _, fold, _⟩ := pass
  rw [show benv.stat.rules.requests = pragueRequests from by rw [rules]; rfl] at fold
  have avoid := fold.prague_noCreateAt_of_code (by rw [rules]; rfl) systemAddress
    (by rw [system]; exact callerCode_runtime.1) (by rw [system]; exact callerCode_runtime.2)
    (by decide) (by decide)
  refine ⟨?_, avoid⟩
  have initialC : benv.state.getCode consolidationRequestPredeployAddress = consolidationRequestCode :=
    codes (consolidationRequestPredeployAddress, consolidationRequestCode)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))
  have factsC := systemContracts_facts (consolidationRequestPredeployAddress, consolidationRequestCode)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  cases fold with
  | @cons typeW targetW restW benvW accW accW' balW balW' postW finalW outW rsW stepsW wRun wRoots later =>
    cases later with
    | cons cRun cRoots later =>
      cases later
      have codeC := (wRoots.chain (a := consolidationRequestPredeployAddress)
        (by change (benv.state.getCode consolidationRequestPredeployAddress).toList ≠ []; rw [initialC]; exact factsC.2.2)
        (by change ¬ isValidDelegation (benv.state.getCode consolidationRequestPredeployAddress); rw [initialC]; exact factsC.2.1)).2
      intro f member
      simp only [requestRootsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.flatMap_append, List.mem_append] at member
      rcases member with member | member
      · exact system_C_callers (benv := benv) (p := (withdrawalRequestPredeployAddress, withdrawalRequestCode))
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (codes (withdrawalRequestPredeployAddress, withdrawalRequestCode)
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) covered wRoots f member
      · exact system_C_callers (benv := benv.withState postW) (p := (consolidationRequestPredeployAddress, consolidationRequestCode))
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
          (codeC.trans initialC) covered cRoots f member

private theorem pre_packets :
    (∀ f ∈ runA.preRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress), f.sevm.caller = systemAddress) ∧
    NoCreateAt systemAddress runA.preRoots ∧
    (∀ f ∈ runB.preRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress), f.sevm.caller = systemAddress) ∧
    NoCreateAt systemAddress runB.preRoots := by
  have a := pre_C_packet (benv := inputA) rootsA.pre rfl initial_installed initial_system
  have b := pre_C_packet (benv := inputB) rootsB.pre rfl stateA_installed stateA_system
  exact ⟨a.1, a.2, b.1, b.2⟩
private theorem request_packets :
    (∀ f ∈ (requestRootsOf runA.requests).flatMap (Root.keptAt consolidationRequestPredeployAddress),
      f.sevm.caller = systemAddress) ∧ NoCreateAt systemAddress (requestRootsOf runA.requests) ∧
    (∀ f ∈ (requestRootsOf runB.requests).flatMap (Root.keptAt consolidationRequestPredeployAddress),
      f.sevm.caller = systemAddress) ∧ NoCreateAt systemAddress (requestRootsOf runB.requests) := by
  have nilWds (benv : Benv) (out : BlockOutput) : withdrawalsPass pragueRules benv out [] =
      (benv.state, out) := by rfl
  have a :
      (∀ f ∈ (requestRootsOf runA.requests).flatMap (Root.keptAt consolidationRequestPredeployAddress),
        f.sevm.caller = systemAddress) ∧ NoCreateAt systemAddress (requestRootsOf runA.requests) := by
    obtain ⟨st, out, pass⟩ := rootsA.requests
    change RequestPass
      (runA.txEnv.withState (withdrawalsPass pragueRules runA.txEnv runA.txOut []).1)
      (withdrawalsPass pragueRules runA.txEnv runA.txOut []).2 st out runA.requests at pass
    rw [nilWds] at pass
    have pass' : RequestPass runA.txEnv runA.txOut st out runA.requests := by
      simpa only [Benv.withState] using pass
    rw [tx_outputA.2.2] at pass'
    exact request_C_packet (benv := txEnvA) pass' rfl
      (fun p member => (history_codesA p.1).trans (initial_installed p member))
      ((history_codesA systemAddress).trans initial_system)
  have b :
      (∀ f ∈ (requestRootsOf runB.requests).flatMap (Root.keptAt consolidationRequestPredeployAddress),
        f.sevm.caller = systemAddress) ∧ NoCreateAt systemAddress (requestRootsOf runB.requests) := by
    obtain ⟨st, out, pass⟩ := rootsB.requests
    change RequestPass
      (runB.txEnv.withState (withdrawalsPass pragueRules runB.txEnv runB.txOut []).1)
      (withdrawalsPass pragueRules runB.txEnv runB.txOut []).2 st out runB.requests at pass
    rw [nilWds] at pass
    have pass' : RequestPass runB.txEnv runB.txOut st out runB.requests := by
      simpa only [Benv.withState] using pass
    rw [tx_outputB.2.2.1] at pass'
    exact request_C_packet (benv := txFinalB) pass' rfl drain_state_installed drain_state_system
  exact ⟨a.1, a.2, b.1, b.2⟩
private theorem tx_create_avoid : NoCreateAt systemAddress runA.txRoots ∧ NoCreateAt systemAddress runB.txRoots := by
  rw [tx_outputA.2.1, tx_outputB.2.1]
  have entrySystem : subAfter.state.getCode systemAddress = callerCode := by
    rw [benvAfterTransfer_ok_getCode sub_transferred systemAddress]
    change subDebit.getCode systemAddress = _
    rw [subDebit, State.setBal_getCode]
    change ((txEnvB.state.incrNonce subSender).get systemAddress).code = _
    rw [State.incrNonce_get_code]
    exact history_systemB
  have a := Root.noCreateAt_of_code subRoot systemAddress
    (by change subAfter.stat.rules.stateGas = none; rw [benvAfterTransfer_stat sub_transferred]; rfl)
    (by change (subAfter.state.getCode systemAddress).toList ≠ []; rw [entrySystem]; exact callerCode_runtime.1)
    (by intro impossible; change (some consolidationRequestPredeployAddress : Option Adr) = none at impossible; cases impossible)
  have b := Root.noCreateAt_of_code drainRoot systemAddress rfl
    (by change (drainDebit.getCode systemAddress).toList ≠ []; rw [drain_code, sub_state_system]; exact callerCode_runtime.1)
    (by intro impossible; change (some systemAddress : Option Adr) = none at impossible; cases impossible)
  constructor
  · intro f member
    cases member
  · intro f member
    simp only [keptAll, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at member
    rcases member with member | member
    · exact a f (by simpa only [keptAll, List.flatMap_cons, List.flatMap_nil, List.append_nil] using member)
    · exact b f (by simpa only [keptAll, List.flatMap_cons, List.flatMap_nil, List.append_nil] using member)

private theorem cleanAB : HistoryClean [keptA, keptB] := by
  refine ⟨?_, ?_, ?_⟩
  · intro b member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change NoSenderAt systemAddress runA.senders
      rw [tx_outputA.1]
      intro p member
      cases member
    · change NoSenderAt systemAddress runB.senders
      rw [tx_outputB.1]
      intro p member
      rcases List.mem_cons.mp member with same | same
      · subst p
        exact subSender_distinct.2.2.1
      · obtain rfl := List.mem_singleton.mp same
        change senderE ≠ systemAddress
        decide
  · intro b member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change NoAuthorityAt systemAddress runA.senders
      rw [tx_outputA.1]
      intro p member
      cases member
    · change NoAuthorityAt systemAddress runB.senders
      rw [tx_outputB.1]
      intro p member auth memberAuth
      rcases List.mem_cons.mp member with same | same
      · subst p
        change auth ∈ ([] : List Auth) at memberAuth
        cases memberAuth
      · obtain rfl := List.mem_singleton.mp same
        change auth ∈ ([] : List Auth) at memberAuth
        cases memberAuth
  · intro b member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change NoCreateAt systemAddress runA.roots
      intro f member
      simp only [BodyRun.roots, keptAll, List.flatMap_append, List.mem_append] at member
      rcases member with (member | member) | member
      · exact pre_packets.2.1 f member
      · exact tx_create_avoid.1 f member
      · exact request_packets.2.1 f member
    · change NoCreateAt systemAddress runB.roots
      intro f member
      simp only [BodyRun.roots, keptAll, List.flatMap_append, List.mem_append] at member
      rcases member with (member | member) | member
      · exact pre_packets.2.2.2 f member
      · exact tx_create_avoid.2 f member
      · exact request_packets.2.2.2 f member

private theorem submissionsAB : ConsolidationRequestPublic.submissions [keptA, keptB] =
    [subSender.toBytes ++ payload96] := by
  let user := fun f : Exec.Frame => decide (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96)
  have excluded (fs : List Exec.Frame) (callers : ∀ f ∈ fs, f.sevm.caller = systemAddress) :
      fs.filter user = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro f member selected
    change decide (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96) = true at selected
    exact (of_decide_eq_true selected).1 (callers f member)
  have preA := excluded _ pre_packets.1
  have preB := excluded _ pre_packets.2.2.1
  have reqA := excluded _ request_packets.1
  have reqB := excluded _ request_packets.2.2.1
  have paidCaller : subFrame.sevm.caller = subSender := rfl
  have paidData : subFrame.sevm.data = payload96 := rfl
  have paidSelect : user subFrame = true := by
    apply decide_eq_true
    exact ⟨by rw [paidCaller]; exact subSender_distinct.2.2.1,
      by rw [paidData]; exact payload96_length⟩
  have drainSelect : user drainChildFrame = false := by
    apply decide_eq_false
    intro admitted
    exact admitted.1 drain_facts.2.1
  have txA : runA.txRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress) = [] := by
    rw [tx_outputA.2.1]
    rfl
  have txB : runB.txRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress) =
      [subFrame, drainChildFrame] := by
    rw [tx_outputB.2.1, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, sub_root_retained, drain_root_retained]
    rfl
  have framesA : keptA.keptAt consolidationRequestPredeployAddress =
      runA.preRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress) ++
      runA.txRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress) ++
      (requestRootsOf runA.requests).flatMap (Root.keptAt consolidationRequestPredeployAddress) := by
    rw [KeptBlock.keptAt, BodyRun.roots, List.flatMap_append, List.flatMap_append]
    rfl
  have framesB : keptB.keptAt consolidationRequestPredeployAddress =
      runB.preRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress) ++
      runB.txRoots.flatMap (Root.keptAt consolidationRequestPredeployAddress) ++
      (requestRootsOf runB.requests).flatMap (Root.keptAt consolidationRequestPredeployAddress) := by
    rw [KeptBlock.keptAt, BodyRun.roots, List.flatMap_append, List.flatMap_append]
    rfl
  unfold ConsolidationRequestPublic.submissions
  change ((([keptA, keptB].flatMap (KeptBlock.keptAt consolidationRequestPredeployAddress)).filter user).map
    ConsolidationRequestPublic.submissionRecord) = _
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, framesA, framesB]
  simp only [List.filter_append, preA, preB, reqA, reqB, txA, txB, List.filter_nil,
    List.nil_append, List.append_nil, List.filter_cons, paidSelect, drainSelect,
    Bool.false_eq_true, ite_true, ite_false, List.map_cons, List.map_nil]
  rw [ConsolidationRequestPublic.submissionRecord, paidCaller, paidData]
private theorem emissionsAB : ConsolidationRequestPublic.emissions [keptA, keptB] = [] := by
  have a : ConsolidationRequestPublic.blockConsolidations keptA = [] := by
    change (outputA.requests.filterMap _).flatten = []
    rw [outputA_facts.2.2]
    rfl
  have b : ConsolidationRequestPublic.blockConsolidations keptB = [] := by
    change (outputB.requests.filterMap _).flatten = []
    rw [outputB_facts.2.2]
    rfl
  unfold ConsolidationRequestPublic.emissions
  rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, a, b]
  rfl
private theorem capAB : (ConsolidationRequestPublic.submissions [keptA, keptB]).length ≤ 2 ^ 253 := by
  rw [submissionsAB]
  decide
private theorem fifo_failure : ¬ ConsolidationRequestPublic.Fifo [keptA, keptB] stateB := by
  unfold ConsolidationRequestPublic.Fifo
  rw [submissionsAB, emissionsAB, final_queue_empty, List.nil_append]
  exact List.cons_ne_nil _ _
private theorem submission_length : (subSender.toBytes ++ payload96).length = 116 := by
  simp only [List.length_append, Adr.toBytes, UInt32.length_toBytes, B128.length_toBytes, payload96_length]

/-- **C-S3 coded-SYSTEM control.** Two actual committed Prague blocks retain one paid
submission, then a private privileged drain before the protocol request pass. All root,
fork, clean-history and cap conditions hold except SYSTEM code emptiness. The exact
whole-storage fold still holds; FIFO fails because neither publication nor the final
live queue contains the submitted record. -/
theorem c_s3_control :
    ∃ (cfg : ChainConfig) (checkpoint final : BlockChain) (blocks : List KeptBlock),
      KeptHistory cfg checkpoint blocks final ∧ blocks.length = 2 ∧
      blocks.map (fun b => b.block.txs) = [[], [Sum.inr txSub, Sum.inr txD]] ∧
      (∀ b ∈ blocks, CoveredFork b.fork) ∧
      ConsolidationRequestPublic.installed checkpoint.state ∧
      ConsolidationRequestPublic.word checkpoint.state 0 = B256.max ∧
      ConsolidationRequestPublic.word checkpoint.state 1 = 0 ∧
      ConsolidationRequestPublic.word checkpoint.state 2 = 0 ∧
      ConsolidationRequestPublic.word checkpoint.state 3 = 0 ∧
      checkpoint.state.getCode systemAddress ≠ ByteArray.empty ∧
      HistoryClean blocks ∧ (ConsolidationRequestPublic.submissions blocks).length ≤ 2 ^ 253 ∧
      ConsolidationRequestPublic.submissions blocks = [subSender.toBytes ++ payload96] ∧
      (subSender.toBytes ++ payload96).length = 116 ∧
      ConsolidationRequestPublic.emissions blocks = [] ∧
      ConsolidationRequestPublic.remainingQueue final.state = [] ∧
      ¬ ConsolidationRequestPublic.Fifo blocks final.state ∧
      final.state.getStor consolidationRequestPredeployAddress =
        ConsolidationRequestPublic.storeAfter (checkpoint.state.getStor consolidationRequestPredeployAddress)
          (blocks.flatMap (KeptBlock.keptAt consolidationRequestPredeployAddress)) := by
  have covered : ∀ b ∈ [keptA, keptB], CoveredFork b.fork := by
    intro b member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact CoveredFork.prague
  have code : ConsolidationRequestPublic.installed initial :=
    initial_installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  have excess : ConsolidationRequestPublic.word initial 0 = B256.max := by
    change (initial.getStor consolidationRequestPredeployAddress).get 0 = _
    rw [initial_storage, Stor.get_set_self]
  have count : ConsolidationRequestPublic.word initial 1 = 0 := by
    change (initial.getStor consolidationRequestPredeployAddress).get 1 = _
    rw [initial_storage, Stor.get_set_ne _ (by decide : (0 : B256) ≠ 1)]
    rfl
  have head : ConsolidationRequestPublic.word initial 2 = 0 := by
    change (initial.getStor consolidationRequestPredeployAddress).get 2 = _
    rw [initial_storage, Stor.get_set_ne _ (by decide : (0 : B256) ≠ 2)]
    rfl
  have tail : ConsolidationRequestPublic.word initial 3 = 0 := by
    change (initial.getStor consolidationRequestPredeployAddress).get 3 = _
    rw [initial_storage, Stor.get_set_ne _ (by decide : (0 : B256) ≠ 3)]
    rfl
  have coded : initial.getCode systemAddress ≠ ByteArray.empty := by
    rw [initial_system]
    intro empty
    apply callerCode_runtime.1
    rw [empty]
    exact ByteArray.toList_empty
  refine ⟨config, start, chainB, [keptA, keptB], historyAB, rfl, rfl, covered,
    code, excess, count, head, tail, coded, cleanAB, capAB, submissionsAB, submission_length,
    emissionsAB, final_queue_empty, fifo_failure, ?_⟩
  exact ConsolidationRequestPublic.history_storage_fold historyAB code covered

end Blanc.Composition.ConsolidationRequestDrainControl
