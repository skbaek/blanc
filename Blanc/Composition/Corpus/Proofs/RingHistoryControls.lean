import Blanc.Lift.BeaconRoots.Writer
import Blanc.Lift.HistoryStorage.Writer
import Blanc.TransactionForwardH
import Blanc.Lift.BeaconRoots.Frame
import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk
import Blanc.Lift.WithdrawalRequest.DrainTx
import Blanc.BlockForward
import Blanc.Lift.WithdrawalRequest.SystemProtocol
import Blanc.Lift.ConsolidationRequest.System
import Blanc.Lift.RequestSystem.Effects
import Blanc.ConcreteRunKept
import Blanc.KeptCreateAvoid
import Blanc.ExecutionKeptConfigured
import Blanc.SystemWordWriterKept
import Blanc.SyntheticBpo2Envelope
import Blanc.Corpus.Freeze.BeaconRoots
import Blanc.Corpus.Freeze.HistoryStorage

/-! Actual signed SYSTEM-writer transactions for the ring-history controls.
The initial checkpoint is arbitrary; new block commitments are constructed from
actual body results. No initial header/world-root consistency is asserted. -/

namespace Blanc.Composition.Corpus.Proofs.RingHistoryControls

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.WithdrawalRequest.FloodTx (txD senderE txD_recoveredSender txD_intrinsic)

namespace R

private def senderAcct (nonce : UInt64) (funds : Nat) : Acct :=
  { Acct.nil with nonce := nonce, bal := funds.toB256 }

private def contracts : State :=
  (((State.setPresent .empty systemAddress
    { Acct.nil with nonce := 1, code := SystemWordWriter.code beaconRootsAddress 1 }).setPresent
    beaconRootsAddress { Acct.nil with nonce := 1, code := beaconRootsCode }).setPresent
    historyStorageAddress { Acct.nil with nonce := 1, code := historyStorageCode }).setPresent
    withdrawalRequestPredeployAddress { Acct.nil with nonce := 1, code := withdrawalRequestCode } |>.setPresent
    consolidationRequestPredeployAddress { Acct.nil with nonce := 1, code := consolidationRequestCode }

-- The first block's two actual pre-calls will produce these storage words.
private def preWorld (h : B256) : State :=
  ((contracts.setStorVal beaconRootsAddress 1 1).setStorVal beaconRootsAddress 8192 0).setStorVal
    historyStorageAddress 0 h
private def state (h : B256) : State := (preWorld h).setPresent senderE (senderAcct 2 (2 ^ 100))
private def debit (h : B256) : State :=
  ((state h).incrNonce senderE).setBal senderE ((2 ^ 100 : Nat).toB256 - (2 ^ 21 : Nat).toB256)
private def initial : State := contracts.setPresent senderE (senderAcct 2 (2 ^ 100))

private def benv (h : B256) : Benv :=
  { (default : Benv) with
    state := state h
    stat := { (default : Benv).stat with
      fork := .prague
      chainId := 1
      number := 1
      time := 1
      origState := initial
      blockHashes := [0, h]
      blockGasLimit := 2 ^ 21
      baseFeePerGas := 1 } }
private def msg (h : B256) : Msg :=
  callMessage { (benv h).beginTransaction with state := debit h }
    (transactionTenv (benv h).beginTransaction txD 0 senderE 2 21000 []) txD systemAddress
private def base (h : B256) : Devm := initDevm (msg h)
private def sevm (h : B256) : Sevm := initSevm (msg h)
private def gas : Nat := 1027549
private def callState (h : B256) : Devm :=
  (base h).setMach ⟨[gas.toB256, beaconRootsAddress.toBytes.toB256, 0, 0, 32, 0, 0],
    SystemWordWriter.wordMemory 1, gas, (base h).stateGas⟩
private def childMsg (h : B256) : Msg :=
  SystemWordWriter.childMsg (sevm h) (base h) beaconRootsAddress 1 gas beaconRootsCode
private def childPost (h : B256) : Devm := BeaconRoots.Writer.writerChild (sevm h) (base h) 1 gas
private def post (h : B256) : Devm := SystemWordWriter.post (base h) beaconRootsAddress 1 gas (childPost h)

-- Closed machine-image facts are checked by the owned narrow kernel build.
private theorem initial_prefix (h : B256) : ConcreteRun.stepN 10 (initEvm (msg h)) =
    some ⟨63, sevm h, callState h⟩ := by
  have closed : (fun h => ConcreteRun.stepN 10 (initEvm (msg h))) =
      (fun h => some (⟨63, sevm h, callState h⟩ : Evm)) := by kernel_rfl
  exact congrFun closed h
private theorem installed (h : B256) : (base h).getCode beaconRootsAddress = beaconRootsCode := by
  have closed : (fun h => (base h).getCode beaconRootsAddress) = (fun (_ : B256) => beaconRootsCode) := by kernel_rfl
  exact congrFun closed h
private theorem runtime (h : B256) : (msg h).code = SystemWordWriter.code beaconRootsAddress 1 := by
  have closed : (fun h => (msg h).code) = (fun (_ : B256) => SystemWordWriter.code beaconRootsAddress 1) := by kernel_rfl
  exact congrFun closed h
private theorem debit_eq (h : B256) : ((state h).incrNonce senderE).subBal senderE (2 ^ 21 : Nat).toB256 =
    some (debit h) := by
  have balance : (state h).bal senderE = (2 ^ 100 : Nat).toB256 := by
    change ((preWorld h).setPresent senderE (senderAcct 2 (2 ^ 100))).bal senderE = _
    unfold State.bal
    rw [State.get_setPresent_self]
    rfl
  have affordable : (2 ^ 21 : Nat).toB256 ≤ (state h).bal senderE := by
    rw [balance]
    decide
  simpa only [balance, debit] using subBal_incrNonce_of_le affordable
private theorem at_call (h : B256) : Ninst.At (sevm h).code 63 (.exec .call) := by
  have closed : (fun h => (sevm h).code.getInst 63) =
      (fun (_ : B256) => some (Inst.next (.exec .call))) := by kernel_rfl
  exact congrFun closed h
private theorem at_stop (h : B256) : (sevm h).code.getInst 64 = some (.last .stop) := by
  have closed : (fun h => (sevm h).code.getInst 64) =
      (fun (_ : B256) => some (Inst.last .stop)) := by kernel_rfl
  exact congrFun closed h

private theorem child_exec (h : B256) : exec (initEvm (childMsg h)) = .ok (childPost h) :=
  BeaconRoots.Writer.writerChild_exec CoveredFork.prague rfl rfl (by decide)
private theorem child_error (h : B256) : (childPost h).error = none := BeaconRoots.Writer.framePost_error (childMsg h)
private theorem child_enter (h : B256) :
    (Frame.ofCall (childMsg h)).enter = .run (initEvm (childMsg h)) := by
  apply Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
  change pragueRules.isPrecomp beaconRootsAddress = false
  decide
private theorem child_settle (h : B256) :
    (Frame.ofCall (childMsg h)).settle (.ok (childPost h)) = .ok (childPost h) := by
  rw [Frame.settle_eq_settleMsg_handleErrorWith, executeCode.handleErrorWith_ok]
  simp only [Frame.ofCall, Frame.settleMsg, processMessage.settle, child_error,
    Option.isSome_none, Bool.false_eq_true, ite_false, bind, Except.bind,
    Devm.recordTouch_of_not_touchedSweep (show (childMsg h).benv.stat.rules.settle.touchedSweep = false from rfl)]
private theorem resume (h : B256) :
    Resume.run (.call (SystemWordWriter.parent (base h) beaconRootsAddress 1 gas) 0 0)
      ((Frame.ofCall (childMsg h)).settle (.ok (childPost h))) = .ok (post h) := by
  rw [child_settle, Resume.run_call_ok (by rw [child_error]; rfl) (by change (0 : Nat) < 1024; decide)]
  rfl

private theorem gas_bound : gas < 2 ^ 256 := by decide +kernel

private theorem spawn (h : B256) : Evm.step ⟨63, sevm h, callState h⟩ =
    .spawn (Frame.ofCall (childMsg h))
      (.call (SystemWordWriter.parent (base h) beaconRootsAddress 1 gas) 0 0) 64 := by
  rw [Evm.step_next (at_call h)]
  have affordable : accessCost beaconRootsAddress (base h).accessedAddresses ≤ gas := by
    have bound := accessCost_le (x := beaconRootsAddress) (a := (base h).accessedAddresses)
    change _ ≤ 2600 at bound
    change _ ≤ 1027549
    omega
  have spawned := SystemWordWriter.call_spawn (word := (1 : B256)) CoveredFork.prague
    (show (sevm h).depth ≠ 0 from by change (1024 : Nat) ≠ 0; decide)
    gas_bound affordable (installed h) (show getDelegatedCodeAddress beaconRootsCode = none from rfl)
  simp only [Ninst.step_exec, callState, spawned, XStep.toStep, childMsg]

private noncomputable def childRun (h : B256) : Exec 0 (initSevm (childMsg h))
    (initDevm (childMsg h)) (.ok (childPost h)) :=
  Classical.choice ((exec_iff_exec_eq _ _ _ _).mpr (child_exec h))
private theorem child_commits (h : B256) : Execution.commits (.ok (childPost h)) = true := by
  change (childPost h).error.isNone = true
  rw [child_error]
  rfl
private noncomputable def childFrame (h : B256) : Exec.Frame := .ofRun (childRun h) (child_commits h)
private noncomputable def tailRun (h : B256) : Exec 64 (sevm h) (post h) (.ok (post h)) :=
  .halt (Evm.step_last (at_stop h))
private noncomputable def callRun (h : B256) : Exec 63 (sevm h) (callState h) (.ok (post h)) :=
  .runOk (spawn h) (child_enter h) (childRun h) (resume h) (tailRun h)
private noncomputable def fullRun (h : B256) : Exec 0 (sevm h) (base h) (.ok (post h)) :=
  ConcreteRun.Exec.ofStepN 10 (initial_prefix h) (callRun h)
private theorem retained (h : B256) : Exec.keptAt beaconRootsAddress (fullRun h) = [childFrame h] := by
  rw [show Exec.keptAt beaconRootsAddress (fullRun h) = Exec.keptAt beaconRootsAddress (callRun h) from
    ConcreteRun.Exec.keptAt_ofStepN _ 10 (initial_prefix h) (callRun h)]
  have commits : Frame.settlementCommits (Frame.ofCall (childMsg h)) (.ok (childPost h)) = true :=
    Frame.settlementCommits_ofCall_of_raw_commits (child_commits h)
  rw [show Exec.keptAt beaconRootsAddress (callRun h) = childFrame h :: Exec.keptAt beaconRootsAddress (tailRun h) from
    Exec.keptAt_settled_here (spawn h) (child_enter h) (childRun h) (resume h) (tailRun h) commits rfl]
  rw [tailRun, Exec.keptAt.eq_def]

private theorem snapshot (h : B256) (k : B256) :
    getOrigStorVal (sevm h) beaconRootsAddress k = (base h).getStorVal beaconRootsAddress k := by
  have closed : (fun h k => getOrigStorVal (sevm h) beaconRootsAddress k) =
      (fun h k => (base h).getStorVal beaconRootsAddress k) := by kernel_rfl
  exact congrFun (congrFun closed h) k
private theorem post_facts (h : B256) :
    (post h).error = none ∧ 0 ≤ (post h).refundCounter ∧ (post h).output = [] := by
  have facts := BeaconRoots.Writer.writer_post_facts (sevm h) (base h) 1 gas CoveredFork.prague (snapshot h)
  exact ⟨facts.1, le_trans (by change (0 : Int) ≤ 0; omega) facts.2.2.2.2.2.1, facts.2.1⟩
private theorem message_enter (h : B256) : (Frame.ofCall (msg h)).enter = .run (initEvm (msg h)) :=
  Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl (by change pragueRules.isPrecomp systemAddress = false; decide)
private noncomputable def root (h : B256) : Root :=
  ⟨Frame.ofCall (msg h), initEvm (msg h), .ok (post h), fullRun h⟩
private theorem root_retained (h : B256) : Root.keptAt beaconRootsAddress (root h) = [childFrame h] := by
  have commits : Frame.settlementCommits (Frame.ofCall (msg h)) (.ok (post h)) = true := by
    apply Frame.settlementCommits_ofCall_of_raw_commits
    change (post h).error.isNone = true
    rw [(post_facts h).1]
    rfl
  change (if hc : Frame.settlementCommits (Frame.ofCall (msg h)) (.ok (post h)) = true then
    if (initSevm (msg h)).currentTarget = beaconRootsAddress then _ else Exec.keptAt beaconRootsAddress (fullRun h) else []) = _
  rw [dite_eq_left commits, ite_eq_right (show (initSevm (msg h)).currentTarget ≠ beaconRootsAddress from by change systemAddress ≠ beaconRootsAddress; decide)]
  exact retained h

private theorem prepared (h : B256) :
    prepareMessage { (benv h).beginTransaction with state := debit h }
      (transactionTenv (benv h).beginTransaction txD 0 senderE 2 21000 []) txD = .ok (msg h) :=
  prepareMessage_call rfl
private theorem after_transfer (h : B256) : (msg h).benvAfterTransfer = .ok (msg h).benv :=
  Msg.benvAfterTransfer_of_value_zero rfl
private theorem undelegated (h : B256) : getDelegatedCodeAddress (msg h).code = none := by
  rw [runtime]
  unfold getDelegatedCodeAddress
  apply ite_eq_right
  intro bad
  have size := bad.1
  rw [SystemWordWriter.code_size] at size
  contradiction
private theorem resolved (h : B256) : messageCallExecutionMessage (msg h) = msg h := by
  unfold messageCallExecutionMessage Msg.resolveCodeDelegation
  have nd : (msg h).benv.stat.rules.delegatedCodeAddress (msg h).code = none := by
    unfold ForkRules.delegatedCodeAddress
    rw [undelegated]
    split <;> rfl
  rw [nd]
private theorem entry (h : B256) : messageEntry (msg h) = some (Frame.ofCall (msg h), initEvm (msg h)) := by
  unfold messageEntry legacyEntry
  change (match messageCallDelegation (msg h) with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none) = _
  have delegated : messageCallDelegation (msg h) = .ok (msg h, 0) := rfl
  rw [delegated]
  change enteredFrame (Frame.ofCall (messageCallExecutionMessage (msg h))) = _
  rw [resolved]
  unfold enteredFrame
  rw [message_enter]
private def messageOut (h : B256) : MsgCallOutput :=
  { gasLeft := (post h).gasLeft, refundCounter := ((0 + (post h).refundCounter.toNat : Nat) : Int)
    logs := (post h).logs, accountsToDelete := (post h).accountsToDelete
    error := none, returnData := (post h).output, touchedAccounts := (post h).meta.touchedAccounts }
private theorem message_process (h : B256) : processMessageCall (msg h) = .ok ((post h).state, messageOut h) := by
  apply processMessageCall_call_of_message rfl rfl rfl (undelegated h)
  · apply processMessage_call_of_exec (after_transfer h) rfl
      (by change pragueRules.isPrecomp systemAddress = false; decide)
      ((exec_iff_exec_eq 0 (sevm h) (base h) (.ok (post h))).mp ⟨fullRun h⟩) (post_facts h).1 rfl
  · exact (post_facts h).1
  · exact Int.toNat?_eq_some_of_nonneg (post_facts h).2.1
private theorem message_roots (h : B256) : MessageRoots (msg h) (post h).state (messageOut h) [root h] := by
  refine ⟨message_process h, ?_⟩
  rw [entry]
  rfl
private theorem tx_valid (h : B256) : validateTransaction (benv h).stat.rules txD 0 = .ok (21000, 21000) := by
  exact validateTransaction_ok_of_facts rfl
    (txD_intrinsic rfl rfl rfl rfl rfl 0) (by decide) (by decide) rfl rfl
private theorem sender_account (h : B256) : (benv h).beginTransaction.state.get senderE = senderAcct 2 (2 ^ 100) :=
  State.get_setPresent_self _ _ _
private theorem tx_checked (h : B256) : checkTransaction (benv h).beginTransaction
    (transactionPreludeBout .init txD 0) txD = .ok (senderE, 2, [], 0) := by
  apply checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
  · exact checkTransactionGasLimits_ok_of_room rfl (by change 2 ^ 20 ≤ 2 ^ 21; decide) (by change 0 ≤ _; exact Nat.zero_le _)
  · exact checkTransactionChainId_two rfl rfl
  · exact txD_recoveredSender
  · exact checkTransactionGasFee_two (benv := (benv h).beginTransaction) (tx := txD)
      (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by change 1 ≤ 8; decide) (by decide)
  · exact checkTransactionBlobData_two rfl _
  · exact checkTransactionReceiver_two rfl
  · exact checkTransactionAuthorizationList_two rfl
  · rw [sender_account]
    exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl
private theorem tx_debit (h : B256) : ((benv h).state.incrNonce senderE).subBal senderE
    (txD.gas * 2 + transactionBlobGasFee (benv h) txD).toB256 = some (debit h) := debit_eq h
private theorem tx_message (h : B256) : transactionMessage (benv h) .init txD 0 = .ok (senderE, msg h) := by
  have valid : validateTransaction (benv h).beginTransaction.stat.rules txD 0 = .ok (21000, 21000) := tx_valid h
  have deb : ((benv h).beginTransaction.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee (benv h).beginTransaction txD).toB256 = some (debit h) := debit_eq h
  have tenv : transactionTenvAt (benv h).beginTransaction txD 0 senderE 2 21000 [] =
      transactionTenv (benv h).beginTransaction txD 0 senderE 2 21000 [] := rfl
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none txD rfl]
  simp only [valid, tx_checked, deb, Except.mapError, bind, Except.bind, Option.toExcept]
  rw [tenv, prepared]
private theorem transaction_roots (h : B256) : ∃ stop bout,
    TransactionRoots (benv h) .init txD 0 stop bout senderE [root h] := by
  have refund : Int.toNat? (messageOut h).refundCounter = some (post h).refundCounter.toNat := by
    change Int.toNat? ((0 + (post h).refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (i := ((post h).refundCounter.toNat : Int)) (by omega)
  obtain ⟨bout, process, _, _⟩ := processTransaction_of_stages_gasUsed
    (bout := .init) (index := 0) rfl rfl rfl rfl (tx_valid h) (tx_checked h) (tx_debit h)
      (prepared h) (message_process h) refund
  exact ⟨_, bout, process, msg h, (post h).state, messageOut h, tx_message h, message_roots h⟩

/-- The original signed txD retains its actual successful canonical R child.
This transaction component is not yet a closed block/history control. -/
theorem exists_retained_writer (h : B256) :
    ∃ (b : Benv) (st : State) (bout : BlockOutput) (r : Root) (f : Exec.Frame),
      b.stat.fork = .prague ∧ recoverSender b.stat.chainId txD = .ok senderE ∧
      TransactionRoots b .init txD 0 st bout senderE [r] ∧ Root.keptAt beaconRootsAddress r = [f] ∧
      f.pc = 0 ∧ f.sevm.code = beaconRootsCode ∧ f.sevm.caller = systemAddress ∧
      f.post.error = none ∧ f.post.state =
        (f.pre.state.setStorVal beaconRootsAddress 1 1).setStorVal beaconRootsAddress 8192 1 := by
  obtain ⟨st, bout, roots⟩ := transaction_roots h
  refine ⟨benv h, st, bout, root h, childFrame h, rfl, txD_recoveredSender, roots, root_retained h,
    rfl, rfl, rfl, ?_, ?_⟩
  · change (childPost h).error = none
    exact child_error h
  · change (childPost h).state =
      (((initDevm (childMsg h)).state).setStorVal beaconRootsAddress 1 1).setStorVal beaconRootsAddress 8192 1
    have run := childRun h
    have runtime : (initSevm (childMsg h)).code = beaconRootsCode := rfl
    have fork : CoveredFork (initSevm (childMsg h)).benvStat.fork := CoveredFork.prague
    have stack : (initDevm (childMsg h)).stack = [] := rfl
    have caller : (initSevm (childMsg h)).caller = systemAddress := rfl
    have data : Sevm.dataWord (initSevm (childMsg h)) 0 = 1 := by
      apply dataWord_of_append (pre := []) (post := []) rfl
      exact SystemWordWriter.childMsg_data (sevm h) (base h) beaconRootsAddress 1 gas beaconRootsCode
    have time : (initSevm (childMsg h)).benvStat.time = 1 := rfl
    have target : (initSevm (childMsg h)).currentTarget = beaconRootsAddress := rfl
    generalize hs : initSevm (childMsg h) = s at *
    generalize hb : initDevm (childMsg h) = b at *
    generalize hp : childPost h = p at *
    have effect := (BeaconRoots.exec_system runtime fork stack caller run).2.1
    rw [time, target, data] at effect
    exact effect

-- The parent header is independent of the writer-bearing world. Only this
-- arbitrary initial checkpoint lacks a state-root consistency assertion.
private def parentHeader : Header :=
  { SyntheticBpo2Envelope.checkpointHeader .empty with gasLimit := 2 ^ 21, gasUsed := 2 ^ 20 }
private def parentBlock : Block := { header := parentHeader, txs := [], wds := [], ommers := [] }
private def start : BlockChain := ⟨[parentBlock], initial, 1⟩
private def template : Header := { parentHeader with number := 1, timestamp := 1 }
private def input : Benv := initBenv .prague start
  (BlockForward.commitHeader Fork.prague.ruleSet parentBlock template initial BlockOutput.init)

private theorem input_after_precalls : input.withState (state parentHeader.hash) = benv parentHeader.hash := by
  rfl

private theorem input_from_commitHeader (st : State) (bout : BlockOutput) :
    initBenv .prague start (BlockForward.commitHeader Fork.prague.ruleSet parentBlock template st bout) = input := by
  simpa only [input] using BlockForward.initBenv_commitHeader_body_eq .prague start Fork.prague.ruleSet
    parentBlock template st initial bout BlockOutput.init

end R
namespace RBody
private theorem initial_R : R.initial.getCode beaconRootsAddress = beaconRootsCode := by
  unfold R.initial R.contracts State.getCode
  rw [State.get_setPresent_ne _ (by decide : senderE ≠ beaconRootsAddress),
    State.get_setPresent_ne _ (by decide : consolidationRequestPredeployAddress ≠ beaconRootsAddress),
    State.get_setPresent_ne _ (by decide : withdrawalRequestPredeployAddress ≠ beaconRootsAddress),
    State.get_setPresent_ne _ (by decide : historyStorageAddress ≠ beaconRootsAddress),
    State.get_setPresent_self]
private theorem initial_H : R.initial.getCode historyStorageAddress = historyStorageCode := by
  unfold R.initial R.contracts State.getCode
  rw [State.get_setPresent_ne _ (by decide : senderE ≠ historyStorageAddress),
    State.get_setPresent_ne _ (by decide : consolidationRequestPredeployAddress ≠ historyStorageAddress),
    State.get_setPresent_ne _ (by decide : withdrawalRequestPredeployAddress ≠ historyStorageAddress),
    State.get_setPresent_self]
private def beaconState : State := (Blanc.Lift.SystemExecution.BeaconRoots.systemPost R.input).state
private def historyEnv : Benv := R.input.withState beaconState
private def historyState : State := (Blanc.Lift.SystemExecution.HistoryStorage.systemPost historyEnv).state
private theorem beacon_call :
    processUncheckedSystemTransaction R.input beaconRootsAddress R.input.stat.parentBeaconBlockRoot.toBytes =
      .ok (beaconState, systemCallOutput (Blanc.Lift.SystemExecution.BeaconRoots.systemPost R.input)) :=
  (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots (benv := R.input) CoveredFork.prague initial_R).1
private theorem history_installed : historyEnv.state.getCode historyStorageAddress = historyStorageCode := by
  have foreign := (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots (benv := R.input) CoveredFork.prague initial_R).2.2
    historyStorageAddress (by decide)
  exact (congrArg Acct.code foreign).trans initial_H
private theorem last : historyEnv.stat.blockHashes.getLast? = some R.parentHeader.hash := by rfl
private theorem history_call :
    processUncheckedSystemTransaction historyEnv historyStorageAddress R.parentHeader.hash.toBytes =
      .ok (historyState, systemCallOutput (Blanc.Lift.SystemExecution.HistoryStorage.systemPost historyEnv)) :=
  (Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage (benv := historyEnv) (lastHash := R.parentHeader.hash) CoveredFork.prague history_installed last).1
private theorem beacon_value : Blanc.Lift.SystemExecution.BeaconRoots.systemValue R.input = 0 := by
  apply dataWord_of_append (pre := []) (post := []) rfl
  rfl
private theorem history_value : Blanc.Lift.SystemExecution.HistoryStorage.systemValue historyEnv = R.parentHeader.hash := by
  apply dataWord_of_append (pre := []) (post := []) rfl
  change (historyEnv.stat.blockHashes.getLast?.getD 0).toBytes = _
  rw [last]
  rfl
private theorem initial_writes :
    (fun h : B256 => (((R.initial.setStorVal beaconRootsAddress 1 1).setStorVal
      beaconRootsAddress 8192 0).setStorVal historyStorageAddress 0 h)) = R.state := by
  kernel_rfl

private theorem history_join : historyState = R.state R.parentHeader.hash := by
  have bh := (Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage (benv := historyEnv) (lastHash := R.parentHeader.hash) CoveredFork.prague history_installed last).2.1
  have br := (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots (benv := R.input) CoveredFork.prague initial_R).2.1
  rw [history_value] at bh
  change historyState = _ at bh
  change (Blanc.Lift.SystemExecution.BeaconRoots.systemPost R.input).state = _ at br
  rw [show Blanc.Lift.SystemExecution.HistoryStorage.systemKey historyEnv = 0 from rfl] at bh
  rw [show Blanc.Lift.SystemExecution.BeaconRoots.systemKey R.input = 1 from rfl,
    show Blanc.Lift.SystemExecution.BeaconRoots.systemRootKey R.input = 8192 from rfl, beacon_value] at br
  rw [bh]
  change ((Blanc.Lift.SystemExecution.BeaconRoots.systemPost R.input).state).setStorVal historyStorageAddress 0 R.parentHeader.hash = _
  rw [br]
  exact congrFun initial_writes R.parentHeader.hash
private theorem state_code (h : B256) (a : Adr) : (R.state h).getCode a = R.initial.getCode a := by
  unfold R.state R.initial State.getCode
  by_cases same : senderE = a
  · subst a
    rw [State.get_setPresent_self, State.get_setPresent_self]
  · rw [State.get_setPresent_ne _ same, State.get_setPresent_ne _ same]
    change (R.preWorld h).getCode a = R.contracts.getCode a
    rw [R.preWorld, State.getCode_setStorVal, State.getCode_setStorVal, State.getCode_setStorVal]
private theorem initial_W : R.initial.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode := by
  unfold R.initial R.contracts State.getCode
  rw [State.get_setPresent_ne _ (by decide : senderE ≠ withdrawalRequestPredeployAddress),
    State.get_setPresent_ne _ (by decide : consolidationRequestPredeployAddress ≠ withdrawalRequestPredeployAddress),
    State.get_setPresent_self]
private theorem initial_C : R.initial.getCode consolidationRequestPredeployAddress = consolidationRequestCode := by
  unfold R.initial R.contracts State.getCode
  rw [State.get_setPresent_ne _ (by decide : senderE ≠ consolidationRequestPredeployAddress),
    State.get_setPresent_self]
private theorem initial_S : R.initial.getCode systemAddress = SystemWordWriter.code beaconRootsAddress 1 := by
  unfold R.initial R.contracts State.getCode
  rw [State.get_setPresent_ne _ (by decide : senderE ≠ systemAddress),
    State.get_setPresent_ne _ (by decide : consolidationRequestPredeployAddress ≠ systemAddress),
    State.get_setPresent_ne _ (by decide : withdrawalRequestPredeployAddress ≠ systemAddress),
    State.get_setPresent_ne _ (by decide : historyStorageAddress ≠ systemAddress),
    State.get_setPresent_ne _ (by decide : beaconRootsAddress ≠ systemAddress),
    State.get_setPresent_self]
private theorem initial_installed : SystemCodeInstalled R.initial := by
  intro p member
  simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact RBody.initial_R
  · exact RBody.initial_H
  · exact initial_W
  · exact initial_C
private theorem system_runtime :
    (SystemWordWriter.code beaconRootsAddress 1).toList ≠ [] ∧
    ¬ isValidDelegation (SystemWordWriter.code beaconRootsAddress 1) := by
  constructor
  · apply List.ne_nil_of_length_pos
    rw [← ByteArray.size_eq_length_toList, SystemWordWriter.code_size]
    decide
  · intro bad
    have size := bad.1
    rw [SystemWordWriter.code_size] at size
    contradiction
private theorem transaction_installed {h : B256} {st : State} {bout : BlockOutput}
    (roots : TransactionRoots (R.benv h) .init txD 0 st bout senderE [R.root h]) :
    SystemCodeInstalled st := by
  intro p member
  have code : (R.benv h).state.getCode p.1 = p.2 :=
    (state_code h p.1).trans (initial_installed p member)
  have facts := systemContracts_facts p member
  have chain := roots.chain (KeptFork.rules (Or.inl CoveredFork.prague))
    (by rw [code]; exact facts.2.2) (by rw [code]; exact facts.2.1)
    (show p.1 ∉ (R.benv h).createdAccounts from AdrSet.not_mem_empty)
  exact chain.2.trans code
private theorem transaction_system {h : B256} {st : State} {bout : BlockOutput}
    (roots : TransactionRoots (R.benv h) .init txD 0 st bout senderE [R.root h]) :
    st.getCode systemAddress = SystemWordWriter.code beaconRootsAddress 1 := by
  have code : (R.benv h).state.getCode systemAddress = SystemWordWriter.code beaconRootsAddress 1 :=
    (state_code h systemAddress).trans initial_S
  exact (roots.chain (KeptFork.rules (Or.inl CoveredFork.prague))
    (by rw [code]; exact system_runtime.1) (by rw [code]; exact system_runtime.2)
    (show systemAddress ∉ (R.benv h).createdAccounts from AdrSet.not_mem_empty)).2.trans code

private theorem transaction_storage {h : B256} {st : State} {bout : BlockOutput}
    (roots : TransactionRoots (R.benv h) .init txD 0 st bout senderE [R.root h]) :
    st.getStor beaconRootsAddress = (R.childFrame h).post.getStor beaconRootsAddress := by
  have code : (R.benv h).state.getCode beaconRootsAddress = beaconRootsCode :=
    (state_code h beaconRootsAddress).trans RBody.initial_R
  have facts := systemContracts_facts (beaconRootsAddress, beaconRootsCode) List.mem_cons_self
  have chain := (roots.chain (KeptFork.rules (Or.inl CoveredFork.prague))
    (by rw [code]; exact facts.2.2) (by rw [code]; exact facts.2.1)
    (show beaconRootsAddress ∉ (R.benv h).createdAccounts from AdrSet.not_mem_empty)).1
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, R.root_retained] at chain
  generalize final : st.getStor beaconRootsAddress = t at chain ⊢
  cases chain with
  | cons starts tail => cases tail; rfl

private theorem child_word (h : B256) :
    ((R.childFrame h).post.getStor beaconRootsAddress).get 8192 = 1 := by
  change ((BeaconRoots.Writer.writerChild (R.sevm h) (R.base h) 1 R.gas).state.getStor beaconRootsAddress).get 8192 = 1
  have fork : CoveredFork (R.sevm h).benvStat.fork := CoveredFork.prague
  have key : BeaconRoots.Writer.valueKey (R.sevm h) = 8192 := by
    change (0x1fff : B256) + (1 : B256) % 0x1fff = 8192
    decide
  generalize hs : R.sevm h = s at *
  generalize hb : R.base h = b at *
  have effect := (BeaconRoots.Writer.writerChild_facts s b 1 R.gas fork).2.2.2.2
  rw [effect, key, State.getStor_setStorVal_self, Stor.get_set_self]

private theorem transaction_word {h : B256} {st : State} {bout : BlockOutput}
    (roots : TransactionRoots (R.benv h) .init txD 0 st bout senderE [R.root h]) :
    (st.getStor beaconRootsAddress).get 8192 = 1 := by
  rw [transaction_storage roots]
  exact child_word h

private theorem transaction_output (h : B256) : ∃ st bout,
    TransactionRoots (R.benv h) .init txD 0 st bout senderE [R.root h] ∧
    bout.blockGasUsed ≤ 2 ^ 20 ∧ parseDepositRequests bout = .ok [] := by
  obtain ⟨st, bout, roots⟩ := R.transaction_roots h
  have refund : Int.toNat? (R.messageOut h).refundCounter = some (R.post h).refundCounter.toNat := by
    change Int.toNat? ((0 + (R.post h).refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (i := ((R.post h).refundCounter.toNat : Int)) (by omega)
  obtain ⟨out, process, cumulative, gasUsed, keys, receipt⟩ := processTransaction_of_stages_receipts
    (bout := .init) (index := 0) rfl rfl rfl rfl (R.tx_valid h) (R.tx_checked h) (R.tx_debit h)
      (R.prepared h) (R.message_process h) refund
  have same : bout = out := congrArg Prod.snd (Except.ok.inj (roots.1.symm.trans process))
  subst out
  have logs : (R.messageOut h).logs = [] :=
    (BeaconRoots.Writer.writer_post_facts (R.sevm h) (R.base h) 1 R.gas CoveredFork.prague (R.snapshot h)).2.2.1
  refine ⟨st, bout, roots, ?_, ?_⟩
  · rw [gasUsed, show BlockOutput.init.blockGasUsed = 0 from rfl, Nat.zero_add]
    change txGasUsed txD.gas 21000 (R.messageOut h).gasLeft (R.post h).refundCounter.toNat ≤ txD.gas
    exact (txGasUsed_le (gas := txD.gas) (floor := 21000) (left := (R.messageOut h).gasLeft)
        (refund := (R.post h).refundCounter.toNat) (by decide))
  · apply BlockForward.parseDepositRequests_of_no_logs
    intro k member
    rw [keys] at member
    change k ∈ [BLT.toBytes (.bytes (0 : Nat).toBytes)] at member
    obtain rfl := List.mem_singleton.mp member
    refine ⟨_, receipt, ?_⟩
    exact logs


private theorem body_effect :
    ∃ st bout, applyBody R.input [Sum.inr txD] [] [] = .ok (st, bout) ∧
      (st.getStor beaconRootsAddress).get 8192 = 1 ∧ bout.blockGasUsed ≤ 2 ^ 20 ∧
      SystemCodeInstalled st ∧ st.getCode systemAddress = SystemWordWriter.code beaconRootsAddress 1 := by
  obtain ⟨st, bout, roots, gas, deposits⟩ := transaction_output R.parentHeader.hash
  let txEnv := (R.benv R.parentHeader.hash).withState st
  have installed := transaction_installed (h := R.parentHeader.hash) (st := st) (bout := bout) roots
  have system := transaction_system (h := R.parentHeader.hash) (st := st) (bout := bout) roots
  have wCode : txEnv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode :=
    installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  let stW := (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).state
  let outW := Blanc.Lift.WithdrawalRequest.systemProtocolOutput txEnv
  have wRun : processCheckedSystemTransaction txEnv withdrawalRequestPredeployAddress [] = .ok (stW, outW) :=
    Blanc.Lift.WithdrawalRequest.processCheckedSystemTransaction_withdrawal (benv := txEnv) CoveredFork.prague wCode
  have wCodeAll (a : Adr) : stW.getCode a = st.getCode a := by
    change (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).getCode a =
      (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv).getCode a
    unfold Blanc.Lift.WithdrawalRequest.systemProtocolPost
    exact Blanc.Lift.WithdrawalRequest.systemFramePost_getCode _ _ _ _ _
  have wStorage : stW.getStor beaconRootsAddress = st.getStor beaconRootsAddress :=
    Blanc.Lift.WithdrawalRequest.systemFramePost_other_storage
      (Blanc.Lift.WithdrawalRequest.systemProtocolSevm txEnv)
      (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv) .empty
      (systemTransactionGas - Blanc.Lift.WithdrawalRequest.systemProtocolGas txEnv) beaconRootsAddress
      (by change withdrawalRequestPredeployAddress ≠ beaconRootsAddress; decide)
  generalize hw : stW = stateW at *
  generalize hout : outW = outputW at *
  have cCode : (txEnv.withState stateW).state.getCode consolidationRequestPredeployAddress = consolidationRequestCode :=
    (wCodeAll consolidationRequestPredeployAddress).trans
      (installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  obtain ⟨outC, cRun, cError, cGas, cData⟩ := Blanc.Lift.ConsolidationRequest.system_call_ok
    (benv := txEnv.withState stateW) CoveredFork.prague cCode
  let stC := RequestSystem.sysState SystemExecution.ConsolidationRequest.Amsterdam.sysShape stateW consolidationRequestPredeployAddress
  have cCodeAll (a : Adr) : stC.getCode a = stateW.getCode a :=
    RequestSystem.sysState_getCode SystemExecution.ConsolidationRequest.Amsterdam.sysShape stateW consolidationRequestPredeployAddress a
  have startEq : (R.input.withState RBody.beaconState).withState RBody.historyState =
      R.benv R.parentHeader.hash := by
    change R.input.withState RBody.historyState = _
    rw [RBody.history_join, R.input_after_precalls]
  have txRun : applyTransactions [txD].putIndex
      ((R.input.withState RBody.beaconState).withState RBody.historyState) .init = .ok (txEnv, bout) := by
    rw [startEq]
    change applyTransactions [(0, txD)] (R.benv R.parentHeader.hash) .init = _
    simp only [applyTransactions, roots.1, bind, Except.bind]
    rfl
  have body : applyBody R.input [Sum.inr txD] [] [] =
      .ok (stC, BlockForward.requestsOutput bout outputW.returnData outC.returnData) :=
    BlockForward.applyBody_forward (benv := R.input) (txs := [Sum.inr txD])
    CoveredFork.prague RBody.beacon_call RBody.last RBody.history_call rfl txRun deposits wRun cRun
  refine ⟨stC, BlockForward.requestsOutput bout outputW.returnData outC.returnData, body, ?_, ?_, ?_, ?_⟩
  · have otherW : stateW.getStor beaconRootsAddress = st.getStor beaconRootsAddress := wStorage
    have otherC : stC.getStor beaconRootsAddress = stateW.getStor beaconRootsAddress :=
      RequestSystem.sysState_getStor_other _ _ (by decide : consolidationRequestPredeployAddress ≠ beaconRootsAddress)
    rw [otherC, otherW]
    exact transaction_word roots
  · exact gas
  · intro p member
    exact (cCodeAll p.1).trans ((wCodeAll p.1).trans (installed p member))
  · exact (cCodeAll systemAddress).trans ((wCodeAll systemAddress).trans system)

private theorem packet_pre {st : State} {bout : BlockOutput} {run : BodyRun}
    (body : BodyRoots R.input [Sum.inr txD] [] [] st bout run) :
    run.preState = RBody.historyState ∧ run.preBal = {} ∧ NoCreateAt systemAddress run.preRoots := by
  have avoid := body.pre.noCreateAt_of_code rfl systemAddress
    (by change (R.initial.getCode systemAddress).toList ≠ []; rw [RBody.initial_S]; exact RBody.system_runtime.1)
    (by change ¬ isValidDelegation (R.initial.getCode systemAddress); rw [RBody.initial_S]; exact RBody.system_runtime.2)
    (by decide) (by decide)
  obtain ⟨beacon, beaconBal, br, hr, hb, cb, hh, ch, hpre⟩ := body.pre
  have hB : beaconRootsCall R.input.stat.rules R.input = .ok (RBody.beaconState, ({} : BalBuilder)) := by
    unfold beaconRootsCall
    simp only [show R.input.stat.rules.sys.beaconRoots = true from rfl, ite_true,
      Except.mapError, RBody.beacon_call, bind, Except.bind]
    rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hb.symm.trans hB))
  have hH : historyStorageCall R.input.stat.rules RBody.historyEnv {} =
      .ok (RBody.historyState, ({} : BalBuilder)) := by
    unfold historyStorageCall
    simp only [show R.input.stat.rules.sys.historyStorage = true from rfl, ite_true,
      RBody.last, Option.toExcept, Except.mapError, RBody.history_call, bind, Except.bind]
    rfl
  have final := Prod.mk.inj (Except.ok.inj (hh.symm.trans hH))
  exact ⟨final.1, final.2, avoid⟩
private theorem packet_tx {st : State} {bout : BlockOutput} {run : BodyRun}
    (body : BodyRoots R.input [Sum.inr txD] [] [] st bout run) :
    run.senders = [(senderE, txD)] ∧
    run.txRoots = [R.root R.parentHeader.hash] ∧ NoCreateAt systemAddress run.txRoots ∧
    run.txEnv.state.getCode systemAddress = SystemWordWriter.code beaconRootsAddress 1 := by
  obtain ⟨preState, preBal, _⟩ := packet_pre body
  obtain ⟨decoded, decodedEq, transactions⟩ := body.transactions
  have decode : [Sum.inr txD].mapM (decodeTx R.input.stat.rules) = .ok [txD] := rfl
  obtain rfl := Except.ok.inj (decodedEq.symm.trans decode)
  rw [preState, preBal] at transactions
  change TransactionsRoots [(0, txD)] (R.input.withState RBody.historyState) .init
    run.txEnv run.txOut run.senders run.txRoots at transactions
  rw [RBody.history_join, R.input_after_precalls] at transactions
  obtain ⟨txState, txOut, roots, _, _⟩ := RBody.transaction_output R.parentHeader.hash
  have chosen : TransactionsRoots [(0, txD)] (R.benv R.parentHeader.hash) .init
      ((R.benv R.parentHeader.hash).withState txState) txOut [(senderE, txD)] [R.root R.parentHeader.hash] := by
    simpa only [List.append_nil] using TransactionsRoots.cons roots (TransactionsRoots.nil _ _)
  have same := transactions.unique chosen
  refine ⟨same.2.2.1, same.2.2.2, ?_, ?_⟩
  · rw [same.2.2.2]
    apply Root.noCreateAt_of_code
    · rfl
    · change (R.msg R.parentHeader.hash).code.toList ≠ []
      rw [R.runtime]
      exact RBody.system_runtime.1
    · change (some systemAddress : Option Adr) = none → systemAddress ≠ systemAddress
      intro impossible
      cases impossible
  · rw [same.1]
    exact RBody.transaction_system roots
private theorem packet_requests {st : State} {bout : BlockOutput} {run : BodyRun}
    (body : BodyRoots R.input [Sum.inr txD] [] [] st bout run) :
    NoCreateAt systemAddress (requestRootsOf run.requests) := by
  have system := (RBody.packet_tx body).2.2.2
  let reqEnv := run.txEnv.withState (withdrawalsPass R.input.stat.rules run.txEnv run.txOut []).1
  have noWd : withdrawalsPass R.input.stat.rules run.txEnv run.txOut [] = (run.txEnv.state, run.txOut) := by
    unfold withdrawalsPass
    rw [show R.input.stat.rules.header.withdrawalsRoot = true from rfl]
    simp only [ite_true]
    unfold BalBuilder.incorporateSystem
    rw [show R.input.stat.rules.bal = none from rfl]
    rfl
  have code : reqEnv.state.getCode systemAddress = SystemWordWriter.code beaconRootsAddress 1 := by
    change (withdrawalsPass R.input.stat.rules run.txEnv run.txOut []).1.getCode systemAddress = _
    rw [noWd]
    exact system
  have nonempty : (reqEnv.state.getCode systemAddress).toList ≠ [] := by
    rw [code]; exact RBody.system_runtime.1
  have nondelegating : ¬ isValidDelegation (reqEnv.state.getCode systemAddress) := by
    rw [code]; exact RBody.system_runtime.2
  have hsg : reqEnv.stat.rules.stateGas = none := by
    change run.txEnv.stat.rules.stateGas = none
    rw [body.txEnv_stat]
    rfl
  have hrequests : reqEnv.stat.rules.requests = pragueRequests := by
    change run.txEnv.stat.rules.requests = pragueRequests
    rw [body.txEnv_stat]
    rfl
  obtain ⟨reqState, reqOut, pass⟩ := body.requests
  change RequestPass reqEnv _ reqState reqOut run.requests at pass
  unfold RequestPass at pass
  have enabled : reqEnv.stat.rules.header.requestsHash = true := by
    change run.txEnv.stat.rules.header.requestsHash = true
    rw [body.txEnv_stat]
    rfl
  rw [ite_eq_left enabled] at pass
  obtain ⟨deposits, acc, bal, _, fold, _⟩ := pass
  rw [hrequests] at fold
  exact fold.prague_noCreateAt_of_code hsg systemAddress nonempty nondelegating (by decide) (by decide)
private theorem packet_clean {st : State} {bout : BlockOutput} {run : BodyRun}
    (body : BodyRoots R.input [Sum.inr txD] [] [] st bout run) :
    NoSenderAt systemAddress run.senders ∧ NoAuthorityAt systemAddress run.senders ∧
      NoCreateAt systemAddress run.roots := by
  have tx := packet_tx body
  refine ⟨?_, ?_, ?_⟩
  · rw [tx.1]
    intro p member
    obtain rfl := List.mem_singleton.mp member
    change senderE ≠ systemAddress
    decide
  · rw [tx.1]
    intro p member auth memberAuth
    obtain rfl := List.mem_singleton.mp member
    change auth ∈ ([] : List Auth) at memberAuth
    cases memberAuth
  · have avoidP := (packet_pre body).2.2
    have avoidT := tx.2.2.1
    have avoidR := packet_requests body
    intro f member
    simp only [BodyRun.roots, keptAll, List.flatMap_append, List.mem_append] at member
    rcases member with (member | member) | member
    · exact avoidP f member
    · exact avoidT f member
    · exact avoidR f member
end RBody

open Blanc.Corpus.Freeze
theorem r_s3_control : BeaconRoots.R_S3_control := by
  obtain ⟨st, bout, applied, word, gas, installed, system⟩ := RBody.body_effect
  obtain ⟨run, body⟩ := exists_bodyRoots applied
  let cfg := ChainConfig.single 1 .prague
  let header := BlockForward.commitHeader Fork.prague.ruleSet R.parentBlock R.template st bout
  let block : Block := {header := header, txs := [Sum.inr txD], wds := [], ommers := []}
  let stop : BlockChain := ⟨appendBlock R.start.blocks block, st, R.start.chainId⟩
  let kb : KeptBlock := ⟨R.start, block, .prague, bout, run⟩
  have headerOK : validateHeader Fork.prague.ruleSet R.start header = .ok () := by
    apply BlockForward.commitHeader_ok CoveredFork.prague rfl rfl rfl
    · exact BlockForward.calculateBaseFeePerGas_unit (by decide) (by decide) (by decide) (by decide)
    · rfl
    · change bout.blockGasUsed ≤ 2 ^ 21
      exact Nat.le_trans gas (by decide)
    · decide
    · rfl
    · rfl
  have envEq : kb.benv = R.input := R.input_from_commitHeader st bout
  have forkAt : cfg.forkAt block.header.number block.header.timestamp = .ok .prague :=
    ChainConfig.single_forkAt 1 .prague _ _
  have step : KeptStep cfg kb stop := by
    refine ⟨?_, forkAt, Or.inl CoveredFork.prague, ?_⟩
    · apply BlockForward.stateTransitionUsing_forward rfl forkAt CoveredFork.prague headerOK rfl
      · change applyBody kb.benv [Sum.inr txD] [] [] = _
        rw [envEq]
        exact applied
      all_goals rfl
    · change BodyRoots kb.benv [Sum.inr txD] [] [] st bout run
      rw [envEq]
      exact body
  have history : KeptHistory cfg R.start [kb] stop := by
    exact KeptHistory.step KeptHistory.refl step
  have clean := RBody.packet_clean body
  refine ⟨cfg, R.start, stop, [kb], 1, history, ?_, RBody.initial_R, ?_, RBody.initial_S, ?_⟩
  · intro b member
    obtain rfl := List.mem_singleton.mp member
    exact CoveredFork.prague
  · refine ⟨?_, ?_, ?_⟩
    all_goals intro b member; obtain rfl := List.mem_singleton.mp member
    · exact clean.1
    · exact clean.2.1
    · exact clean.2.2
  · intro equal
    have value := congrFun equal 8192
    have expected : BeaconRoots.writeAll (storOf R.start.state BeaconRoots.addr)
        ([kb].map BeaconRoots.blockWrite) 8192 = 0 := by
      change BeaconRoots.writeAll (storOf R.start.state BeaconRoots.addr) [(1, 0)] 8192 = 0
      simp only [BeaconRoots.writeAll, BeaconRoots.write]
      rw [ite_eq_left (by decide : (8192 : B256) = BeaconRoots.rootKey 1)]
    change (st.getStor beaconRootsAddress).get 8192 = _ at value
    rw [word, expected] at value
    exact (by decide : (1 : B256) ≠ 0) value
namespace H
private def initial (w : B256) : State := R.initial.setPresent systemAddress
  {Acct.nil with nonce := 1, code := SystemWordWriter.code historyStorageAddress w}
private def start (w : B256) : BlockChain := ⟨[R.parentBlock], initial w, 1⟩
private def input (w : B256) : Benv := initBenv .prague (start w)
  (BlockForward.commitHeader Fork.prague.ruleSet R.parentBlock R.template (initial w) .init)
private theorem initial_code (w : B256) (a : Adr) (different : systemAddress ≠ a) :
    (initial w).getCode a = R.initial.getCode a := by
  change ((R.initial.setPresent systemAddress _).get a).code = _
  rw [State.get_setPresent_ne _ different]
  rfl
private theorem initial_system (w : B256) :
    (initial w).getCode systemAddress = SystemWordWriter.code historyStorageAddress w := by
  change ((R.initial.setPresent systemAddress _).get systemAddress).code = _
  rw [State.get_setPresent_self]
private theorem initial_R (w : B256) : (initial w).getCode beaconRootsAddress = beaconRootsCode :=
  (initial_code w _ (by decide)).trans RBody.initial_R
private theorem initial_H (w : B256) : (initial w).getCode historyStorageAddress = historyStorageCode :=
  (initial_code w _ (by decide)).trans RBody.initial_H
private def beaconState (w : B256) := (Blanc.Lift.SystemExecution.BeaconRoots.systemPost (input w)).state
private def historyEnv (w : B256) := (input w).withState (beaconState w)
private def preState (w : B256) := (Blanc.Lift.SystemExecution.HistoryStorage.systemPost (historyEnv w)).state
private def txBenv (w : B256) := (input w).withState (preState w)
private theorem beacon_call (w : B256) :
 processUncheckedSystemTransaction (input w) beaconRootsAddress (input w).stat.parentBeaconBlockRoot.toBytes =
   .ok (beaconState w, systemCallOutput (Blanc.Lift.SystemExecution.BeaconRoots.systemPost (input w))) :=
 (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
  (benv := input w) CoveredFork.prague (initial_R w)).1
private theorem beacon_code (w : B256) (a : Adr) : (beaconState w).getCode a = (initial w).getCode a := by
  have effect := (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := input w) CoveredFork.prague (initial_R w)).2.1
  change beaconState w = _ at effect
  rw [effect, State.getCode_setStorVal, State.getCode_setStorVal]
  rfl
private theorem history_installed (w : B256) : (historyEnv w).state.getCode historyStorageAddress = historyStorageCode :=
 (beacon_code w _).trans (initial_H w)
private theorem last (w : B256) : (historyEnv w).stat.blockHashes.getLast? = some R.parentHeader.hash := by rfl
private theorem history_call (w : B256) :
 processUncheckedSystemTransaction (historyEnv w) historyStorageAddress R.parentHeader.hash.toBytes =
   .ok (preState w, systemCallOutput (Blanc.Lift.SystemExecution.HistoryStorage.systemPost (historyEnv w))) :=
 (Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
  (benv := historyEnv w) CoveredFork.prague (history_installed w) (last w)).1
private theorem pre_code (w : B256) (a : Adr) : (preState w).getCode a = (initial w).getCode a := by
  have effect := (Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnv w) CoveredFork.prague (history_installed w) (last w)).2.1
  change preState w = _ at effect
  rw [effect, State.getCode_setStorVal]
  exact beacon_code w a
private theorem sender_account (w : B256) : (txBenv w).state.get senderE = R.senderAcct 2 (2 ^ 100) := by
  have h := (Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnv w) CoveredFork.prague (history_installed w) (last w)).2.2 senderE (by decide)
  have b := (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := input w) CoveredFork.prague (initial_R w)).2.2 senderE (by decide)
  change (preState w).get senderE = _ at h
  change (beaconState w).get senderE = _ at b
  change (preState w).get senderE = _
  rw [h]
  change (beaconState w).get senderE = _
  rw [b]
  change (R.initial.setPresent systemAddress _).get senderE = _
  rw [State.get_setPresent_ne _ (by decide : systemAddress ≠ senderE)]
  exact State.get_setPresent_self _ _ _
private def debit (w : B256) : State := ((txBenv w).state.incrNonce senderE).setBal senderE
  ((txBenv w).state.bal senderE - (2 ^ 21 : Nat).toB256)
private def msg (w : B256) : Msg := callMessage {(txBenv w).beginTransaction with state := debit w}
  (transactionTenv (txBenv w).beginTransaction txD 0 senderE 2 21000 []) txD systemAddress
private def post (w : B256) : Devm := SystemWordWriter.post (initDevm (msg w)) historyStorageAddress w
  ((msg w).gas - 27) (HistoryStorage.Writer.writerChild (initSevm (msg w)) (initDevm (msg w)) w ((msg w).gas - 27))
private theorem runtime (w : B256) : (msg w).code = SystemWordWriter.code historyStorageAddress w := by
  change (debit w).getCode systemAddress = _
  rw [debit, State.setBal_getCode]
  change (((txBenv w).state.incrNonce senderE).get systemAddress).code = _
  rw [State.incrNonce_get_code]
  exact (pre_code w _).trans (initial_system w)
private theorem installed (w : B256) : (msg w).benv.state.getCode historyStorageAddress = historyStorageCode := by
  change (debit w).getCode historyStorageAddress = _
  rw [debit, State.setBal_getCode]
  change (((txBenv w).state.incrNonce senderE).get historyStorageAddress).code = _
  rw [State.incrNonce_get_code]
  exact (pre_code w _).trans (initial_H w)
private theorem snapshot (w : B256) (k : B256) :
    getOrigStorVal (initSevm (msg w)) historyStorageAddress k =
      (initDevm (msg w)).getStorVal historyStorageAddress k := by
  change ((txBenv w).state.getStor historyStorageAddress).get k = ((debit w).getStor historyStorageAddress).get k
  unfold debit State.getStor
  rw [State.setBal_get_ne (by decide : senderE ≠ historyStorageAddress)]
  rw [State.incrNonce_get_stor, ite_eq_right (by rintro ⟨same, _⟩; exact (by decide : senderE ≠ historyStorageAddress) same)]
private theorem exec (w : B256) : Jaune.exec (initEvm (msg w)) = .ok (post w) := by
  have installed := installed w
  have runtime := runtime w
  have fork : CoveredFork (msg w).benv.stat.fork := CoveredFork.prague
  have depth : (msg w).depth ≠ 0 := by change (1024 : Nat) ≠ 0; decide
  have dynamic : (msg w).isStatic = false := rfl
  have target : (msg w).currentTarget = systemAddress := rfl
  have gasEq : (msg w).gas = 1027576 := by
    simp only [msg, callMessage, transactionTenv]
    rfl
  have gasLt : (msg w).gas < 2 ^ 256 := by rw [gasEq]; decide
  have enough : 52027 ≤ (msg w).gas := by rw [gasEq]; decide
  unfold post
  generalize hm : msg w = m at *
  exact HistoryStorage.Writer.message_exec fork depth dynamic target gasLt enough installed runtime
private theorem debit_code (w : B256) (a : Adr) : (debit w).getCode a = (initial w).getCode a := by
  rw [debit, State.setBal_getCode]
  change (((txBenv w).state.incrNonce senderE).get a).code = _
  rw [State.incrNonce_get_code]
  exact pre_code w a
private theorem post_facts (w : B256) :
    (post w).error = none ∧ (post w).logs = [] ∧
    (∀ a, (post w).getCode a = (initial w).getCode a) ∧
    (post w).accountsToDelete.isEmpty = true ∧ 0 ≤ (post w).refundCounter ∧
    (post w).state = (debit w).setStorVal historyStorageAddress 0 w := by
  have fork : CoveredFork (initSevm (msg w)).benvStat.fork := CoveredFork.prague
  have origin := snapshot w
  have key : HistoryStorage.Writer.key (initSevm (msg w)) = 0 := by
    change ((1 : B256) - 1) % 8191 = 0
    decide
  have code (a : Adr) : (initDevm (msg w)).getCode a = (initial w).getCode a := debit_code w a
  have err : (initDevm (msg w)).error = none := rfl
  have logs : (initDevm (msg w)).logs = [] := rfl
  have dels : (initDevm (msg w)).accountsToDelete.isEmpty = true := rfl
  have refund : (0 : Int) ≤ (initDevm (msg w)).refundCounter := by rfl
  unfold post
  generalize hs : initSevm (msg w) = s at *
  generalize hb : initDevm (msg w) = b at *
  have facts := HistoryStorage.Writer.writer_post_facts s b w ((msg w).gas - 27) fork origin
  refine ⟨facts.1.trans err, facts.2.2.1.trans logs, ?_, facts.2.2.2.2.1.trans dels,
    le_trans refund facts.2.2.2.2.2.1, ?_⟩
  · intro a
    exact (facts.2.2.2.1 a).trans (code a)
  · rw [facts.2.2.2.2.2.2, key]
    rw [← hb]
    rfl
private theorem initial_installed (w : B256) : SystemCodeInstalled (initial w) := by
  intro p member
  have different : systemAddress ≠ p.1 := by
    simp only [systemContracts, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  exact (initial_code w p.1 different).trans (RBody.initial_installed p member)
private theorem tx_valid (w : B256) : validateTransaction (txBenv w).stat.rules txD 0 = .ok (21000, 21000) := by
  exact validateTransaction_ok_of_facts rfl
    (txD_intrinsic rfl rfl rfl rfl rfl 0) (by decide) (by decide) rfl rfl
private theorem tx_checked (w : B256) : checkTransaction (txBenv w).beginTransaction
    (transactionPreludeBout .init txD 0) txD = .ok (senderE, 2, [], 0) := by
  apply checkTransaction_ok_of_parts (maxFee := 2 ^ 20 * 8) (maxFee' := 2 ^ 20 * 8)
  · exact checkTransactionGasLimits_ok_of_room rfl (by change 2 ^ 20 ≤ 2 ^ 21; decide) (by change 0 ≤ _; exact Nat.zero_le _)
  · exact checkTransactionChainId_two rfl rfl
  · exact txD_recoveredSender
  · exact checkTransactionGasFee_two (benv := (txBenv w).beginTransaction) (tx := txD)
      (maxPriorityFee := 1) (maxFee := 8) rfl (by decide) (by change 1 ≤ 8; decide) (by decide)
  · exact checkTransactionBlobData_two rfl _
  · exact checkTransactionReceiver_two rfl
  · exact checkTransactionAuthorizationList_two rfl
  · rw [show (txBenv w).beginTransaction.state.get senderE = R.senderAcct 2 (2 ^ 100) from sender_account w]
    exact checkTransactionSenderAccount_ok_of_noCode rfl (by decide) rfl
private theorem tx_debit (w : B256) : ((txBenv w).state.incrNonce senderE).subBal senderE
    (txD.gas * 2 + transactionBlobGasFee (txBenv w) txD).toB256 = some (debit w) := by
  have balance : (txBenv w).state.bal senderE = (2 ^ 100 : Nat).toB256 :=
    congrArg Acct.bal (sender_account w)
  have affordable : (2 ^ 21 : Nat).toB256 ≤ (txBenv w).state.bal senderE := by rw [balance]; decide
  exact subBal_incrNonce_of_le affordable
private theorem prepared (w : B256) : prepareMessage {(txBenv w).beginTransaction with state := debit w}
    (transactionTenv (txBenv w).beginTransaction txD 0 senderE 2 21000 []) txD = .ok (msg w) :=
  prepareMessage_call rfl
private theorem undelegated (w : B256) : getDelegatedCodeAddress (msg w).code = none := by
  rw [runtime]
  unfold getDelegatedCodeAddress
  apply ite_eq_right
  intro bad
  have size := bad.1
  rw [SystemWordWriter.code_size] at size
  contradiction
private def messageOut (w : B256) : MsgCallOutput :=
  { gasLeft := (post w).gasLeft, refundCounter := ((0 + (post w).refundCounter.toNat : Nat) : Int)
    logs := (post w).logs, accountsToDelete := (post w).accountsToDelete
    error := none, returnData := (post w).output, touchedAccounts := (post w).meta.touchedAccounts }
private theorem message_process (w : B256) : processMessageCall (msg w) = .ok ((post w).state, messageOut w) := by
  apply processMessageCall_call_of_message rfl rfl rfl (undelegated w)
  · have unchanged : (msg w).withBenv (msg w).benv = msg w := by cases msg w; rfl
    apply processMessage_call_of_exec (msg := msg w) (benv := (msg w).benv)
      (Msg.benvAfterTransfer_of_value_zero rfl) rfl
      (by change pragueRules.isPrecomp systemAddress = false; decide)
    · rw [unchanged]
      exact exec w
    · exact (post_facts w).1
    · rfl
  · exact (post_facts w).1
  · exact Int.toNat?_eq_some_of_nonneg (post_facts w).2.2.2.2.1
private theorem entry (w : B256) : messageEntry (msg w) = some (Frame.ofCall (msg w), initEvm (msg w)) := by
  have resolved : messageCallExecutionMessage (msg w) = msg w := by
    unfold messageCallExecutionMessage Msg.resolveCodeDelegation
    have nd : (msg w).benv.stat.rules.delegatedCodeAddress (msg w).code = none := by
      unfold ForkRules.delegatedCodeAddress
      rw [undelegated]
      split <;> rfl
    rw [nd]
  have enter : (Frame.ofCall (msg w)).enter = .run (initEvm (msg w)) :=
    Frame.enter_run_of_nonprecompile (Msg.benvAfterTransfer_of_value_zero rfl) rfl
      (by change pragueRules.isPrecomp systemAddress = false; decide)
  unfold messageEntry legacyEntry
  change (match messageCallDelegation (msg w) with
    | .ok (d, _) => enteredFrame (Frame.ofCall (messageCallExecutionMessage d))
    | .error _ => none) = _
  rw [show messageCallDelegation (msg w) = .ok (msg w, 0) from rfl]
  change enteredFrame (Frame.ofCall (messageCallExecutionMessage (msg w))) = _
  rw [resolved]
  unfold enteredFrame
  rw [enter]
private noncomputable def root (w : B256) : Root :=
  ⟨Frame.ofCall (msg w), initEvm (msg w), .ok (post w),
    Classical.choice ((exec_iff_exec_eq _ _ _ _).mpr (exec w))⟩
private theorem message_roots (w : B256) : MessageRoots (msg w) (post w).state (messageOut w) [root w] := by
  refine ⟨message_process w, ?_⟩
  rw [entry]
  rfl
private theorem tx_message (w : B256) : transactionMessage (txBenv w) .init txD 0 = .ok (senderE, msg w) := by
  have valid : validateTransaction (txBenv w).beginTransaction.stat.rules txD 0 = .ok (21000, 21000) := tx_valid w
  have deb : ((txBenv w).beginTransaction.state.incrNonce senderE).subBal senderE
      (txD.gas * 2 + transactionBlobGasFee (txBenv w).beginTransaction txD).toB256 = some (debit w) := tx_debit w
  have tenv : transactionTenvAt (txBenv w).beginTransaction txD 0 senderE 2 21000 [] =
      transactionTenv (txBenv w).beginTransaction txD 0 senderE 2 21000 [] := rfl
  unfold transactionMessage
  dsimp only
  rw [recoverValidationSender_of_stateGas_none txD rfl]
  simp only [valid, tx_checked, deb, Except.mapError, bind, Except.bind, Option.toExcept]
  rw [tenv, prepared]
private theorem transaction_output (w : B256) : ∃ st bout,
    TransactionRoots (txBenv w) .init txD 0 st bout senderE [root w] ∧
    bout.blockGasUsed ≤ 2 ^ 20 ∧ parseDepositRequests bout = .ok [] ∧
    (st.getStor historyStorageAddress).get 0 = w ∧ SystemCodeInstalled st ∧
    st.getCode systemAddress = SystemWordWriter.code historyStorageAddress w := by
  have refund : Int.toNat? (messageOut w).refundCounter = some (post w).refundCounter.toNat := by
    change Int.toNat? ((0 + (post w).refundCounter.toNat : Nat) : Int) = _
    simp only [Nat.zero_add]
    exact Int.toNat?_eq_some_of_nonneg (by omega)
  obtain ⟨bout, process, cumulative, gasUsed, keys, receipt⟩ := processTransaction_of_stages_receipts
    (bout := .init) (index := 0) rfl rfl rfl rfl (tx_valid w) (tx_checked w) (tx_debit w)
      (prepared w) (message_process w) refund
  have roots : TransactionRoots (txBenv w) .init txD 0 _ bout senderE [root w] :=
    ⟨process, msg w, (post w).state, messageOut w, tx_message w, message_roots w⟩
  have facts := post_facts w
  have noDels : (post w).accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    exact facts.2.2.2.1
  have hcode : ((post w).state.getCode historyStorageAddress).toList ≠ [] := by
    change ((post w).getCode historyStorageAddress).toList ≠ []
    rw [facts.2.2.1, initial_H]
    exact (systemContracts_facts (historyStorageAddress, historyStorageCode)
      (List.mem_cons_of_mem _ List.mem_cons_self)).2.2
  refine ⟨_, bout, roots, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gasUsed, show BlockOutput.init.blockGasUsed = 0 from rfl, Nat.zero_add]
    change txGasUsed txD.gas 21000 (messageOut w).gasLeft (post w).refundCounter.toNat ≤ txD.gas
    exact txGasUsed_le (by decide)
  · apply BlockForward.parseDepositRequests_of_no_logs
    intro k member
    rw [keys] at member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨_, receipt, facts.2.1⟩
  · change (((post w).accountsToDelete.toList.foldl destroyAccount _).getStor historyStorageAddress).get 0 = w
    rw [noDels, List.foldl_nil]
    rw [getStor_addBal_of_code_nonempty _ (by rw [State.addBal_getCode]; exact hcode),
      getStor_addBal_of_code_nonempty _ hcode, facts.2.2.2.2.2,
      State.getStor_setStorVal_self, Stor.get_set_self]
  · intro p member
    have code : (txBenv w).state.getCode p.1 = p.2 := (pre_code w p.1).trans (initial_installed w p member)
    have pf := systemContracts_facts p member
    exact (roots.chain (KeptFork.rules (Or.inl CoveredFork.prague))
      (by rw [code]; exact pf.2.2) (by rw [code]; exact pf.2.1)
      (show p.1 ∉ (txBenv w).createdAccounts from AdrSet.not_mem_empty)).2.trans code
  · have code : (txBenv w).state.getCode systemAddress = SystemWordWriter.code historyStorageAddress w :=
      (pre_code w _).trans (initial_system w)
    have ne : (SystemWordWriter.code historyStorageAddress w).toList ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [← ByteArray.size_eq_length_toList, SystemWordWriter.code_size]
      decide
    have nd : ¬ isValidDelegation (SystemWordWriter.code historyStorageAddress w) := by
      intro bad
      have size := bad.1
      rw [SystemWordWriter.code_size] at size
      exact (by decide : (65 : Nat) ≠ 23) size
    exact (roots.chain (KeptFork.rules (Or.inl CoveredFork.prague))
      (by rw [code]; exact ne) (by rw [code]; exact nd)
      (show systemAddress ∉ (txBenv w).createdAccounts from AdrSet.not_mem_empty)).2.trans code
end H

namespace HBody
private theorem body_effect (w : B256) :
    ∃ st bout, applyBody (H.input w) [Sum.inr txD] [] [] = .ok (st, bout) ∧
      (st.getStor historyStorageAddress).get 0 = w ∧ bout.blockGasUsed ≤ 2 ^ 20 ∧
      SystemCodeInstalled st ∧ st.getCode systemAddress = SystemWordWriter.code historyStorageAddress w := by
  obtain ⟨st, bout, roots, gas, deposits, word, installed, system⟩ := H.transaction_output w
  let txEnv := (H.txBenv w).withState st
  have wCode : txEnv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode :=
    installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  let stW := (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).state
  let outW := Blanc.Lift.WithdrawalRequest.systemProtocolOutput txEnv
  have wRun : processCheckedSystemTransaction txEnv withdrawalRequestPredeployAddress [] = .ok (stW, outW) :=
    Blanc.Lift.WithdrawalRequest.processCheckedSystemTransaction_withdrawal (benv := txEnv) CoveredFork.prague wCode
  have wCodeAll (a : Adr) : stW.getCode a = st.getCode a := by
    change (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).getCode a =
      (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv).getCode a
    unfold Blanc.Lift.WithdrawalRequest.systemProtocolPost
    exact Blanc.Lift.WithdrawalRequest.systemFramePost_getCode _ _ _ _ _
  have wStorage : stW.getStor historyStorageAddress = st.getStor historyStorageAddress :=
    Blanc.Lift.WithdrawalRequest.systemFramePost_other_storage
      (Blanc.Lift.WithdrawalRequest.systemProtocolSevm txEnv)
      (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv) .empty
      (systemTransactionGas - Blanc.Lift.WithdrawalRequest.systemProtocolGas txEnv) historyStorageAddress
      (by change withdrawalRequestPredeployAddress ≠ historyStorageAddress; decide)
  generalize hw : stW = stateW at *
  generalize hout : outW = outputW at *
  have cCode : (txEnv.withState stateW).state.getCode consolidationRequestPredeployAddress = consolidationRequestCode :=
    (wCodeAll consolidationRequestPredeployAddress).trans
      (installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  obtain ⟨outC, cRun, cError, cGas, cData⟩ := Blanc.Lift.ConsolidationRequest.system_call_ok
    (benv := txEnv.withState stateW) CoveredFork.prague cCode
  let stC := RequestSystem.sysState SystemExecution.ConsolidationRequest.Amsterdam.sysShape stateW consolidationRequestPredeployAddress
  have cCodeAll (a : Adr) : stC.getCode a = stateW.getCode a :=
    RequestSystem.sysState_getCode SystemExecution.ConsolidationRequest.Amsterdam.sysShape stateW consolidationRequestPredeployAddress a
  have txRun : applyTransactions [txD].putIndex
      (((H.input w).withState (H.beaconState w)).withState (H.preState w)) .init = .ok (txEnv, bout) := by
    change applyTransactions [(0, txD)] (H.txBenv w) .init = _
    simp only [applyTransactions, roots.1, bind, Except.bind]
    rfl
  have body : applyBody (H.input w) [Sum.inr txD] [] [] =
      .ok (stC, BlockForward.requestsOutput bout outputW.returnData outC.returnData) :=
    BlockForward.applyBody_forward (benv := H.input w) (txs := [Sum.inr txD])
      CoveredFork.prague (H.beacon_call w) (H.last w) (H.history_call w) rfl txRun deposits wRun cRun
  refine ⟨stC, BlockForward.requestsOutput bout outputW.returnData outC.returnData, body, ?_, gas, ?_, ?_⟩
  · have otherC : stC.getStor historyStorageAddress = stateW.getStor historyStorageAddress :=
      RequestSystem.sysState_getStor_other _ _ (by decide : consolidationRequestPredeployAddress ≠ historyStorageAddress)
    rw [otherC, wStorage]
    exact word
  · intro p member
    exact (cCodeAll p.1).trans ((wCodeAll p.1).trans (installed p member))
  · exact (cCodeAll systemAddress).trans ((wCodeAll systemAddress).trans system)
private theorem system_runtime (w : B256) :
    (SystemWordWriter.code historyStorageAddress w).toList ≠ [] ∧
    ¬ isValidDelegation (SystemWordWriter.code historyStorageAddress w) := by
  constructor
  · apply List.ne_nil_of_length_pos
    rw [← ByteArray.size_eq_length_toList, SystemWordWriter.code_size]
    decide
  · intro bad
    have size := bad.1
    rw [SystemWordWriter.code_size] at size
    exact (by decide : (65 : Nat) ≠ 23) size
private theorem pre_state (w : B256) {st : State} {bout : BlockOutput} {run : BodyRun}
    (body : BodyRoots (H.input w) [Sum.inr txD] [] [] st bout run) :
    run.preState = H.preState w ∧ run.preBal = {} := by
  obtain ⟨beacon, beaconBal, br, hr, hb, cb, hh, ch, hpre⟩ := body.pre
  have hB : beaconRootsCall (H.input w).stat.rules (H.input w) = .ok (H.beaconState w, ({} : BalBuilder)) := by
    unfold beaconRootsCall
    simp only [show (H.input w).stat.rules.sys.beaconRoots = true from rfl, ite_true,
      Except.mapError, H.beacon_call, bind, Except.bind]
    rfl
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hb.symm.trans hB))
  have hH : historyStorageCall (H.input w).stat.rules (H.historyEnv w) {} =
      .ok (H.preState w, ({} : BalBuilder)) := by
    unfold historyStorageCall
    simp only [show (H.input w).stat.rules.sys.historyStorage = true from rfl, ite_true,
      H.last, Option.toExcept, Except.mapError, H.history_call, bind, Except.bind]
    rfl
  exact Prod.mk.inj (Except.ok.inj (hh.symm.trans hH))
private theorem tx_packet (w : B256) {st : State} {bout : BlockOutput} {run : BodyRun}
    (body : BodyRoots (H.input w) [Sum.inr txD] [] [] st bout run) :
    run.senders = [(senderE, txD)] ∧ NoCreateAt systemAddress run.txRoots ∧
    run.txEnv.state.getCode systemAddress = SystemWordWriter.code historyStorageAddress w := by
  obtain ⟨pre, bal⟩ := pre_state w body
  obtain ⟨decoded, decode, transactions⟩ := body.transactions
  have actual : [Sum.inr txD].mapM (decodeTx (H.input w).stat.rules) = .ok [txD] := rfl
  obtain rfl := Except.ok.inj (decode.symm.trans actual)
  rw [pre, bal] at transactions
  change TransactionsRoots [(0, txD)] (H.txBenv w) .init run.txEnv run.txOut run.senders run.txRoots at transactions
  obtain ⟨txState, txOut, roots, _, _, _, _, sys⟩ := H.transaction_output w
  have chosen : TransactionsRoots [(0, txD)] (H.txBenv w) .init
      ((H.txBenv w).withState txState) txOut [(senderE, txD)] [H.root w] := by
    simpa only [List.append_nil] using TransactionsRoots.cons roots (TransactionsRoots.nil _ _)
  have same := transactions.unique chosen
  refine ⟨same.2.2.1, ?_, ?_⟩
  · rw [same.2.2.2]
    apply Root.noCreateAt_of_code
    · rfl
    · change (H.msg w).code.toList ≠ []
      rw [H.runtime]
      exact (system_runtime w).1
    · change (some systemAddress : Option Adr) = none → systemAddress ≠ systemAddress
      intro impossible
      cases impossible
  · rw [same.1]
    exact sys
private theorem clean (w : B256) {st : State} {bout : BlockOutput} {run : BodyRun}
    (body : BodyRoots (H.input w) [Sum.inr txD] [] [] st bout run) :
    NoSenderAt systemAddress run.senders ∧ NoAuthorityAt systemAddress run.senders ∧
    NoCreateAt systemAddress run.roots := by
  obtain ⟨senders, txAvoid, system⟩ := tx_packet w body
  have preAvoid := body.pre.noCreateAt_of_code rfl systemAddress
    (by change ((H.initial w).getCode systemAddress).toList ≠ []; rw [H.initial_system]; exact (system_runtime w).1)
    (by change ¬ isValidDelegation ((H.initial w).getCode systemAddress); rw [H.initial_system]; exact (system_runtime w).2)
    (by decide) (by decide)
  have noWd : withdrawalsPass (H.input w).stat.rules run.txEnv run.txOut [] = (run.txEnv.state, run.txOut) := by
    unfold withdrawalsPass
    rw [show (H.input w).stat.rules.header.withdrawalsRoot = true from rfl]
    simp only [ite_true]
    unfold BalBuilder.incorporateSystem
    rw [show (H.input w).stat.rules.bal = none from rfl]
    rfl
  obtain ⟨reqSt, reqOut, pass⟩ := body.requests
  rw [noWd] at pass
  have self : run.txEnv.withState run.txEnv.state = run.txEnv := by cases run.txEnv; rfl
  rw [self] at pass
  unfold RequestPass at pass
  have enabled : run.txEnv.stat.rules.header.requestsHash = true := by rw [body.txEnv_stat]; rfl
  rw [ite_eq_left enabled] at pass
  obtain ⟨deps, acc, bal, _, fold, _⟩ := pass
  have reqs : run.txEnv.stat.rules.requests = pragueRequests := by rw [body.txEnv_stat]; rfl
  rw [reqs] at fold
  have reqAvoid := fold.prague_noCreateAt_of_code
    (by rw [body.txEnv_stat]; rfl) systemAddress
    (by rw [system]; exact (system_runtime w).1)
    (by rw [system]; exact (system_runtime w).2) (by decide) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [senders]
    intro p member
    obtain rfl := List.mem_singleton.mp member
    change senderE ≠ systemAddress
    decide
  · rw [senders]
    intro p member auth memberAuth
    obtain rfl := List.mem_singleton.mp member
    change auth ∈ ([] : List Auth) at memberAuth
    cases memberAuth
  · intro f member
    simp only [BodyRun.roots, keptAll, List.flatMap_append, List.mem_append] at member
    rcases member with (member | member) | member
    · exact preAvoid f member
    · exact txAvoid f member
    · exact reqAvoid f member
private def firstHeader (_w : B256) (st : State) (bout : BlockOutput) : Header :=
  BlockForward.commitHeader Fork.prague.ruleSet R.parentBlock R.template st bout
private def firstBlock (w : B256) (st : State) (bout : BlockOutput) : Block :=
  {header := firstHeader w st bout, txs := [Sum.inr txD], wds := [], ommers := []}
private def firstStop (w : B256) (st : State) (bout : BlockOutput) : BlockChain :=
  ⟨appendBlock (H.start w).blocks (firstBlock w st bout), st, 1⟩
private def secondTemplate (w : B256) (st : State) (bout : BlockOutput) : Header :=
  {firstHeader w st bout with number := 2, timestamp := 2}
private def secondInput (w : B256) (st : State) (bout : BlockOutput) : Benv :=
  initBenv .prague (firstStop w st bout)
    (BlockForward.commitHeader Fork.prague.ruleSet (firstBlock w st bout) (secondTemplate w st bout) st .init)
private theorem body2 (w : B256) (st1 : State) (bout1 : BlockOutput)
    (installed : SystemCodeInstalled st1)
    (system : st1.getCode systemAddress = SystemWordWriter.code historyStorageAddress w)
    (word : (st1.getStor historyStorageAddress).get 0 = w) :
    ∃ st2 bout2 run2, BodyRoots (secondInput w st1 bout1) [] [] [] st2 bout2 run2 ∧
      (st2.getStor historyStorageAddress).get 0 = w ∧ bout2.blockGasUsed = 0 ∧
      (run2.preState.getStor historyStorageAddress).get 0 = w ∧
      NoSenderAt systemAddress run2.senders ∧ NoAuthorityAt systemAddress run2.senders ∧
      NoCreateAt systemAddress run2.roots := by
  let input := secondInput w st1 bout1
  have rCode : input.state.getCode beaconRootsAddress = beaconRootsCode := installed _ List.mem_cons_self
  let stateR := (Blanc.Lift.SystemExecution.BeaconRoots.systemPost input).state
  have rRun := (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := input) CoveredFork.prague rCode).1
  have rState := (Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
    (benv := input) CoveredFork.prague rCode).2.1
  change stateR = _ at rState
  have rCodeAll (a : Adr) : stateR.getCode a = st1.getCode a := by
    rw [rState, State.getCode_setStorVal, State.getCode_setStorVal]
    rfl
  have rStor : stateR.getStor historyStorageAddress = st1.getStor historyStorageAddress :=
    congrArg Acct.stor ((Blanc.Lift.SystemExecution.BeaconRoots.processUncheckedSystemTransaction_beaconRoots
      (benv := input) CoveredFork.prague rCode).2.2 historyStorageAddress (by decide))
  let historyEnv := input.withState stateR
  have hCode : historyEnv.state.getCode historyStorageAddress = historyStorageCode :=
    (rCodeAll _).trans (installed _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have last : historyEnv.stat.blockHashes.getLast? = some (firstHeader w st1 bout1).hash := by rfl
  let stateH := (Blanc.Lift.SystemExecution.HistoryStorage.systemPost historyEnv).state
  have hRun := (Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnv) CoveredFork.prague hCode last).1
  have hState := (Blanc.Lift.SystemExecution.HistoryStorage.processUncheckedSystemTransaction_historyStorage
    (benv := historyEnv) CoveredFork.prague hCode last).2.1
  change stateH = _ at hState
  change processUncheckedSystemTransaction historyEnv historyStorageAddress (firstHeader w st1 bout1).hash.toBytes =
    .ok (stateH, systemCallOutput (Blanc.Lift.SystemExecution.HistoryStorage.systemPost historyEnv)) at hRun
  have hCodeAll (a : Adr) : stateH.getCode a = st1.getCode a := by
    rw [hState, State.getCode_setStorVal]
    exact rCodeAll a
  have preWord : (stateH.getStor historyStorageAddress).get 0 = w := by
    rw [hState]
    have key : Blanc.Lift.SystemExecution.HistoryStorage.systemKey historyEnv = 1 := by
      change ((2 : B256) - 1) % 8191 = 1
      decide
    rw [key, State.getStor_setStorVal_self, Stor.get_set_ne _ (by decide : (1 : B256) ≠ 0)]
    change (stateR.getStor historyStorageAddress).get 0 = w
    rw [rStor]
    exact word
  generalize hHstate : stateH = preWorld at *
  let txEnv := input.withState preWorld
  have wCode : txEnv.state.getCode withdrawalRequestPredeployAddress = withdrawalRequestCode :=
    (hCodeAll _).trans (installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  let stateW := (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).state
  let outputW := Blanc.Lift.WithdrawalRequest.systemProtocolOutput txEnv
  have wRun := Blanc.Lift.WithdrawalRequest.processCheckedSystemTransaction_withdrawal
    (benv := txEnv) CoveredFork.prague wCode
  have wCodeAll (a : Adr) : stateW.getCode a = st1.getCode a := by
    trans preWorld.getCode a
    · change (Blanc.Lift.WithdrawalRequest.systemProtocolPost txEnv).getCode a =
        (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv).getCode a
      unfold Blanc.Lift.WithdrawalRequest.systemProtocolPost
      exact Blanc.Lift.WithdrawalRequest.systemFramePost_getCode _ _ _ _ _
    · exact hCodeAll a
  have wStor : stateW.getStor historyStorageAddress = preWorld.getStor historyStorageAddress :=
    Blanc.Lift.WithdrawalRequest.systemFramePost_other_storage
      (Blanc.Lift.WithdrawalRequest.systemProtocolSevm txEnv)
      (Blanc.Lift.WithdrawalRequest.systemProtocolBase txEnv) .empty
      (systemTransactionGas - Blanc.Lift.WithdrawalRequest.systemProtocolGas txEnv) historyStorageAddress
      (by change withdrawalRequestPredeployAddress ≠ historyStorageAddress; decide)
  change processCheckedSystemTransaction txEnv withdrawalRequestPredeployAddress [] = .ok (stateW, outputW) at wRun
  generalize hw : stateW = freshW at *
  generalize hout : outputW = freshOutputW at *
  have cCode : (txEnv.withState freshW).state.getCode consolidationRequestPredeployAddress = consolidationRequestCode :=
    (wCodeAll _).trans (installed _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  obtain ⟨outC, cRun, _, _, _⟩ := Blanc.Lift.ConsolidationRequest.system_call_ok
    (benv := txEnv.withState freshW) CoveredFork.prague cCode
  let stateC := RequestSystem.sysState SystemExecution.ConsolidationRequest.Amsterdam.sysShape freshW consolidationRequestPredeployAddress
  have actual : applyBody input [] [] [] =
      .ok (stateC, BlockForward.requestsOutput .init freshOutputW.returnData outC.returnData) :=
    BlockForward.applyBody_forward (benv := input) (txs := []) CoveredFork.prague
      rRun last hRun rfl rfl rfl wRun cRun
  obtain ⟨run, body⟩ := exists_bodyRoots actual
  have hB : beaconRootsCall input.stat.rules input = .ok (stateR, ({} : BalBuilder)) := by
    unfold beaconRootsCall
    simp only [show input.stat.rules.sys.beaconRoots = true from rfl, ite_true, Except.mapError, rRun, bind, Except.bind]
    rfl
  have hH : historyStorageCall input.stat.rules historyEnv {} = .ok (preWorld, ({} : BalBuilder)) := by
    unfold historyStorageCall
    simp only [show input.stat.rules.sys.historyStorage = true from rfl, ite_true, last,
      Option.toExcept, Except.mapError, hRun, bind, Except.bind]
    rfl
  have pre : run.preState = preWorld := by
    obtain ⟨beacon, bbal, br, hr, hb, cb, hh, ch, hpre⟩ := body.pre
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (hb.symm.trans hB))
    exact (Prod.mk.inj (Except.ok.inj (hh.symm.trans hH))).1
  have preAvoid := body.pre.noCreateAt_of_code rfl systemAddress
    (by change (st1.getCode systemAddress).toList ≠ []; rw [system]; exact (system_runtime w).1)
    (by change ¬ isValidDelegation (st1.getCode systemAddress); rw [system]; exact (system_runtime w).2)
    (by decide) (by decide)
  obtain ⟨decoded, decode, transactions⟩ := body.transactions
  have decodeEmpty : ([] : List (Bytes ⊕ Tx)).mapM (decodeTx input.stat.rules) = .ok [] := rfl
  obtain rfl := Except.ok.inj (decode.symm.trans decodeEmpty)
  have txSame := transactions.unique (TransactionsRoots.nil _ _)
  have sysTx : run.txEnv.state.getCode systemAddress = SystemWordWriter.code historyStorageAddress w := by
    rw [txSame.1]
    change run.preState.getCode systemAddress = _
    rw [pre]
    exact (hCodeAll _).trans system
  have noWd : withdrawalsPass input.stat.rules run.txEnv run.txOut [] = (run.txEnv.state, run.txOut) := by
    unfold withdrawalsPass
    rw [show input.stat.rules.header.withdrawalsRoot = true from rfl]
    simp only [ite_true]
    unfold BalBuilder.incorporateSystem
    rw [show input.stat.rules.bal = none from rfl]
    rfl
  obtain ⟨reqSt, reqOut, pass⟩ := body.requests
  rw [noWd] at pass
  have self : run.txEnv.withState run.txEnv.state = run.txEnv := by cases run.txEnv; rfl
  rw [self] at pass
  unfold RequestPass at pass
  have enabled : run.txEnv.stat.rules.header.requestsHash = true := by rw [body.txEnv_stat]; rfl
  rw [ite_eq_left enabled] at pass
  obtain ⟨deps, acc, bal, _, fold, _⟩ := pass
  have reqs : run.txEnv.stat.rules.requests = pragueRequests := by rw [body.txEnv_stat]; rfl
  rw [reqs] at fold
  have reqAvoid := fold.prague_noCreateAt_of_code
    (by rw [body.txEnv_stat]; rfl) systemAddress
    (by rw [sysTx]; exact (system_runtime w).1)
    (by rw [sysTx]; exact (system_runtime w).2) (by decide) (by decide)
  refine ⟨stateC, BlockForward.requestsOutput .init freshOutputW.returnData outC.returnData, run, body, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · have otherC : stateC.getStor historyStorageAddress = freshW.getStor historyStorageAddress :=
      RequestSystem.sysState_getStor_other _ _ (by decide : consolidationRequestPredeployAddress ≠ historyStorageAddress)
    rw [otherC, wStor]
    exact preWord
  · rw [pre]
    exact preWord
  · rw [txSame.2.2.1]
    intro p member
    cases member
  · rw [txSame.2.2.1]
    intro p member
    cases member
  · intro f member
    change f ∈ keptAll (run.preRoots ++ run.txRoots ++ requestRootsOf run.requests) at member
    rw [txSame.2.2.2] at member
    simp only [List.append_nil, keptAll, List.flatMap_append, List.mem_append] at member
    rcases member with member | member
    · exact preAvoid f member
    · exact reqAvoid f member
private theorem controls :
    Blanc.Corpus.Freeze.HistoryStorage.H_S3_control ∧
      Blanc.Corpus.Freeze.HistoryStorage.H_S8_control := by
  let w := R.parentHeader.hash ^^^ (1 : B256)
  have unequal : w ≠ R.parentHeader.hash := by
    intro equal
    have eqNat := congrArg B256.toNat equal
    change (R.parentHeader.hash ^^^ (1 : B256)).toNat = R.parentHeader.hash.toNat at eqNat
    rw [B256.toNat_xor] at eqNat
    have cancel := congrArg (fun n => R.parentHeader.hash.toNat ^^^ n) eqNat
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at cancel
    exact (by decide : (1 : Nat) ≠ 0) cancel
  obtain ⟨st1, bout1, applied1, word1, gas1, installed1, system1⟩ := body_effect w
  obtain ⟨run1, body1⟩ := exists_bodyRoots applied1
  obtain ⟨st2, bout2, run2, body2, word2, gas2, preWord, senders2, auth2, avoid2⟩ :=
    body2 w st1 bout1 installed1 system1 word1
  let cfg := ChainConfig.single 1 .prague
  let block1 := firstBlock w st1 bout1
  let middle := firstStop w st1 bout1
  let header2 := BlockForward.commitHeader Fork.prague.ruleSet block1 (secondTemplate w st1 bout1) st2 bout2
  let block2 : Block := {header := header2, txs := [], wds := [], ommers := []}
  let stop : BlockChain := ⟨appendBlock middle.blocks block2, st2, 1⟩
  let kb1 : KeptBlock := ⟨H.start w, block1, .prague, bout1, run1⟩
  let kb2 : KeptBlock := ⟨middle, block2, .prague, bout2, run2⟩
  have header1OK : validateHeader Fork.prague.ruleSet (H.start w) block1.header = .ok () := by
    apply BlockForward.commitHeader_ok CoveredFork.prague rfl rfl rfl
    · exact BlockForward.calculateBaseFeePerGas_unit (by decide) (by decide) (by decide) (by decide)
    · rfl
    · change bout1.blockGasUsed ≤ 2 ^ 21
      exact Nat.le_trans gas1 (by decide)
    · decide
    · rfl
    · rfl
  have env1 : kb1.benv = H.input w := by
    change initBenv .prague (H.start w) (firstHeader w st1 bout1) = H.input w
    simpa only [H.input, firstHeader] using BlockForward.initBenv_commitHeader_body_eq .prague (H.start w) Fork.prague.ruleSet
      R.parentBlock R.template st1 (H.initial w) bout1 BlockOutput.init
  have fork1 : cfg.forkAt block1.header.number block1.header.timestamp = .ok .prague :=
    ChainConfig.single_forkAt 1 .prague _ _
  have step1 : KeptStep cfg kb1 middle := by
    refine ⟨?_, fork1, Or.inl CoveredFork.prague, ?_⟩
    · apply BlockForward.stateTransitionUsing_forward rfl fork1 CoveredFork.prague header1OK rfl
      · change applyBody kb1.benv [Sum.inr txD] [] [] = _
        rw [env1]
        exact applied1
      all_goals rfl
    · change BodyRoots kb1.benv [Sum.inr txD] [] [] st1 bout1 run1
      rw [env1]
      exact body1
  have header2OK : validateHeader Fork.prague.ruleSet middle header2 = .ok () := by
    apply BlockForward.commitHeader_ok CoveredFork.prague rfl rfl rfl
    · change calculateBaseFeePerGas (2 ^ 21) (2 ^ 21) bout1.blockGasUsed 1 = .ok 1
      exact BlockForward.calculateBaseFeePerGas_unit (by decide) (by decide) (by decide) gas1
    · rfl
    · change bout2.blockGasUsed ≤ 2 ^ 21
      rw [gas2]
      exact Nat.zero_le _
    · change (0 : Nat) ≤ 32
      decide
    · rfl
    · rfl
  have env2 : kb2.benv = secondInput w st1 bout1 := by
    change initBenv .prague middle header2 = secondInput w st1 bout1
    simpa only [secondInput] using BlockForward.initBenv_commitHeader_body_eq .prague middle Fork.prague.ruleSet
      block1 (secondTemplate w st1 bout1) st2 st1 bout2 BlockOutput.init
  have fork2 : cfg.forkAt block2.header.number block2.header.timestamp = .ok .prague :=
    ChainConfig.single_forkAt 1 .prague _ _
  have step2 : KeptStep cfg kb2 stop := by
    refine ⟨?_, fork2, Or.inl CoveredFork.prague, ?_⟩
    · apply BlockForward.stateTransitionUsing_forward rfl fork2 CoveredFork.prague header2OK rfl
      · change applyBody kb2.benv [] [] [] = _
        rw [env2]
        exact body2.applied
      all_goals rfl
    · change BodyRoots kb2.benv [] [] [] st2 bout2 run2
      rw [env2]
      exact body2
  have history1 : KeptHistory cfg (H.start w) [kb1] middle := KeptHistory.step KeptHistory.refl step1
  have history : KeptHistory cfg (H.start w) [kb1, kb2] stop := KeptHistory.step history1 step2
  have clean1 := clean w body1
  have covered : ∀ b ∈ [kb1, kb2], CoveredFork b.fork := by
    intro b member
    rcases List.mem_cons.mp member with rfl | member
    · exact CoveredFork.prague
    · obtain rfl := List.mem_singleton.mp member
      exact CoveredFork.prague
  have cleanBoth : HistoryClean [kb1, kb2] := by
    refine ⟨?_, ?_, ?_⟩
    all_goals intro b member; rcases List.mem_cons.mp member with rfl | member
    · exact clean1.1
    · obtain rfl := List.mem_singleton.mp member
      exact senders2
    · exact clean1.2.1
    · obtain rfl := List.mem_singleton.mp member
      exact auth2
    · exact clean1.2.2
    · obtain rfl := List.mem_singleton.mp member
      exact avoid2
  have fit : Blanc.Corpus.Freeze.HistoryNumbersFit [kb1, kb2] := by
    intro b member
    rcases List.mem_cons.mp member with rfl | member
    · change 1 + 8191 < 2 ^ 256
      decide
    · obtain rfl := List.mem_singleton.mp member
      change 2 + 8191 < 2 ^ 256
      decide
  have wrongHistory : ¬ Blanc.Corpus.Freeze.HistoryStorage.StorageIsHistory (H.start w) stop [kb1, kb2] := by
    intro holds
    have value := congrFun holds 0
    have expected : Blanc.Corpus.Freeze.HistoryStorage.writeAll
        (Blanc.Corpus.Freeze.storOf (H.start w).state historyStorageAddress)
        ([kb1, kb2].map Blanc.Corpus.Freeze.HistoryStorage.blockWrite) 0 = R.parentHeader.hash := by
      change Blanc.Corpus.Freeze.HistoryStorage.writeAll
        (Blanc.Corpus.Freeze.storOf (H.start w).state historyStorageAddress)
        [(1, R.parentHeader.hash), (2, (firstHeader w st1 bout1).hash)] 0 = R.parentHeader.hash
      simp only [Blanc.Corpus.Freeze.HistoryStorage.writeAll, Blanc.Corpus.Freeze.HistoryStorage.write]
      rw [ite_eq_right (by decide : (0 : B256) ≠ Blanc.Corpus.Freeze.HistoryStorage.key 2),
        ite_eq_left (by decide : (0 : B256) = Blanc.Corpus.Freeze.HistoryStorage.key 1)]
    change (st2.getStor historyStorageAddress).get 0 = _ at value
    rw [word2, expected] at value
    exact unequal value
  have read : Blanc.Corpus.Freeze.HistoryStorage.read
      (Blanc.Corpus.Freeze.storOf run2.preState historyStorageAddress) 2 0 = some w := by
    rw [Blanc.Corpus.Freeze.HistoryStorage.read,
      ite_eq_left (by decide : Blanc.Corpus.Freeze.HistoryStorage.InWindow 2 0)]
    change some ((run2.preState.getStor historyStorageAddress).get ((0 : B256) % 8191)) = some w
    rw [show (0 : B256) % 8191 = 0 from by decide, preWord]
  constructor
  · exact ⟨cfg, H.start w, stop, [kb1, kb2], w, history, covered, H.initial_H w,
      cleanBoth, H.initial_system w, wrongHistory⟩
  · refine ⟨cfg, H.start w, stop, [kb1, kb2], w, history, covered, H.initial_H w,
      cleanBoth, fit, H.initial_system w, 0, 1, ?_, ?_, w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 < 2
      decide
    · change 1 < 2
      decide
    · change 1 + 8191 < 2 ^ 256
      decide
    · decide
    · change 2 ≤ 1 - 1 + 8191
      decide
    · change Blanc.Corpus.Freeze.HistoryStorage.InWindow 2 0
      decide
    · exact read
    · exact unequal
end HBody
theorem h_s3_control : Blanc.Corpus.Freeze.HistoryStorage.H_S3_control := HBody.controls.1
theorem h_s8_control : Blanc.Corpus.Freeze.HistoryStorage.H_S8_control := HBody.controls.2

end Blanc.Composition.Corpus.Proofs.RingHistoryControls
