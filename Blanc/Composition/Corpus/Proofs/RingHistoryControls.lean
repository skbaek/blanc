import Blanc.Lift.BeaconRoots.Writer
import Blanc.Lift.BeaconRoots.Frame
import Blanc.Lift.WithdrawalRequest.DrainTx
import Blanc.BlockForward
import Blanc.ConcreteRunKept
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
private def benv (h : B256) : Benv :=
  { (default : Benv) with
    state := state h
    stat := { (default : Benv).stat with
      fork := .prague
      chainId := 1
      number := 1
      time := 1
      origState := state h
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
  have code := installed h
  have callAt := at_call h
  have depth : (sevm h).depth ≠ 0 := by change (1024 : Nat) ≠ 0; decide
  have fork : CoveredFork (sevm h).benvStat.fork := CoveredFork.prague
  unfold callState childMsg
  generalize hs : sevm h = s at *
  generalize hb : base h = b at *
  let bare := b.setMach ⟨[], SystemWordWriter.wordMemory 1, gas, b.stateGas⟩
  have delegation : accessDelegation (addAccessedAddress bare beaconRootsAddress) beaconRootsAddress =
      (false, beaconRootsAddress, beaconRootsCode, 0, addAccessedAddress bare beaconRootsAddress) := by
    unfold accessDelegation
    change (match getDelegatedCodeAddress (b.getCode beaconRootsAddress) with
      | some a => (true, a, b.getCode a, accessCost a (addAccessedAddress bare beaconRootsAddress).accessedAddresses, addAccessedAddress (addAccessedAddress bare beaconRootsAddress) a)
      | none => (false, beaconRootsAddress, b.getCode beaconRootsAddress, 0, addAccessedAddress bare beaconRootsAddress)) = _
    rw [code, show getDelegatedCodeAddress beaconRootsCode = none from rfl]
  have splitGas : calculateMsgCallGas 0 gas.toB256.toNat gas 0
      (accessCost beaconRootsAddress b.accessedAddresses) =
      (SystemWordWriter.forwardedGas b beaconRootsAddress gas +
        accessCost beaconRootsAddress b.accessedAddresses,
        SystemWordWriter.forwardedGas b beaconRootsAddress gas) := by
    have affordable : accessCost beaconRootsAddress b.accessedAddresses + 0 ≤ gas := by
      have bound := accessCost_le (x := beaconRootsAddress) (a := b.accessedAddresses)
      change _ ≤ 2600 at bound
      change _ ≤ 1027549
      omega
    rw [calculateMsgCallGas_zero affordable, B256.toNat_toB256_of_lt gas_bound]
    simp only [Nat.sub_zero]
    have bound : SystemWordWriter.forwardedGas b beaconRootsAddress gas ≤ gas := by
      unfold SystemWordWriter.forwardedGas except64th
      omega
    unfold SystemWordWriter.forwardedGas at bound
    rw [Nat.min_eq_right bound]
    rfl
  have run := Xinst.step_call_zero_value_spawn
    (sevm := s) (devm := b.setMach ⟨[gas.toB256, beaconRootsAddress.toBytes.toB256, 0, 0, 32, 0, 0], SystemWordWriter.wordMemory 1, gas, b.stateGas⟩) (gw := gas.toB256) (cw := beaconRootsAddress.toBytes.toB256)
    (iiw := 0) (isw := 32) (oiw := 0) (osw := 0) (s := []) (dp := false)
    (dadr := beaconRootsAddress) (code := beaconRootsCode) (dgc := 0)
    (d1 := addAccessedAddress bare beaconRootsAddress) (ext := 0)
    (acc := accessCost beaconRootsAddress b.accessedAddresses)
    (mcs := SystemWordWriter.forwardedGas b beaconRootsAddress gas)
    (mcc := SystemWordWriter.forwardedGas b beaconRootsAddress gas +
      accessCost beaconRootsAddress b.accessedAddresses)
    (fork.callEra false) rfl ?_ ?_ ?_ splitGas ?_ depth
  · rw [Evm.step_next callAt]
    simp only [Ninst.step_exec, run, XStep.toStep, SystemWordWriter.childMsg,
      SystemWordWriter.parent, bare, SystemWordWriter.target_word, Nat.add_zero,
      B256.toNat_zero, show (32 : B256).toNat = 32 from rfl, Nat.reduceAdd]
  · apply Devm.extCost_covered
    change memExtsSize (SystemWordWriter.wordMemory 1).size [(0, 32), (0, 0)] = _
    rw [show (SystemWordWriter.wordMemory 1).size = 32 from Mem.size_write_word]
    rfl
  · rw [SystemWordWriter.target_word]
    exact delegation
  · rw [SystemWordWriter.target_word]
    rfl
  · change SystemWordWriter.forwardedGas b beaconRootsAddress gas +
      accessCost beaconRootsAddress b.accessedAddresses + 0 ≤ gas
    have access := accessCost_le (x := beaconRootsAddress) (a := b.accessedAddresses)
    change _ ≤ 2600 at access
    unfold SystemWordWriter.forwardedGas except64th gas
    omega

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

end R
end Blanc.Composition.Corpus.Proofs.RingHistoryControls
