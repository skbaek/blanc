import Blanc.Lift.WithdrawalRequest.FloodTx
import Blanc.Lift.WithdrawalRequest.FloodTxRecover
import Blanc.Lift.WithdrawalRequest.ProtocolOccurrences
import Blanc.Lift.WithdrawalRequest.BalanceHistory
import Blanc.BlockForward
import Blanc.ExecutionTraceRootFrame

/-!
# The mathematical-fee refutation: block assembly

The witness history is three configured blocks on a Prague chain:

* **A** activates the fork: no transactions, the four system calls.
* **B** carries `txB`, which runs the flood caller for `2895` fee-1 submissions.
* **C** carries `txC`, the direct `2 ^ 245`-wei submission at excess `2893`.

This module assembles each block's body from its transaction forward lemma
(`txB_processTransaction`, `txC_processTransaction`) and the block-forward
constructor, with the system-call results, the deposit parse, and the header
facts carried as hypotheses, and chains the three `ConfiguredBlockTrace`s into
a `ConfiguredHistoryTrace`.  The two `recoverSender` premises stay isolated,
one per transaction.
-/

namespace Blanc.Lift.WithdrawalRequest.FeeCounterexample

open Jaune Blanc.Lift Blanc.ExecutionTrace Blanc.BlockForward FloodTx

/-- The transaction fold over a single indexed transaction is that transaction's
settlement, its state installed. -/
theorem applyTransactions_single {benv : Benv} {bout bout' : BlockOutput} {tx : Tx}
    {index : Nat} {st : State}
    (h : processTransaction benv bout tx index = .ok (st, bout')) :
    applyTransactions [(index, tx)] benv bout = .ok (benv.withState st, bout') := by
  unfold applyTransactions
  rw [h]
  rfl

theorem putIndex_single (tx : Tx) : [tx].putIndex = [(0, tx)] := rfl

theorem decode_single (tx : Tx) : [Sum.inr tx].mapM decodeTx = .ok [tx] := rfl

/-- A one-transaction body retains exactly that decoded transaction. -/
theorem AppliedBodyTrace.decodedTxs_eq {benv : Benv} {tx : Tx} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv [Sum.inr tx] wds state bout) :
    trace.decodedTxs = [tx] := by
  exact Except.ok.inj (trace.decodeRun.symm.trans (decode_single tx))

theorem AppliedBodyTrace.decodedTxs_eq_of_txs_eq
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {tx : Tx} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (htxs : txs = [Sum.inr tx]) :
    trace.decodedTxs = [tx] := by
  have hdecode : txs.mapM decodeTx = .ok [tx] := by
    rw [htxs]
    exact decode_single tx
  exact Except.ok.inj (trace.decodeRun.symm.trans hdecode)

theorem noSenderAt_single {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {tx : Tx} (trace : ApplyTransactionsTrace [(0, tx)] benv bout finalBenv finalBout)
    (hrecover : recoverSender benv.stat.chainId tx = .ok senderE) :
    trace.NoSenderAt systemAddress := by
  cases trace with
  | cons head tail =>
    cases tail with
    | nil =>
      refine ⟨?_, trivial⟩
      intro hsender
      have hrecover' := checkTransaction_sender head.checked
      have hrecover'' : recoverSender benv.stat.chainId tx = .ok head.sender := by
        simpa only [Benv.beginTransaction] using hrecover'
      have hsender' : senderE = head.sender :=
        Except.ok.inj (hrecover.symm.trans hrecover'')
      exact (by decide : senderE ≠ systemAddress) (hsender'.trans hsender)

theorem noAuthorityAt_decoded {benv : Benv} {txs : List (Bytes ⊕ Tx)} {tx : Tx}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hdecoded : trace.decodedTxs = [tx]) (hauths : tx.auths = []) :
    ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ systemAddress := by
  rw [hdecoded, putIndex_single]
  intro p hp
  rw [List.mem_singleton] at hp
  subst p
  rw [hauths]
  intro auth hauth
  exact False.elim (List.not_mem_nil hauth)

theorem noAuthorityAt_single {benv : Benv} {tx : Tx} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv [Sum.inr tx] wds state bout)
    (hauths : tx.auths = []) :
    ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
      recoverAuthority auth = .ok authority → authority ≠ systemAddress := by
  apply noAuthorityAt_decoded trace (AppliedBodyTrace.decodedTxs_eq trace)
  exact hauths

/-- The settled state of a transaction whose frame scheduled no deletion and whose
sender and coinbase are credited, as `processTransaction` returns it. -/
def settledState (post : Devm) (E coinbase : Adr) (refund tip : B256) : State :=
  (post.state.addBal E refund).addBal coinbase tip

/-- The settled state once the frame's deletion set is known empty. -/
theorem settled_of_no_deletions (post : Devm) (E coinbase : Adr) (refund tip : B256)
    (hdel : post.accountsToDelete.isEmpty = true) :
    post.accountsToDelete.toList.foldl destroyAccount
      ((post.state.addBal E refund).addBal coinbase tip) =
      settledState post E coinbase refund tip := by
  have hlist : post.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    exact hdel
  rw [hlist]
  rfl

/-- The deposit parse of a block output holding one receipt whose logs all sit at the
withdrawal predeploy. -/
theorem parseDepositRequests_of_predeploy_logs {bout : BlockOutput} {tx : Tx} {cum : Nat}
    {logs : List Log} {index : Nat}
    (hkeys : bout.receiptKeys = [BLT.toBytes (.bytes index.toBytes)])
    (hreceipt : bout.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx none cum logs))
    (hlogs : ∀ log ∈ logs, log.address = withdrawalRequestPredeployAddress) :
    parseDepositRequests bout = .ok [] := by
  apply parseDepositRequests_of_no_deposit_logs
  intro key hkey
  rw [hkeys, List.mem_singleton] at hkey
  subst hkey
  refine ⟨_, hreceipt, ?_⟩
  intro log hlog
  change log ∈ logs at hlog
  rw [hlogs log hlog]
  decide

/-! ## Block C -/

/-- **Block C's body.**  The two unchecked system calls and the two checked request
calls are hypotheses (their walks live in the system-path modules); the transaction
is `txC_processTransaction`. -/
theorem blockC_body {benv : Benv} {iters : Nat} {out : B256}
    {σ : Blanc.WithdrawalRequest.State}
    {stBeacon stHistory : State} {outBeacon outHistory : MsgCallOutput} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork)
    (hbeacon : processUncheckedSystemTransaction benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes = .ok (stBeacon, outBeacon))
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hhistory : processUncheckedSystemTransaction (benv.withState stBeacon)
      historyStorageAddress lastHash.toBytes = .ok (stHistory, outHistory))
    -- the transaction's premises, on the state the system calls leave
    (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas ≤ 8)
    (hroom : 2 ^ 20 ≤ benv.stat.blockGasLimit)
    (hnonce : (stHistory.get senderE).nonce = 1)
    (hnocode : (stHistory.get senderE).code.isEmpty = true)
    (hfunds : 2 ^ 20 * 8 + 2 ^ 245 ≤ (stHistory.get senderE).bal.toNat)
    (hcode : stHistory.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (stHistory.getStor withdrawalRequestPredeployAddress).get σ)
    (hbounds : SubmissionBounds σ)
    (hexcess : σ.excess + 1 < 2 ^ 256)
    (hrun : WordFakeExponential.Run σ.excess.toB256 17 1 17 0 iters out)
    (hpaid : (out / (17 : B256)).toNat ≤ 2 ^ 245)
    (hiters : iters ≤ 10000)
    -- the request calls, on whatever the transaction leaves
    (hW : ∀ benvTxs : Benv, ∃ stW outW,
      processCheckedSystemTransaction benvTxs withdrawalRequestPredeployAddress [] =
        .ok (stW, outW))
    (hC : ∀ benvTxs : Benv, ∃ stC outC,
      processCheckedSystemTransaction benvTxs consolidationRequestPredeployAddress [] =
        .ok (stC, outC)) :
    ∃ (post : Devm) (boutTxs : BlockOutput) (stW stC : State) (outW outC : MsgCallOutput),
      TxCPost (benv.withState stHistory) σ iters post ∧
      applyBody benv [Sum.inr txC] [] =
        .ok (stC, requestsOutput boutTxs outW.returnData outC.returnData) ∧
      processCheckedSystemTransaction
        (((benv.withState stBeacon).withState stHistory).withState
          (settledState post senderE benv.stat.coinbase
            ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256))
        withdrawalRequestPredeployAddress [] = .ok (stW, outW) ∧
      processCheckedSystemTransaction
        ((((benv.withState stBeacon).withState stHistory).withState
          (settledState post senderE benv.stat.coinbase
            ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256)).withState stW)
        consolidationRequestPredeployAddress [] = .ok (stC, outC) := by
  set benvTx : Benv := (benv.withState stBeacon).withState stHistory with hbenvTx
  have hstat : benvTx.stat = benv.stat := rfl
  have hstate : benvTx.state = stHistory := rfl
  have hrecover : recoverSender benv.stat.chainId txC = .ok senderE := by
    rw [hchain]
    exact txC_recoveredSender
  obtain ⟨post, bout', hQ, hproc, -, -, hkeys, hreceipt⟩ := txC_processTransaction
    (benv := benv.withState stHistory) (bout := BlockOutput.init) (index := 0)
    hfork hchain hbase (by show 2 ^ 20 ≤ benv.stat.blockGasLimit - 0; exact hroom) hrecover
    hnonce hnocode hfunds hcode hrep hbounds hexcess hrun hpaid hiters
  have hdeposit : parseDepositRequests bout' = .ok [] :=
    parseDepositRequests_of_predeploy_logs hkeys hreceipt (by
      rw [hQ.2.1]
      intro log hlog
      rw [List.mem_singleton] at hlog
      rw [hlog])
  have hproc' : processTransaction benvTx BlockOutput.init txC 0 = .ok
      (settledState post senderE benv.stat.coinbase
        ((txC.gas - txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat) *
          (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
        (txGasUsed txC.gas 23000 post.gasLeft post.refundCounter.toNat *
          (min 1 (8 - benv.stat.baseFeePerGas))).toB256, bout') := by
    have hdel := hQ.2.2.2.2.1
    rw [settled_of_no_deletions post senderE _ _ _ hdel] at hproc
    exact hproc
  obtain ⟨stW, outW, hWrun⟩ := hW (benvTx.withState _)
  obtain ⟨stC, outC, hCrun⟩ := hC ((benvTx.withState _).withState stW)
  refine ⟨post, bout', stW, stC, outW, outC, hQ, ?_, hWrun, hCrun⟩
  exact applyBody_forward hfork hbeacon hlast hhistory (decode_single txC)
    (by rw [putIndex_single]; exact applyTransactions_single hproc') hdeposit hWrun hCrun

/-! ## Block B -/

/-- **Block B's body.**  As for block C, with `txB_processTransaction`; the flood
frame schedules no deletions (`TxBPost.no_deletions`), settling to `settledState`. -/
theorem blockB_body {benv : Benv} {σ0 : Blanc.WithdrawalRequest.State}
    {stBeacon stHistory : State} {outBeacon outHistory : MsgCallOutput} {lastHash : B256}
    (hfork : CoveredFork benv.stat.fork)
    (hbeacon : processUncheckedSystemTransaction benv beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toBytes = .ok (stBeacon, outBeacon))
    (hlast : benv.stat.blockHashes.getLast? = some lastHash)
    (hhistory : processUncheckedSystemTransaction (benv.withState stBeacon)
      historyStorageAddress lastHash.toBytes = .ok (stHistory, outHistory))
    (hnocap : benv.stat.rules.tx.maxGas = none)
    (hchain : benv.stat.chainId = 1)
    (hbase : benv.stat.baseFeePerGas ≤ 8)
    (hroom : 2 ^ 28 ≤ benv.stat.blockGasLimit)
    (hnonce : (stHistory.get senderE).nonce = 0)
    (hnocode : (stHistory.get senderE).code.isEmpty = true)
    (hfunds : 2 ^ 28 * 8 + 2895 ≤ (stHistory.get senderE).bal.toNat)
    (hLcode : stHistory.getCode looperAddress = Blanc.Lift.FloodLooper.code)
    (hLbal : (stHistory.bal looperAddress).toNat + 2895 < 2 ^ 256)
    (hcode : stHistory.getCode withdrawalRequestPredeployAddress = Blanc.withdrawalRequestCode)
    (hrep : Blanc.WithdrawalRequest.RepresentsStorage
      (stHistory.getStor withdrawalRequestPredeployAddress).get σ0)
    (hexcess : σ0.excess = 0)
    (hcountLt : σ0.count + 2895 < 2 ^ 256)
    (htailLt : Blanc.WithdrawalRequest.queueBase (σ0.tail + 2895) + 2 < 2 ^ 256)
    (hqueue : ∀ n o, σ0.tail ≤ n → n < σ0.tail + 2895 → o ≤ 2 →
      (stHistory.getStor withdrawalRequestPredeployAddress).get
        (Blanc.WithdrawalRequest.queueSlot n o) = 0)
    (hW : ∀ benvTxs : Benv, ∃ stW outW,
      processCheckedSystemTransaction benvTxs withdrawalRequestPredeployAddress [] =
        .ok (stW, outW))
    (hC : ∀ benvTxs : Benv, ∃ stC outC,
      processCheckedSystemTransaction benvTxs consolidationRequestPredeployAddress [] =
        .ok (stC, outC)) :
    ∃ (post : Devm) (boutTxs : BlockOutput) (stW stC : State) (outW outC : MsgCallOutput),
      TxBPost (benv.withState stHistory) σ0 post ∧
      applyBody benv [Sum.inr txB] [] =
        .ok (stC, requestsOutput boutTxs outW.returnData outC.returnData) ∧
      processCheckedSystemTransaction
        (((benv.withState stBeacon).withState stHistory).withState
          (settledState post senderE benv.stat.coinbase
            ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256))
        withdrawalRequestPredeployAddress [] = .ok (stW, outW) ∧
      processCheckedSystemTransaction
        ((((benv.withState stBeacon).withState stHistory).withState
          (settledState post senderE benv.stat.coinbase
            ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
            (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256)).withState stW)
        consolidationRequestPredeployAddress [] = .ok (stC, outC) := by
  set benvTx : Benv := (benv.withState stBeacon).withState stHistory with hbenvTx
  have hrecover : recoverSender benv.stat.chainId txB = .ok senderE := by
    rw [hchain]
    exact txB_recoveredSender
  obtain ⟨post, bout', hQ, hproc, -, -, hkeys, hreceipt⟩ := txB_processTransaction
    (benv := benv.withState stHistory) (bout := BlockOutput.init) (index := 0)
    hfork hnocap hchain hbase (by show 2 ^ 28 ≤ benv.stat.blockGasLimit - 0; exact hroom)
    hrecover hnonce hnocode hfunds hLcode hLbal hcode hrep hexcess hcountLt htailLt hqueue
  have hdeposit : parseDepositRequests bout' = .ok [] :=
    parseDepositRequests_of_predeploy_logs hkeys hreceipt (by
      rw [hQ.2.2.1]
      intro log hlog
      rw [(List.mem_replicate.mp hlog).2])
  have hproc' : processTransaction benvTx BlockOutput.init txB 0 = .ok
      (settledState post senderE benv.stat.coinbase
        ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
          (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256
        (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
          (min 1 (8 - benv.stat.baseFeePerGas))).toB256, bout') := by
    rw [TxBPost.no_deletions hQ] at hproc
    exact hproc
  obtain ⟨stW, outW, hWrun⟩ := hW (benvTx.withState _)
  obtain ⟨stC, outC, hCrun⟩ := hC ((benvTx.withState _).withState stW)
  refine ⟨post, bout', stW, stC, outW, outC, hQ, ?_, hWrun, hCrun⟩
  exact applyBody_forward hfork hbeacon hlast hhistory (decode_single txB)
    (by rw [putIndex_single]; exact applyTransactions_single hproc') hdeposit hWrun hCrun

/-! ## From a body to a configured block trace -/

/-- A block without ommers or withdrawals whose header validates and commits to its
body's results is a configured block trace. -/
theorem blockTrace_of_body {cfg : ChainConfig} {pre : BlockChain} {block : Block}
    {fork : Fork} {st : State} {bout : BlockOutput}
    (hbound : sum pre.state.bal < 2 ^ 256) (hwds : block.wds = [])
    (hid : cfg.chainId = pre.chainId)
    (hforkAt : cfg.forkAt block.header.timestamp = .ok fork)
    (hcovered : CoveredFork fork)
    (hheader : validateHeader fork.ruleSet pre block.header = .ok ())
    (hommers : block.ommers = [])
    (hbody : applyBody (initBenv fork pre block.header) block.txs block.wds = .ok (st, bout))
    (hgasUsed : block.header.gasUsed = bout.blockGasUsed)
    (htxsRoot : block.header.txsRoot = getTransactionsRoot bout)
    (hstateRoot : block.header.stateRoot = st.root)
    (hreceiptRoot : block.header.receiptRoot = getReceiptRoot bout)
    (hbloom : block.header.bloom = logsBloom bout.blockLogs)
    (hwithdrawalsRoot : block.header.withdrawalsRoot = getWithdrawalsRoot bout)
    (hblobGasUsed : block.header.blobGasUsed = bout.blobGasUsed)
    (hrequestsHash : block.header.requestsHash = some (computeRequestsHash bout.requests)) :
    Nonempty (ConfiguredBlockTrace cfg pre ⟨appendBlock pre.blocks block, st, pre.chainId⟩) :=
  configuredBlockTrace_forward hbound hwds hforkAt hcovered
    (stateTransitionUsing_forward hid hforkAt hcovered hheader hommers hbody hgasUsed htxsRoot
      hstateRoot hreceiptRoot hbloom hwithdrawalsRoot hblobGasUsed hrequestsHash)

/-! ## The three-block history -/

/-- Three configured block traces from a valid checkpoint chain into a configured
history trace. -/
def history_of_three {cfg : ChainConfig} {checkpoint chainA chainB chainC : BlockChain}
    (hcfg : cfg.Valid) (hctx : checkpoint.ValidContext) (hid : cfg.chainId = checkpoint.chainId)
    (traceA : ConfiguredBlockTrace cfg checkpoint chainA)
    (traceB : ConfiguredBlockTrace cfg chainA chainB)
    (traceC : ConfiguredBlockTrace cfg chainB chainC) :
    ConfiguredHistoryTrace cfg checkpoint chainC :=
  .step (.step (.step (.refl hcfg hctx hid) traceA) traceB) traceC

/-! ## The statement -/

/-- **B, the mathematical-fee guarantee**, in the vocabulary of the retained word-fee
theorem: on every configured history under the original hypotheses, every committed
submission frame whose word fee loop ran to `output` and was paid at least `output / 17`
also paid at least the Nat reference fee `fakeExp 1 excess 17` of the model at its incoming
excess. -/
def NatFeeGuarantee : Prop :=
  ∀ (cfg : ChainConfig) (checkpoint future : BlockChain)
    (trace : ConfiguredHistoryTrace cfg checkpoint future),
    SystemCodeInstalled checkpoint.state →
    trace.NoSenderAt systemAddress → trace.NoAuthorityAt systemAddress →
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) →
    checkpoint.state.getCode systemAddress = ByteArray.empty →
    Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial →
    ∀ frame ∈ trace.settledFrames.flatMap balanceFrameObservation,
      ∀ (model : Blanc.WithdrawalRequest.State) (iterations : Nat) (output : B256),
        submissionPaymentFrame frame →
        model.excess = ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0).toNat →
        WordFakeExponential.Run ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0)
          17 1 17 0 iterations output →
        (output / 17).toNat ≤ frame.sevm.value.toNat →
        Blanc.WithdrawalRequest.fee model ≤ frame.sevm.value.toNat

/-- **The refutation of B**: a configured history under the original hypotheses with a
committed submission frame that paid its executed word fee but less than the Nat fee. -/
def NatFeeGuaranteeRefuted : Prop :=
  ∃ (cfg : ChainConfig) (checkpoint future : BlockChain)
    (trace : ConfiguredHistoryTrace cfg checkpoint future),
    SystemCodeInstalled checkpoint.state ∧
    trace.NoSenderAt systemAddress ∧ trace.NoAuthorityAt systemAddress ∧
    (∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress) ∧
    checkpoint.state.getCode systemAddress = ByteArray.empty ∧
    Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial ∧
    ∃ frame ∈ trace.settledFrames.flatMap balanceFrameObservation,
      ∃ (model : Blanc.WithdrawalRequest.State) (iterations : Nat) (output : B256),
        submissionPaymentFrame frame ∧
        model.excess = ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0).toNat ∧
        WordFakeExponential.Run ((frame.pre.getStor withdrawalRequestPredeployAddress).get 0)
          17 1 17 0 iterations output ∧
        (output / 17).toNat ≤ frame.sevm.value.toNat ∧
        frame.sevm.value.toNat < Blanc.WithdrawalRequest.fee model

theorem not_natFeeGuarantee_of_refuted (h : NatFeeGuaranteeRefuted) : ¬ NatFeeGuarantee := by
  intro guarantee
  obtain ⟨cfg, checkpoint, future, trace, installed, senders, authorities, avoid, systemEmpty,
    init, frame, member, model, iterations, output, payment, excess, run, paid, below⟩ := h
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le below
    (guarantee cfg checkpoint future trace installed senders authorities avoid systemEmpty init
      frame member model iterations output payment excess run paid))

/-- The witness history's remaining inputs: the three-block configured history with the
original hypotheses, and block C's submission frame among its settled frames at excess
`2893` and value `2 ^ 245`. -/
structure RefutationWitness where
  cfg : ChainConfig
  checkpoint : BlockChain
  future : BlockChain
  trace : ConfiguredHistoryTrace cfg checkpoint future
  installed : SystemCodeInstalled checkpoint.state
  senders : trace.NoSenderAt systemAddress
  authorities : trace.NoAuthorityAt systemAddress
  avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
    root.sevm.currentTarget ≠ systemAddress
  systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty
  init : Blanc.WithdrawalRequest.RepresentsStorage
    (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
    Blanc.WithdrawalRequest.initial
  frame : Exec.Frame
  member : frame ∈ trace.settledFrames.flatMap balanceFrameObservation
  payment : submissionPaymentFrame frame
  excess : (frame.pre.getStor withdrawalRequestPredeployAddress).get 0 = (2893 : Nat).toB256
  value : frame.sevm.value = (2 ^ 245 : Nat).toB256

/-- The Nat fee at excess `2893` (U2a's `fee_2893`). -/
def natFee2893 : Nat :=
  80668064690921409049190791237320678716946849613533250306370202067869504081

/-- The word fee loop's output at excess `2893` (U2a's `word_run_2893_existing`). -/
def wordOutput2893 : Nat :=
  545485220060489857066268109499810576327418688227975047986437738206577926843

/-- The executed word fee at excess `2893` (U2a's `word_run_2893_fee`). -/
def wordFee2893 : Nat :=
  32087365885911168062721653499988857431024628719292649881555161070975172167

/-- **B is refuted by the witness.**  The numeric inputs are stated in the shapes of
U2a's `NumericFacts` (`word_run_2893_existing`, `word_run_2893_fee`,
`word_fee_2893_le_two_pow_245`, `fee_2893`, `two_pow_245_lt_nat_fee_2893`) so they
discharge by citation once that module is merged. -/
theorem natFeeGuaranteeRefuted_of_witness (w : RefutationWitness)
    (word_run_2893_existing : WordFakeExponential.Run (2893 : Nat).toB256 (17 : Nat).toB256
      (1 : Nat).toB256 (17 : Nat).toB256 (0 : Nat).toB256 457 wordOutput2893.toB256)
    (word_run_2893_fee : (wordOutput2893.toB256 / (17 : Nat).toB256).toNat = wordFee2893)
    (word_fee_2893_le_two_pow_245 : wordFee2893 ≤ 2 ^ 245)
    (fee_2893 : ∀ {state : Blanc.WithdrawalRequest.State}, state.excess = 2893 →
      Blanc.WithdrawalRequest.fee state = natFee2893)
    (two_pow_245_lt_nat_fee_2893 : 2 ^ 245 < natFee2893) :
    NatFeeGuaranteeRefuted := by
  have h17 : (17 : Nat).toB256 = (17 : B256) := by decide
  have h1 : (1 : Nat).toB256 = (1 : B256) := by decide
  have h0 : (0 : Nat).toB256 = (0 : B256) := by decide
  have h2893 : ((2893 : Nat).toB256).toNat = 2893 := B256.toNat_toB256_of_lt (by decide)
  have h245 : ((2 ^ 245 : Nat).toB256).toNat = 2 ^ 245 := B256.toNat_toB256_of_lt (by decide)
  rw [h17, h1, h0] at word_run_2893_existing
  rw [h17] at word_run_2893_fee
  refine ⟨w.cfg, w.checkpoint, w.future, w.trace, w.installed, w.senders, w.authorities, w.avoid,
    w.systemEmpty, w.init, w.frame, w.member, ⟨2893, 0, 0, 0, []⟩, 457, wordOutput2893.toB256,
    w.payment, ?_, ?_, ?_, ?_⟩
  · rw [w.excess, h2893]
  · rw [w.excess]; exact word_run_2893_existing
  · rw [w.value, h245, word_run_2893_fee]; exact word_fee_2893_le_two_pow_245
  · rw [w.value, h245, fee_2893 rfl]; exact two_pow_245_lt_nat_fee_2893

/-- The witness from three configured block traces: per-block sender, authority and
creation-frame facts, and block C's submission frame. -/
def RefutationWitness.ofBlocks {cfg : ChainConfig} {checkpoint chainA chainB chainC : BlockChain}
    (hcfg : cfg.Valid) (hctx : checkpoint.ValidContext) (hid : cfg.chainId = checkpoint.chainId)
    (traceA : ConfiguredBlockTrace cfg checkpoint chainA)
    (traceB : ConfiguredBlockTrace cfg chainA chainB)
    (traceC : ConfiguredBlockTrace cfg chainB chainC)
    (installed : SystemCodeInstalled checkpoint.state)
    (sendersA : traceA.bodyTrace.transactions.NoSenderAt systemAddress)
    (sendersB : traceB.bodyTrace.transactions.NoSenderAt systemAddress)
    (sendersC : traceC.bodyTrace.transactions.NoSenderAt systemAddress)
    (authoritiesA : ∀ p ∈ traceA.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ systemAddress)
    (authoritiesB : ∀ p ∈ traceB.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ systemAddress)
    (authoritiesC : ∀ p ∈ traceC.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ systemAddress)
    (avoidA : ∀ root ∈ traceA.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress)
    (avoidB : ∀ root ∈ traceB.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress)
    (avoidC : ∀ root ∈ traceC.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ systemAddress)
    (systemEmpty : checkpoint.state.getCode systemAddress = ByteArray.empty)
    (init : Blanc.WithdrawalRequest.RepresentsStorage
      (checkpoint.state.getStor withdrawalRequestPredeployAddress).get
      Blanc.WithdrawalRequest.initial)
    (frame : Exec.Frame)
    (memberC : frame ∈ traceC.settledFrames.flatMap balanceFrameObservation)
    (payment : submissionPaymentFrame frame)
    (excess : (frame.pre.getStor withdrawalRequestPredeployAddress).get 0 = (2893 : Nat).toB256)
    (value : frame.sevm.value = (2 ^ 245 : Nat).toB256) : RefutationWitness :=
  { cfg := cfg, checkpoint := checkpoint, future := chainC
    trace := history_of_three hcfg hctx hid traceA traceB traceC
    installed := installed
    senders := ⟨⟨⟨trivial, sendersA⟩, sendersB⟩, sendersC⟩
    authorities := ⟨⟨⟨trivial, authoritiesA⟩, authoritiesB⟩, authoritiesC⟩
    avoid := by
      intro root member
      simp only [history_of_three, ConfiguredHistoryTrace.rawFrames, List.nil_append,
        List.mem_append] at member
      rcases member with (hA | hB) | hC
      · exact avoidA root hA
      · exact avoidB root hB
      · exact avoidC root hC
    systemEmpty := systemEmpty
    init := init
    frame := frame
    member := by
      simp only [history_of_three, ConfiguredHistoryTrace.settledFrames, List.nil_append,
        List.flatMap_append]
      exact List.mem_append_right _ memberC
    payment := payment
    excess := excess
    value := value }

end Blanc.Lift.WithdrawalRequest.FeeCounterexample
