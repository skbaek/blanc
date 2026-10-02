import Blanc.Lift.WithdrawalRequest.FloodTx
import Blanc.BlockForward

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
    (hrecover : recoverSender benv.stat.chainId txC = .ok senderE)
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
    -- the rest of the body, on whatever the transaction leaves
    (hdeposit : ∀ bout : BlockOutput, parseDepositRequests bout = .ok [])
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
  obtain ⟨post, bout', hQ, hproc, -, -⟩ := txC_processTransaction
    (benv := benv.withState stHistory) (bout := BlockOutput.init) (index := 0)
    hfork hchain hbase (by show 2 ^ 20 ≤ benv.stat.blockGasLimit - 0; exact hroom) hrecover
    hnonce hnocode hfunds hcode hrep hbounds hexcess hrun hpaid hiters
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
    (by rw [putIndex_single]; exact applyTransactions_single hproc') (hdeposit bout') hWrun hCrun

/-! ## Block B -/

/-- **Block B's body.**  As for block C, with `txB_processTransaction`; the flood
frame's deletion set is not yet exposed by `flood_exec`, so the settled state keeps
the deletion fold. -/
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
    (hrecover : recoverSender benv.stat.chainId txB = .ok senderE)
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
    (hdeposit : ∀ bout : BlockOutput, parseDepositRequests bout = .ok [])
    (hW : ∀ benvTxs : Benv, ∃ stW outW,
      processCheckedSystemTransaction benvTxs withdrawalRequestPredeployAddress [] =
        .ok (stW, outW))
    (hC : ∀ benvTxs : Benv, ∃ stC outC,
      processCheckedSystemTransaction benvTxs consolidationRequestPredeployAddress [] =
        .ok (stC, outC)) :
    ∃ (post : Devm) (boutTxs : BlockOutput) (stTx stW stC : State) (outW outC : MsgCallOutput),
      TxBPost (benv.withState stHistory) σ0 post ∧
      stTx = post.accountsToDelete.toList.foldl destroyAccount
        ((post.state.addBal senderE
            ((txB.gas - txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat) *
              (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256).addBal
          benv.stat.coinbase
            (txGasUsed txB.gas 23380 post.gasLeft post.refundCounter.toNat *
              (min 1 (8 - benv.stat.baseFeePerGas))).toB256) ∧
      applyBody benv [Sum.inr txB] [] =
        .ok (stC, requestsOutput boutTxs outW.returnData outC.returnData) ∧
      processCheckedSystemTransaction
        (((benv.withState stBeacon).withState stHistory).withState stTx)
        withdrawalRequestPredeployAddress [] = .ok (stW, outW) ∧
      processCheckedSystemTransaction
        ((((benv.withState stBeacon).withState stHistory).withState stTx).withState stW)
        consolidationRequestPredeployAddress [] = .ok (stC, outC) := by
  set benvTx : Benv := (benv.withState stBeacon).withState stHistory with hbenvTx
  obtain ⟨post, bout', hQ, hproc, -, -⟩ := txB_processTransaction
    (benv := benv.withState stHistory) (bout := BlockOutput.init) (index := 0)
    hfork hnocap hchain hbase (by show 2 ^ 28 ≤ benv.stat.blockGasLimit - 0; exact hroom)
    hrecover hnonce hnocode hfunds hLcode hLbal hcode hrep hexcess hcountLt htailLt hqueue
  obtain ⟨stW, outW, hWrun⟩ := hW (benvTx.withState _)
  obtain ⟨stC, outC, hCrun⟩ := hC ((benvTx.withState _).withState stW)
  refine ⟨post, bout', _, stW, stC, outW, outC, hQ, rfl, ?_, hWrun, hCrun⟩
  exact applyBody_forward hfork hbeacon hlast hhistory (decode_single txB)
    (by rw [putIndex_single]; exact applyTransactions_single hproc) (hdeposit bout') hWrun hCrun

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

end Blanc.Lift.WithdrawalRequest.FeeCounterexample
