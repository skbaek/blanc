import Blanc.Composition.UniswapV2PairWeth9Tx1Frame
import Blanc.BlockForward
import Blanc.TransactionForward
import Blanc.CodeDelegation

/-!
# The closed instance's first transaction, on any agreeing world

`tx1_transaction`: for any block environment satisfying `Tx1Context` (BPO2, chain 1, base fee 1,
coinbase `0`, gas room; the trader's nonce `0`, ether `10^7` and no code; Token20's code at `X`,
`X` not created in this block, and `X`'s two touched balance slots holding `xT ≥ amountIn + 1`
and `xP ≠ 0` without a wrapping credit), processing the signed type-2 `tx1 v r s` as the block's
first transaction succeeds with the exact settled world `tx1SettledState` and the exact gas and
receipt facts.  Signature recovery is the explicit hypothesis `recoverSender 1 (tx1 v r s) = .ok
trader`, discharged where the signature is fixed.  Nothing else of the world is assumed.

Numbers: intrinsic gas 21584 (calldata floor 22460), frame 10173, gas used 31757, effective gas
price 2 (priority fee 1 over base fee 1): the trader pays 63514 wei, the coinbase earns 31757.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.VyperNonreentrantDeployed.Token20 (balSlot code)

/-- **What `tx1` needs of the block environment**: admission facts and `X`'s touched slots. -/
structure Tx1Context (benv : Benv) (xT xP : B256) : Prop where
  fork : benv.stat.fork = .bpo2
  chain : benv.stat.chainId = 1
  baseFee : benv.stat.baseFeePerGas = 1
  coinbase : benv.stat.coinbase = 0
  room : 50000 ≤ benv.stat.blockGasLimit
  nonce : (benv.state.get trader).nonce = 0
  balance : benv.state.bal trader = 10000000
  noCode : (benv.state.getCode trader).size = 0
  code : benv.state.getCode tokenX = code
  created : tokenX ∉ benv.createdAccounts
  slotTrader : (benv.state.getStor tokenX).get (balSlot trader) = xT
  slotPair : (benv.state.getStor tokenX).get (balSlot pair) = xP
  covers : amountIn < xT
  pairNonzero : xP ≠ 0
  noWrap : B256.Nof amountIn xP

/-- After admission: the trader's nonce bumped and the maximal fee `50000 × 2` taken. -/
def tx1DebitState (st : Jaune.State) : Jaune.State :=
  (st.incrNonce trader).setBal trader 9900000

/-- After the token frame. -/
def tx1FrameState (st : Jaune.State) (xT xP : B256) : Jaune.State :=
  tx1FrameWrites (tx1DebitState st) xT xP

/-- **The settled world of `tx1`**: the unused gas `18243 × 2` refunded to the trader and the
priority fee `31757 × 1` paid to the coinbase `0`. -/
def tx1SettledState (st : Jaune.State) (xT xP : B256) : Jaune.State :=
  ((tx1FrameState st xT xP).addBal trader 36486).addBal 0 31757

/-- Token20's runtime is no EIP-7702 delegation designator. -/
theorem getDelegatedCodeAddress_token20 : getDelegatedCodeAddress code = none :=
  getDelegatedCodeAddress_eq_none_of_size_ne (by decide +kernel)

theorem tx1_gas (v : Nat) (r s : Bytes) : (tx1 v r s).gas = 50000 := rfl

theorem tx1_value (v : Nat) (r s : Bytes) : (tx1 v r s).value = 0 := rfl

theorem tx1_intrinsic {rules : ForkRules} (v : Nat) (r s : Bytes)
    (hsg : rules.stateGas = none) (hbase : rules.gas.txBase = 21000)
    (hfloor : rules.gas.floorTokenCost = 10) :
    calculateIntrinsicCost rules (tx1 v r s) trader = (21584, 22460) := by
  rw [calculateIntrinsicCost_two_call hsg (by rfl)]
  simp only [tx1, hbase, hfloor]
  decide +kernel

/-- **`tx1`'s message runs the token frame**: any message to `X` with Token20's code, from the
trader, with `tx1`'s calldata and 28416 gas, on a world whose two touched slots hold `xT` and `xP`
(also at transaction start, `X` not created), executes to exactly `tx1FrameWrites`. -/
theorem tx1_message_success {msg : Msg} {xT xP : B256}
    (hcode : msg.code = code) (hfork : CoveredFork msg.benv.stat.fork)
    (hcaller : msg.caller = trader) (htarget : msg.currentTarget = tokenX)
    (hstatic : msg.isStatic = false) (hdata : msg.data = tx1Data) (hgas : msg.gas = 28416)
    (hT : (msg.benv.state.getStor tokenX).get (balSlot trader) = xT)
    (hP : (msg.benv.state.getStor tokenX).get (balSlot pair) = xP)
    (hTo : (msg.benv.stat.origState.getStor tokenX).get (balSlot trader) = xT)
    (hPo : (msg.benv.stat.origState.getStor tokenX).get (balSlot pair) = xP)
    (hcreated : tokenX ∉ msg.benv.createdAccounts)
    (hcoldT : (tokenX, balSlot trader) ∉ msg.accessedStorageKeys)
    (hcoldP : (tokenX, balSlot pair) ∉ msg.accessedStorageKeys)
    (hcov : amountIn < xT) (hP0 : xP ≠ 0) (hnof : B256.Nof amountIn xP) :
    ∃ post, exec (initEvm msg) = .ok post ∧
      post.error = none ∧ post.refundCounter = 0 ∧
      post.gasLeft = 18243 ∧ post.accountsToDelete.toList = [] ∧
      post.state = tx1FrameWrites msg.benv.state xT xP ∧ post.logs = [] := by
  have created : tokenX ∉ (initDevm msg).createdAccounts := hcreated
  obtain ⟨post, execution, gas, error, refund, deleted, logs, state, _⟩ :=
    tx1_frame_success (xT := xT) (xP := xP) (sevm := initSevm msg) (pre := initDevm msg)
      hcode hfork hcaller htarget hstatic hdata rfl rfl hgas hT
      (by unfold Devm.getOrigStorVal; rw [ite_eq_right created]; exact hTo) hP
      (by unfold Devm.getOrigStorVal; rw [ite_eq_right created]; exact hPo)
      hcoldT hcoldP hcov hP0 hnof rfl rfl
  refine ⟨post, execution, error, refund, gas, ?_, state, ?_⟩
  · rw [deleted]
    change (Std.HashSet.emptyWithCapacity : AdrSet).toList = []
    exact Std.HashSet.toList_emptyWithCapacity
  · rw [logs]
    change (match msg.benv.stat.rules.stateGas with | none => [] | some _ => _) = []
    rw [CoveredFork.rules_stateGas_none hfork]

theorem tx1_prepared_success {benv : Benv} {xT xP : B256} (ctx : Tx1Context benv xT xP)
    (v : Nat) (r s : Bytes) (debit : Jaune.State) (msg : Msg) (after : Benv)
    (hdebit : (benv.state.incrNonce trader).subBal trader
      ((tx1 v r s).gas * (min 1 (8 - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas)).toB256 = some debit)
    (hprepare : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction (tx1 v r s) 0 trader
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        21584 []) (tx1 v r s) = .ok msg)
    (hentry : msg.benvAfterTransfer = .ok after) :
    ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧
      post.error = none ∧ post.refundCounter = 0 ∧
      post.gasLeft = 18243 ∧ post.accountsToDelete.toList = [] ∧
      post.state = tx1FrameState benv.state xT xP ∧ post.logs = [] := by
  have debitEq : debit = tx1DebitState benv.state := by
    obtain ⟨_, equation⟩ := State.of_subBal hdebit
    rw [State.incrNonce_bal, ctx.balance, ctx.baseFee] at equation
    have fee : (10000000 : B256) - Nat.toB256 ((tx1 v r s).gas * (min 1 (8 - 1) + 1)) = 9900000 := by
      change (10000000 : B256) - Nat.toB256 (50000 * (min 1 (8 - 1) + 1)) = 9900000
      decide +kernel
    rw [fee] at equation
    exact equation
  subst debit
  rw [prepareMessage_call (by rfl)] at hprepare
  have msgEq := (Except.ok.inj hprepare).symm
  subst msg
  rw [Msg.benvAfterTransfer_of_value_zero (by rfl)] at hentry
  have afterEq := (Except.ok.inj hentry).symm
  subst after
  have fork : CoveredFork benv.stat.fork := by
    rw [ctx.fork]
    exact .bpo2
  have hsc : trader ≠ tokenX := trader_ne_tokenX
  have hstor : ((tx1DebitState benv.state).getStor tokenX) = benv.state.getStor tokenX := by
    change (((benv.state.incrNonce trader).setBal trader 9900000).get tokenX).stor = _
    rw [State.setBal_get_ne hsc, State.incrNonce_get_stor, ite_eq_right (fun h => hsc h.1)]
    rfl
  have hkeys : ∀ k, (tokenX, k) ∉ (Std.HashSet.ofList ([] : List (Adr × B256))) := by
    intro k
    rw [Std.HashSet.mem_ofList]
    simp only [List.contains_nil, Bool.false_eq_true, not_false_eq_true]
  let m := callMessage { benv.beginTransaction with state := tx1DebitState benv.state }
    (transactionTenv benv.beginTransaction (tx1 v r s) 0 trader
      (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) 21584 []) (tx1 v r s) tokenX
  obtain ⟨post, execution, error, refund, gas, deleted, state, logs⟩ :=
    tx1_message_success (xT := xT) (xP := xP) (msg := m.withBenv m.benv)
      (by change (tx1DebitState benv.state).getCode tokenX = code
          rw [tx1DebitState, State.setBal_getCode]
          exact State.incrNonce_get_code.trans ctx.code)
      fork rfl rfl rfl rfl
      (by change (tx1 v r s).gas - 21584 = 28416
          rw [tx1_gas])
      (by change ((tx1DebitState benv.state).getStor tokenX).get (balSlot trader) = xT
          rw [hstor]; exact ctx.slotTrader)
      (by change ((tx1DebitState benv.state).getStor tokenX).get (balSlot pair) = xP
          rw [hstor]; exact ctx.slotPair)
      ctx.slotTrader ctx.slotPair ctx.created (hkeys _) (hkeys _)
      ctx.covers ctx.pairNonzero ctx.noWrap
  exact ⟨post, execution, error, refund, gas, deleted, state, logs⟩

/-- **The first transaction of the closed instance**, on any block environment satisfying
`Tx1Context`, with sender recovery as a hypothesis: processing `tx1 v r s` as the block's first
transaction yields exactly `tx1SettledState`, gas used 31757, and the one success receipt with no
log; it creates no deposit request. -/
theorem tx1_transaction {benv : Benv} {xT xP : B256} (ctx : Tx1Context benv xT xP)
    {v : Nat} {r s : Bytes} (hrecover : recoverSender 1 (tx1 v r s) = .ok trader) :
    ∃ bout : BlockOutput,
      processTransaction benv BlockOutput.init (tx1 v r s) 0 =
        .ok (tx1SettledState benv.state xT xP, bout) ∧
      bout.blockGasUsed = 31757 ∧ bout.cumulativeGasUsed = 31757 ∧
      bout.receiptKeys = [[0x80]] ∧
      bout.receiptsTrie[([0x80] : Bytes)]? = some (makeReceipt (tx1 v r s) none 31757 []) ∧
      parseDepositRequests bout = .ok [] := by
  have fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2
  let Q : Jaune.State → Devm → Prop := fun _ post =>
    post.state = tx1FrameState benv.state xT xP ∧ post.gasLeft = 18243 ∧
      post.refundCounter = 0 ∧ post.accountsToDelete.toList = [] ∧ post.logs = []
  obtain ⟨debit, post, bout, facts, process, cumulative, gas, keys, receipt⟩ :=
    processTransaction_call_value_of_exec_receipts (Q := Q) (bout := BlockOutput.init)
      (tx := tx1 v r s) (E := trader) (t := tokenX) (chainId := 1)
      (maxPriorityFee := 1) (maxFee := 8) (intrinsicGas := 21584)
      (calldataFloorGas := 22460) (index := 0)
      fork (by rfl) ctx.chain.symm (by decide) (by rw [ctx.baseFee]; decide)
      (tx1_intrinsic v r s (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by rw [tx1_gas]; decide)
      (CoveredFork.checkTransactionGasCap_ok fork (by rw [tx1_gas]; decide))
      (by change (0 : UInt64) ≠ UInt64.max; decide) ctx.room
      (by rw [ctx.chain]; exact hrecover)
      ctx.nonce
      (by change (benv.state.getCode trader).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by rw [tx1_gas, tx1_value, show (benv.state.get trader).bal = 10000000 from ctx.balance]; decide +kernel)
      (by rw [ctx.code]; exact getDelegatedCodeAddress_token20)
      (by unfold BenvStat.rules; rw [ctx.fork]; decide +kernel)
      (by intro debit msg after hdebit hprepare hentry
          obtain ⟨post, execution, error, refund, gas, deletion, state, logs⟩ :=
            tx1_prepared_success ctx v r s debit msg after hdebit hprepare hentry
          exact ⟨post, execution, error, by rw [refund], state, gas, refund, deletion, logs⟩)
  obtain ⟨state, left, refund, deleted, logs⟩ := facts
  have used : txGasUsed (tx1 v r s).gas 22460 post.gasLeft post.refundCounter.toNat = 31757 := by
    rw [left, refund, tx1_gas]
    decide +kernel
  have process' : processTransaction benv BlockOutput.init (tx1 v r s) 0 =
      .ok (tx1SettledState benv.state xT xP, bout) := by
    have refundWei : (((tx1 v r s).gas - 31757) * (min 1 (8 - 1) + 1)).toB256 = (36486 : B256) := by
      rw [tx1_gas]
      decide +kernel
    have tipWei : (31757 * min 1 (8 - 1)).toB256 = (31757 : B256) := by decide +kernel
    rw [deleted, List.foldl_nil, state, used, ctx.baseFee, ctx.coinbase, refundWei, tipWei] at process
    exact process
  have gas' : bout.blockGasUsed = 31757 := by rw [used] at gas; exact gas
  have cumulative' : bout.cumulativeGasUsed = 31757 := by
    rw [used] at cumulative; exact cumulative
  have keys' : bout.receiptKeys = [[0x80]] := by
    rw [receiptKey_zero] at keys
    exact keys
  have receipt' : bout.receiptsTrie[([0x80] : Bytes)]? =
      some (makeReceipt (tx1 v r s) none 31757 []) := by
    rw [receiptKey_zero, cumulative', logs] at receipt
    exact receipt
  refine ⟨bout, process', gas', cumulative', keys', receipt', ?_⟩
  apply BlockForward.parseDepositRequests_of_no_deposit_logs
  intro key member
  rw [keys'] at member
  have keyEq : key = [0x80] := List.mem_singleton.mp member
  subst key
  refine ⟨_, receipt', ?_⟩
  intro log member
  exact absurd member List.not_mem_nil

end Blanc.Composition.UniswapV2PairWeth9Instance
