import Blanc.Composition.UniswapV2PairWeth9Tx2Run
import Blanc.Composition.UniswapV2PairWeth9Tx2Receipts
import Blanc.BlockForward

/-!
# The closed instance's second transaction, on any agreeing world

`tx2_transaction`: for any block environment satisfying `Tx2Context` (BPO2, chain 1, base fee 1,
coinbase `0`, timestamp `1`, gas room; the trader's nonce `1`, ether `9936486` (what `tx1` leaves)
and no code; the Pair's code and `W0`'s Pair storage; WETH9's code with the Pair's balance `10^6`
and the trader's `0`; Token20's code at `X` with the Pair's balance `1001000` (what `tx1` leaves);
none of the three created in this block), processing the signed type-2 `tx2 v r s` as the block's
second transaction, after a first one that used `31757` gas and left no deposit log, succeeds with
the exact settled world `tx2SettledState` and the exact gas and receipt facts.  Signature recovery is
the explicit hypothesis `recoverSender 1 (tx2 v r s) = .ok trader`.

Numbers: intrinsic gas 21980 (calldata floor 23450), frame 105225 of its 278020, refund 2800, gas
used 124405, effective gas price 2: the trader pays 248810 wei, the coinbase earns 124405.  The
trader's WETH9 balance slot goes `0 → 996`, the Pair's `10^6 → 999004`; the Pair's reserves become
`1001000`/`999004` at timestamp `1`, the lock is restored.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.Lift.UniswapV2Pair

/-- **What `tx2` needs of the block environment.** -/
structure Tx2Context (benv : Benv) : Prop where
  fork : benv.stat.fork = .bpo2
  chain : benv.stat.chainId = 1
  baseFee : benv.stat.baseFeePerGas = 1
  coinbase : benv.stat.coinbase = 0
  time : benv.stat.time = 1
  room : 331757 ≤ benv.stat.blockGasLimit
  nonce : (benv.state.get trader).nonce = 1
  balance : benv.state.bal trader = 9936486
  noCode : (benv.state.getCode trader).size = 0
  pairCode : benv.state.getCode pair = UniswapV2Pair.code
  pairStor : benv.state.getStor pair = w0PairStor
  wethCode : benv.state.getCode weth = Weth9.code
  wethPair : (benv.state.getStor weth).get (Weth9.balSlot pair) = 1000000
  wethTrader : (benv.state.getStor weth).get (Weth9.balSlot trader) = 0
  xCode : benv.state.getCode tokenX = VyperNonreentrantDeployed.Token20.code
  xPair : (benv.state.getStor tokenX).get (VyperNonreentrantDeployed.Token20.balSlot pair) = 1001000
  createdPair : pair ∉ benv.createdAccounts
  createdWeth : weth ∉ benv.createdAccounts
  createdX : tokenX ∉ benv.createdAccounts

/-- After admission: the trader's nonce bumped and the maximal fee `300000 × 2` taken. -/
def tx2DebitState (st : Jaune.State) : Jaune.State :=
  (st.incrNonce trader).setBal trader 9336486

/-- The swap frame's writes: the lock cleared, WETH9's two balance writes, the accumulators, the
reserves, the lock restored. -/
def tx2FrameWrites (st : Jaune.State) : Jaune.State :=
  ((((wethTransferWrites (st.setStorVal pair 12 0)).setStorVal pair 9 tx2Acc0).setStorVal pair 10
    tx2Acc0).setStorVal pair 8 tx2Packed1).setStorVal pair 12 1

/-- **The settled world of `tx2`**: the unused gas `175595 × 2` refunded to the trader and the
priority fee `124405 × 1` paid to the coinbase `0`. -/
def tx2SettledState (st : Jaune.State) : Jaune.State :=
  ((tx2FrameWrites (tx2DebitState st)).addBal trader 351190).addBal 0 124405

/-- `tx2`'s logs: WETH9's `Transfer`, the Pair's `Sync` and `Swap`. -/
def tx2Logs : List Log := [wethTransferLog, tx2SyncLog, tx2SwapLog]

theorem tx2_gas (v : Nat) (r s : Bytes) : (tx2 v r s).gas = 300000 := rfl

theorem tx2_value (v : Nat) (r s : Bytes) : (tx2 v r s).value = 0 := rfl

theorem tx2_intrinsic {rules : ForkRules} (v : Nat) (r s : Bytes)
    (hsg : rules.stateGas = none) (hbase : rules.gas.txBase = 21000)
    (hfloor : rules.gas.floorTokenCost = 10) :
    calculateIntrinsicCost rules (tx2 v r s) trader = (21980, 23450) := by
  rw [calculateIntrinsicCost_two_call hsg (by rfl)]
  simp only [tx2, hbase, hfloor]
  decide +kernel

theorem tx2DebitState_get_ne (st : Jaune.State) {a : Adr} (ha : trader ≠ a) :
    ((tx2DebitState st).get a).stor = (st.get a).stor ∧
      ((tx2DebitState st).get a).code = (st.get a).code := by
  unfold tx2DebitState
  rw [State.setBal_get_ne ha, State.incrNonce_get_stor, ite_eq_right (fun h => ha h.1)]
  exact ⟨rfl, by rw [State.incrNonce_get_code]⟩

theorem tx2_cold_list {a : Adr} (ha : a = tokenX ∨ a = weth) :
    a ∉ (Std.HashSet.ofList [(0 : Adr)]).insertMany (Fork.bpo2.ruleSet.precompiles ++ [trader, pair]) := by
  rw [Std.HashSet.mem_insertMany_list, Std.HashSet.mem_ofList]
  rcases ha with rfl | rfl <;> decide +kernel

/-- **`tx2`'s message enters the swap frame**: for the debited state, the prepared message and its
entry environment, the message's entry machine satisfies `Tx2Frame` over the debited world. -/
theorem tx2_prepared_frame {benv : Benv} (ctx : Tx2Context benv)
    (v : Nat) (r s : Bytes) (debit : Jaune.State) (msg : Msg) (after : Benv)
    (hdebit : (benv.state.incrNonce trader).subBal trader
      ((tx2 v r s).gas * (min 1 (8 - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas)).toB256 = some debit)
    (hprepare : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction (tx2 v r s) 1 trader
        (min 1 (8 - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
        21980 []) (tx2 v r s) = .ok msg)
    (hentry : msg.benvAfterTransfer = .ok after) :
    Tx2Frame (initSevm (msg.withBenv after)) (initDevm (msg.withBenv after)) ∧
      (initDevm (msg.withBenv after)).state = tx2DebitState benv.state := by
  have debitEq : debit = tx2DebitState benv.state := by
    obtain ⟨_, equation⟩ := State.of_subBal hdebit
    rw [State.incrNonce_bal, ctx.balance, ctx.baseFee] at equation
    have fee : (9936486 : B256) - Nat.toB256 ((tx2 v r s).gas * (min 1 (8 - 1) + 1)) = 9336486 := by
      rw [tx2_gas]
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
  have hP := tx2DebitState_get_ne benv.state trader_ne_pair
  have hW := tx2DebitState_get_ne benv.state trader_ne_weth
  have hX := tx2DebitState_get_ne benv.state trader_ne_tokenX
  have hsg : benv.stat.rules.stateGas = none := by rw [rules_bpo2 ctx.fork]; rfl
  refine ⟨⟨?code, ctx.fork, rfl, rfl, rfl, rfl, rfl, rfl, ctx.time, ctx.pairStor, ctx.wethPair,
    ctx.wethTrader, rfl, rfl, ?gas, rfl, rfl, rfl, ?logs, ?deleted, ?keys, ?coldX, ?coldW,
    ctx.createdPair, ctx.createdWeth, ctx.createdX, ?pairStor, ?pairCode, ?wethCode, ?xCode,
    ?wethPair, ?wethTrader, ?xPair⟩, rfl⟩
  case code =>
    change ((tx2DebitState benv.state).get pair).code = _
    rw [hP.2]
    exact ctx.pairCode
  case gas =>
    rw [initDevm_gasLeft]
    change (tx2 v r s).gas - 21980 = 278020
    rw [tx2_gas]
  case logs =>
    change (match benv.stat.rules.stateGas with | none => [] | some _ => _) = []
    rw [hsg]
  case deleted => exact fun _ => Std.HashSet.not_mem_emptyWithCapacity
  case keys =>
    intro k hk
    change k ∈ Std.HashSet.ofList ([] : List (Adr × B256)) at hk
    rw [Std.HashSet.mem_ofList] at hk
    simp only [List.contains_nil, Bool.false_eq_true] at hk
  case coldX =>
    change tokenX ∉ (Std.HashSet.ofList [benv.stat.coinbase]).insertMany
      (benv.stat.rules.precompiles ++ [trader, pair])
    rw [ctx.coinbase, rules_bpo2 ctx.fork]
    exact tx2_cold_list (Or.inl rfl)
  case coldW =>
    change weth ∉ (Std.HashSet.ofList [benv.stat.coinbase]).insertMany
      (benv.stat.rules.precompiles ++ [trader, pair])
    rw [ctx.coinbase, rules_bpo2 ctx.fork]
    exact tx2_cold_list (Or.inr rfl)
  case pairStor => exact hP.1.trans ctx.pairStor
  case pairCode => exact hP.2.trans ctx.pairCode
  case wethCode => exact hW.2.trans ctx.wethCode
  case xCode => exact hX.2.trans ctx.xCode
  case wethPair =>
    change ((tx2DebitState benv.state).getStor weth).get _ = _
    unfold State.getStor
    rw [hW.1]
    exact ctx.wethPair
  case wethTrader =>
    change ((tx2DebitState benv.state).getStor weth).get _ = _
    unfold State.getStor
    rw [hW.1]
    exact ctx.wethTrader
  case xPair =>
    change ((tx2DebitState benv.state).getStor tokenX).get _ = _
    unfold State.getStor
    rw [hX.1]
    exact ctx.xPair

/-- The Pair's runtime is no EIP-7702 delegation designator. -/
theorem getDelegatedCodeAddress_pair : getDelegatedCodeAddress UniswapV2Pair.code = none := by
  unfold getDelegatedCodeAddress
  have h : ¬ isValidDelegation UniswapV2Pair.code := fun h => by
    have h1 := h.1
    change UniswapV2Pair.code.size = eoaDelegatedCodeLength at h1
    revert h1
    decide +kernel
  simp only [h, ↓reduceIte]

theorem tx2FrameWrites_eq (b : Devm) : tx2PostState b = tx2FrameWrites b.state := rfl

theorem tx2_logs_noDeposit : ∀ log ∈ tx2Logs, log.address ≠ depositContractAddress := by
  intro log member
  simp only [tx2Logs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> decide +kernel

/-- **The second transaction of the closed instance**, on any block environment satisfying
`Tx2Context`, after a first transaction that used `31757` gas and logged no deposit, with sender
recovery as a hypothesis: processing `tx2 v r s` as the block's second transaction yields exactly
`tx2SettledState`, gas used 124405, the success receipt with `tx2Logs` at key `[0x01]`, the earlier
receipts untouched, no deposit request, and block gas used within the configured limit. -/
theorem tx2_transaction {benv : Benv} (ctx : Tx2Context benv) {bout : BlockOutput}
    (hused : bout.blockGasUsed = 31757) (hkeys : bout.receiptKeys = [[0x80]])
    (hprev : ∀ key ∈ bout.receiptKeys, ∃ entry, bout.receiptsTrie[key]? = some entry ∧
      ∀ log ∈ entry.2.logs, log.address ≠ depositContractAddress)
    {v : Nat} {r s : Bytes} (hrecover : recoverSender 1 (tx2 v r s) = .ok trader) :
    ∃ bout2 : BlockOutput,
      processTransaction benv bout (tx2 v r s) 1 = .ok (tx2SettledState benv.state, bout2) ∧
      bout2.blockGasUsed = 156162 ∧ bout2.cumulativeGasUsed = bout.cumulativeGasUsed + 124405 ∧
      bout2.receiptKeys = bout.receiptKeys ++ [[0x01]] ∧
      bout2.receiptsTrie[([0x01] : Bytes)]? =
        some (makeReceipt (tx2 v r s) none bout2.cumulativeGasUsed tx2Logs) ∧
      (∀ key : Bytes, key ≠ [0x01] → bout2.receiptsTrie[key]? = bout.receiptsTrie[key]?) ∧
      parseDepositRequests bout2 = .ok [] ∧ bout2.blockGasUsed ≤ 1000000 := by
  have fork : CoveredFork benv.stat.fork := ctx.fork ▸ .bpo2
  let Q : Jaune.State → Devm → Prop := fun _ post =>
    post.state = tx2FrameWrites (tx2DebitState benv.state) ∧ post.gasLeft = 172795 ∧
      post.refundCounter = 2800 ∧ (∀ a, a ∉ post.accountsToDelete) ∧ post.logs = tx2Logs
  obtain ⟨debit, post, bout', facts, process, cumulative, gas, keys, receipt, other⟩ :=
    processTransaction_call_value_of_exec_receipts_frame (Q := Q) (bout := bout)
      (tx := tx2 v r s) (E := trader) (t := pair) (chainId := 1)
      (maxPriorityFee := 1) (maxFee := 8) (intrinsicGas := 21980)
      (calldataFloorGas := 23450) (index := 1)
      fork (by rfl) ctx.chain.symm (by decide) (by rw [ctx.baseFee]; decide)
      (tx2_intrinsic v r s (CoveredFork.rules_stateGas_none fork)
        (CoveredFork.rules_txBase fork) (CoveredFork.rules_floorTokenCost fork))
      (by rw [tx2_gas]; decide)
      (CoveredFork.checkTransactionGasCap_ok fork (by rw [tx2_gas]; decide))
      (by change (1 : UInt64) ≠ UInt64.max; decide)
      (by rw [tx2_gas, hused]; have := ctx.room; omega)
      (by rw [ctx.chain]; exact hrecover)
      ctx.nonce
      (by change (benv.state.getCode trader).isEmpty = true
          simp only [ByteArray.isEmpty, ctx.noCode]; rfl)
      (by rw [tx2_gas, tx2_value, show (benv.state.get trader).bal = 9936486 from ctx.balance]
          decide +kernel)
      (by rw [ctx.pairCode]; exact getDelegatedCodeAddress_pair)
      (by rw [rules_bpo2 ctx.fork]; decide +kernel)
      (by intro debit msg after hdebit hprepare hentry
          obtain ⟨frame, state0⟩ := tx2_prepared_frame ctx v r s debit msg after hdebit hprepare hentry
          obtain ⟨post, execution, gasLeft, error, refund, deleted, logs, state⟩ :=
            tx2_frame_success frame
          refine ⟨post, execution, error, by rw [refund]; decide, ?_, gasLeft, refund, deleted, logs⟩
          rw [state, tx2FrameWrites_eq, state0])
  obtain ⟨state, left, refund, deleted, logs⟩ := facts
  have used : txGasUsed (tx2 v r s).gas 23450 post.gasLeft post.refundCounter.toNat = 124405 := by
    rw [left, refund, tx2_gas]
    decide +kernel
  have nil : post.accountsToDelete.toList = [] := List.isEmpty_iff.mp (by
    rw [Std.HashSet.isEmpty_toList]
    exact Std.HashSet.isEmpty_iff_forall_not_mem.mpr deleted)
  have process' : processTransaction benv bout (tx2 v r s) 1 =
      .ok (tx2SettledState benv.state, bout') := by
    have refundWei : (((tx2 v r s).gas - 124405) * (min 1 (8 - 1) + 1)).toB256 = (351190 : B256) := by
      rw [tx2_gas]
      decide +kernel
    have tipWei : (124405 * min 1 (8 - 1)).toB256 = (124405 : B256) := by decide +kernel
    rw [nil, List.foldl_nil, state, used, ctx.baseFee, ctx.coinbase, refundWei, tipWei] at process
    exact process
  have gas' : bout'.blockGasUsed = 156162 := by rw [used, hused] at gas; exact gas
  have cumulative' : bout'.cumulativeGasUsed = bout.cumulativeGasUsed + 124405 := by
    rw [used] at cumulative; exact cumulative
  have keys' : bout'.receiptKeys = bout.receiptKeys ++ [[0x01]] := by
    rw [receiptKey_one] at keys
    exact keys
  have receipt' : bout'.receiptsTrie[([0x01] : Bytes)]? =
      some (makeReceipt (tx2 v r s) none bout'.cumulativeGasUsed tx2Logs) := by
    rw [receiptKey_one, logs] at receipt
    exact receipt
  have other' : ∀ key : Bytes, key ≠ [0x01] → bout'.receiptsTrie[key]? = bout.receiptsTrie[key]? := by
    intro key hk
    exact other key (by rw [receiptKey_one]; exact hk)
  refine ⟨bout', process', gas', cumulative', keys', receipt', other', ?_, by rw [gas']; decide⟩
  apply BlockForward.parseDepositRequests_of_no_deposit_logs
  intro key member
  rw [keys', List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · have hne : key ≠ [0x01] := by
      rw [hkeys, List.mem_singleton] at member
      rw [member]
      decide
    obtain ⟨entry, hentry, hlogs⟩ := hprev key member
    exact ⟨entry, by rw [other' key hne]; exact hentry, hlogs⟩
  · exact ⟨_, receipt', tx2_logs_noDeposit⟩

/-! ## The settled world, account by account -/

theorem pair_ne_zero : pair ≠ 0 := by decide +kernel
theorem weth_ne_zero : weth ≠ 0 := by decide +kernel

theorem tx2FrameWrites_get_ne (st : Jaune.State) {a : Adr} (hp : pair ≠ a) (hw : weth ≠ a) :
    (tx2FrameWrites st).get a = st.get a := by
  unfold tx2FrameWrites wethTransferWrites State.setStorVal
  rw [State.get_set_ne _ hp, State.get_set_ne _ hp, State.get_set_ne _ hp, State.get_set_ne _ hp,
    State.get_set_ne _ hw, State.get_set_ne _ hw, State.get_set_ne _ hp]

/-- **Every account other than the trader, the Pair, WETH9 and the coinbase `0` is untouched by
`tx2`.** -/
theorem tx2_settled_get_other (st : Jaune.State) {a : Adr}
    (ht : trader ≠ a) (hp : pair ≠ a) (hw : weth ≠ a) (h0 : (0 : Adr) ≠ a) :
    (tx2SettledState st).get a = st.get a := by
  unfold tx2SettledState
  rw [addBal_get_ne _ h0, addBal_get_ne _ ht, tx2FrameWrites_get_ne _ hp hw, tx2DebitState,
    debit_get_ne ht]

/-- **WETH9's storage after `tx2`**: the Pair's balance slot written `999004`, then the trader's
`996`. -/
theorem tx2_settled_wethStor (st : Jaune.State) :
    (tx2SettledState st).getStor weth =
      ((st.getStor weth).set (Weth9.balSlot pair) 999004).set (Weth9.balSlot trader) 996 := by
  unfold tx2SettledState State.getStor
  rw [addBal_get_ne _ weth_ne_zero.symm, addBal_get_ne _ trader_ne_weth]
  change (tx2FrameWrites (tx2DebitState st)).getStor weth = _
  unfold tx2FrameWrites wethTransferWrites
  rw [State.setStorVal_getStor_ne _ pair_ne_weth, State.setStorVal_getStor_ne _ pair_ne_weth,
    State.setStorVal_getStor_ne _ pair_ne_weth, State.setStorVal_getStor_ne _ pair_ne_weth,
    State.setStorVal_getStor_self, State.setStorVal_getStor_self,
    State.setStorVal_getStor_ne _ pair_ne_weth]
  unfold State.getStor tx2DebitState
  rw [debit_get_ne trader_ne_weth]

/-- **The Pair's storage after `tx2`**: the lock cleared and restored, both accumulators, the
packed reserves. -/
theorem tx2_settled_pairStor (st : Jaune.State) :
    (tx2SettledState st).getStor pair =
      (((((st.getStor pair).set 12 0).set 9 tx2Acc0).set 10 tx2Acc0).set 8 tx2Packed1).set 12 1 := by
  unfold tx2SettledState State.getStor
  rw [addBal_get_ne _ pair_ne_zero.symm, addBal_get_ne _ trader_ne_pair]
  change (tx2FrameWrites (tx2DebitState st)).getStor pair = _
  unfold tx2FrameWrites wethTransferWrites
  rw [State.setStorVal_getStor_self, State.setStorVal_getStor_self, State.setStorVal_getStor_self,
    State.setStorVal_getStor_self, State.setStorVal_getStor_ne _ pair_ne_weth.symm,
    State.setStorVal_getStor_ne _ pair_ne_weth.symm, State.setStorVal_getStor_self]
  unfold State.getStor tx2DebitState
  rw [debit_get_ne trader_ne_pair]

/-- **The trader gains `996` and the Pair loses `996` in WETH9's ledger** (from `0` and `10^6`). -/
theorem tx2_settled_weth_balances {benv : Benv} (ctx : Tx2Context benv) :
    ((tx2SettledState benv.state).getStor weth).get (Weth9.balSlot trader) =
        ((benv.state.getStor weth).get (Weth9.balSlot trader)) + swapOut ∧
      ((tx2SettledState benv.state).getStor weth).get (Weth9.balSlot pair) =
        ((benv.state.getStor weth).get (Weth9.balSlot pair)) - swapOut := by
  rw [tx2_settled_wethStor, Stor.get_set_self, Stor.get_set_ne _ weth_balSlot_trader_ne_pair,
    Stor.get_set_self, ctx.wethTrader, ctx.wethPair]
  exact ⟨by decide, by decide⟩

/-- **The Pair's stored reserves equal its new balances** (`reserve0 = 1001000`, `X`'s Pair balance
after `tx1`; `reserve1 = 10^6 − 996`, WETH9's Pair balance after `tx2`), at timestamp `1`, and the
lock is open again. -/
theorem tx2_settled_reserves (st : Jaune.State) :
    reserve0Read (((tx2SettledState st).getStor pair).get 8) = 1001000 ∧
      reserve1Read (((tx2SettledState st).getStor pair).get 8) = 999004 ∧
      reserveTimestampRead (((tx2SettledState st).getStor pair).get 8) = 1 ∧
      ((tx2SettledState st).getStor pair).get 12 = 1 := by
  rw [tx2_settled_pairStor, Stor.get_set_ne _ (by decide), Stor.get_set_self, Stor.get_set_self]
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, rfl⟩

end Blanc.Composition.UniswapV2PairWeth9Instance
