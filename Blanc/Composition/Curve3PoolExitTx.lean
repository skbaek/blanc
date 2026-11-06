import Blanc.Composition.Curve3PoolPublicGas

/-!
# A direct call to the pool as a transaction

`tx_of_frame`: `TxForm`, `SignerReady` and `GasRoom` make `processTransaction` run the message, and a message that
commits having spent exactly `F`, with refund `r`, uses `afterRefund (callIntrinsic data + F) r`. The refund's cap is
Jaune's; the calldata floor never binds, on `132` bytes of calldata and a frame of at least `50000`.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The gas used, from what the transaction's message left. -/
theorem txGasUsed_afterRefund {gas floor spent left r : Nat} (hle : spent ≤ gas) (hleft : left = gas - spent)
    (hfloor : floor ≤ spent - spent / 5) : txGasUsed gas floor left r = afterRefund spent r := by
  subst hleft
  unfold txGasUsed afterRefund
  have e : gas - (gas - spent) = spent := by omega
  rw [e]
  have : min (spent / 5) r ≤ spent / 5 := Nat.min_le_left _ _
  omega

/-- The message's gas, its caller, its calldata and its code. -/
theorem tx_message {benv : Benv} {tx : Tx} {index : Nat} {E : Adr} {price intrinsic : Nat} {debit : State} {msg : Msg}
    {after : Benv} (hrec : tx.type.receiver? = some pool) (hv : tx.value = 0)
    (hprepare : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index E price intrinsic []) tx = .ok msg)
    (hentry : msg.benvAfterTransfer = .ok after) :
    msg = callMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index E price intrinsic []) tx pool ∧
    after = msg.benv := by
  rw [prepareMessage_call hrec] at hprepare
  have hm := (Except.ok.inj hprepare).symm
  subst hm
  refine ⟨rfl, ?_⟩
  rw [Msg.benvAfterTransfer_of_value_zero (by simp only [callMessage, hv]; rfl)] at hentry
  exact (Except.ok.inj hentry).symm

/-- What a direct call's message starts warm. -/
theorem tx_addr_mem {benv : Benv} {tx : Tx} {index : Nat} {E : Adr} {price intrinsic : Nat} {debit : State}
    {chainId : UInt64} {prio maxFee : Nat} {x : Adr} (htype : tx.type = .two chainId prio maxFee (some pool) [])
    (h : x ∈ (callMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index E price intrinsic []) tx pool).accessedAddresses) :
    x = benv.stat.coinbase ∨ x ∈ benv.stat.rules.precompiles ∨ x = E ∨ x = pool := by
  have hl : tx.accessList = [] := by simp only [Tx.accessList, TxType.accessList, htype]
  have h' := Std.HashSet.mem_insertMany_list.1 h
  rcases h' with h1 | h1
  · left
    have h2 : x ∈ (if benv.stat.rules.txr.warmCoinbase = true then Std.HashSet.ofList [benv.stat.coinbase]
        else (Std.HashSet.ofList [] : AdrSet)) := by
      have this := h1
      simp only [callMessage, transactionTenv, Benv.beginTransaction, hl, List.map_nil] at this
      exact this
    split at h2
    · exact List.mem_singleton.1 (List.contains_iff_mem.1 (Std.HashSet.mem_ofList.1 h2))
    · exact absurd (List.contains_iff_mem.1 (Std.HashSet.mem_ofList.1 h2)) List.not_mem_nil
  · right
    have h2 : x ∈ benv.stat.rules.precompiles ++ [E, pool] := by
      have := List.contains_iff_mem.1 h1
      exact this
    simpa only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] using h2

/-- A precompile starts warm in a direct call's message. -/
theorem tx_addr_precomp {benv : Benv} {tx : Tx} {index : Nat} {E : Adr} {price intrinsic : Nat} {debit : State}
    {x : Adr} (hx : x ∈ benv.stat.rules.precompiles) :
    x ∈ (callMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index E price intrinsic []) tx pool).accessedAddresses :=
  Std.HashSet.mem_insertMany_list.2 (.inr (List.contains_iff_mem.2 (List.mem_append_left _ hx)))

/-- **A direct call to the pool, from the outcome of its message.** -/
theorem tx_of_frame {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E : Adr} {prio maxFee F r : Nat}
    {Q : State → Devm → Prop} (hfork : CoveredFork benv.stat.fork) (form : TxForm benv tx prio maxFee)
    (ready : SignerReady benv tx E maxFee) (room : GasRoom benv bout tx (callIntrinsic tx.data + F + callRoom))
    (hlen : tx.data.length = 132) (hF : 50000 ≤ F)
    (hnodeleg : getDelegatedCodeAddress (benv.state.getCode pool) = none)
    (hprec : benv.stat.rules.isPrecomp pool = false)
    (hrun : ∀ (debit : State) (msg : Msg) (after : Benv),
      (benv.state.incrNonce E).subBal E (tx.gas * (min prio (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256 = some debit →
      prepareMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction tx index E
          (min prio (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
          (callIntrinsic tx.data) []) tx = .ok msg →
      msg.benvAfterTransfer = .ok after →
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none ∧
        post.gasLeft = tx.gas - (callIntrinsic tx.data + F) ∧ post.refundCounter = (r : Int) ∧ Q debit post) :
    ∃ (debit : State) (post : Devm) (bout' : BlockOutput), Q debit post ∧
      processTransaction benv bout tx index = .ok
        (post.accountsToDelete.toList.foldl destroyAccount
          ((post.state.addBal E
              ((tx.gas - afterRefund (callIntrinsic tx.data + F) r) *
                (min prio (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256).addBal
            benv.stat.coinbase
              (afterRefund (callIntrinsic tx.data + F) r * (min prio (maxFee - benv.stat.baseFeePerGas))).toB256),
          bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + afterRefund (callIntrinsic tx.data + F) r := by
  have htk : calldataTokens tx.data ≤ 528 := by
    have := calldataTokens_le tx.data
    omega
  have hneed := room.enough
  have hR : callRoom = 2201 := rfl
  have hI : callIntrinsic tx.data = 21000 + 4 * calldataTokens tx.data := rfl
  have hcost : calculateIntrinsicCost benv.stat.rules tx E =
      (callIntrinsic tx.data, calldataTokens tx.data * 10 + 21000) := by
    rw [calculateIntrinsicCost_two_call (CoveredFork.rules_stateGas_none hfork) form.type
      (CoveredFork.rules_dataNonZero hfork) (CoveredFork.rules_calldataFloor hfork),
      CoveredFork.rules_txBase hfork, CoveredFork.rules_floorTokenCost hfork, hI]
    simp only [standardCallDataTokenCost, Nat.mul_comm]
  obtain ⟨debit, post, bout', hq, process, cum, -, -, -⟩ :=
    processTransaction_call_value_of_exec_receipts (Q := fun d p =>
        p.gasLeft = tx.gas - (callIntrinsic tx.data + F) ∧ p.refundCounter = (r : Int) ∧ Q d p)
      (bout := bout) (tx := tx) (E := E) (t := pool) (chainId := benv.stat.chainId) (maxPriorityFee := prio)
      (maxFee := maxFee) (intrinsicGas := callIntrinsic tx.data)
      (calldataFloorGas := calldataTokens tx.data * 10 + 21000) (index := index)
      hfork form.type rfl form.tip form.base hcost (by omega)
      (CoveredFork.checkTransactionGasCap_ok hfork room.cap) ready.nonce.2 room.block ready.signed ready.nonce.1
      (by
        change (benv.state.getCode E).isEmpty = true
        simp only [ByteArray.isEmpty, ready.noCode]; rfl)
      (by rw [form.value]; exact ready.funds)
      hnodeleg hprec
      (fun debit msg after hd hp he => by
        obtain ⟨post, hx, herr, hg, hrf, hq⟩ := hrun debit msg after hd hp he
        exact ⟨post, hx, herr, by rw [hrf]; exact Int.natCast_nonneg r, hg, hrf, hq⟩)
  obtain ⟨hg, hrf, hq⟩ := hq
  have hU : txGasUsed tx.gas (calldataTokens tx.data * 10 + 21000) post.gasLeft post.refundCounter.toNat =
      afterRefund (callIntrinsic tx.data + F) r := by
    rw [hrf, Int.toNat_natCast]
    exact txGasUsed_afterRefund (by omega) hg (by omega)
  rw [hU] at process cum
  exact ⟨debit, post, bout', hq, process, cum⟩

end Blanc.Composition.Curve3PoolPublic
