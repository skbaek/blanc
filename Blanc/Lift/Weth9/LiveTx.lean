import Blanc.Lift.Weth9.LiveHistory
import Blanc.TransactionForward

/-!
# WETH9 `withdraw` as a transaction

A type-2 transaction from an externally owned account `E` to the deployed WETH9 with `withdraw(wad)`
calldata is processed by Jaune's `processTransaction` -- with the signature recovery
(`recoverSender … = .ok E`) as the only cryptographic premise -- whenever the WETH9 footprint invariant
holds at the block's state, `E`'s tracked balance covers `wad`, and the transaction's gas covers its
intrinsic cost and the frame's.
-/

namespace Blanc.Lift.Weth9

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The calldata of `withdraw(wad)`: the four selector bytes and the amount word. -/
def withdrawCalldata (wad : B256) : Bytes := abiSelectorBytes wdSel ++ wad.toBytes

theorem abiSelectorBytes_wdSel : Bytes.toB256 (abiSelectorBytes wdSel) = wdSel := by
  rw [wdSel_eq]; decide

theorem withdrawCalldata_length (wad : B256) : (withdrawCalldata wad).length = 36 := by
  unfold withdrawCalldata
  simp [abiSelectorBytes, B256.length_toBytes]

theorem selector_withdrawCalldata {sevm : Sevm} {wad : B256}
    (h : sevm.data = withdrawCalldata wad) : Sevm.selector sevm = wdSel :=
  selector_eq_of_data_eq_abiSelectorBytes_append abiSelectorBytes_wdSel h

theorem dataWord_withdrawCalldata {sevm : Sevm} {wad : B256}
    (h : sevm.data = withdrawCalldata wad) : Sevm.dataWord sevm 4 = wad := by
  unfold Sevm.dataWord
  rw [h]
  have hl : (abiSelectorBytes wdSel).length = 4 := by simp [abiSelectorBytes, B256.length_toBytes]
  have h4 : (4 : B256).toNat = 4 := by decide
  have hw : wad.toBytes.length = 32 := B256.length_toBytes wad
  rw [h4]
  unfold withdrawCalldata List.sliceD
  rw [List.drop_left' hl, List.takeD_eq_take _ (by omega), List.take_of_length_le (by omega),
    B256.toB256_toBytes]

/-! ## What the frame costs, at a transaction's entry

At a transaction's entry the balance slot is cold, the caller (the origin) is warm and not an empty
account, and the slot's original value is its current one: `withdraw(wad)` for `0 < wad ≤ balance` then
costs `2040 + 2100 + 100 + 2900 + 6800 = 13940`. -/

/-- A selected `SLOAD` leaves its key warm. -/
theorem mem_afterSload_accessedStorageKeys (sevm : Sevm) (b : Devm) (key : B256) :
    (⟨sevm.currentTarget, key⟩ : Adr × B256) ∈ (afterSload sevm b key).accessedStorageKeys := by
  rw [afterSload_accessedStorageKeys]
  unfold sloadAccessedStorageKeys
  split
  · assumption
  · simp

/-- The frame's cost at a transaction's entry: the cold `SLOAD` (2100), the warm one (100), the
`SSTORE` of a changed nonzero original (2900), the ether send to the warm, non-empty caller (6800),
and the fixed 2040. -/
theorem withdrawGas_eq {sevm : Sevm} {pre : Devm} {b wad : B256} {E ca : Adr}
    (hcaller : sevm.caller = E) (hct : sevm.currentTarget = ca)
    (hcold : (⟨ca, balSlot E⟩ : Adr × B256) ∉ pre.accessedStorageKeys)
    (hwarm : E ∈ pre.accessedAddresses) (hne : ¬ (pre.getAcct E).Empty)
    (hb : pre.getStorVal ca (balSlot E) = b) (horig : getOrigStorVal sevm ca (balSlot E) = b)
    (hdw : Sevm.dataWord sevm 4 = wad) (hwad : wad ≠ 0) (hle : wad ≤ b) :
    withdrawGas sevm pre = 13940 := by
  subst hcaller hct hdw
  have hb0 : b ≠ 0 := by
    intro h0
    subst h0
    exact hwad (le_antisymm hle (B256.zero_le _))
  have hlt : b - Sevm.dataWord sevm 4 ≠ b := by
    intro h
    apply hwad
    have h1 := B256.toNat_sub_eq_of_le _ _ hle
    have h2 := congrArg B256.toNat h
    rw [h1] at h2
    have h3 := B256.toNat_le_toNat hle
    apply B256.toNat_inj
    show (Sevm.dataWord sevm 4).toNat = 0
    omega
  have hk1 : (⟨sevm.currentTarget, balSlot sevm.caller⟩ : Adr × B256) ∈
      (wB1 sevm pre).accessedStorageKeys := by
    exact mem_afterSload_accessedStorageKeys sevm pre _
  have hk2 : (⟨sevm.currentTarget, balSlot sevm.caller⟩ : Adr × B256) ∈
      (wB2 sevm pre).accessedStorageKeys := by
    exact mem_afterSload_accessedStorageKeys sevm (wB1 sevm pre) _
  have e1 : sloadCost sevm pre (balSlot sevm.caller) = 2100 := by
    unfold sloadCost; simp only [hcold, ↓reduceIte]; rfl
  have e2 : sloadCost sevm (wB1 sevm pre) (balSlot sevm.caller) = 100 := by
    unfold sloadCost; simp only [hk1, ↓reduceIte]; rfl
  have hcur : (wB2 sevm pre).getStorVal sevm.currentTarget (balSlot sevm.caller) = b := by
    rw [← hb]; simp [wB2, wB1, getStorVal_afterSload]
  have e3 : sstoreCost sevm (wB2 sevm pre) (balSlot sevm.caller)
      (wV sevm pre (Sevm.dataWord sevm 4)) = 2900 := by
    unfold sstoreCost
    simp only [hk2, ↓reduceIte, horig, hcur]
    have hv : wV sevm pre (Sevm.dataWord sevm 4) = b - Sevm.dataWord sevm 4 := by
      unfold wV
      simp [wB1, getStorVal_afterSload, hb]
    rw [hv]
    unfold sstoreValueCost
    have hne' : b ≠ b - Sevm.dataWord sevm 4 := fun h => hlt h.symm
    simp [hne', hb0, gasStorageUpdate, gasColdSload]
  have e4 : callNet pre sevm.caller = 6800 := by
    unfold callNet accessCost
    simp only [hwarm, hne, not_false_eq_true, ↓reduceIte]
    rfl
  unfold withdrawGas
  omega

/-! ## The frame at a transaction's entry -/

/-- The debit's `SSTORE` changes the storage of the contract and nothing else of any account. -/
theorem wB3_getAcct (sevm : Sevm) (pre : Devm) (wad : B256) (a : Adr) :
    ∃ st, (wB3 sevm pre wad).getAcct a = { pre.getAcct a with stor := st } := by
  obtain ⟨st, h⟩ := afterSstore_getAcct (sevm := sevm) (b := wB2 sevm pre) (key := balSlot sevm.caller)
    (value := wV sevm pre wad) a
  exact ⟨st, by simpa only [wB3, wB2, wB1, afterSload_getAcct] using h⟩

/-- What the withdrawal moves: the caller's balance grows by `wad` and its nonce is kept, the
contract's balance falls by `wad`. -/
theorem WithdrawPost.acct {sevm : Sevm} {pre post : Devm} {wad : B256} (h : WithdrawPost sevm pre post wad)
    (hEca : sevm.caller ≠ sevm.currentTarget) :
    (post.state.get sevm.caller).bal = (pre.state.get sevm.caller).bal + wad ∧
      (post.state.get sevm.caller).nonce = (pre.state.get sevm.caller).nonce ∧
      (post.state.get sevm.currentTarget).bal = (pre.state.get sevm.currentTarget).bal - wad := by
  obtain ⟨stmid, hsub, hst⟩ := h.state
  obtain ⟨-, hmid⟩ := State.of_subBal hsub
  obtain ⟨sE, hE⟩ := wB3_getAcct sevm pre wad sevm.caller
  obtain ⟨sC, hC⟩ := wB3_getAcct sevm pre wad sevm.currentTarget
  have hE' : (wB3 sevm pre wad).state.get sevm.caller = { pre.state.get sevm.caller with stor := sE } := hE
  have hC' : (wB3 sevm pre wad).state.get sevm.currentTarget =
      { pre.state.get sevm.currentTarget with stor := sC } := hC
  have hmidE : stmid.get sevm.caller = (wB3 sevm pre wad).state.get sevm.caller := by
    rw [hmid, State.setBal_get_ne (Ne.symm hEca)]
  have hmidC : (stmid.get sevm.currentTarget).bal = (pre.state.get sevm.currentTarget).bal - wad := by
    rw [hmid, State.setBal_get_self]
    show (wB3 sevm pre wad).state.bal sevm.currentTarget - wad = _
    show ((wB3 sevm pre wad).state.get sevm.currentTarget).bal - wad = _
    rw [hC']
  refine ⟨?_, ?_, ?_⟩
  · rw [hst]
    show ((stmid.setBal sevm.caller (stmid.bal sevm.caller + wad)).get sevm.caller).bal = _
    rw [State.setBal_get_self]
    show (stmid.get sevm.caller).bal + wad = _
    rw [hmidE, hE']
  · rw [hst]
    show ((stmid.setBal sevm.caller (stmid.bal sevm.caller + wad)).get sevm.caller).nonce = _
    rw [State.setBal_get_self]
    show (stmid.get sevm.caller).nonce = _
    rw [hmidE, hE']
  · rw [hst]
    show ((stmid.setBal sevm.caller (stmid.bal sevm.caller + wad)).get sevm.currentTarget).bal = _
    rw [State.setBal_get_ne hEca]
    exact hmidC

/-- **The `withdraw(wad)` frame at a transaction's entry.**  The frame the message of a call
transaction from `E` to `ca` enters -- `withdraw(wad)` calldata, value `0`, not static, not the
outermost (depth `1024`), the deployed code, the origin an externally owned account that is warm and
non-empty and not a precompile, the balance slot cold and its original value the current one `b` with
`0 < wad ≤ b`, the contract holding the ether, and `13940 + G` gas with `811 ≤ G` -- runs to success,
ending at gas `G` with the debit's refund (`4800` when the balance is emptied), no accounts to delete,
the balance slot debited by `wad` and no other storage touched, and `wad` ether moved from the contract
to `E`. -/
theorem weth9_withdraw_entry {sevm : Sevm} {pre : Devm} {E ca : Adr} {b wad : B256} {G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcaller : sevm.caller = E) (hct : sevm.currentTarget = ca)
    (h_static : sevm.isStatic = false) (h_value : sevm.value = 0)
    (hdata : sevm.data = withdrawCalldata wad) (hwad : wad ≠ 0)
    (h_stack : pre.stack = []) (h_mem : pre.memory = Mem.empty) (h_depth : sevm.depth ≠ 0)
    (hb : pre.getStorVal ca (balSlot E) = b) (hle : wad ≤ b)
    (horig : getOrigStorVal sevm ca (balSlot E) = b)
    (h_eoa : (pre.getCode E).size = 0) (h_prec : sevm.benvStat.rules.isPrecomp E = false)
    (h_eth : ¬ (pre.getAcct ca).bal < wad)
    (hcold : (⟨ca, balSlot E⟩ : Adr × B256) ∉ pre.accessedStorageKeys)
    (hwarm : E ∈ pre.accessedAddresses) (hne : ¬ (pre.getAcct E).Empty)
    (hEca : E ≠ ca) (h_error : pre.error = none) (h_refund : pre.refundCounter = 0)
    (h_gas : pre.gasLeft = G + 13940) (hG : 811 ≤ G) :
    ∃ post, exec ⟨0, sevm, pre⟩ = .ok post ∧ post.error = none ∧ post.gasLeft = G ∧
      post.refundCounter = (if wad = b then 4800 else 0) ∧
      post.accountsToDelete.isEmpty = pre.accountsToDelete.isEmpty ∧
      post.state.getStor ca = (pre.state.getStor ca).set (balSlot E) (b - wad) ∧
      (∀ a, a ≠ ca → post.state.getStor a = pre.state.getStor a) ∧
      (post.state.get E).bal = (pre.state.get E).bal + wad ∧
      (post.state.get E).nonce = (pre.state.get E).nonce ∧
      (post.state.get ca).bal = (pre.state.get ca).bal - wad := by
  have hdw : Sevm.dataWord sevm 4 = wad := dataWord_withdrawCalldata hdata
  have hsel : Sevm.selector sevm = wdSel := selector_withdrawCalldata hdata
  have hlen : sevm.data.length = 36 := by rw [hdata]; exact withdrawCalldata_length wad
  subst hcaller hct
  have hgas : withdrawGas sevm pre = 13940 :=
    withdrawGas_eq rfl rfl hcold hwarm hne hb horig hdw hwad hle
  obtain ⟨post, hex, hg, hp, hs1, hs2⟩ := weth9_withdraw_live_post (G := G) hcode hfork h_static
    h_value hsel (by omega) (by omega) h_stack h_mem h_depth (by rw [hdw]; exact hwad)
    (by rw [hdw, hb]; exact hle) h_eoa h_prec (by rw [hdw]; exact h_eth)
    (by rw [h_gas, hgas]) hG
  rw [hdw] at hp
  have hb0 : b ≠ 0 := by
    intro h0
    subst h0
    exact hwad (le_antisymm hle (B256.zero_le _))
  have hlt : b - wad ≠ b := by
    intro h
    apply hwad
    have h1 := B256.toNat_sub_eq_of_le _ _ hle
    have h2 := congrArg B256.toNat h
    rw [h1] at h2
    have h3 := B256.toNat_le_toNat hle
    apply B256.toNat_inj
    show wad.toNat = 0
    omega
  have hv : wV sevm pre wad = b - wad := by
    unfold wV
    simp [wB1, getStorVal_afterSload, hb]
  refine ⟨post, hex, ?_, hg, ?_, hp.accountsToDelete, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp.error, h_error]
  · rw [hp.refund, h_refund, hv, horig]
    have hcur : pre.getStorVal sevm.currentTarget (balSlot sevm.caller) = b := hb
    have hne' : b ≠ b - wad := fun h => hlt h.symm
    have hz : b - wad = 0 ↔ wad = b := by
      have h1 := B256.toNat_sub_eq_of_le _ _ hle
      have h3 := B256.toNat_le_toNat hle
      constructor
      · intro h
        have h2 := congrArg B256.toNat h
        rw [h1] at h2
        apply B256.toNat_inj
        rw [B256.toNat_zero] at h2
        omega
      · intro h
        subst h
        apply B256.toNat_inj
        rw [h1, B256.toNat_zero]
        omega
    unfold sstoreNewRefundCounter
    simp only [hcur, CoveredFork.rules_storageClearRefund hfork, hne', ne_eq, not_false_eq_true,
      ↓reduceIte, hb0, and_false, hz]
    by_cases h : wad = b <;> simp [h]
  · have h1 := hs1
    rw [hdw, hb] at h1
    exact h1
  · intro a ha
    exact hs2 a ha
  · exact (hp.acct hEca).1
  · exact (hp.acct hEca).2.1
  · exact (hp.acct hEca).2.2

/-! ## The transaction -/

/-- The intrinsic gas of a `withdraw(wad)` transaction: the base cost and four gas per calldata token. -/
def withdrawIntrinsicGas (wad : B256) : Nat := 21000 + 4 * calldataTokens (withdrawCalldata wad)

/-- The refund the debit leaves: `4800` when the transaction empties the caller's balance. -/
def withdrawRefund (bal wad : B256) : Nat := if wad = bal then 4800 else 0

/-- **The gas a `withdraw(wad)` transaction uses** at a state where the caller's balance is `bal`
(`0 < wad ≤ bal`): the intrinsic gas plus the frame's `13940` (the cold balance `SLOAD` 2100, the warm
one 100, the `SSTORE` 2900, the ether send to the warm caller 6800, the dispatch and the rest 2040),
less the refund. -/
def withdrawGasUsed (bal wad : B256) : Nat :=
  withdrawIntrinsicGas wad + 13940 - withdrawRefund bal wad

theorem withdrawTx_intrinsic (wad : B256) {rules : ForkRules} {tx : Tx} {sender : Adr}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat} {t : Adr}
    (hsg : rules.stateGas = none) (htx : rules.gas.txBase = 21000) (hfl : rules.gas.floorTokenCost = 10)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some t) [])
    (hdata : tx.data = withdrawCalldata wad) :
    calculateIntrinsicCost rules tx sender =
      (withdrawIntrinsicGas wad, calldataTokens (withdrawCalldata wad) * 10 + 21000) := by
  rw [calculateIntrinsicCost_two_call hsg htype, hdata, htx, hfl]
  unfold withdrawIntrinsicGas standardCallDataTokenCost
  rw [Nat.mul_comm]

theorem code_size_ne_zero : code.size ≠ 0 := by decide +kernel

theorem getDelegatedCodeAddress_code : getDelegatedCodeAddress code = none := by
  unfold getDelegatedCodeAddress
  have h : ¬ isValidDelegation code := fun h => by
    have h1 := h.1
    change code.size = eoaDelegatedCodeLength at h1
    revert h1
    decide +kernel
  simp [h]

/-- **`withdraw(wad)` as a transaction: `processTransaction` succeeds.**  A type-2 transaction `tx` from
the externally owned account `E` (no code, nonce `tx.nonce`, funds for the maximum fee) to the deployed
WETH9 `ca`, with value `0` and `withdraw(wad)` calldata (`0 < wad`), no access list and honest fee
fields (`maxPriorityFee ≤ maxFee`, the block's base fee at most `maxFee`), is processed by Jaune's
`processTransaction` at a block whose state carries the footprint invariant `FootInv U` at `ca`, with
`E`'s balance slot a tracked holder covering `wad`, provided the signature recovers `E`
(`recoverSender … = .ok E`, the only cryptographic premise), the transaction's gas is at least its
intrinsic gas plus the frame's `13940` plus `811` (and within the EIP-7825 cap), and the block has room
for it.  The gas the receipt records is `withdrawGasUsed`; the world it returns has `E`'s WETH9 balance
slot debited by `wad`, no other storage touched, the nonce of `E` advanced, `wad` ether moved from `ca`
to `E` (the fee `tx.gas * effectiveGasPrice` taken from `E` and the unused part refunded), the coinbase
being neither. -/
theorem weth9_tx_withdraw
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E ca : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat} {U : Key → Prop}
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some ca) [])
    (hvalue : tx.value = 0) (hdata : tx.data = withdrawCalldata wad) (hwad : wad ≠ 0)
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : withdrawIntrinsicGas wad + 13940 + 811 ≤ tx.gas) (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hprecE : benv.stat.rules.isPrecomp E = false) (hprecCa : benv.stat.rules.isPrecomp ca = false)
    (hcode : benv.state.getCode ca = code)
    (hinv : FootInv U (benv.state.getStor ca) (benv.state.bal ca)) (hholder : U (.bal E))
    (hbal : wad ≤ (benv.state.getStor ca).get (balSlot E))
    (hcbE : benv.stat.coinbase ≠ E) (hcbCa : benv.stat.coinbase ≠ ca) :
    ∃ (st : Jaune.State) (bout' : BlockOutput), processTransaction benv bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad ∧
      st.getStor ca = (benv.state.getStor ca).set (balSlot E)
        ((benv.state.getStor ca).get (balSlot E) - wad) ∧
      (∀ a, a ≠ ca → st.getStor a = benv.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get E).bal = benv.state.bal E -
          (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 + wad +
        ((tx.gas - withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
            benv.stat.baseFeePerGas)).toB256 ∧
      (st.get ca).bal = benv.state.bal ca - wad ∧
      ((benv.state.bal E).toNat + wad.toNat < 2 ^ 256 →
        (st.get E).bal.toNat + withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) =
          (benv.state.bal E).toNat + wad.toNat) := by
  have hsg : benv.stat.rules.stateGas = none := CoveredFork.rules_stateGas_none hfork
  have hEca : E ≠ ca := by
    intro h
    subst h
    rw [hcode] at hnocode
    exact code_size_ne_zero hnocode
  have htk : calldataTokens (withdrawCalldata wad) ≤ 144 := by
    have := calldataTokens_le (withdrawCalldata wad)
    rw [withdrawCalldata_length] at this
    omega
  have hcost := withdrawTx_intrinsic wad (tx := tx) (sender := E) hsg
    (CoveredFork.rules_txBase (s := benv.stat) hfork)
    (CoveredFork.rules_floorTokenCost (s := benv.stat) hfork) htype hdata
  have hmaxgas : max (withdrawIntrinsicGas wad) (calldataTokens (withdrawCalldata wad) * 10 + 21000) ≤
      tx.gas := by
    have hi : withdrawIntrinsicGas wad = 21000 + 4 * calldataTokens (withdrawCalldata wad) := rfl
    omega
  have hnodeleg : getDelegatedCodeAddress (benv.state.getCode ca) = none := by
    rw [hcode]; exact getDelegatedCodeAddress_code
  have hexec : ∀ (debit : Jaune.State) (msg : Msg) (after : Benv),
      (benv.state.incrNonce E).subBal E
        (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
          benv.stat.baseFeePerGas)).toB256 = some debit →
      prepareMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction tx index E
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
          (withdrawIntrinsicGas wad) []) tx = .ok msg →
      msg.benvAfterTransfer = .ok after →
      ∃ post, exec (initEvm (msg.withBenv after)) = .ok post ∧ post.error = none ∧
        0 ≤ post.refundCounter ∧
        (post.gasLeft + withdrawIntrinsicGas wad + 13940 = tx.gas ∧
          post.refundCounter = (if wad = (benv.state.getStor ca).get (balSlot E) then 4800 else 0) ∧
          post.accountsToDelete.isEmpty = true ∧
          post.state.getStor ca = (benv.state.getStor ca).set (balSlot E)
            ((benv.state.getStor ca).get (balSlot E) - wad) ∧
          (∀ a, a ≠ ca → post.state.getStor a = benv.state.getStor a) ∧
          (post.state.get E).bal = benv.state.bal E -
            (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
              benv.stat.baseFeePerGas)).toB256 + wad ∧
          (post.state.get E).nonce = tx.nonce + 1 ∧
          (post.state.get ca).bal = benv.state.bal ca - wad) := by
    intro debit msg after hdebit hprep hentry
    set v : B256 := (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
      benv.stat.baseFeePerGas)).toB256 with hv
    rw [prepareMessage_call (by rw [htype]; rfl)] at hprep
    have hm : callMessage { benv.beginTransaction with state := debit }
        (transactionTenv benv.beginTransaction tx index E
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)
          (withdrawIntrinsicGas wad) []) tx ca = msg := Except.ok.inj hprep
    obtain ⟨-, hdeb⟩ := State.of_subBal hdebit
    have hd_ne : ∀ a, E ≠ a → debit.get a = benv.state.get a := fun a h => by
      rw [hdeb]; exact debit_get_ne h
    have hd_E : debit.get E = { benv.state.get E with
        nonce := (benv.state.get E).nonce + 1, bal := benv.state.bal E - v } := by
      rw [hdeb, debit_get_self, State.incrNonce_bal]
    have hm_caller : msg.caller = E := by rw [← hm]; rfl
    have hm_ct : msg.currentTarget = ca := by rw [← hm]; rfl
    have hm_value : msg.value = 0 := by rw [← hm]; show tx.value.toB256 = 0; rw [hvalue]; rfl
    have hm_data : msg.data = tx.data := by rw [← hm]; rfl
    have hm_static : msg.isStatic = false := by rw [← hm]; rfl
    have hm_depth : msg.depth = 1024 := by rw [← hm]; rfl
    have hm_code : msg.code = debit.getCode ca := by rw [← hm]; rfl
    have hm_gas : msg.gas = tx.gas - withdrawIntrinsicGas wad := by rw [← hm]; rfl
    have hm_state : msg.benv.state = debit := by rw [← hm]; rfl
    have hm_keys : (⟨ca, balSlot E⟩ : Adr × B256) ∉ msg.accessedStorageKeys := by
      rw [← hm]
      simp [callMessage, transactionTenv, Tx.accessList, htype, TxType.accessList]
    have hm_addrs : E ∈ msg.accessedAddresses := by
      rw [← hm]
      simp [callMessage, transactionTenv, Std.HashSet.mem_insertMany_list]
    have hafter : ∀ a, after.state.get a = debit.get a := fun a => by
      have := benvAfterTransfer_get_of_value_zero hm_value hentry a
      rw [this, hm_state]
    have hstat : after.stat = benv.beginTransaction.stat := by
      rw [benvAfterTransfer_stat hentry, ← hm]; rfl
    have hpre_stor : ∀ a, after.state.getStor a = benv.state.getStor a := fun a => by
      show (after.state.get a).stor = (benv.state.get a).stor
      rw [hafter]
      by_cases h : E = a
      · subst h; rw [hd_E]
      · rw [hd_ne a h]
    have hpre_ca : after.state.get ca = benv.state.get ca := by
      rw [hafter, hd_ne ca hEca]
    have hpre_E : after.state.get E = { benv.state.get E with
        nonce := (benv.state.get E).nonce + 1, bal := benv.state.bal E - v } := by
      rw [hafter, hd_E]
    obtain ⟨post, hex, herr, hgl, hrf, hatd, hst, hso, hbE, hnE, hbC⟩ := weth9_withdraw_entry
      (sevm := initSevm (msg.withBenv after)) (pre := initDevm (msg.withBenv after))
      (E := E) (ca := ca) (b := (benv.state.getStor ca).get (balSlot E)) (wad := wad)
      (G := tx.gas - withdrawIntrinsicGas wad - 13940)
      (by show msg.code = code; rw [hm_code, State.getCode, hd_ne ca hEca]; exact hcode)
      (by show CoveredFork after.stat.fork; rw [hstat]; exact hfork)
      hm_caller hm_ct hm_static hm_value (by show msg.data = _; rw [hm_data]; exact hdata) hwad
      rfl rfl (by show msg.depth ≠ 0; rw [hm_depth]; decide)
      (by show (after.state.get ca).stor.get _ = _; rw [hpre_ca]; rfl) hbal
      (by show ((after.stat.origState.get ca).stor).get _ = _; rw [hstat]; rfl)
      (by show ((after.state.get E).code).size = 0; rw [hpre_E]; exact hnocode)
      (by show after.stat.rules.isPrecomp E = false; rw [hstat]; exact hprecE)
      (by
        show ¬ (after.state.get ca).bal < wad
        rw [hpre_ca]
        intro hlt
        have h1 := B256.toNat_lt_toNat hlt
        have h2 := B256.toNat_le_toNat hbal
        have h3 := hinv.balance_le hholder
        change (benv.state.get ca).bal.toNat < wad.toNat at h1
        change ((benv.state.getStor ca).get (balSlot E)).toNat ≤ (benv.state.get ca).bal.toNat at h3
        omega)
      hm_keys hm_addrs
      (by
        show ¬ (after.state.get E).Empty
        rw [hpre_E]
        rintro ⟨-, h0, -⟩
        exact UInt64.add_one_ne_zero (by rw [hnonce]; exact hnonceMax) h0)
      hEca rfl rfl
      (by show msg.gas = _; rw [hm_gas]; omega)
      (by omega)
    have hE' : (initDevm (msg.withBenv after)).state.get E = after.state.get E := rfl
    have hC' : (initDevm (msg.withBenv after)).state.get ca = after.state.get ca := rfl
    refine ⟨post, hex, herr, ?_, by omega, hrf, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hrf]; split_ifs <;> decide
    · rw [hatd]; rfl
    · have h1 := hst
      rw [show (initDevm (msg.withBenv after)).state.getStor ca = benv.state.getStor ca from
        hpre_stor ca] at h1
      exact h1
    · intro a ha
      exact (hso a ha).trans (hpre_stor a)
    · rw [hbE, hE', hpre_E]
    · rw [hnE, hE', hpre_E]
      show (benv.state.get E).nonce + 1 = tx.nonce + 1
      rw [hnonce]
    · rw [hbC, hC', hpre_ca]
      rfl
  obtain ⟨debit, post, bout', hQ, hproc, hcum, hblk⟩ := processTransaction_call_of_exec
    (E := E) (t := ca) (Q := fun _ post => post.gasLeft + withdrawIntrinsicGas wad + 13940 = tx.gas ∧
          post.refundCounter = (if wad = (benv.state.getStor ca).get (balSlot E) then 4800 else 0) ∧
          post.accountsToDelete.isEmpty = true ∧
          post.state.getStor ca = (benv.state.getStor ca).set (balSlot E)
            ((benv.state.getStor ca).get (balSlot E) - wad) ∧
          (∀ a, a ≠ ca → post.state.getStor a = benv.state.getStor a) ∧
          (post.state.get E).bal = benv.state.bal E -
            (tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
              benv.stat.baseFeePerGas)).toB256 + wad ∧
          (post.state.get E).nonce = tx.nonce + 1 ∧
          (post.state.get ca).bal = benv.state.bal ca - wad)
    hfork htype hvalue hchain hprio hbase hcost hmaxgas (CoveredFork.checkTransactionGasCap_ok (s := benv.stat) hfork hcap)
    hnonceMax hroom hrecover hnonce (by
      have h0 : (benv.state.get E).code.size = 0 := hnocode
      simp [ByteArray.isEmpty, h0]) hfunds hnodeleg hprecCa hexec
  obtain ⟨hgl, hrf, hatd, hstCa, hstOther, hbalE, hnonceE, hbalCa⟩ := hQ
  have hdel : post.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    exact hatd
  have hrfn : post.refundCounter.toNat = withdrawRefund ((benv.state.getStor ca).get (balSlot E)) wad := by
    rw [hrf]
    unfold withdrawRefund
    split_ifs <;> rfl
  have hU : txGasUsed tx.gas (calldataTokens (withdrawCalldata wad) * 10 + 21000) post.gasLeft
      post.refundCounter.toNat = withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad := by
    unfold txGasUsed withdrawGasUsed
    rw [hrfn]
    have hi : withdrawIntrinsicGas wad = 21000 + 4 * calldataTokens (withdrawCalldata wad) := rfl
    unfold withdrawRefund
    split_ifs <;> omega
  rw [hU, hdel] at hproc
  rw [hU] at hcum hblk
  refine ⟨((post.state.addBal E ((tx.gas - withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas)).toB256).addBal
        benv.stat.coinbase (withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas))).toB256), bout', hproc, hcum, hblk,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [getStor_addBal, getStor_addBal]
    exact hstCa
  · intro a ha
    rw [getStor_addBal, getStor_addBal]
    exact hstOther a ha
  · rw [addBal_get_ne _ hcbE, addBal_get_self]
    exact hnonceE
  · rw [addBal_get_ne _ hcbE, addBal_get_self]
    show (post.state.get E).bal + _ = _
    rw [hbalE]
  · rw [addBal_get_ne _ hcbCa, addBal_get_ne _ hEca]
    exact hbalCa
  · intro hnof
    rw [addBal_get_ne _ hcbE, addBal_get_self]
    show ((post.state.get E).bal + _).toNat + _ = _
    rw [hbalE]
    have hused : withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad ≤ tx.gas := by
      have hu : withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad ≤
          withdrawIntrinsicGas wad + 13940 := by unfold withdrawGasUsed; omega
      omega
    have heff : min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas ≤
        maxFee := by omega
    have hF : tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas) ≤ (benv.state.bal E).toNat :=
      le_trans (Nat.mul_le_mul_left _ heff) hfunds
    rw [sender_net_toNat hF (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) hnof]
    have hsplit : tx.gas * (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas) =
        (tx.gas - withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad) *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) +
        withdrawGasUsed ((benv.state.getStor ca).get (balSlot E)) wad *
          (min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) + benv.stat.baseFeePerGas) := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hused]
    omega

/-- **After any configured history, a holder's `withdraw(wad)` transaction is processed.**  The
transaction of `weth9_tx_withdraw` at the block whose state is the future state of a configured
history (`trace`) from a checkpoint holding the deployed WETH9 (`installed`, `sumNof`, `initial`,
`fresh`: the premises of `weth9_history_withdraw_live`): the holder `E` is one of the history's tracked
keys, its recorded balance covers `wad`, and everything else is the transaction's own.  The world the
transaction returns has the holder's balance slot debited by `wad`, no other storage touched, and the
holder paid `wad` ether. -/
theorem weth9_history_tx_withdraw
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {K₀ : Key → Prop}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode ca).toList = weth9Sem.image)
    (sumNof : SumNof checkpoint.state.bal)
    (initial : FootInv K₀ (checkpoint.state.getStor ca) (checkpoint.state.bal ca))
    (fresh : KeysFresh K₀ (historyTouchedKeys ca trace))
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E : Adr} {wad : B256}
    {chainId : UInt64} {maxPriorityFee maxFee : Nat}
    (hstate : benv.state = future.state)
    (hfork : CoveredFork benv.stat.fork)
    (htype : tx.type = .two chainId maxPriorityFee maxFee (some ca) [])
    (hvalue : tx.value = 0) (hdata : tx.data = withdrawCalldata wad) (hwad : wad ≠ 0)
    (hchain : chainId = benv.stat.chainId)
    (hprio : maxPriorityFee ≤ maxFee) (hbase : benv.stat.baseFeePerGas ≤ maxFee)
    (hgas : withdrawIntrinsicGas wad + 13940 + 811 ≤ tx.gas) (hcap : tx.gas ≤ 16777216)
    (hroom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hrecover : recoverSender benv.stat.chainId tx = .ok E)
    (hnonce : (benv.state.get E).nonce = tx.nonce) (hnonceMax : tx.nonce ≠ UInt64.max)
    (hnocode : (benv.state.getCode E).size = 0)
    (hfunds : tx.gas * maxFee ≤ (benv.state.get E).bal.toNat)
    (hprecE : benv.stat.rules.isPrecomp E = false) (hprecCa : benv.stat.rules.isPrecomp ca = false)
    (hholder : historyKeyUniverse ca trace K₀ (.bal E))
    (hbal : wad ≤ (future.state.getStor ca).get (balSlot E))
    (hcbE : benv.stat.coinbase ≠ E) (hcbCa : benv.stat.coinbase ≠ ca) :
    ∃ (st : Jaune.State) (bout' : BlockOutput), processTransaction benv bout tx index = .ok (st, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed +
        withdrawGasUsed ((future.state.getStor ca).get (balSlot E)) wad ∧
      bout'.blockGasUsed = bout.blockGasUsed +
        withdrawGasUsed ((future.state.getStor ca).get (balSlot E)) wad ∧
      st.getStor ca = (future.state.getStor ca).set (balSlot E)
        ((future.state.getStor ca).get (balSlot E) - wad) ∧
      (∀ a, a ≠ ca → st.getStor a = future.state.getStor a) ∧
      (st.get E).nonce = tx.nonce + 1 ∧
      (st.get ca).bal = future.state.bal ca - wad := by
  obtain ⟨hc, -, hfoot⟩ := weth9_history_footprint_universe trace installed sumNof initial fresh
  have hcode : benv.state.getCode ca = code := by
    rw [hstate]
    exact code_eq_of_toList (Option.some.inj hc)
  have hbal' : wad ≤ (benv.state.getStor ca).get (balSlot E) := by rw [hstate]; exact hbal
  have hinv : FootInv (historyKeyUniverse ca trace K₀) (benv.state.getStor ca) (benv.state.bal ca) := by
    rw [hstate]; exact hfoot
  obtain ⟨st, bout', hproc, hcum, hblk, hst, hoth, hnE, -, hbC, -⟩ := weth9_tx_withdraw hfork htype
    hvalue hdata hwad hchain hprio hbase hgas hcap hroom hrecover hnonce hnonceMax hnocode hfunds
    hprecE hprecCa hcode hinv hholder hbal' hcbE hcbCa
  rw [hstate] at hcum hblk hst hoth hbC
  exact ⟨st, bout', hproc, hcum, hblk, hst, hoth, hnE, hbC⟩

end Blanc.Lift.Weth9
