import Blanc.Lift.BuilderRequest.Revert
import Blanc.Lift.TransactionAmsterdam

/-!
# Direct transactions to the builder contracts under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`Submissions.transaction_ok` takes a valid type-2 transaction to the contract, ordinary gas (empty reservoir), from an
account with no code, through `processTransaction`: admission, gas allocation, the message, settlement, post state,
receipt logs and gas used. `Submissions.transaction_reverts` is the same for a transaction whose frame reverts. Validity
comes from `DirectTx`, which states what the transaction takes from its block and sender. Nothing here proves a block
valid. Direct calls only: no nested frames, no authorizations, no history.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune ExecutionTrace

theorem txDebit_get_ne {σ : State} {E t : Adr} {fee : Nat} (hne : E ≠ t) : (txDebit σ E fee).get t = σ.get t := by
  rw [txDebit, State.setBal, State.setAccount_get_ne _ hne, State.incrNonce, State.setAccount_get_ne _ hne]

theorem setBal_bal_self (σ : State) (a : Adr) (v : B256) : (σ.setBal a v).bal a = v := by
  rw [State.bal, State.setBal, State.setAccount, State.get_set_self, Acct.clearIfEmpty]
  split
  · rename_i h
    have hb : ((σ.get a).withBal v).bal = 0 := h.2.2
    have hv : v = 0 := hb
    rw [hv]
    rfl
  · rfl

namespace Submissions

variable (c : Submissions) {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr} {chainId : UInt64}
  {prio maxFee i f : Nat}

/-- The price a direct transaction pays. -/
local notation "P" => twoPrice benv.stat.baseFeePerGas prio maxFee

/-- The message a direct transaction prepares. -/
local notation "TM" => txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i

/-- A code-bearing target is not the sender. -/
theorem sender_ne (d : DirectTx benv bout tx E t chainId prio maxFee i f) (installed : benv.state.getCode t = c.code) :
    E ≠ t := by
  intro h
  subst h
  have hc : (benv.state.get E).code = c.code := installed
  have hn := d.noCode
  rw [hc, c.nonempty] at hn
  cases hn

/-- The value moves: debit, then credit, over the debited state. -/
theorem entry_exists (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (value : tx.value.toB256 ≠ 0) :
    ∃ entry : Benv, (TM).benvAfterTransfer = .ok entry ∧
      entry.state = (((TM).benv.state.setBal E ((TM).benv.state.bal E - tx.value.toB256))).addBal t tx.value.toB256 := by
  have hbal : (benv.state.bal E).toNat < 2 ^ 256 := B256.toNat_lt _
  have hbalEq : (benv.state.bal E).toNat = (benv.state.get E).bal.toNat := rfl
  have hfunds := d.funds
  have hprice : twoPrice benv.stat.baseFeePerGas prio maxFee ≤ maxFee := by
    have := d.baseLe
    have := d.prioLe
    simp only [twoPrice]
    omega
  have hmul : tx.gas * twoPrice benv.stat.baseFeePerGas prio maxFee ≤ tx.gas * maxFee := Nat.mul_le_mul_left _ hprice
  have hdebit : (txDebit benv.state E (tx.gas * P)).bal E = benv.state.bal E - (tx.gas * P).toB256 :=
    setBal_bal_self _ _ _
  have hfeeNat : ((tx.gas * P).toB256).toNat = tx.gas * P := B256.toNat_toB256_of_lt (by omega)
  have hvalNat : (tx.value.toB256).toNat = tx.value := B256.toNat_toB256_of_lt (by omega)
  have hsub : (benv.state.bal E - (tx.gas * P).toB256).toNat =
      (benv.state.get E).bal.toNat - tx.gas * P := by
    rw [B256.toNat_sub, Nat.lo, hfeeNat, Nat.add_sub_mod_eq_sub hbal (by omega)]
    rfl
  have hafford : ¬ (TM).benv.state.bal (TM).caller < (TM).value := by
    show ¬ (txDebit benv.state E (tx.gas * P)).bal E < tx.value.toB256
    rw [hdebit, B256.lt_iff_toNat_lt_toNat, hsub, hvalNat]
    omega
  obtain ⟨stmid, hmid, hentry⟩ := Msg.benvAfterTransfer_of_affordable TM rfl hafford value
  refine ⟨_, hentry, ?_⟩
  have : stmid = (TM).benv.state.setBal E ((TM).benv.state.bal E - tx.value.toB256) := by
    simp only [State.subBal, hafford, ↓reduceIte, Option.some.injEq] at hmid
    exact hmid.symm
  subst this
  rfl

/-- What a direct message's frame reads, in the sender's and block's terms. -/
theorem msg_stor (d : DirectTx benv bout tx E t chainId prio maxFee i f) (installed : benv.state.getCode t = c.code) :
    (TM).benv.state.getStor t = benv.state.getStor t :=
  congrArg Acct.stor (txDebit_get_ne (c.sender_ne d installed))

/-- **A direct submission, under Amsterdam, through `processTransaction`.** A valid type-2 transaction (`DirectTx`) to the
contract's code, carrying value, calldata of the submission's length, slot 0 off the inhibitor, and the guards' `Admit` at
the quote read from the contract's storage. Its gas is at most the execution budget, so the reservoir is empty, and covers
the intrinsic cost, the frame's regular gas, its state gas and the `SSTORE` sentry's 2300. It succeeds. The value moves
over the debited state. The state is the submission's world over that, with the refund and the fee credited by
`settleTransactionGas`. The receipt has no error and its logs are the EIP-7708 transfer log and then the frame's `LOG0`.
`X` is all the frame takes from `gasLeft`, exactly, and is at most `regularBound n + stateBound`. Gas used is the larger of
`i + X` less its capped refund and the calldata floor. -/
theorem transaction_ok {n : Nat} {out : B256}
    (d : DirectTx benv bout tx E t chainId prio maxFee i f) (installed : benv.state.getCode t = c.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp t) (hnew : t ∉ benv.createdAccounts) (caller : E ≠ systemAddress)
    (value : tx.value.toB256 ≠ 0) (hlen : tx.data.length = c.len)
    (hgas : i + c.regularBound n + c.stateBound + gCallStipend < tx.gas)
    (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess c.target (benv.state.getStor t)) 17 1 17 0 n out)
    (admit : c.Admit tx.data tx.value.toB256 (out / (17 : B256)))
    (noAlias : ((benv.state.getStor t).get 3).toNat < 2 ^ 253) :
    ∃ entry : Benv, (TM).benvAfterTransfer = .ok entry ∧
      entry.state = (((TM).benv.state.setBal E ((TM).benv.state.bal E - tx.value.toB256))).addBal t tx.value.toB256 ∧
      ∃ used : Nat,
      let s := userSevm TM c.code entry
      let e := userEntry TM entry
      let X := c.Gas s e .empty n
      let frame := c.Post s e .empty (tx.gas - i - X)
      let settlement := settleTransactionGas benv.stat.rules tx.gas f (tx.gas - i - X) 0
        frame.refundCounter.toNat (Int.ofNat used)
      let refunded := (c.world s entry.state).addBal E (settlement.gasLeft * P).toB256
      let final := txFinal (c.world s entry.state) E benv.stat.coinbase (settlement.gasLeft * P)
        (settlement.gasUsed * (P - benv.stat.baseFeePerGas))
      X ≤ c.regularBound n + c.stateBound ∧ used ≤ c.stateBound ∧
      settlement.gasUsed = max (i + X - min ((i + X) / 5) frame.refundCounter.toNat) f ∧
      ∃ bout', processTransaction benv bout tx index = .ok (final, bout') ∧
        frame.logs = [transferLog E t tx.value.toB256, c.log s] ∧
        bout'.cumulativeGasUsed = bout.cumulativeGasUsed + settlement.gasUsed ∧
        bout'.blockGasUsed = bout.blockGasUsed + settlement.executionGasUsed ∧
        bout'.blockStateGasUsed = bout.blockStateGasUsed + settlement.stateGasUsed ∧
        bout'.blockLogs = bout.blockLogs ++ frame.logs ∧
        bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
        bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
          some (makeReceipt tx none bout'.cumulativeGasUsed frame.logs) ∧
        bout'.bal = bout.bal.incorporate (index + 1) benv.state final
          (E :: benv.stat.coinbase :: frame.meta.accountReads.toList) frame.meta.storageReads.toList
          (txSettledWrites frame.world.storageWrites refunded final E benv.stat.coinbase).toList := by
  obtain ⟨entry, hentry, hstate⟩ := entry_exists (index := index) d value
  have hne := c.sender_ne d installed
  have hstor := c.msg_stor (index := index) d installed
  have hget := txDebit_get_ne (σ := benv.state) (fee := tx.gas * P) hne
  have hX' := c.gas_le_bound (userSevm TM c.code entry) (userEntry TM entry) n
  have hX := hX'
  have hsize : i + c.Gas (userSevm TM c.code entry) (userEntry TM entry) .empty n + gCallStipend < tx.gas := by
    omega
  have hmgas : (TM).gas = (tx.gas - i - c.Gas (userSevm TM c.code entry) (userEntry TM entry) .empty n) +
      c.Gas (userSevm TM c.code entry) (userEntry TM entry) .empty n := by
    show tx.gas - i = _
    omega
  have hmsg := c.message_ok (M := TM) (benv := entry) (G := tx.gas - i - c.Gas (userSevm TM c.code entry) (userEntry TM entry) .empty n)
    (n := n) (out := out) d.fork
    (by
      show (tx.auths).isEmpty = true
      unfold Tx.auths
      rw [d.type]
      rfl)
    rfl (by
      show (txDebit benv.state E (tx.gas * P)).getCode t = _
      show (((txDebit benv.state E (tx.gas * P)).get t).code) = _
      rw [hget]
      exact installed)
    hprecomp hentry hnew
    (by
      show (benv.state.get t).stor = ((txDebit benv.state E (tx.gas * P)).get t).stor
      rw [hget])
    Std.HashSet.toList_emptyWithCapacity caller hlen rfl (by omega) hmgas
    (by
      show ((TM).benv.state.getStor t).get 0 ≠ _
      rw [hstor]
      exact off)
    (by
      show WordFakeExponential.Run (storageExcess c.target ((TM).benv.state.getStor t)) 17 1 17 0 n out
      rw [hstor]
      exact wordRun)
    admit
    (by
      show (((TM).benv.state.getStor t).get 3).toNat < _
      rw [hstor]
      exact noAlias)
  obtain ⟨used, hused, hcall, hlogs, hgasLeft, hstateUsed, hleft, hdel⟩ := hmsg
  obtain ⟨hvs, hvalid, hchecked, halloc, hdebit, hprep⟩ := d.stages (t := t) index
  generalize hXdef : c.Gas (userSevm TM c.code entry) (userEntry TM entry) .empty n = X at *
  generalize hfdef : c.Post (userSevm TM c.code entry) (userEntry TM entry) .empty (tx.gas - i - X) = frame at *
  have hleft0 : frame.stateGas.left = 0 := Nat.le_zero.mp hleft
  have hrefund : Int.toNat? (systemCallOutputA TM frame).refundCounter = some frame.refundCounter.toNat := rfl
  have stage := processTransaction_amsterdam_of_stages d.fork hvs hvalid hchecked halloc hdebit hprep hcall hrefund hdel
  have hS : settleTransactionGas benv.stat.rules tx.gas f (systemCallOutputA TM frame).gasLeft
      (systemCallOutputA TM frame).stateGasLeft frame.refundCounter.toNat (systemCallOutputA TM frame).stateGasUsed =
      settleTransactionGas benv.stat.rules tx.gas f (tx.gas - i - X) 0 frame.refundCounter.toNat (Int.ofNat used) := by
    rw [hstateUsed]
    have h1 : (systemCallOutputA TM frame).gasLeft = tx.gas - i - X := hgasLeft
    have h2 : (systemCallOutputA TM frame).stateGasLeft = 0 := hleft0
    rw [h1, h2]
  dsimp only at stage
  rw [hS] at stage
  obtain ⟨bout', hproc, hcum, hblock, hstateCtr, hblockLogs, hkeys, hreceipt, hbal⟩ := stage
  refine ⟨entry, hentry, hstate, used, ?_⟩
  dsimp only
  rw [hXdef, hfdef]
  refine ⟨hX', hused, ?_, bout', hproc, ?_, hcum, hblock, hstateCtr, hblockLogs, hkeys, hreceipt, hbal⟩
  · have hrules : benv.stat.rules = amsterdamRules := amsterdam_rules d.fork
    rw [hrules]
    show max (tx.gas - (tx.gas - i - X) - 0 - min ((tx.gas - (tx.gas - i - X) - 0) / 5) frame.refundCounter.toNat) f = _
    rw [show tx.gas - (tx.gas - i - X) - 0 = i + X by omega]
  · rw [hlogs, initDevm_logs_transfer (M := TM) d.fork rfl hne value]
    rfl

/-- What a direct transaction whose frame reverts leaves, its frame's charge `X` at most `bound` regular gas. The state is
the debited state, so the value is back and only the gas is spent, with the refund and fee credited by
`settleTransactionGas`. The receipt holds the `REVERT` and no log, the block's logs are unchanged, and no state gas is used. -/
def TxReverted (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (E : Adr) (price i f bound : Nat) : Prop :=
  ∃ X, X ≤ bound ∧
    let settlement := settleTransactionGas benv.stat.rules tx.gas f (tx.gas - i - X) 0 0 (0 : Int)
    let debited := txDebit benv.state E (tx.gas * price)
    let refunded := debited.addBal E (settlement.gasLeft * price).toB256
    let final := txFinal debited E benv.stat.coinbase (settlement.gasLeft * price)
      (settlement.gasUsed * (price - benv.stat.baseFeePerGas))
    settlement.gasUsed = max (i + X) f ∧ settlement.stateGasUsed = 0 ∧
    ∃ (out : MsgCallOutput) (bout' : BlockOutput), processTransaction benv bout tx index = .ok (final, bout') ∧
      out.logs = [] ∧ out.error = some .revert ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + settlement.gasUsed ∧
      bout'.blockGasUsed = bout.blockGasUsed + settlement.executionGasUsed ∧
      bout'.blockStateGasUsed = bout.blockStateGasUsed + settlement.stateGasUsed ∧
      bout'.blockLogs = bout.blockLogs ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx (some .revert) bout'.cumulativeGasUsed []) ∧
      bout'.bal = bout.bal.incorporate (index + 1) benv.state final
        (E :: benv.stat.coinbase :: out.accountReads.toList) out.storageReads.toList
        (txSettledWrites out.storageWrites refunded final E benv.stat.coinbase).toList

/-- The entry transfer of a direct transaction always succeeds: its value is in the funds it was admitted with. -/
theorem entry_ok (d : DirectTx benv bout tx E t chainId prio maxFee i f) :
    ∃ entry : Benv, (TM).benvAfterTransfer = .ok entry := by
  by_cases value : tx.value.toB256 = 0
  · exact ⟨_, Msg.benvAfterTransfer_of_value_zero value⟩
  · obtain ⟨entry, h, -⟩ := entry_exists (index := index) d value
    exact ⟨entry, h⟩

/-- **A direct transaction whose frame reverts, under Amsterdam, through `processTransaction`.** A valid type-2 transaction
(`DirectTx`) to the code, whose gas covers the intrinsic cost and the frame's charge. -/
theorem transaction_reverts {bound : Nat} (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = c.code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (hrev : ∀ entry : Benv, (TM).benvAfterTransfer = .ok entry →
      FrameReverts (userSevm TM c.code entry) (userEntry TM entry) bound)
    (hgas : i + bound ≤ tx.gas) :
    TxReverted benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f bound := by
  obtain ⟨entry, hentry⟩ := entry_ok (index := index) d
  have hne := c.sender_ne d installed
  have hget := txDebit_get_ne (σ := benv.state) (fee := tx.gas * P) hne
  obtain ⟨X, hX, out, hcall, hlogs, herror, hleft, hstateLeft, hstateUsed, hrefund, -, hdel⟩ :=
    c.message_reverts (M := TM) (benv := entry) d.fork
      (by
        show (tx.auths).isEmpty = true
        unfold Tx.auths
        rw [d.type]
        rfl)
      rfl (by
        show (((txDebit benv.state E (tx.gas * P)).get t).code) = _
        rw [hget]
        exact installed)
      hprecomp hentry (hrev entry hentry) (by show bound ≤ tx.gas - i; omega)
  obtain ⟨hvs, hvalid, hchecked, halloc, hdebit, hprep⟩ := d.stages (t := t) index
  have hmgas : (TM).gas = tx.gas - i := rfl
  have hgrant : (TM).stateGasGrant = 0 := rfl
  rw [hmgas] at hleft
  rw [hgrant] at hstateLeft
  have hrefund' : Int.toNat? out.refundCounter = some 0 := by rw [hrefund]; rfl
  have stage := processTransaction_amsterdam_of_stages d.fork hvs hvalid hchecked halloc hdebit hprep hcall hrefund' hdel
  dsimp only at stage
  rw [hleft, hstateLeft, hstateUsed] at stage
  obtain ⟨bout', hproc, hcum, hblock, hstateCtr, hblockLogs, -, hreceipt, hbal⟩ := stage
  have hrules : benv.stat.rules = amsterdamRules := amsterdam_rules d.fork
  refine ⟨X, hX, ?_, ?_, out, bout', hproc, hlogs, herror, hcum, hblock, hstateCtr, ?_, ?_, hbal⟩
  · rw [hrules]
    show max (tx.gas - (tx.gas - i - X) - 0 - min ((tx.gas - (tx.gas - i - X) - 0) / 5) 0) f = _
    rw [show tx.gas - (tx.gas - i - X) - 0 = i + X by omega, Nat.min_zero, Nat.sub_zero]
  · rw [hrules]
    rfl
  · rw [hblockLogs, hlogs, List.append_nil]
  · rw [hreceipt, herror, hlogs]

/-- The frame's fork, at a direct transaction. -/
theorem frame_fork (d : DirectTx benv bout tx E t chainId prio maxFee i f) {entry : Benv}
    (hentry : (TM).benvAfterTransfer = .ok entry) :
    (userSevm TM c.code entry).benvStat.fork = .amsterdam := by
  show entry.stat.fork = _
  rw [benvAfterTransfer_stat hentry]
  exact d.fork

/-- The frame reads the contract's storage as it stood before the transaction. -/
theorem frame_read (d : DirectTx benv bout tx E t chainId prio maxFee i f) (installed : benv.state.getCode t = c.code)
    {entry : Benv} (hentry : (TM).benvAfterTransfer = .ok entry) (k : B256) :
    (userEntry TM entry).getStorVal t k = (benv.state.getStor t).get k := by
  have hne := c.sender_ne d installed
  have hget := txDebit_get_ne (σ := benv.state) (fee := tx.gas * P) hne
  have hcode : (TM).benv.state.getCode (TM).currentTarget = c.code := by
    show (((txDebit benv.state E (tx.gas * P)).get t).code) = _
    rw [hget]
    exact installed
  have hstor := entry_stor hcode c.nonempty hentry
  show (entry.state.getStor t).get k = _
  have h2 : entry.state.getStor t = (TM).benv.state.getStor t := hstor
  rw [h2, c.msg_stor d installed]

/-- The fee the frame quotes is the one read from the storage before the transaction. -/
theorem frame_excess (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = c.code) {entry : Benv} (hentry : (TM).benvAfterTransfer = .ok entry)
    (target : B256) :
    storedExcess target (userSevm TM c.code entry) (userEntry TM entry) =
      storageExcess target (benv.state.getStor t) := by
  show targetExcess target ((userEntry TM entry).getStorVal t 0) ((userEntry TM entry).getStorVal t 1) = _
  rw [c.frame_read d installed hentry, c.frame_read d installed hentry]
  rfl

end Submissions

end Blanc.Lift.BuilderRequest
