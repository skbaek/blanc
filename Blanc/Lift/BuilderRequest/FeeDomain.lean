import Blanc.Lift.BuilderRequest.Transaction
import Blanc.RequestFeeWordBound

/-!
# The builder statements on the fee's domain

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`Submissions.message_ok` and `Submissions.transaction_ok` take a run of the fee loop, with its iteration count `n` and output,
as premises. Where the quoted excess is at most 2892 they need not: the run exists, takes at most 462 iterations
(`RequestFeeWord.fee_run`) and quotes `fake_exponential(1, excess, 17)`. These are corollaries, with the excess condition in
place of the run and a concrete gas bound in place of a formula in `n`. Regular gas and state gas are stated apart.
The nonzero-value premise goes too: the quote is at least 1 wei, and a submission's value covers it. Direct calls only.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune ExecutionTrace

/-- A wider bound still holds a frame that reverts. -/
theorem FrameReverts.mono {s : Sevm} {b : Devm} {x y : Nat} (h : FrameReverts s b x) (hle : x ≤ y) : FrameReverts s b y := by
  obtain ⟨X, hX, rest⟩ := h
  exact ⟨X, hX.trans hle, rest⟩

theorem revertBound_le {n : Nat} (hn : n ≤ 462) : revertBound n ≤ revertBound 462 := by
  unfold revertBound
  omega

/-- **A reverting path's bound on the domain:** dispatch, the fee path at its longest, two cold reads and the guards. Regular
gas; a reverting frame charges no state gas. -/
theorem revertBound_462 : revertBound 462 = 44673 := rfl

/-- A reverting frame on the domain, from one that takes the run. -/
theorem frameReverts_of_domain {s : Sevm} {b : Devm} {e q : B256} (he : e.toNat ≤ 2892)
    (hq : q = (fakeExp 1 e.toNat 17).toB256)
    (h : ∀ n out, WordFakeExponential.Run e 17 1 17 0 n out → out / (17 : B256) = q → FrameReverts s b (revertBound n)) :
    FrameReverts s b 44673 := by
  obtain ⟨n, out, hn, run, -, hv⟩ := RequestFeeWord.fee_run he
  exact (h n out run (hv.trans hq.symm)).mono (revertBound_le hn)

namespace Submissions

variable (c : Submissions)

theorem regularBound_le {n : Nat} (hn : n ≤ 462) : c.regularBound n ≤ c.regularBound 462 := by
  unfold regularBound
  omega

section Message

variable {M : Msg} {benv : Benv}

/-- The frame's static environment at a message to the code. -/
local notation "S" => userSevm M c.code benv

/-- The frame's entry machine. -/
local notation "E" => userEntry M benv

/-- **A direct submission on the fee's domain, under Amsterdam, on any state-gas meter.** `message_ok`, with the quoted excess at
most 2892 in place of the loop's run. The guards' `Admit` is at `fake_exponential(1, excess, 17)`. The gas needs no formula: a
message with more than `regularBound 462 + stateBound + 2300` gas succeeds, and the frame's charge `X` is at most
`regularBound 462` regular gas plus `stateBound` state gas. -/
theorem message_ok_quoted (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = c.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (hnew : M.currentTarget ∉ M.benv.createdAccounts)
    (origin : (M.benv.stat.origState.get M.currentTarget).stor = (M.benv.state.get M.currentTarget).stor)
    (inherited : M.inheritedDeletions.toList = [])
    (caller : M.caller ≠ systemAddress) (hlen : M.data.length = c.len) (dynamic : M.isStatic = false)
    (hgas : c.regularBound 462 + c.stateBound + gCallStipend < M.gas)
    (off : (M.benv.state.getStor M.currentTarget).get 0 ≠ B256.max)
    (he : (storageExcess c.target (M.benv.state.getStor M.currentTarget)).toNat ≤ 2892)
    (admit : c.Admit M.data M.value
      (fakeExp 1 (storageExcess c.target (M.benv.state.getStor M.currentTarget)).toNat 17).toB256)
    (noAlias : ((M.benv.state.getStor M.currentTarget).get 3).toNat < 2 ^ 253) :
    ∃ X used, X ≤ c.regularBound 462 + c.stateBound ∧ used ≤ c.stateBound ∧
      processMessageCall M = .ok (c.world S benv.state, systemCallOutputA M (c.Post S E .empty (M.gas - X))) ∧
      (c.Post S E .empty (M.gas - X)).logs = (initDevm M).logs ++ [c.log S] ∧
      (c.Post S E .empty (M.gas - X)).gasLeft = M.gas - X ∧
      (systemCallOutputA M (c.Post S E .empty (M.gas - X))).stateGasUsed = Int.ofNat used := by
  obtain ⟨n, out, hn, run, -, hq⟩ := RequestFeeWord.fee_run he
  have hX := c.gas_le_bound S E n
  have hb := c.regularBound_le hn
  obtain ⟨used, hu, hcall, hlogs, hleft, hused, -, -⟩ := c.message_ok (benv := benv)
    (G := M.gas - c.Gas S E .empty n) (n := n) (out := out) hfork hauth htarget installed hprecomp entry hnew origin
    inherited caller hlen dynamic (by omega) (by omega) off run (by rw [hq]; exact admit) noAlias
  exact ⟨_, used, by omega, hu, hcall, hlogs, hleft, hused⟩

end Message

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr} {chainId : UInt64} {prio maxFee i f : Nat}

/-- What a direct submission's transaction leaves, at frame charge `X` from `gasLeft` and state gas used `used`: the submission's
world, the refund and the fee credited, gas used, the receipt and its logs (the transfer log, then the frame's `LOG0`), the block's
counters and the access-list builder. -/
def TxApplied (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) (E t : Adr) (price i f : Nat) (entry : Benv)
    (X used : Nat) : Prop :=
  let s := userSevm (txMsg benv tx index E t price i) c.code entry
  let e := userEntry (txMsg benv tx index E t price i) entry
  let frame := c.Post s e .empty (tx.gas - i - X)
  let settlement := settleTransactionGas benv.stat.rules tx.gas f (tx.gas - i - X) 0
    frame.refundCounter.toNat (Int.ofNat used)
  let refunded := (c.world s entry.state).addBal E (settlement.gasLeft * price).toB256
  let final := txFinal (c.world s entry.state) E benv.stat.coinbase (settlement.gasLeft * price)
    (settlement.gasUsed * (price - benv.stat.baseFeePerGas))
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
        (txSettledWrites frame.world.storageWrites refunded final E benv.stat.coinbase).toList

/-- The message a direct transaction prepares. -/
local notation "TM" => txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i

/-- **A direct submission on the fee's domain, under Amsterdam, through `processTransaction`.** `transaction_ok`, with the quoted
excess at most 2892 in place of the loop's run, and with the value's being nonzero derived: the quote is at least 1 wei and `covers`
says what the guards admit pays it. The gas is a bound, not a formula: `i + regularBound 462 + stateBound + 2300 < tx.gas`, and the
frame's charge `X` is within `regularBound 462 + stateBound`. -/
theorem transaction_ok_quoted (covers : ∀ d v q, c.Admit d v q → q.toNat ≤ v.toNat)
    (d : DirectTx benv bout tx E t chainId prio maxFee i f) (installed : benv.state.getCode t = c.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp t) (hnew : t ∉ benv.createdAccounts) (caller : E ≠ systemAddress)
    (hlen : tx.data.length = c.len)
    (hgas : i + c.regularBound 462 + c.stateBound + gCallStipend < tx.gas)
    (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (he : (storageExcess c.target (benv.state.getStor t)).toNat ≤ 2892)
    (admit : c.Admit tx.data tx.value.toB256 (fakeExp 1 (storageExcess c.target (benv.state.getStor t)).toNat 17).toB256)
    (noAlias : ((benv.state.getStor t).get 3).toNat < 2 ^ 253) :
    ∃ entry : Benv, (TM).benvAfterTransfer = .ok entry ∧
      entry.state = (((TM).benv.state.setBal E ((TM).benv.state.bal E - tx.value.toB256))).addBal t tx.value.toB256 ∧
      ∃ X used, X ≤ c.regularBound 462 + c.stateBound ∧ used ≤ c.stateBound ∧
        c.TxApplied benv bout tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i f entry X used := by
  obtain ⟨n, out, hn, run, hv, hq⟩ := RequestFeeWord.fee_run he
  have hb := c.regularBound_le hn
  have hval : tx.value.toB256 ≠ 0 := by
    intro h0
    have hpay := covers _ _ _ admit
    rw [← hq, hv, h0] at hpay
    have hpos := RequestFeeWord.fakeExp_pos (storageExcess c.target (benv.state.getStor t)).toNat
    have hz : (0 : B256).toNat = 0 := rfl
    omega
  obtain ⟨entry, hentry, hstate, used, hX, hused, rest⟩ :=
    c.transaction_ok (index := index) (n := n) (out := out) d installed hprecomp hnew caller hval hlen (by omega) off run
      (by rw [hq]; exact admit) noAlias
  exact ⟨entry, hentry, hstate, _, used, by omega, hused, rest⟩

/-- A reverted transaction with a wider bound. -/
theorem _root_.Blanc.Lift.BuilderRequest.Submissions.TxReverted.mono {price x y : Nat}
    (h : TxReverted benv bout tx index E price i f x) (hle : x ≤ y) : TxReverted benv bout tx index E price i f y := by
  obtain ⟨X, hX, rest⟩ := h
  exact ⟨X, hX.trans hle, rest⟩

/-- A reverting transaction on the domain, from one that takes the run. -/
theorem txReverted_of_domain {price : Nat} {e q : B256} (he : e.toNat ≤ 2892)
    (hq : q = (fakeExp 1 e.toNat 17).toB256) (hgas : i + 44673 ≤ tx.gas)
    (h : ∀ n out, WordFakeExponential.Run e 17 1 17 0 n out → out / (17 : B256) = q → i + revertBound n ≤ tx.gas →
      TxReverted benv bout tx index E price i f (revertBound n)) :
    TxReverted benv bout tx index E price i f 44673 := by
  obtain ⟨n, out, hn, run, -, hv⟩ := RequestFeeWord.fee_run he
  have hb := revertBound_le hn
  rw [revertBound_462] at hb
  exact (h n out run (hv.trans hq.symm) (by omega)).mono hb

end Submissions

end Blanc.Lift.BuilderRequest
