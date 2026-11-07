import Blanc.Lift.BuilderRequest.Deposit.Transaction
import Blanc.Lift.BuilderRequest.FeeRead

/-!
# The deposit contract on the fee's domain, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

Concrete gas, with no fee-loop premise, wherever `slot0 + max(0, count - 8)`, as a word, is at most 2892. The loop then runs at
most 462 iterations (`RequestFeeWord.fee_run`, tight at 2892). A submission takes at most 147,683 regular gas, state gas excluded,
and at most 783,360 state gas; a reverting frame at most 44,673 regular gas and no state gas. These are upper bounds: the exact
charge depends on warm slots and earlier writes in the transaction. A fee read takes at most 44,616 regular gas and no state gas. Direct calls only.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {E t : Adr} {chainId : UInt64} {prio maxFee i f : Nat}

theorem regularBound_462 : submissions.regularBound 462 = 147683 := rfl
theorem stateBound_eq : submissions.stateBound = 783360 := rfl

/-- **A direct submission's message on the fee's domain.** `Submissions.message_ok_quoted` at this contract. -/
abbrev message_ok_quoted := @Submissions.message_ok_quoted submissions

/-- **A direct submission to the deposit contract, on the fee's domain.** `Submissions.transaction_ok_quoted`, with its
numbers: more than `i + 147683 + 783360 + 2300` gas, slot 0 off the inhibitor, the quoted excess at most 2892, and the guards'
admission at `fake_exponential(1, excess, 17)`. The value's being nonzero is derived. -/
theorem transaction_ok_quoted {index : Nat} (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (hnew : t ∉ benv.createdAccounts) (caller : E ≠ systemAddress) (hlen : tx.data.length = 184)
    (hgas : i + 147683 + 783360 + 2300 < tx.gas) (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (he : (storageExcess 8 (benv.state.getStor t)).toNat ≤ 2892)
    (admit : Admits tx.data tx.value.toB256 (fakeExp 1 (storageExcess 8 (benv.state.getStor t)).toNat 17).toB256)
    (noAlias : ((benv.state.getStor t).get 3).toNat < 2 ^ 253) :
    ∃ entry : Benv,
      (txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i).benvAfterTransfer = .ok entry ∧
      ∃ X used, X ≤ 147683 + 783360 ∧ used ≤ 783360 ∧
        submissions.TxApplied benv bout tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i f entry X used := by
  obtain ⟨entry, hentry, -, X, used, hX, hu, rest⟩ := submissions.transaction_ok_quoted (index := index)
    (fun _ _ _ h => by
    have := h.2
    omega) d installed hprecomp hnew caller hlen hgas off he admit noAlias
  exact ⟨entry, hentry, X, used, hX, hu, rest⟩

/-- **A direct submission the guards reject, on the fee's domain, reverts within 44,673 regular gas.** -/
theorem transaction_not_admitted_quoted (index : Nat) (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (caller : E ≠ systemAddress) (hlen : tx.data.length = 184) (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (he : (storageExcess 8 (benv.state.getStor t)).toNat ≤ 2892)
    (rejected : ¬ Admits tx.data tx.value.toB256 (fakeExp 1 (storageExcess 8 (benv.state.getStor t)).toNat 17).toB256)
    (hgas : i + 44673 ≤ tx.gas) :
    Submissions.TxReverted benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f 44673 :=
  Submissions.txReverted_of_domain he rfl hgas fun _ _ run hq hg =>
    transaction_not_admitted index d installed hprecomp caller hlen off run (by rw [hq]; exact rejected) hg

/-- **A direct transaction with calldata of neither form, on the fee's domain, reverts within 44,673 regular gas.** -/
theorem transaction_badLength_quoted (index : Nat) (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (caller : E ≠ systemAddress) (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (he : (storageExcess 8 (benv.state.getStor t)).toNat ≤ 2892)
    (other : tx.data.length.toB256 ≠ (184 : B256)) (nonzero : tx.data.length.toB256 ≠ 0) (hgas : i + 44673 ≤ tx.gas) :
    Submissions.TxReverted benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f 44673 :=
  Submissions.txReverted_of_domain he rfl hgas fun _ _ run _ hg =>
    transaction_badLength index d installed hprecomp caller off run other nonzero hg

/-- **A direct fee read carrying value, on the fee's domain, reverts within 44,673 regular gas.** -/
theorem transaction_paidRead_quoted (index : Nat) (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (caller : E ≠ systemAddress) (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (he : (storageExcess 8 (benv.state.getStor t)).toNat ≤ 2892)
    (empty : tx.data = []) (paid : tx.value.toB256 ≠ 0) (hgas : i + 44673 ≤ tx.gas) :
    Submissions.TxReverted benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f 44673 :=
  Submissions.txReverted_of_domain he rfl hgas fun _ _ run _ hg =>
    transaction_paidRead index d installed hprecomp caller off run empty paid hg

variable {s : Sevm} {b : Devm}

/-- **A frame the guards reject, on the fee's domain, executes `REVERT`** within 44,673 regular gas. `message_reverts` takes it through
the message. -/
theorem frameReverts_not_admitted_quoted (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (hlen : s.data.length = 184)
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max) (he : (storedExcess 8 s b).toNat ≤ 2892)
    (rejected : ¬ Admits s.data s.value (fakeExp 1 (storedExcess 8 s b).toNat 17).toB256) :
    FrameReverts s b 44673 :=
  frameReverts_of_domain he rfl fun _ _ run hq =>
    frameReverts_not_admitted hcode hfork caller hlen off run (by rw [hq]; exact rejected)

/-- **A frame with calldata of neither form, on the fee's domain, executes `REVERT`** within 44,673 regular gas. -/
theorem frameReverts_badLength_quoted (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (he : (storedExcess 8 s b).toNat ≤ 2892)
    (other : s.data.length.toB256 ≠ (184 : B256)) (nonzero : s.data.length.toB256 ≠ 0) : FrameReverts s b 44673 :=
  frameReverts_of_domain he rfl fun _ _ run _ =>
    frameReverts_badLength hcode hfork caller off run other nonzero

/-- **A fee read carrying value, on the fee's domain, executes `REVERT`** within 44,673 regular gas. -/
theorem frameReverts_paidRead_quoted (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam)
    (caller : s.caller ≠ systemAddress) (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (he : (storedExcess 8 s b).toNat ≤ 2892) (empty : s.data = []) (paid : s.value ≠ 0) : FrameReverts s b 44673 :=
  frameReverts_of_domain he rfl fun _ _ run _ =>
    frameReverts_paidRead hcode hfork caller off run empty paid

variable {M : Msg}

/-- **A fee read through `processMessageCall`, on the fee's domain.** `BuilderRequest.message_feeRead_quoted` at this contract: zero value, empty
calldata, slot 0 off the inhibitor, at least 44,616 gas and the quoted excess at most 2892 return exactly the 32-byte quote and leave the state as it
was. -/
theorem message_feeRead_quoted (hfork : M.benv.stat.fork = .amsterdam) (hauth : M.tenv.stat.auths.isEmpty = true)
    (htarget : M.target.isNone = false) (installed : M.benv.state.getCode M.currentTarget = code)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (inherited : M.inheritedDeletions.toList = [])
    (caller : M.caller ≠ systemAddress) (empty : M.data = []) (zero : M.value = 0) (hgas : 44616 ≤ M.gas)
    (off : (M.benv.state.getStor M.currentTarget).get 0 ≠ B256.max)
    (he : (storageExcess 8 (M.benv.state.getStor M.currentTarget)).toNat ≤ 2892) :
    ∃ X o, X ≤ 44616 ∧ processMessageCall M = .ok (M.benv.state, o) ∧
      FeeReadOutput M o (fakeExp 1 (storageExcess 8 (M.benv.state.getStor M.currentTarget)).toNat 17).toB256 (M.gas - X) ∧
      o.returnData.length = 32 :=
  BuilderRequest.message_feeRead_quoted userPath submissions.nonempty submissions.undelegated hfork hauth htarget installed hprecomp
    inherited caller empty zero hgas off he

/-- **A direct fee read through `processTransaction`, on the fee's domain.** `BuilderRequest.transaction_feeRead` at this contract. -/
theorem transaction_feeRead {index : Nat} (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t) (caller : E ≠ systemAddress)
    (empty : tx.data = []) (zero : tx.value.toB256 = 0) (hgas : i + 44616 ≤ tx.gas)
    (off : (benv.state.getStor t).get 0 ≠ B256.max) (he : (storageExcess 8 (benv.state.getStor t)).toNat ≤ 2892) :
    ∃ X o, X ≤ 44616 ∧
      processMessageCall (txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i) =
        .ok ((txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i).benv.state, o) ∧
      FeeReadOutput (txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i) o
        (fakeExp 1 (storageExcess 8 (benv.state.getStor t)).toNat 17).toB256 (tx.gas - i - X) ∧
      o.returnData.length = 32 ∧
      FeeReadTx benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f X ∧
      (benv.stat.coinbase ≠ t → ∀ final bout', processTransaction benv bout tx index = .ok (final, bout') →
        final.get t = benv.state.get t) :=
  BuilderRequest.transaction_feeRead userPath submissions.nonempty submissions.undelegated d installed hprecomp caller empty zero hgas off he

end Blanc.Lift.BuilderRequest.Deposit
