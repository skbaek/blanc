import Blanc.Lift.BuilderRequest.TransactionWitness
import Blanc.Lift.BuilderRequest.Deposit.FeeDomain
import Blanc.Lift.BuilderRequest.Exit.FeeDomain

/-!
# The fee-domain statements have closed models

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

The closed transactions of `TransactionWitness` meet every premise of the concrete-gas corollaries, and two more signed transactions, zero value and empty
calldata, meet every premise of the fee reads. The sender's key is the published test key 1.
-/

namespace Blanc.Lift.BuilderRequest.FeeDomainWitness

open Jaune
open TransactionWitness

/-- A signed fee read of the deposit contract: zero value, empty calldata. -/
def depositReadTx : Tx :=
  { nonce := 1, gas := 1000000, value := 0, data := [], v := 0
    r := (0xf01d6b9018ab421dd410404cb869072065522bf85734008f105cf385a023a80f : B256).toBytes
    s := (0x5248226eaccae0e756c0edbe9798c5d6740d9ed6bc750e65562a98ea80415d30 : B256).toBytes
    type := .two 1 1 8 (some Deposit.Creation.address) [] }

/-- A signed fee read of the exit contract: zero value, empty calldata. -/
def exitReadTx : Tx :=
  { nonce := 1, gas := 1000000, value := 0, data := [], v := 1
    r := (0xf01d6b9018ab421dd410404cb869072065522bf85734008f105cf385a023a80f : B256).toBytes
    s := (0x3df05a787ce0602d15cd97d099c0e40f7b607321b3130944d5506d8a7d1913de : B256).toBytes
    type := .two 1 1 8 (some Exit.Creation.address) [] }

theorem depositReadTx_recovers : recoverSender 1 depositReadTx = .ok sender := by
  have h : depositReadTx.signingHash = some (0x375e296563fd4a1bae6713d6e17aa2a986ec076555050911c006ed5fa8ff4902 : B256) := by
    simp only [Tx.signingHash, depositReadTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

theorem exitReadTx_recovers : recoverSender 1 exitReadTx = .ok sender := by
  have h : exitReadTx.signingHash = some (0xeb5d50adc7529c02932da9f9ae4cb64567d00a4a43f19f13d724efdd258c8576 : B256) := by
    simp only [Tx.signingHash, exitReadTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

theorem depositRead_direct : DirectTx (preBenv Deposit.Creation.address Deposit.code) preBout depositReadTx sender
    Deposit.Creation.address 1 1 8 15000 15000 where
  fork := rfl
  type := rfl
  chain := rfl
  prioLe := by decide
  baseLe := by decide
  cost := by decide +kernel
  intrinsic := by decide
  floor := by decide
  budget := by decide
  room := by decide
  stateRoom := by decide
  recover := depositReadTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

theorem exitRead_direct : DirectTx (preBenv Exit.Creation.address Exit.code) preBout exitReadTx sender
    Exit.Creation.address 1 1 8 15000 15000 where
  fork := rfl
  type := rfl
  chain := rfl
  prioLe := by decide
  baseLe := by decide
  cost := by decide +kernel
  intrinsic := by decide
  floor := by decide
  budget := by decide
  room := by decide
  stateRoom := by decide
  recover := exitReadTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

/-- At excess 0 the natural fee is 1 wei. -/
theorem fakeExp_zero : fakeExp 1 0 17 = 1 := by
  have h : FakeExponentialEval.runFuel 512 0 17 1 17 = some (1, 17) := by decide +kernel
  have out := (FakeExponentialEval.run_of_runFuel h).output_eq
  show fakeExpAux 0 17 1 17 / 17 = _
  rw [← out]

theorem excess_empty (t : B256) : (storageExcess t Stor.empty).toNat = 0 := by
  have h0 : (Stor.empty.get 0).toNat = 0 := rfl
  have h1 : (Stor.empty.get 1).toNat = 0 := rfl
  rw [storageExcess, targetExcess_toNat, h0, h1, Nat.zero_sub, Nat.add_zero, Nat.zero_mod]

/-- **The concrete-gas submission has a model at the deposit contract**: `deposit_direct` meets `transaction_ok_quoted`'s premises. -/
theorem deposit_quoted_model :
    ∃ entry : Benv, ∃ X used, X ≤ 147683 + 783360 ∧ used ≤ 783360 ∧
      Deposit.submissions.TxApplied (preBenv Deposit.Creation.address Deposit.code) preBout depositTx 0 sender
        Deposit.Creation.address (twoPrice (preBenv Deposit.Creation.address Deposit.code).stat.baseFeePerGas 1 8) 23944 32776 entry X used := by
  obtain ⟨entry, -, h⟩ := Deposit.transaction_ok_quoted (index := 0) deposit_direct
    (by decide +kernel) (by decide +kernel) Std.HashSet.not_mem_emptyWithCapacity (by decide +kernel) rfl (by decide)
    (by rw [deposit_stor]; decide +kernel) (by rw [deposit_stor, excess_empty]; decide)
    (by
      rw [deposit_stor, excess_empty, fakeExp_zero]
      exact ⟨by decide +kernel, by decide +kernel⟩)
    (by rw [deposit_stor]; decide +kernel)
  exact ⟨entry, h⟩

/-- **The concrete-gas submission has a model at the exit contract**: `exit_direct` meets `transaction_ok_quoted`'s premises. -/
theorem exit_quoted_model :
    ∃ entry : Benv, ∃ X used, X ≤ 110330 + 489600 ∧ used ≤ 489600 ∧
      Exit.submissions.TxApplied (preBenv Exit.Creation.address Exit.code) preBout exitTx 0 sender
        Exit.Creation.address (twoPrice (preBenv Exit.Creation.address Exit.code).stat.baseFeePerGas 1 8) 21768 24072 entry X used := by
  obtain ⟨entry, -, h⟩ := Exit.transaction_ok_quoted (index := 0) exit_direct
    (by decide +kernel) (by decide +kernel) Std.HashSet.not_mem_emptyWithCapacity (by decide +kernel) rfl (by decide)
    (by rw [exit_stor]; decide +kernel) (by rw [exit_stor, excess_empty]; decide)
    (by
      rw [exit_stor, excess_empty, fakeExp_zero]
      show (Nat.toB256 1).toNat ≤ (Nat.toB256 1).toNat
      exact Nat.le_refl _)
    (by rw [exit_stor]; decide +kernel)
  exact ⟨entry, h⟩

/-- **The transaction fee read has a model at the deposit contract**: its quote on empty storage is 1 wei, 32 bytes, and no log. -/
theorem deposit_feeRead_model :
    ∃ (X : Nat) (o : MsgCallOutput), X ≤ 44616 ∧ o.returnData = (1 : B256).toBytes ∧ o.logs = [] ∧ o.error = none ∧
      FeeReadTx (preBenv Deposit.Creation.address Deposit.code) preBout depositReadTx 0 sender
        (twoPrice (preBenv Deposit.Creation.address Deposit.code).stat.baseFeePerGas 1 8) 15000 15000 X := by
  obtain ⟨X, o, hX, -, ho, -, htx, -⟩ := Deposit.transaction_feeRead (index := 0) depositRead_direct
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide)
    (by rw [deposit_stor]; decide +kernel) (by rw [deposit_stor, excess_empty]; decide)
  refine ⟨X, o, hX, ho.returnData.trans ?_, ho.logs, ho.error, htx⟩
  rw [deposit_stor, excess_empty, fakeExp_zero]
  rfl

/-- **The transaction fee read has a model at the exit contract.** On empty storage, off the inhibitor. -/
theorem exit_feeRead_model :
    ∃ (X : Nat) (o : MsgCallOutput), X ≤ 44616 ∧ o.returnData = (1 : B256).toBytes ∧ o.logs = [] ∧ o.error = none ∧
      FeeReadTx (preBenv Exit.Creation.address Exit.code) preBout exitReadTx 0 sender
        (twoPrice (preBenv Exit.Creation.address Exit.code).stat.baseFeePerGas 1 8) 15000 15000 X := by
  obtain ⟨X, o, hX, -, ho, -, htx, -⟩ := Exit.transaction_feeRead (index := 0) exitRead_direct
    (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl (by decide +kernel) (by decide)
    (by rw [exit_stor]; decide +kernel) (by rw [exit_stor, excess_empty]; decide)
  refine ⟨X, o, hX, ho.returnData.trans ?_, ho.logs, ho.error, htx⟩
  rw [exit_stor, excess_empty, fakeExp_zero]
  rfl

end Blanc.Lift.BuilderRequest.FeeDomainWitness
