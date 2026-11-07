import Jaune.RlpEval
import Blanc.Lift.BuilderRequest.Deposit.Transaction
import Blanc.Lift.BuilderRequest.Exit.Transaction
import Blanc.Lift.BuilderRequest.Deposit.Creation.Address
import Blanc.Lift.BuilderRequest.Exit.Creation.Address

/-!
# Closed direct transactions under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`transaction_ok` and `transaction_not_admitted` have models: explicit signed type-2 transactions from the published
secp256k1 key 1, gas 1,000,000, fee cap 8, tip 1, on a pre-state with the contract's code and empty storage. Every premise
is met by evaluation. The exit contract's storage here has slot 0 at zero: this is a model of the premises, not its
deployed storage.
-/

namespace Blanc.Lift.BuilderRequest.TransactionWitness

open Jaune

/-- The key-1 externally owned account. -/
def sender : Adr := 0x7e5f4552091a69125d5dfcb7b8c2659029395bdf

/-- A pre-state: the sender with 2^100 wei at nonce 1, and `code` at `target` with empty storage. -/
def preState (target : Adr) (code : ByteArray) : State :=
  State.setPresent (State.setPresent .empty sender
      { nonce := 1, bal := (2 ^ 100 : Nat).toB256, stor := .empty, code := .empty })
    target { nonce := 1, bal := 0, stor := .empty, code := code }

/-- A block environment under Amsterdam, chain 1, with no base fee. -/
def preBenv (target : Adr) (code : ByteArray) : Benv :=
  { (default : Benv) with
    state := preState target code
    stat := { (default : Benv).stat with
      fork := .amsterdam, chainId := 1, origState := preState target code, blockGasLimit := 60000000 } }

/-- An empty block output. -/
def preBout : BlockOutput := BlockOutput.init

/-- The value a deposit of all-ones calldata needs at excess 0: the credit plus the fee of one wei. -/
def goodValue : Nat := (2 ^ 64 - 1) * 10 ^ 9 + 1

/-- A signed deposit of all-ones calldata carrying `goodValue`. -/
def depositTx : Tx :=
  { nonce := 1, gas := 1000000, value := goodValue, data := List.replicate 184 0xff, v := 0
    r := (0xd47644539acec3da5e3ecf5fe8863c628a9c97e8b71e9ea9167a6f4f83c03c32 : B256).toBytes
    s := (0x4b82ef4a9f9132ce9403818ab8e7928f372ed839693a66041c8416d5c74d43a7 : B256).toBytes
    type := .two 1 1 8 (some Deposit.Creation.address) [] }

/-- The same, one wei short of the credit plus the fee. -/
def lowDepositTx : Tx :=
  { nonce := 1, gas := 1000000, value := goodValue - 1, data := List.replicate 184 0xff, v := 0
    r := (0xd47644539acec3da5e3ecf5fe8863c628a9c97e8b71e9ea9167a6f4f83c03c32 : B256).toBytes
    s := (0x43449602820b9eeeacd505c53a502be5f40989735274f999584671a9e5eb607f : B256).toBytes
    type := .two 1 1 8 (some Deposit.Creation.address) [] }

/-- A signed exit submission of all-ones calldata carrying one wei. -/
def exitTx : Tx :=
  { nonce := 1, gas := 1000000, value := 1, data := List.replicate 48 0xff, v := 1
    r := (0xd47644539acec3da5e3ecf5fe8863c628a9c97e8b71e9ea9167a6f4f83c03c32 : B256).toBytes
    s := (0x1c28737e6f4672d484a5cc6bc6365d686f67139e3df1607e5e6ddcd88254100c : B256).toBytes
    type := .two 1 1 8 (some Exit.Creation.address) [] }

theorem depositTx_recovers : recoverSender 1 depositTx = .ok sender := by
  have h : depositTx.signingHash = some (0xd98a81c17c209b2461c4e282805f3d0abdaafd37046672ab905fa38f83daf472 : B256) := by
    simp only [Tx.signingHash, depositTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

theorem lowDepositTx_recovers : recoverSender 1 lowDepositTx = .ok sender := by
  have h : lowDepositTx.signingHash = some (0x3d6a96f18302f8e82535f4d41056112ed681e3430adb43208122ce8a0c824a35 : B256) := by
    simp only [Tx.signingHash, lowDepositTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

theorem exitTx_recovers : recoverSender 1 exitTx = .ok sender := by
  have h : exitTx.signingHash = some (0xa769b2bb1b52f86c3470950a828db00842f5abde1151c14f9f44e8748893e359 : B256) := by
    simp only [Tx.signingHash, exitTx, BLT.toBytes_eq_toBytesS, Nat.toBytes_eq_toBytesS]
    decide +kernel
  rw [recoverSender, h]
  decide +kernel

/-- The admission facts of a closed transaction, by evaluation. -/
theorem deposit_direct : DirectTx (preBenv Deposit.Creation.address Deposit.code) preBout depositTx sender
    Deposit.Creation.address 1 1 8 23944 32776 where
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
  recover := depositTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

theorem low_direct : DirectTx (preBenv Deposit.Creation.address Deposit.code) preBout lowDepositTx sender
    Deposit.Creation.address 1 1 8 23944 32776 where
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
  recover := lowDepositTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

theorem exit_direct : DirectTx (preBenv Exit.Creation.address Exit.code) preBout exitTx sender
    Exit.Creation.address 1 1 8 21768 24072 where
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
  recover := exitTx_recovers
  nonce := by decide +kernel
  nonceMax := by decide +kernel
  noCode := by decide +kernel
  funds := by decide +kernel

theorem deposit_stor : (preBenv Deposit.Creation.address Deposit.code).state.getStor Deposit.Creation.address = .empty := by
  kernel_rfl

theorem exit_stor : (preBenv Exit.Creation.address Exit.code).state.getStor Exit.Creation.address = .empty := by
  kernel_rfl

/-- **`transaction_ok` has a model at the deposit contract.** The closed transaction succeeds, and its receipt holds the
EIP-7708 transfer log and then the frame's `LOG0` of the calldata. -/
theorem deposit_transaction_ok :
    ∃ (st : State) (bout' : BlockOutput),
      processTransaction (preBenv Deposit.Creation.address Deposit.code) preBout depositTx 0 = .ok (st, bout') ∧
      bout'.blockLogs = [transferLog sender Deposit.Creation.address goodValue.toB256,
        ⟨Deposit.Creation.address, [], List.replicate 184 0xff⟩] := by
  obtain ⟨_, _, _, _, _, _, _, bout', hproc, hlogs, _, _, _, hblock, _⟩ :=
    Deposit.transaction_ok (index := 0) (n := 1) (out := 17) deposit_direct
      (by decide +kernel) (by decide +kernel) (Std.HashSet.not_mem_emptyWithCapacity) (by decide) (by decide +kernel) rfl
      (by decide)
      (by rw [deposit_stor]; decide +kernel)
      (by
        rw [deposit_stor]
        have hz : storageExcess 8 (Stor.empty) = 0 := by decide +kernel
        show WordFakeExponential.Run (storageExcess 8 Stor.empty) 17 1 17 0 1 17
        rw [hz]
        exact quote_zero_excess)
      ⟨by decide +kernel, by decide +kernel⟩
      (by rw [deposit_stor]; decide +kernel)
  refine ⟨_, bout', hproc, hblock.trans ?_⟩
  rw [hlogs]
  rfl

/-- **`transaction_bal` has a model**: on an empty builder, the closed deposit's first count write and its tail write each
gain a change at index 1, with the post value. -/
theorem deposit_transaction_bal :
    ∃ (entry : Benv) (st : State) (bout' : BlockOutput),
      processTransaction (preBenv Deposit.Creation.address Deposit.code) preBout depositTx 0 = .ok (st, bout') ∧
      (st.get Deposit.Creation.address).bal = goodValue.toB256 ∧
      (st.get Deposit.Creation.address).stor.get 3 = 1 ∧
      balChanges bout'.bal Deposit.Creation.address 3 = [(1, 1)] := by
  obtain ⟨entry, st, bout', hproc, hstor, hbal, hch, -, -⟩ :=
    Deposit.transaction_bal (index := 0) (n := 1) (out := 17) deposit_direct
      (by decide +kernel) (by decide +kernel) (Std.HashSet.not_mem_emptyWithCapacity) (by decide) (by decide +kernel) rfl
      (by decide)
      (by rw [deposit_stor]; decide +kernel)
      (by
        rw [deposit_stor]
        have hz : storageExcess 8 (Stor.empty) = 0 := by decide +kernel
        show WordFakeExponential.Run (storageExcess 8 Stor.empty) 17 1 17 0 1 17
        rw [hz]
        exact quote_zero_excess)
      ⟨by decide +kernel, by decide +kernel⟩
      (by rw [deposit_stor]; decide +kernel)
      (by decide +kernel) (fun _ => rfl) (fun _ _ h => by cases h)
  have hprebal : ((preBenv Deposit.Creation.address Deposit.code).state.get Deposit.Creation.address).bal = 0 := by
    kernel_rfl
  have h3 : (st.get Deposit.Creation.address).stor.get 3 = 1 := by
    rw [hstor, deposit_stor]
    show (Deposit.submittedStorage _ Stor.empty).get 3 = 1
    unfold Deposit.submittedStorage
    dsimp only
    rw [Stor.get_set_self]
    decide +kernel
  refine ⟨entry, st, bout', hproc, ?_, h3, ?_⟩
  · rw [hbal, hprebal]
    decide +kernel
  · rw [hch 3, h3]
    have hkeys : (3 : B256) ∈ Deposit.submissions.keys ((((preBenv Deposit.Creation.address Deposit.code).state.getStor
        Deposit.Creation.address)).get 3) := by
      rw [deposit_stor]
      decide +kernel
    have hmoved : ((preBenv Deposit.Creation.address Deposit.code).state.get Deposit.Creation.address).stor.get 3 ≠ 1 := by
      have : ((preBenv Deposit.Creation.address Deposit.code).state.get Deposit.Creation.address).stor = Stor.empty :=
        deposit_stor
      rw [this]
      decide +kernel
    rw [ite_eq_left ⟨hkeys, hmoved⟩]
    rfl

/-- **`transaction_not_admitted` has a model.** One wei short of the credit plus the quoted fee, the same transaction
reverts, and the block's logs stay empty. -/
theorem deposit_transaction_low :
    Submissions.TxReverted (preBenv Deposit.Creation.address Deposit.code) preBout lowDepositTx 0 sender
      (twoPrice 0 1 8) 23944 32776 (revertBound 1) :=
  Deposit.transaction_not_admitted (out := 17) 0 low_direct (by decide +kernel) (by decide +kernel) (by decide)
    rfl (by rw [deposit_stor]; decide +kernel)
    (by
      rw [deposit_stor]
      have hz : storageExcess 8 (Stor.empty) = 0 := by decide +kernel
      show WordFakeExponential.Run (storageExcess 8 Stor.empty) 17 1 17 0 1 17
      rw [hz]
      exact quote_zero_excess)
    (by
      intro h
      have h2 := h.2
      revert h2
      decide +kernel)
    (by decide +kernel)

/-- **`transaction_ok` has a model at the exit contract**, on storage with slot 0 at zero. -/
theorem exit_transaction_ok :
    ∃ (st : State) (bout' : BlockOutput),
      processTransaction (preBenv Exit.Creation.address Exit.code) preBout exitTx 0 = .ok (st, bout') ∧
      bout'.blockLogs = [transferLog sender Exit.Creation.address (1 : Nat).toB256,
        ⟨Exit.Creation.address, [], sender.toBytes ++ List.replicate 48 0xff⟩] := by
  obtain ⟨_, _, _, _, _, _, _, bout', hproc, hlogs, _, _, _, hblock, _⟩ :=
    Exit.transaction_ok (index := 0) (n := 1) (out := 17) exit_direct
      (by decide +kernel) (by decide +kernel) (Std.HashSet.not_mem_emptyWithCapacity) (by decide) (by decide +kernel) rfl
      (by decide)
      (by rw [exit_stor]; decide +kernel)
      (by
        rw [exit_stor]
        have hz : storageExcess 2 (Stor.empty) = 0 := by decide +kernel
        show WordFakeExponential.Run (storageExcess 2 Stor.empty) 17 1 17 0 1 17
        rw [hz]
        exact quote_zero_excess)
      (by
        show ((17 : B256) / (17 : B256)).toNat ≤ ((1 : Nat).toB256).toNat
        decide +kernel)
      (by rw [exit_stor]; decide +kernel)
  refine ⟨_, bout', hproc, hblock.trans ?_⟩
  rw [hlogs]
  rfl

end Blanc.Lift.BuilderRequest.TransactionWitness
