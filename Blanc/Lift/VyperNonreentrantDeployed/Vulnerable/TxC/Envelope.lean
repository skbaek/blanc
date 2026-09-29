import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Closed
import Blanc.TransactionForward

/-!
# V- as an admitted transaction under every covered fork: the transaction envelope

The transaction `txC` (a real signature over its signing hash under `E`'s key, type 2, zero fees,
zero value, an access list naming every precompile and `A'`, **16,043,200 gas: below the EIP-7825
per-transaction cap of 2^24 = 16,777,216** that Osaka and the BPO forks enforce) is run by Jaune's
`processTransaction` over the block `benvPre` with its fork set to any covered fork (Prague, Osaka,
BPO1, BPO2).  Every admission check is discharged here by evaluating it on the concrete
transaction and block under each fork -- validation and intrinsic gas (with the per-transaction
gas cap), chain id, fee rules with base fee 0, blob rules, nonce, balance against the maximum fee
and value, EIP-3607 (the sender `E` has no code), receiver, authorization list -- except two
things that are not evaluations of this block: the signature recovery, which is the one premise
(`recoverSender 0 txC = .ok E`, true by evaluation: the `#guard` in `TxTopC`), and the room in the
block for the transaction's gas (`bout.blockGasUsed`).  The debit, the prepared message (which is
the message of the closed message-level theorem) and the settlement are
`Blanc.processTransaction_of_stages`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Witness Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

variable {g : Fork}

/-! ### The admission checks, evaluated on the concrete transaction and block under each fork -/

theorem benvG_stateGas (hg : CoveredFork g) : (benvPre.withFork g).stat.rules.stateGas = none :=
  CoveredFork.rules_stateGas_none (s := (benvPre.withFork g).stat) hg

theorem benvG_bal (hg : CoveredFork g) : (benvPre.withFork g).stat.rules.bal = none :=
  CoveredFork.rules_bal_none (s := (benvPre.withFork g).stat) hg

/-- Validation: the transaction is well formed, within the fork's per-transaction gas cap, and its
intrinsic gas (21,000, the 64 of its four nonzero calldata bytes and the 45,600 of its access
list) and calldata floor (21,160) are within its gas. -/
theorem txC_validated (hg : CoveredFork g) :
    validateTransaction (benvPre.withFork g).stat.rules txC 0 = .ok (66664, 21160) :=
  hg.cases (motive := fun g => validateTransaction (benvPre.withFork g).stat.rules txC 0 =
    .ok (66664, 21160)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

/-- The type-2 transaction's chain id is the block's. -/
theorem txC_chain (hg : CoveredFork g) :
    checkTransactionChainId (benvPre.withFork g).beginTransaction txC = .ok () :=
  hg.cases (motive := fun g => checkTransactionChainId (benvPre.withFork g).beginTransaction txC =
    .ok ()) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

/-- Fee rules with base fee 0: `maxPriorityFee = maxFee = 0` is legal, and the effective gas
price and the maximum fee are 0. -/
theorem txC_fee (hg : CoveredFork g) :
    checkTransactionGasFee (benvPre.withFork g).beginTransaction txC = .ok (0, 0) :=
  hg.cases (motive := fun g => checkTransactionGasFee (benvPre.withFork g).beginTransaction txC =
    .ok (0, 0)) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem txC_blob (hg : CoveredFork g) :
    checkTransactionBlobData (benvPre.withFork g).beginTransaction txC 0 = .ok (0, []) :=
  hg.cases (motive := fun g => checkTransactionBlobData (benvPre.withFork g).beginTransaction txC
    0 = .ok (0, [])) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem txC_receiver : checkTransactionReceiver txC = .ok () := by kernel_rfl

theorem txC_auth : checkTransactionAuthorizationList txC = .ok () := by kernel_rfl

/-- The sender account: nonce 0 is the transaction's nonce, its balance 0 covers the maximum fee
0 plus the value 0, and it has no code (EIP-3607): `E` is an EOA. -/
theorem txC_sender :
    checkTransactionSenderAccount (benvPre.beginTransaction.state.get eAddress) txC 0 = .ok () := by
  kernel_rfl

/-- **Admission**: with the signature recovering `E` and room in the block for the transaction's
gas, `checkTransaction` accepts `txC` (blob-free, effective gas price 0). -/
theorem txC_checked (hg : CoveredFork g) (bout : BlockOutput)
    (hroom : bout.blockGasUsed + txC.gas ≤ 60000000)
    (hrecover : recoverSender benvPre.stat.chainId txC = .ok eAddress) :
    checkTransaction (benvPre.withFork g).beginTransaction (transactionPreludeBout bout txC 0) txC =
      .ok (eAddress, 0, [], 0) := by
  have hgas : checkTransactionGasLimits (benvPre.withFork g).beginTransaction
      (transactionPreludeBout bout txC 0) txC = .ok 0 := by
    have h := checkTransactionGasLimits_ok_of_room (benv := (benvPre.withFork g).beginTransaction)
      (bout := transactionPreludeBout bout txC 0) (tx := txC) (benvG_stateGas hg)
      (by
        show txC.gas ≤ 60000000 - bout.blockGasUsed
        omega)
      (Nat.zero_le _)
    exact h
  exact checkTransaction_ok_of_parts hgas (txC_chain hg) hrecover (txC_fee hg) (txC_blob hg)
    txC_receiver txC_auth txC_sender

/-! ### The debit, the prepared message and the call wrapper -/

/-- The zero-fee debit of `E` is the world the message runs in. -/
theorem txC_debit (hg : CoveredFork g) :
    ((benvPre.withFork g).state.incrNonce eAddress).subBal eAddress
      (txC.gas * 0 + transactionBlobGasFee (benvPre.withFork g) txC).toB256 = some worldTx := by
  rw [show (txC.gas * 0 + transactionBlobGasFee (benvPre.withFork g) txC).toB256 = 0 from
    hg.cases (motive := fun g => (txC.gas * 0 + transactionBlobGasFee (benvPre.withFork g)
      txC).toB256 = 0) rfl rfl rfl rfl]
  exact worldPre_debit

/-- **The prepared message is the closed message-level theorem's**, `msgC` with its fork
changed. -/
theorem txC_prepared (hg : CoveredFork g) :
    prepareMessage { (benvPre.withFork g).beginTransaction with state := worldTx }
      (transactionTenv (benvPre.withFork g).beginTransaction txC 0 eAddress 0 66664 []) txC =
      .ok (msgC.withFork g) :=
  prepareMessage_at hg

theorem msgC_call_shape0 : msgC.target.isNone = false ∧ msgC.tenv.stat.auths.isEmpty = true ∧
    getDelegatedCodeAddress msgC.code = none := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

theorem msgC_call_shape (hg : CoveredFork g) :
    (msgC.withFork g).benv.stat.rules.stateGas = none ∧ (msgC.withFork g).target.isNone = false ∧
      (msgC.withFork g).tenv.stat.auths.isEmpty = true ∧
      getDelegatedCodeAddress (msgC.withFork g).code = none :=
  ⟨CoveredFork.rules_stateGas_none (s := (msgC.withFork g).benv.stat) hg, msgC_call_shape0.1,
    msgC_call_shape0.2.1, msgC_call_shape0.2.2⟩

/-! ### The transaction -/

/-- **V- as an admitted transaction, under every covered fork.**  Jaune's `processTransaction`
accepts `txC` -- a type-2, zero-fee, zero-value transaction signed by the EOA `E` (nonce 0, no
code), with 16,043,200 gas, below the EIP-7825 per-transaction cap of 2^24 -- over the block
`benvPre` at any covered fork (Prague, Osaka, BPO1, BPO2), and in the world it returns the pool
`P`'s ledger is corrupted: `totalSupply = 1800 < 1906 = balanceOf[A']`, `A'` being the attacker
contract the transaction calls (the reentrant `add_liquidity` inside `remove_liquidity`).  Every
admission check (validation, intrinsic gas and the gas cap, chain id, fee rules with base fee 0,
blob rules, nonce, balance against fee and value, EIP-3607 sender code, receiver, authorization
list) is discharged above by evaluation; the premises are the signature (`hrecover`, true by
evaluation: the `#guard` in `TxTopC`) and that the block has the room (`hroom`).  The settlement
(the sender's gas refund and the coinbase's priority fee, both zero, and the message's empty set
of accounts to delete) leaves `P`'s storage alone. -/
theorem vminus_txC_process (g : Fork) (hg : CoveredFork g) (bout : BlockOutput)
    (hroom : bout.blockGasUsed + txC.gas ≤ 60000000)
    (hrecover : recoverSender benvPre.stat.chainId txC = .ok eAddress) :
    txC.gas < 2 ^ 24 ∧
    ∃ (st : State) (bout' : BlockOutput),
      processTransaction (benvPre.withFork g) bout txC 0 = .ok (st, bout') ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf st proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat <
        (storOf st proxyAddress balanceOfA2Slot.toB256).toNat := by
  refine ⟨by decide, ?_⟩
  obtain ⟨-, -, -, -, -, -, post, -, hpm, herr, -, -, hrf, hatd, h26, hA, hlt⟩ :=
    vminus_txC_message g hg
  obtain ⟨hsg, htarget, hauths, hdeleg⟩ := msgC_call_shape hg
  have hrefund : Int.toNat? post.refundCounter = some 42600 := by rw [hrf]; rfl
  have hcall := processMessageCall_call_of_message hsg htarget hauths hdeleg hpm herr hrefund
  obtain ⟨bout', hproc⟩ := processTransaction_of_stages (benv := benvPre.withFork g) (bout := bout)
    (tx := txC) (index := 0) (intrinsicGas := 66664) (calldataFloorGas := 21160)
    (sender := eAddress) (effectiveGasPrice := 0) (blobVersionedHashes := []) (txBlobGasUsed := 0)
    (debit := worldTx) (msg := msgC.withFork g) (benvG_stateGas hg) (benvG_bal hg)
    (txC_validated hg) (txC_checked hg bout hroom hrecover) (txC_debit hg) (txC_prepared hg)
    hcall (by rfl)
  refine ⟨_, bout', hproc, ?_⟩
  have hlist : Std.HashSet.toList post.accountsToDelete = [] := by rw [hatd]; simp
  have hst : ∀ (v₁ v₂ : B256) (a : Adr) (k : B256),
      storOf ((post.state.addBal eAddress v₁).addBal (benvPre.withFork g).stat.coinbase v₂) a k =
        storOf post.state a k := by
    intro v₁ v₂ a k
    simp only [State.addBal, storOf_setBal]
  simp only [hlist, List.foldl_nil, hst]
  exact ⟨h26, hA, hlt⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
