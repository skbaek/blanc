import Blanc.Weth10Stable
import Blanc.Weth10TransferFunctional
import Blanc.Weth10Live
import Blanc.ForwardCall
import Init.Data.Ord.UInt

/-!
Constructive redemption for the exact Blanc WETH10 runtime.

This module's admissibility records deliberately describe only fresh execution
envelopes.  Successful code, message, and transaction executions occur only in
the enabledness conclusions below.  The public claim remains bounded by
`PORTING.md`, `WETH10_COMPATIBILITY.md`, and `WETH10_DEVIATIONS.md`.
-/

namespace Blanc

open Jaune

namespace Weth10

set_option maxRecDepth 8000

open Jaune.Ninst Ninst

private theorem pinnedJauneListCompare_eq_compareLex {α : Type u} [Ord α]
    (xs ys : List α) :
    Jaune.List.compare xs ys = List.compareLex compare xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          cases h : compare x y <;>
            simp [Jaune.List.compare, List.compareLex, h, ih]

private instance : Std.TransCmp
    (compare : Bytes → Bytes → Ordering) := by
  rw [show (compare : Bytes → Bytes → Ordering) =
      List.compareLex (compare : UInt8 → UInt8 → Ordering) by
    funext xs ys
    exact pinnedJauneListCompare_eq_compareLex xs ys]
  infer_instance

/-! ## Canonical natural-amount interface -/

/-- The booked WETH10 balance exposed to downstream arithmetic in `Nat`. -/
def bookedBalanceNat (w : Jaune.State) (ca owner : Adr) : Nat :=
  (Stor.rest (w.getStor ca) owner).toNat

def withdrawSelector : B256 := selector "withdraw" [.uint256]

def withdrawToSelector : B256 :=
  selector "withdrawTo" [.address, .uint256]

/-- Canonical `withdraw(uint256)` calldata. -/
def withdrawCalldata (q : Nat) : Bytes :=
  abiSelectorBytes withdrawSelector ++ q.toB256.toBytes

/-- Canonical `withdrawTo(address,uint256)` calldata. -/
def withdrawToCalldata (recipient : Adr) (q : Nat) : Bytes :=
  abiSelectorBytes withdrawToSelector ++
    recipient.toB256.toBytes ++ q.toB256.toBytes

/-- The exact public WETH burn log for either redemption selector. -/
def redemptionBurnLog (ca owner : Adr) (q : Nat) : Log :=
  ⟨ca, [Blanc.transferEvent, owner.toB256, 0], q.toB256.toBytes⟩

/-! ## Explicit access/account and gas cases -/

inductive AddressAccessCase (accessed : AdrSet) (a : Adr) : Prop
  | warm (h : a ∈ accessed)
  | cold (h : a ∉ accessed)

inductive StorageAccessCase (accessed : KeySet) (a : Adr) (k : B256) : Prop
  | warm (h : (a, k) ∈ accessed)
  | cold (h : (a, k) ∉ accessed)

inductive RecipientAccountCase (w : Jaune.State) (recipient : Adr) : Prop
  | empty (h : (w.get recipient).Empty)
  | existing (h : ¬ (w.get recipient).Empty)

/-- Child gas added by EVM value-call semantics.  This is not an additional
caller-paid charge: the nonzero branch is covered by `gasCallValue`. -/
def redemptionChildSupplement (q : Nat) : Nat :=
  if q = 0 then 0 else gCallStipend

/-- Gas charged by the balanced selector walk before entering either body. -/
def redemptionSelectorDispatchGas : Nat := 182

/-- Closed body budget consumed by the mechanized forward walk.  This remains
separate from the component model so the latter never disguises proof slack as
an opcode charge. -/
def redemptionMechanizedBodyGas : Nat := 100000

def redemptionExecutionGasFloor : Nat :=
  redemptionSelectorDispatchGas + redemptionMechanizedBodyGas

/-- Conservative allowance for fixed stack, jump, memory, and log work in the
component model.  The independently named execution floor above dominates it. -/
def redemptionFixedModelGas : Nat := 10000

def redemptionStorageReadWorstGas : Nat := gasColdSload

/-- A cold surcharge plus the largest EIP-2200 value charge.  The actual
withdrawal read warms this key first, so this deliberately bounds more cases
than the canonical walk needs. -/
def redemptionStorageWriteWorstGas : Nat :=
  gasColdSload + gasStorageSet

def redemptionSuccessTailGas : Nat := 16

def redemptionStorageReadCharge
    (accessed : KeySet) (ca owner : Adr) : Nat :=
  if (ca, owner.toB256) ∈ accessed then gasWarmAccess else gasColdSload

def redemptionRecipientCreationCharge
    (w : State) (recipient : Adr) (q : Nat) : Nat :=
  if ¬ (w.get recipient).Empty ∨ q = 0 then 0 else gNewAccount

def redemptionValueCallCharge (q : Nat) : Nat :=
  if q = 0 then 0 else gasCallValue

def redemptionCallCharge
    (accessed : AdrSet) (w : State) (recipient : Adr) (q : Nat) : Nat :=
  accessCost recipient accessed +
    redemptionRecipientCreationCharge w recipient q +
    redemptionValueCallCharge q

/-- Closed worst-case caller-paid `CALL` charge.  The child stipend is absent:
on the nonzero branch it is dominated by `gasCallValue`. -/
def redemptionCallWorstGas (q : Nat) : Nat :=
  gasColdAccountAccess +
    (if q = 0 then 0 else gNewAccount + gasCallValue)

/-- All explicit Prague components, before taking the mechanized proof floor. -/
def redemptionModeledRuntime (q : Nat) : Nat :=
  redemptionSelectorDispatchGas + redemptionFixedModelGas +
    redemptionStorageReadWorstGas + redemptionStorageWriteWorstGas +
    redemptionCallWorstGas q + redemptionSuccessTailGas

/-- Closed conservative Prague runtime bound.  It is the maximum of the exact
forward-proof budget and the explicit worst-case component schedule. -/
def redemptionRuntimeCeiling (q : Nat) : Nat :=
  max redemptionExecutionGasFloor (redemptionModeledRuntime q)

/-- The EIP-2200 charge of a store, including the possible cold surcharge. -/
def redemptionSstoreCharge
    (cold : Bool) (original current new : B256) : Nat :=
  (if cold then gasColdSload else 0) +
    sstoreValueCost original current new

theorem AddressAccessCase.accessCost_le
    {accessed : AdrSet} {a : Adr}
    (h : AddressAccessCase accessed a) :
    accessCost a accessed ≤ gasColdAccountAccess := by
  cases h with
  | warm hw => simp [accessCost, hw, gasWarmAccess, gasColdAccountAccess]
  | cold hc => simp [accessCost, hc]

theorem StorageAccessCase.readCharge_le
    {accessed : KeySet} {ca owner : Adr}
    (h : StorageAccessCase accessed ca owner.toB256) :
    redemptionStorageReadCharge accessed ca owner ≤ gasColdSload := by
  cases h with
  | warm hw =>
      simp [redemptionStorageReadCharge, hw, gasWarmAccess, gasColdSload]
  | cold hc => simp [redemptionStorageReadCharge, hc]

theorem RecipientAccountCase.creationCharge_le
    {w : State} {recipient : Adr} {q : Nat}
    (h : RecipientAccountCase w recipient) :
    redemptionRecipientCreationCharge w recipient q ≤ gNewAccount := by
  cases h with
  | empty he =>
      simp only [redemptionRecipientCreationCharge, he, not_true_eq_false,
        false_or]
      split <;> simp [gNewAccount]
  | existing he => simp [redemptionRecipientCreationCharge, he]

theorem redemptionCallCharge_le
    {accessed : AdrSet} {w : State} {recipient : Adr} {q : Nat}
    (ha : AddressAccessCase accessed recipient)
    (he : RecipientAccountCase w recipient) :
    redemptionCallCharge accessed w recipient q ≤ redemptionCallWorstGas q := by
  cases ha <;> cases he <;>
    simp_all [redemptionCallCharge, redemptionCallWorstGas, accessCost,
      redemptionRecipientCreationCharge, redemptionValueCallCharge,
      gasWarmAccess, gasColdAccountAccess, gNewAccount, gasCallValue]
  all_goals split <;> simp_all

theorem redemptionCallCharge_warm_existing_of_ne
    {accessed : AdrSet} {w : State} {recipient : Adr} {q : Nat}
    (ha : recipient ∈ accessed) (he : ¬ (w.get recipient).Empty)
    (hq : q ≠ 0) :
    redemptionCallCharge accessed w recipient q = 9100 := by
  simp [redemptionCallCharge, redemptionRecipientCreationCharge,
    redemptionValueCallCharge, accessCost, ha, he, hq,
    gasWarmAccess, gasCallValue]

theorem redemptionCallCharge_cold_existing_of_ne
    {accessed : AdrSet} {w : State} {recipient : Adr} {q : Nat}
    (ha : recipient ∉ accessed) (he : ¬ (w.get recipient).Empty)
    (hq : q ≠ 0) :
    redemptionCallCharge accessed w recipient q = 11600 := by
  simp [redemptionCallCharge, redemptionRecipientCreationCharge,
    redemptionValueCallCharge, accessCost, ha, he, hq,
    gasColdAccountAccess, gasCallValue]

theorem redemptionCallCharge_warm_empty_of_ne
    {accessed : AdrSet} {w : State} {recipient : Adr} {q : Nat}
    (ha : recipient ∈ accessed) (he : (w.get recipient).Empty)
    (hq : q ≠ 0) :
    redemptionCallCharge accessed w recipient q = 34100 := by
  simp [redemptionCallCharge, redemptionRecipientCreationCharge,
    redemptionValueCallCharge, accessCost, ha, he, hq,
    gasWarmAccess, gNewAccount, gasCallValue]

theorem redemptionCallCharge_cold_empty_of_ne
    {accessed : AdrSet} {w : State} {recipient : Adr} {q : Nat}
    (ha : recipient ∉ accessed) (he : (w.get recipient).Empty)
    (hq : q ≠ 0) :
    redemptionCallCharge accessed w recipient q = 36600 := by
  simp [redemptionCallCharge, redemptionRecipientCreationCharge,
    redemptionValueCallCharge, accessCost, ha, he, hq,
    gasColdAccountAccess, gNewAccount, gasCallValue]

theorem redemptionCallCharge_warm_zero
    {accessed : AdrSet} {w : State} {recipient : Adr}
    (ha : recipient ∈ accessed) :
    redemptionCallCharge accessed w recipient 0 = 100 := by
  simp [redemptionCallCharge, redemptionRecipientCreationCharge,
    redemptionValueCallCharge, accessCost, ha, gasWarmAccess]

theorem redemptionCallCharge_cold_zero
    {accessed : AdrSet} {w : State} {recipient : Adr}
    (ha : recipient ∉ accessed) :
    redemptionCallCharge accessed w recipient 0 = 2600 := by
  simp [redemptionCallCharge, redemptionRecipientCreationCharge,
    redemptionValueCallCharge, accessCost, ha, gasColdAccountAccess]

theorem redemptionSstoreCharge_warm_clean_zero
    {new : B256} (hne : new ≠ 0) :
    redemptionSstoreCharge false 0 0 new = 20000 := by
  have hz : (0 : B256) ≠ new := Ne.symm hne
  simp [redemptionSstoreCharge, sstoreValueCost, hz, gasStorageSet]

theorem redemptionSstoreCharge_cold_clean_zero
    {new : B256} (hne : new ≠ 0) :
    redemptionSstoreCharge true 0 0 new = 22100 := by
  have hz : (0 : B256) ≠ new := Ne.symm hne
  simp [redemptionSstoreCharge, sstoreValueCost, hz, gasColdSload,
    gasStorageSet]

theorem redemptionSstoreCharge_warm_clean_nonzero
    {original new : B256} (ho : original ≠ 0) (hne : original ≠ new) :
    redemptionSstoreCharge false original original new = 2900 := by
  simp [redemptionSstoreCharge, sstoreValueCost, ho, hne,
    gasStorageUpdate, gasColdSload]

theorem redemptionSstoreCharge_cold_clean_nonzero
    {original new : B256} (ho : original ≠ 0) (hne : original ≠ new) :
    redemptionSstoreCharge true original original new = 5000 := by
  simp [redemptionSstoreCharge, sstoreValueCost, ho, hne,
    gasStorageUpdate, gasColdSload]

theorem redemptionSstoreCharge_warm_noop
    {original current : B256} :
    redemptionSstoreCharge false original current current = 100 := by
  simp [redemptionSstoreCharge, sstoreValueCost, gasWarmAccess]

theorem redemptionSstoreCharge_cold_noop
    {original current : B256} :
    redemptionSstoreCharge true original current current = 2200 := by
  simp [redemptionSstoreCharge, sstoreValueCost, gasWarmAccess,
    gasColdSload]

theorem redemptionSstoreCharge_warm_dirty
    {original current new : B256} (hdirty : original ≠ current) :
    redemptionSstoreCharge false original current new = 100 := by
  simp [redemptionSstoreCharge, sstoreValueCost, hdirty, gasWarmAccess]

theorem redemptionSstoreCharge_cold_dirty
    {original current new : B256} (hdirty : original ≠ current) :
    redemptionSstoreCharge true original current new = 2200 := by
  simp [redemptionSstoreCharge, sstoreValueCost, hdirty, gasWarmAccess,
    gasColdSload]

theorem redemptionSstoreCharge_le
    (cold : Bool) (original current new : B256) :
    redemptionSstoreCharge cold original current new ≤
      redemptionStorageWriteWorstGas := by
  unfold redemptionSstoreCharge redemptionStorageWriteWorstGas
    sstoreValueCost
  split_ifs <;>
    norm_num [gasWarmAccess, gasColdSload, gasStorageSet, gasStorageUpdate]

@[simp] theorem redemptionChildSupplement_zero :
    redemptionChildSupplement 0 = 0 := by
  simp [redemptionChildSupplement]

theorem redemptionChildSupplement_of_ne {q : Nat} (hq : q ≠ 0) :
    redemptionChildSupplement q = 2300 := by
  simp [redemptionChildSupplement, hq, gCallStipend]

theorem redemptionChildSupplement_le_valueCharge (q : Nat) :
    redemptionChildSupplement q ≤ redemptionValueCallCharge q := by
  by_cases hq : q = 0
  · simp [hq, redemptionChildSupplement, redemptionValueCallCharge]
  · simp [hq, redemptionChildSupplement, redemptionValueCallCharge,
      gCallStipend, gasCallValue]

theorem redemptionModeledRuntime_zero :
    redemptionModeledRuntime 0 = 36998 := by
  decide

theorem redemptionModeledRuntime_of_ne {q : Nat} (hq : q ≠ 0) :
    redemptionModeledRuntime q = 70998 := by
  simp [redemptionModeledRuntime, redemptionSelectorDispatchGas,
    redemptionFixedModelGas, redemptionStorageReadWorstGas,
    redemptionStorageWriteWorstGas, redemptionCallWorstGas,
    redemptionSuccessTailGas, hq, gasColdSload, gasStorageSet,
    gasColdAccountAccess, gNewAccount, gasCallValue]

theorem redemptionExecutionGasFloor_eq :
    redemptionExecutionGasFloor = 100182 := by decide

theorem redemptionExecutionGasFloor_le_runtimeCeiling (q : Nat) :
    redemptionExecutionGasFloor ≤ redemptionRuntimeCeiling q :=
  Nat.le_max_left _ _

theorem redemptionRuntimeCeiling_eq (q : Nat) :
    redemptionRuntimeCeiling q = 100182 := by
  by_cases hq : q = 0
  · subst q
    simp [redemptionRuntimeCeiling, redemptionModeledRuntime_zero,
      redemptionExecutionGasFloor_eq]
  · rw [redemptionRuntimeCeiling, redemptionModeledRuntime_of_ne hq,
      redemptionExecutionGasFloor_eq]
    decide

/-! ## Success-free message envelope -/

/-- Fields common to the actual `withdrawTo` and `withdraw` message wrappers. -/
structure AdmissibleRedemptionMessageCore
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (w : State) (msg : Msg) : Prop where
  state_eq : msg.benv.state = w
  rules_eq : msg.benv.stat.rules = pragueRules
  target_eq : msg.target = some ca
  currentTarget_eq : msg.currentTarget = ca
  codeAddress_eq : msg.codeAddress = some ca
  code_eq : some msg.code.toList = Prog.compile (weth10 dp)
  installedCode_eq : msg.code = w.getCode ca
  caller_eq : msg.caller = owner
  value_eq : msg.value = 0
  depth_eq : msg.depth = 1024
  shouldTransferValue_eq : msg.shouldTransferValue = true
  isStatic_eq : msg.isStatic = false
  auths_eq : msg.tenv.stat.auths = []
  disablePrecompiles_eq : msg.disablePrecompiles = false
  target_not_precompile : pragueRules.isPrecomp ca = false
  recipient_ne_zero : recipient ≠ 0
  recipient_not_precompile : pragueRules.isPrecomp recipient = false
  recipient_code_free : (w.getCode recipient).toList = []
  original_storage_eq : msg.benv.stat.origState.getStor ca = w.getStor ca
  target_access : AddressAccessCase msg.accessedAddresses ca
  recipient_access : AddressAccessCase msg.accessedAddresses recipient
  owner_storage_access :
    StorageAccessCase msg.accessedStorageKeys ca owner.toB256
  recipient_account : RecipientAccountCase w recipient
  gas_bound : redemptionRuntimeCeiling q ≤ msg.gas

/-- Canonical generic `withdrawTo` envelope.  No field contains an execution
result, post-state, recipient-child success, or receipt. -/
structure AdmissibleRedemptionMessage
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (w : State) (msg : Msg) : Prop
    extends AdmissibleRedemptionMessageCore dp ca owner recipient q w msg where
  data_eq : msg.data = withdrawToCalldata recipient q
  selector_eq : Sevm.selector (initSevm msg) = withdrawToSelector

/-- Canonical direct-holder `withdraw` envelope. -/
structure AdmissibleSelfRedemptionMessage
    (dp : DeployParams) (ca owner : Adr) (q : Nat)
    (w : State) (msg : Msg) : Prop
    extends AdmissibleRedemptionMessageCore dp ca owner owner q w msg where
  data_eq : msg.data = withdrawCalldata q
  selector_eq : Sevm.selector (initSevm msg) = withdrawSelector

/-! ## Exact message result -/

structure MessageRedemptionExactEffect
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (w post : State) (out : MsgCallOutput) : Prop where
  outError : out.error = none
  ownerDebit :
    bookedBalanceNat post ca owner + q = bookedBalanceNat w ca owner
  otherBookedUnchanged :
    ∀ a, a ≠ owner →
      bookedBalanceNat post ca a = bookedBalanceNat w ca a
  contractEthDebit : (post.bal ca).toNat + q = (w.bal ca).toNat
  recipientEthCredit :
    (post.bal recipient).toNat = (w.bal recipient).toNat + q
  otherEthUnchanged :
    ∀ a, a ≠ ca → a ≠ recipient → post.bal a = w.bal a
  sumPreserved : sum post.bal = sum w.bal
  burnLog : out.logs = [redemptionBurnLog ca owner q]
  returnData : out.returnData = []
  codePreserved : ∀ a, post.getCode a = w.getCode a
  flashZero : (post.getStor ca).get flashMintedSlot = 0
  postStable : Stable dp ca post

def MessageRedemptionEnabled
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (w : State) (msg : Msg) : Prop :=
  ∃ post out,
    processMessageCall msg = .ok (post, out) ∧
    MessageRedemptionExactEffect dp ca owner recipient q w post out

/-! ## Success-free canonical type-2 transaction envelope -/

def redemptionTxPreludeBout
    (bout : BlockOutput) (tx : Tx) (index : Nat) : BlockOutput :=
  {bout with
    transactionsTrie :=
      bout.transactionsTrie.insert (BLT.bytes index.toBytes).toBytes tx}

def redemptionReceiptKey (index : Nat) : Bytes :=
  BLT.toBytes (.bytes index.toBytes)

def redemptionIntrinsicGas (tx : Tx) : Nat :=
  (calculateIntrinsicCost tx).1

def redemptionCalldataFloorGas (tx : Tx) : Nat :=
  (calculateIntrinsicCost tx).2

/-- The mandatory transaction budget: calldata-floor gas versus intrinsic gas
plus the complete caller-paid runtime ceiling. -/
def redemptionTransactionGasBound (q : Nat) (tx : Tx) : Nat :=
  max (redemptionCalldataFloorGas tx)
    (redemptionIntrinsicGas tx + redemptionRuntimeCeiling q)

def redemptionEffectiveGasPrice (benv : Benv) (tx : Tx) : Nat :=
  match tx.type with
  | .two _ maxPriorityFee maxFee _ _ =>
      min maxPriorityFee (maxFee - benv.stat.baseFeePerGas) +
        benv.stat.baseFeePerGas
  | _ => 0

def redemptionTxGasUsed (bout bout' : BlockOutput) : Nat :=
  bout'.blockGasUsed - bout.blockGasUsed

def redemptionGasRefund
    (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) : Nat :=
  (tx.gas - redemptionTxGasUsed bout bout') *
    redemptionEffectiveGasPrice benv tx

def redemptionPriorityFee
    (benv : Benv) (bout bout' : BlockOutput) (tx : Tx) : Nat :=
  redemptionTxGasUsed bout bout' *
    (redemptionEffectiveGasPrice benv tx - benv.stat.baseFeePerGas)

def redemptionBaseFeeBurn
    (benv : Benv) (bout bout' : BlockOutput) : Nat :=
  redemptionTxGasUsed bout bout' * benv.stat.baseFeePerGas

def redemptionUsedGasFromMessage
    (tx : Tx) (out : MsgCallOutput) (refundCounter : Nat) : Nat :=
  max
    (tx.gas - out.gasLeft -
      min ((tx.gas - out.gasLeft) / 5) refundCounter)
    (redemptionCalldataFloorGas tx)

def redemptionFinalState
    (benv : Benv) (tx : Tx) (owner : Adr)
    (messagePost : State) (usedGas : Nat) : State :=
  (messagePost.addBal owner
      ((tx.gas - usedGas) *
        redemptionEffectiveGasPrice benv tx).toB256).addBal
    benv.stat.coinbase
      (usedGas *
        (redemptionEffectiveGasPrice benv tx -
          benv.stat.baseFeePerGas)).toB256

def redemptionFinalBout
    (bout : BlockOutput) (tx : Tx) (index : Nat)
    (out : MsgCallOutput) (usedGas : Nat) : BlockOutput :=
  let prelude := redemptionTxPreludeBout bout tx index
  let charged :=
    {prelude with
      blockGasUsed := prelude.blockGasUsed + usedGas
      blobGasUsed := prelude.blobGasUsed}
  let receipt := makeReceipt tx out.error charged.blockGasUsed out.logs
  {charged with
    receiptKeys := charged.receiptKeys ++ [redemptionReceiptKey index]
    receiptsTrie := charged.receiptsTrie.insert
      (redemptionReceiptKey index) receipt
    blockLogs := charged.blockLogs ++ out.logs}

def redemptionTenv
    (benv : Benv) (tx : Tx) (owner : Adr) (index : Nat) : Tenv :=
  { transientStorage := .empty
    stat :=
      { origin := owner
        gasPrice := redemptionEffectiveGasPrice benv tx
        gas := tx.gas - redemptionIntrinsicGas tx
        accessListAddresses := .ofList [benv.stat.coinbase]
        accessListStorageKeys := .ofList []
        blobVersionedHashes := []
        auths := []
        indexInBlock := index
        txHash := getTxHash tx } }

def redemptionPreparedMessage
    (benv : Benv) (tx : Tx) (owner ca : Adr) (index : Nat)
    (debit : State) : Msg :=
  let tenv := redemptionTenv benv tx owner index
  let preparedBenv := {benv.beginTransaction with state := debit}
  { benv := preparedBenv
    tenv := tenv
    caller := owner
    target := some ca
    gas := tenv.stat.gas
    value := tx.value.toB256
    data := tx.data
    code := debit.getCode ca
    depth := 1024
    currentTarget := ca
    codeAddress := some ca
    shouldTransferValue := true
    isStatic := false
    accessedAddresses :=
      tenv.stat.accessListAddresses.insertMany
        (preparedBenv.stat.rules.precompiles ++ [owner, ca])
    accessedStorageKeys := tenv.stat.accessListStorageKeys
    disablePrecompiles := false }

/-- A fully formed type-2 envelope whose validation, recovery, fee, nonce,
target, access-list, and gas facts are explicit, but whose fields contain no
message execution or receipt result. -/
structure AdmissibleRedemptionTx
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) : Prop where
  rules_eq : benv.stat.rules = pragueRules
  type_eq : ∃ maxPriorityFee maxFee,
    tx.type = .two benv.stat.chainId maxPriorityFee maxFee (some ca) []
  data_eq : tx.data = withdrawToCalldata recipient q
  selector_eq : ∀ e : Sevm, e.data = tx.data →
    Sevm.selector e = withdrawToSelector
  value_eq : tx.value = 0
  nonce_eq : tx.nonce = benv.state.getNonce owner
  nonce_not_max : tx.nonce ≠ UInt64.max
  recoveredSender : recoverSender benv.stat.chainId tx = .ok owner
  owner_ne_zero : owner ≠ 0
  owner_code_free : (benv.state.getCode owner).toList = []
  validated :
    validateTransaction pragueRules tx = .ok (calculateIntrinsicCost tx)
  checked :
    checkTransaction benv.beginTransaction
      (redemptionTxPreludeBout bout tx index) tx =
      .ok (owner, redemptionEffectiveGasPrice benv tx, [], 0)
  base_fee_le_effective :
    benv.stat.baseFeePerGas ≤ redemptionEffectiveGasPrice benv tx
  upfront_funded :
    tx.gas * redemptionEffectiveGasPrice benv tx ≤
      (benv.state.bal owner).toNat
  gas_bound : redemptionTransactionGasBound q tx ≤ tx.gas
  block_gas_room :
    tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed
  target_code :
    some (benv.state.getCode ca).toList = Prog.compile (weth10 dp)
  target_not_precompile : pragueRules.isPrecomp ca = false
  target_not_created : ca ∉ benv.createdAccounts
  recipient_ne_zero : recipient ≠ 0
  recipient_not_precompile : pragueRules.isPrecomp recipient = false
  recipient_code_free : (benv.state.getCode recipient).toList = []
  recipient_account : RecipientAccountCase benv.state recipient

/-! ## Exact transaction result and fee accounting -/

/-- The message-level execution extracted while inverting a successful
transaction.  Unlike `AdmissibleRedemptionTx`, this is conclusion evidence and
therefore intentionally contains the constructed message success. -/
structure TransactionRedemptionTrace
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) : Prop where
  execution :
    ∃ intrinsicGas calldataFloorGasCost effectiveGasPrice
        debitState msg messagePost messageOut,
      validateTransaction pragueRules tx =
          .ok (intrinsicGas, calldataFloorGasCost) ∧
      checkTransaction benv.beginTransaction
          (redemptionTxPreludeBout bout tx index) tx =
          .ok (owner, effectiveGasPrice, [], 0) ∧
      (benv.state.incrNonce owner).subBal owner
          (tx.gas * effectiveGasPrice).toB256 = some debitState ∧
      prepareMessage {benv.beginTransaction with state := debitState}
          { transientStorage := .empty
            stat :=
              { origin := owner
                gasPrice := effectiveGasPrice
                gas := tx.gas - intrinsicGas
                accessListAddresses := .ofList [benv.stat.coinbase]
                accessListStorageKeys := .ofList []
                blobVersionedHashes := []
                auths := []
                indexInBlock := index
                txHash := getTxHash tx } }
          tx = .ok msg ∧
      processMessageCall msg = .ok (messagePost, messageOut) ∧
      MessageRedemptionExactEffect
        dp ca owner recipient q debitState messagePost messageOut

/-- Alias-safe per-address accounting.  Equalities remain valid when the
coinbase aliases any participant and when `owner = recipient`; the global row
names the base-fee burn separately. -/
structure TransactionEthAccounting
    (_dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (_index : Nat)
    (post : State) (bout' : BlockOutput) : Prop where
  perAddress :
    ∀ a,
      (post.bal a).toNat +
          (if a = owner then
            tx.gas * redemptionEffectiveGasPrice benv tx
          else 0) +
          (if a = ca then q else 0) =
        (benv.state.bal a).toNat +
          (if a = recipient then q else 0) +
          (if a = owner then redemptionGasRefund benv bout bout' tx else 0) +
          (if a = benv.stat.coinbase then
            redemptionPriorityFee benv bout bout' tx
          else 0)
  totalAfterBaseFeeBurn :
    sum post.bal + redemptionBaseFeeBurn benv bout bout' =
      sum benv.state.bal

structure TransactionRedemptionExactEffect
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat)
    (post : State) (bout' : BlockOutput) : Prop where
  trace : TransactionRedemptionTrace
    dp ca owner recipient q benv bout tx index
  receiptAt : ∃ receipt,
    Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index) =
      some ((2 : Fin 5), receipt)
  receiptSucceeded :
    (Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index)).map
      (fun entry => entry.2.succeeded) = some true
  receiptLogs :
    (Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index)).map
      (fun entry => entry.2.logs) = some [redemptionBurnLog ca owner q]
  ownerDebit :
    bookedBalanceNat post ca owner + q =
      bookedBalanceNat benv.state ca owner
  otherBookedUnchanged :
    ∀ a, a ≠ owner →
      bookedBalanceNat post ca a = bookedBalanceNat benv.state ca a
  codePreserved : ∀ a, post.getCode a = benv.state.getCode a
  flashZero : (post.getStor ca).get flashMintedSlot = 0
  postStable : Stable dp ca post
  ethAccounting :
    TransactionEthAccounting
      dp ca owner recipient q benv bout tx index post bout'

def TransactionRedemptionEnabled
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (benv : Benv) (bout : BlockOutput) (tx : Tx) (index : Nat) : Prop :=
  ∃ post bout',
    processTransaction benv bout tx index = .ok (post, bout') ∧
    TransactionRedemptionExactEffect
      dp ca owner recipient q benv bout tx index post bout'

/-! ## Transaction preprocessing -/

structure TransactionDebitOutcome
    (owner : Adr) (fee : Nat) (w debit : State) : Prop where
  subBal :
    (w.incrNonce owner).subBal owner fee.toB256 = some debit
  feeEncoded : fee.toB256.toNat = fee
  storagePreserved : ∀ a, debit.getStor a = w.getStor a
  codePreserved : ∀ a, debit.getCode a = w.getCode a
  otherBalancePreserved : ∀ a, a ≠ owner → debit.bal a = w.bal a
  ownerDebit : (debit.bal owner).toNat + fee = (w.bal owner).toNat
  sumDebit : sum debit.bal + fee = sum w.bal

theorem AdmissibleRedemptionTx.upfrontDebit_exists
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index) :
    ∃ debit,
      TransactionDebitOutcome owner
        (tx.gas * redemptionEffectiveGasPrice benv tx)
        benv.state debit := by
  let fee := tx.gas * redemptionEffectiveGasPrice benv tx
  have hfee_le : fee ≤ (benv.state.bal owner).toNat := by
    exact henv.upfront_funded
  have hfee_lt : fee < 2 ^ 256 :=
    hfee_le.trans_lt (B256.toNat_lt _)
  have hfeeEncoded : fee.toB256.toNat = fee :=
    B256.toNat_toB256_of_lt hfee_lt
  have hnotlt : ¬ (benv.state.incrNonce owner).bal owner < fee.toB256 := by
    rw [B256.lt_iff_toNat_lt_toNat, hfeeEncoded]
    change ¬ ((benv.state.incrNonce owner).get owner).bal.toNat < fee
    rw [State.incrNonce_get_bal]
    exact not_lt_of_ge hfee_le
  have hsub : (benv.state.incrNonce owner).subBal owner fee.toB256 =
      some ((benv.state.incrNonce owner).setBal owner
        ((benv.state.incrNonce owner).bal owner - fee.toB256)) := by
    unfold State.subBal
    rw [if_neg hnotlt]
  let debit := (benv.state.incrNonce owner).setBal owner
    ((benv.state.incrNonce owner).bal owner - fee.toB256)
  have hsub' : (benv.state.incrNonce owner).subBal owner fee.toB256 =
      some debit := hsub
  refine ⟨debit, hsub', hfeeEncoded, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    dsimp only [debit]
    change (((benv.state.incrNonce owner).setBal owner _).get a).stor = _
    rw [State.setBal_get_stor, State.incrNonce_get_stor]
    rfl
  · intro a
    dsimp only [debit]
    change (((benv.state.incrNonce owner).setBal owner _).get a).code = _
    rw [State.setBal_get_code, State.incrNonce_get_code]
    rfl
  · intro a hne
    dsimp only [debit]
    change (((benv.state.incrNonce owner).setBal owner _).get a).bal = _
    rw [State.setBal_get_ne hne.symm, State.incrNonce_get_bal]
    rfl
  · dsimp only [debit]
    change
      (((benv.state.incrNonce owner).setBal owner _).get owner).bal.toNat +
          fee = (benv.state.get owner).bal.toNat
    rw [State.setBal_get_self]
    change
      ((benv.state.incrNonce owner).bal owner - fee.toB256).toNat +
          fee = (benv.state.bal owner).toNat
    have hb256le : fee.toB256 ≤ (benv.state.incrNonce owner).bal owner := by
      rw [B256.le_iff_toNat_le_toNat, hfeeEncoded]
      change fee ≤ ((benv.state.incrNonce owner).get owner).bal.toNat
      rw [State.incrNonce_get_bal]
      exact hfee_le
    rw [B256.toNat_sub_eq_of_le _ _ hb256le,
      hfeeEncoded, State.incrNonce_bal]
    exact Nat.sub_add_cancel hfee_le
  · have hsum := State.balSum_subBal hsub'
    rw [hfeeEncoded] at hsum
    simpa [State.balSum, State.incrNonce_bal, fee] using hsum

/-! ## Individual capacity and no-wrap projection -/

/-- Stable aggregate backing bounds every individual booked balance. -/
theorem Stable.bookedBalanceNat_le_contractEth
    {dp : DeployParams} {ca owner : Adr} {w : State}
    (hstable : Stable dp ca w) :
    bookedBalanceNat w ca owner ≤ (w.bal ca).toNat := by
  exact (Blanc.le_sum (f := Stor.rest (w.getStor ca))
    (k := owner)).trans hstable.solvent

/-- Every natural amount admitted by the public balance bound encodes into
`B256` without wrapping. -/
theorem Stable.amount_lt_modulus_of_le
    {dp : DeployParams} {ca owner : Adr} {q : Nat} {w : State}
    (_hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner) :
    q < 2 ^ 256 := by
  exact lt_of_le_of_lt hq (B256.toNat_lt _)

/-- The public byte encoder's two static words are the recipient and natural
amount consumed by the compiled `withdrawTo` body. -/
theorem withdrawToCalldata_argWords (e : Sevm) (recipient : Adr) (q : Nat)
    (hdata : e.data = withdrawToCalldata recipient q) :
    Sevm.argWord e 0 = recipient.toB256 ∧
      Sevm.argWord e 1 = q.toB256 := by
  constructor
  · exact dataWord_of_append
      (e := e) (idx := (32 * 0 + 4 : B256))
      (pre := abiSelectorBytes withdrawToSelector)
      (w := recipient.toB256) (post := q.toB256.toBytes)
      (by rw [abiSelectorBytes_length]; rfl)
      (by simpa [withdrawToCalldata, List.append_assoc] using hdata)
  · exact dataWord_of_append
      (idx := (32 * 1 + 4 : B256))
      (pre := abiSelectorBytes withdrawToSelector ++ recipient.toB256.toBytes)
      (post := [])
      (by rw [List.length_append, abiSelectorBytes_length,
          B256.length_toBytes]; rfl)
      (by simpa [withdrawToCalldata, List.append_assoc] using hdata)

/-- The direct-holder encoder's static word is the natural amount consumed by
the actual `withdraw` body. -/
theorem withdrawCalldata_argWord (e : Sevm) (q : Nat)
    (hdata : e.data = withdrawCalldata q) : Sevm.argWord e 0 = q.toB256 := by
  exact dataWord_of_append
    (e := e) (idx := (32 * 0 + 4 : B256))
    (pre := abiSelectorBytes withdrawSelector)
    (w := q.toB256) (post := [])
    (by rw [abiSelectorBytes_length]; rfl)
    (by simpa [withdrawCalldata, List.append_assoc] using hdata)

/-- The stack image produced by walking an `arg` instruction. -/
lemma Sevm.argWord_eq_dataWord {e : Sevm} {k : B256} :
    Sevm.argWord e k = Sevm.dataWord e (32 * k + 4) := rfl

/-- Exact frame-local observations supplied by a successful code-free value
call.  The transfer witness names the semantic debit state instead of assuming
that the child succeeded. -/
structure RedemptionCallEffect (e : Sevm) (pre post : Devm)
    (recipient : Adr) (value : B256) : Prop where
  error : post.error = pre.error
  output : post.output = pre.output
  returnData : post.returnData = []
  logs : post.logs = pre.logs
  refund : post.refundCounter = pre.refundCounter
  accountsToDeleteEmpty :
    post.accountsToDelete.isEmpty = pre.accountsToDelete.isEmpty
  transfer : ∃ debit,
    pre.state.subBal e.currentTarget value = some debit ∧
      post.state = debit.addBal recipient value

/-- The code-altitude result retained for the ordinary message wrapper. -/
structure RedemptionCodeOutcome (e : Sevm) (pre post : Devm)
    (owner recipient : Adr) (amount : B256) : Prop where
  error : post.error = pre.error
  output : post.output = pre.output
  returnData : post.returnData = []
  logs : post.logs = pre.logs ++
    [ordinaryTransferLog e owner.toB256 0 amount]
  refundNonnegative : 0 ≤ post.refundCounter
  accountsToDeleteEmpty :
    post.accountsToDelete.isEmpty = pre.accountsToDelete.isEmpty
  storageDebit :
    post.getStorVal e.currentTarget owner.toB256 =
      pre.getStorVal e.currentTarget owner.toB256 - amount
  storageOther : ∀ a k, (a, k) ≠ (e.currentTarget, owner.toB256) →
    post.getStorVal a k = pre.getStorVal a k
  transfer : ∃ (callState debit : State),
    (∀ a, callState.bal a = pre.getBal a) ∧
    (∀ a, callState.getCode a = pre.getCode a) ∧
    callState.subBal e.currentTarget amount = some debit ∧
    post.state = debit.addBal recipient amount

lemma RedemptionCodeOutcome.of_setMach {e : Sevm} {pre post : Devm}
    {owner recipient : Adr} {amount : B256} {mach : Mach}
    (h : RedemptionCodeOutcome e (pre.setMach mach) post
      owner recipient amount) :
    RedemptionCodeOutcome e pre post owner recipient amount := by
  rcases h with
    ⟨herror, houtput, hreturnData, hlogs, hrefund, hdelete, hdebit, hother,
      htransfer⟩
  exact ⟨herror, houtput, hreturnData, hlogs, hrefund, hdelete, hdebit, hother,
    htransfer⟩

/-- An `SSTORE` starting from the original value and a zero refund counter
cannot make that counter negative, regardless of the new value. -/
lemma sstoreNewRefundCounter_nonnegative_of_original_eq_current
    {original current new : B256} (h : original = current) :
    0 ≤ sstoreNewRefundCounter new original current 0 := by
  subst original
  unfold sstoreNewRefundCounter
  split_ifs <;> norm_num [rSClear, gasStorageSet, gasWarmAccess,
    gasStorageUpdate, gasColdSload] at *

/-! ## Constructive withdrawal body up to the value call -/

/-- The real `withdrawTo` body reaches its internal `CALL` after debiting the
caller's booked balance and emitting the burn log.  Balance/code observations
are transported to this exact point, which is where stable backing discharges
the call sender-affordability branch. -/
theorem withdrawTo_runCompiledTo_callPrefix
    {fs : List Func} {e : Sevm} {pre : Devm} {out : Execution}
    (h_amount : Sevm.argWord e 1 ≤
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_static : e.isStatic = false)
    (h_gas : 100000 ≤ pre.gasLeft)
    (h_cont : ∀ (b : Devm) (G : Nat),
      b.getStorVal e.currentTarget e.caller.toB256 =
          pre.getStorVal e.currentTarget e.caller.toB256 - Sevm.argWord e 1 →
      (∀ (a : Adr) (k : B256),
        (a, k) ≠ (e.currentTarget, e.caller.toB256) →
          b.getStorVal a k = pre.getStorVal a k) →
      (∀ a : Adr, b.getBal a = pre.getBal a) →
      (∀ a : Adr, b.getCode a = pre.getCode a) →
      b.logs = pre.logs ++
        [ordinaryTransferLog e e.caller.toB256 0 (Sevm.argWord e 1)] →
      50000 ≤ G → G ≤ pre.gasLeft →
      Func.RunCompiledTo fs e
        (b.setMach ⟨[
          Nat.toB256 G, Sevm.argWord e 0, Sevm.argWord e 1,
          0, 0, 0, 0],
          Mem.empty.write 0 (Sevm.argWord e 1).toBytes, G⟩)
        (Ninst.call ::: (Ninst.iszero :::
          (.call ethTransferErrorSlot) <?> Func.stop)) out) :
    Func.RunCompiledTo fs e
      (pre.setMach ⟨[], Mem.empty, pre.gasLeft⟩) withdrawTo out := by
  simp only [withdrawTo]
  func_run (2)
  refine Func.runCompiledTo_sload_step rfl (by simp)
    (v := pre.getStorVal e.currentTarget e.caller.toB256) rfl
    (M := Mem.empty) ?_ ?_ ?_
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload]
    omega
  · intro b₁ c₁ G₁ hw₁ hacc₁ hstor₁ hbal₁ hcode₁ hrc₁ hlog₁ hlo₁ hhi₁ hG₁
    simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload]
      at hG₁ hlo₁ hhi₁
    func_run (9) [0]
    · show (if pre.getStorVal e.currentTarget e.caller.toB256 <
          Sevm.argWord e 1 then (1 : B256) else 0) = 0
      rw [if_neg (not_lt_of_ge h_amount)]
    refine Func.runCompiledTo_sstore_warm_step rfl hw₁ h_static
      (M := Mem.empty) rfl
      (by simp only [Devm.gasLeft_setMach, gasStorageSet]; omega) ?_
    intro b₂ c₂ G₂ hkey₂ hoth₂ hbal₂ hcode₂ hacc₂ hlog₂ hc₂ hG₂
    simp only [Devm.gasLeft_setMach, gasStorageSet] at hG₂ hc₂
    func_run (11) [gMemory]
    · exact Devm.extCost_empty_word
    refine Func.runCompiledTo_log_step
      (topics := [transferEvent, e.caller.toB256, 0])
      (s := [Sevm.argWord e 1, e.caller.toB256]) rfl rfl h_static
      (M := Mem.empty.write 0 (Sevm.argWord e 1).toBytes) rfl
      (c := 1756) (payload := (Sevm.argWord e 1).toBytes)
      (M' := Mem.empty.write 0 (Sevm.argWord e 1).toBytes) ?_ ?_ ?_
      (by simp only [Devm.gasLeft_setMach]; omega) ?_
    · exact Devm.extCost_add_of_size Mem.size_write_word (by decide)
    · exact Mem.read_write_word
    · exact Mem.read_snd_eq_self (by rw [Mem.size_write_word]; decide)
    · intro b₃ G₃ hlogs₃ hstor₃ hbal₃ hcode₃ hacc₃ hG₃
      simp only [Devm.gasLeft_setMach] at hG₃
      func_run (20)
      rw [← Sevm.argWord_eq_dataWord]
      simp only [prepend]
      refine h_cont b₃ (G₃ - 24) ?_ ?_ ?_ ?_ ?_ (by omega) (by omega)
      · simp only [hstor₃, Devm.getStorVal_setMach, hkey₂,
          ← Sevm.argWord_eq_dataWord]
      · intro a k hne
        simp only [hstor₃, Devm.getStorVal_setMach, hoth₂ _ _ hne,
          hstor₁]
      · intro a
        exact (hbal₃ a).trans ((hbal₂ a).trans (hbal₁ a))
      · intro a
        exact (hcode₃ a).trans ((hcode₂ a).trans (hcode₁ a))
      · let l : Log :=
          ⟨e.currentTarget, [transferEvent, e.caller.toB256, 0],
            (Sevm.argWord e 1).toBytes⟩
        calc
          b₃.logs = b₂.logs ++ [l] := hlogs₃
          _ = b₁.logs ++ [l] := congrArg (fun xs => xs ++ [l]) hlog₂
          _ = pre.logs ++ [l] := congrArg (fun xs => xs ++ [l]) hlog₁
          _ = pre.logs ++
              [ordinaryTransferLog e e.caller.toB256 0 (Sevm.argWord e 1)] := rfl

/-- A successful internal call flag makes the withdrawal's post-call guard take
the `STOP` branch. -/
lemma callSuccessTail_runCompiled {fs : List Func} {e : Sevm} {d : Devm}
    (hstack : d.stack = [1]) (hgas : 16 ≤ d.gasLeft) :
    ∃ out, Func.RunCompiled fs e d
      (Ninst.iszero ::: (.call ethTransferErrorSlot) <?> Func.stop) out ∧
      out.error = d.error ∧ out.output = d.output ∧
      out.returnData = d.returnData ∧ out.logs = d.logs ∧
      out.refundCounter = d.refundCounter ∧
      out.accountsToDelete = d.accountsToDelete ∧
      out.state = d.state := by
  have hd : d = d.setMach ⟨[1], d.memory, d.gasLeft⟩ := by
    apply Devm.eq_of_proj
    · exact hstack
    all_goals rfl
  rw [hd]
  let out := d.setMach ⟨[], d.memory, d.gasLeft - 16⟩
  refine ⟨out, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  func_run [0]
  · simp [out]
    exact .last rfl

/-- A call state built by either withdrawal body crosses an EOA recipient and
returns the success flag with enough gas to execute the body guard.  The proof
enumerates the zero- and nonzero-value schedules separately; the latter charges
the cold-access, new-account and value-transfer maxima before using the child
stipend exactly once. -/
lemma redemptionCall_runCompiled {e : Sevm} {b : Devm}
    {G : Nat} {recipient : Adr} {value : B256}
    (h_static : e.isStatic = false)
    (h_depth : e.depth ≠ 0)
    (h_nonprecompile : e.benvStat.rules.isPrecomp recipient = false)
    (h_code : (b.getCode recipient).size = 0)
    (h_sender : ¬ b.getBal e.currentTarget < value)
    (h_gas : 50000 ≤ G) :
    ∃ post,
      Ninst.RunCompiled e
        (b.setMach ⟨[
          Nat.toB256 G, recipient.toB256, value, 0, 0, 0, 0],
          Mem.empty.write 0 value.toBytes, G⟩)
        (.exec .call) post ∧ post.stack = [1] ∧ 16 ≤ post.gasLeft ∧
        RedemptionCallEffect e b post recipient value := by
  let d := b.setMach ⟨[
    Nat.toB256 G, recipient.toB256, value, 0, 0, 0, 0],
    Mem.empty.write 0 value.toBytes, G⟩
  let d0 := addAccessedAddress
    (d.setMach ⟨[], d.memory, d.gasLeft⟩) recipient
  rcases hdel : accessDelegation d0 recipient with ⟨dp, dadr, code, dgc, d1⟩
  obtain ⟨_hd1s, _hd1m, hd1g, hdgc⟩ := accessDelegation_inv hdel
  have hd1g' : d1.gasLeft = G := by
    rw [hd1g]
    rfl
  have hd1state : d1.state = d0.state := by
    have hs := accessDelegation_state (devm := d0) (adr := recipient)
    rw [hdel] at hs
    exact hs
  have hd0state : d0.state = b.state := rfl
  have hd1bal : d1.getBal e.currentTarget = b.getBal e.currentTarget := by
    exact getBal_eq_of_state_eq (hd1state.trans hd0state) _
  have h_sender' : ¬ d1.getBal e.currentTarget < value := by
    rw [hd1bal]
    exact h_sender
  have hnotdel : ¬ isValidDelegation (d0.state.getCode recipient) := by
    intro hv
    have hs := hv.1
    change (b.getCode recipient).size = eoaDelegatedCodeLength at hs
    rw [h_code] at hs
    norm_num [eoaDelegatedCodeLength] at hs
  have hcodeeq : code = d0.state.getCode recipient := by
    have hc := accessDelegation_code_of_not hnotdel
    rw [hdel] at hc
    exact hc
  have hcode0 : code.size = 0 := by
    rw [hcodeeq]
    change (b.getCode recipient).size = 0
    exact h_code
  have hext :
      (d.setMach ⟨[], d.memory, d.gasLeft⟩).extCost
        [⟨(0 : B256).toNat, (0 : B256).toNat⟩,
          ⟨(0 : B256).toNat, (0 : B256).toNat⟩] = 0 := by
    rw [show (0 : B256).toNat = 0 from by decide]
    change calculateMemoryGasCost
        (memExtsSize d.memory.size [(0, 0), (0, 0)]) -
      calculateMemoryGasCost d.memory.size = 0
    simp [memExtsSize, memExtSize]
  let acc := accessCost recipient
    (d.setMach ⟨[], d.memory, d.gasLeft⟩).accessedAddresses + dgc
  have hacc :
      accessCost recipient
        (d.setMach ⟨[], d.memory, d.gasLeft⟩).accessedAddresses + dgc = acc := rfl
  have hacc_le : acc ≤ 5200 := by
    have ha := accessCost_le
      (x := recipient)
      (a := (d.setMach ⟨[], d.memory, d.gasLeft⟩).accessedAddresses)
    have hsum : acc ≤ gasColdAccountAccess + gasColdAccountAccess := by
      exact Nat.add_le_add ha hdgc
    norm_num [gasColdAccountAccess] at hsum
    exact hsum
  by_cases hv : value = 0
  · subst value
    have hafford : acc + 0 ≤ d1.gasLeft := by
      rw [hd1g']
      omega
    rcases hsplit : calculateMsgCallGas 0 (Nat.toB256 G).toNat d1.gasLeft 0 acc
        with ⟨mcc, mcs⟩
    have hcost : mcc + 0 ≤ d1.gasLeft := by
      have hc := calculateMsgCallGas_cost_le
        (value := 0) (gas := (Nat.toB256 G).toNat)
        (gasLeft := d1.gasLeft) (mem := 0) (extra := acc) hafford
      rw [hsplit] at hc
      exact hc
    have hret := le_retained_of_calculateMsgCallGas_zero hafford hsplit
    have hdel' : accessDelegation
        (addAccessedAddress
          (d.setMach ⟨[], d.memory, d.gasLeft⟩) recipient.toB256.toAdr)
          recipient.toB256.toAdr = ⟨dp, dadr, code, dgc, d1⟩ := by
      simpa only [toAdr_toB256] using hdel
    rcases Ninst.runCompiled_call_zero_value_codeFree
        (sevm := e) (devm := d)
        (dp := dp) (dadr := dadr) (code := code) (dgc := dgc) (d1 := d1)
        (ext := 0) (acc := acc) (mcc := mcc) (mcs := mcs)
        rfl hext hdel' (by simpa only [toAdr_toB256] using hacc.symm)
        hsplit hcost h_depth
        (by simpa only [toAdr_toB256] using h_nonprecompile) hcode0
        (by decide) with
          ⟨post, hrun, hstack, _hmem, hpostgas, herr, hout, hreturn,
            hlogs, hrefund, hdelete, debit, hsub, hstate⟩
    refine ⟨post, hrun, hstack, ?_, ?_⟩
    · rw [hpostgas, hd1g'] at *
      have hret16 : 16 ≤ (G - 0 - acc) / 64 := by omega
      omega
    · refine ⟨?_, ?_, hreturn, ?_, ?_, ?_, debit, ?_, ?_⟩
      · change post.error = b.error at herr
        exact herr
      · change post.output = b.output at hout
        exact hout
      · change post.logs = b.logs at hlogs
        exact hlogs
      · change post.refundCounter = b.refundCounter at hrefund
        exact hrefund
      · exact hdelete
      · change b.state.subBal e.currentTarget 0 = some debit at hsub
        exact hsub
      · simpa only [toAdr_toB256] using hstate
  · let create := if ¬ (d1.getAcct recipient).Empty then 0 else gNewAccount
    have hcreate :
        (if ¬ (d1.getAcct recipient).Empty then 0 else gNewAccount) = create := rfl
    have hcreate_le : create ≤ 25000 := by
      dsimp only [create]
      split <;> norm_num [gNewAccount]
    have hafford : acc + create + gasCallValue + 0 ≤ d1.gasLeft := by
      rw [hd1g']
      norm_num [gasCallValue]
      omega
    rcases hsplit : calculateMsgCallGas value.toNat (Nat.toB256 G).toNat
        d1.gasLeft 0 (acc + create + gasCallValue) with ⟨mcc, mcs⟩
    have hcost_full :
        (calculateMsgCallGas value.toNat (Nat.toB256 G).toNat
          d1.gasLeft 0 (acc + create + gasCallValue)).1 + 0 ≤ d1.gasLeft := by
      exact calculateMsgCallGas_cost_le
        (value := value.toNat) (gas := (Nat.toB256 G).toNat)
        (gasLeft := d1.gasLeft) (mem := 0)
        (extra := acc + create + gasCallValue) hafford
    have hcost : mcc + 0 ≤ d1.gasLeft := by
      have hc := hcost_full
      rw [hsplit] at hc
      exact hc
    have hstip := calculateMsgCallGas_stipend hcost_full
    rw [hsplit] at hstip
    rcases hstip with ⟨avail, hmcs⟩
    have hvnat : value.toNat ≠ 0 := by
      intro h
      apply hv
      exact B256.toNat_inj value 0 (by
        calc
          value.toNat = 0 := h
          _ = (0 : B256).toNat := by decide)
    have hmcs16 : 16 ≤ mcs := by
      change mcs = min (Nat.toB256 G).toNat (except64th avail) +
        (if value.toNat = 0 then 0 else gCallStipend) at hmcs
      rw [hmcs, if_neg hvnat]
      norm_num [gCallStipend]
    have hdel' : accessDelegation
        (addAccessedAddress
          (d.setMach ⟨[], d.memory, d.gasLeft⟩) recipient.toB256.toAdr)
          recipient.toB256.toAdr = ⟨dp, dadr, code, dgc, d1⟩ := by
      simpa only [toAdr_toB256] using hdel
    rcases Ninst.runCompiled_call_nonzero_codeFree
        (sevm := e) (devm := d)
        (dp := dp) (dadr := dadr) (code := code) (dgc := dgc) (d1 := d1)
        (ext := 0) (acc := acc) (create := create)
        (mcc := mcc) (mcs := mcs)
        rfl hv hext hdel' (by simpa only [toAdr_toB256] using hacc.symm)
        (by simpa only [toAdr_toB256] using hcreate) hsplit hcost
        h_static h_sender' h_depth
        (by simpa only [toAdr_toB256] using h_nonprecompile) hcode0 (by decide)
        with ⟨post, hrun, hstack, _hmem, hpostgas, herr, hout, hreturn,
          hlogs, hrefund, hdelete, debit, hsub, hstate⟩
    refine ⟨post, hrun, hstack, ?_, ?_⟩
    · rw [hpostgas]
      omega
    · refine ⟨?_, ?_, hreturn, ?_, ?_, ?_, debit, ?_, ?_⟩
      · change post.error = b.error at herr
        exact herr
      · change post.output = b.output at hout
        exact hout
      · change post.logs = b.logs at hlogs
        exact hlogs
      · change post.refundCounter = b.refundCounter at hrefund
        exact hrefund
      · exact hdelete
      · change b.state.subBal e.currentTarget value = some debit at hsub
        exact hsub
      · simpa only [toAdr_toB256] using hstate

/-- The actual compiled `withdrawTo` body reaches a successful outcome for an
admitted code-free recipient.  `ExecSat` keeps that outcome existential while
the storage/log walk introduces its deterministic intermediate states. -/
theorem withdrawTo_execSat {fs : List Func} {e : Sevm} {pre : Devm}
    {recipient : Adr} {P : Execution → Prop}
    (h_recipient : Sevm.argWord e 0 = recipient.toB256)
    (h_amount : Sevm.argWord e 1 ≤
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_static : e.isStatic = false)
    (h_depth : e.depth ≠ 0)
    (h_nonprecompile : e.benvStat.rules.isPrecomp recipient = false)
    (h_code : (pre.getCode recipient).size = 0)
    (h_sender : ¬ pre.getBal e.currentTarget < Sevm.argWord e 1)
    (h_original : getOrigStorVal e e.currentTarget e.caller.toB256 =
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_refund : pre.refundCounter = 0)
    (h_gas : 100000 ≤ pre.gasLeft)
    (hP : ∀ post : Devm,
      RedemptionCodeOutcome e pre post e.caller recipient
        (Sevm.argWord e 1) → P (.ok post)) :
    Func.ExecSat fs e
      (pre.setMach ⟨[], Mem.empty, pre.gasLeft⟩) withdrawTo P := by
  simp only [withdrawTo]
  apply Func.execSat_segment
  · intro ex hex
    func_run (2)
    exact hex
  refine Func.execSat_sload_step rfl (by simp)
    (v := pre.getStorVal e.currentTarget e.caller.toB256) rfl
    (M := Mem.empty) ?_ ?_ ?_
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload]
    omega
  · intro b₁ c₁ G₁ hw₁ _hacc₁ hstor₁ hbal₁ hcode₁ hrc₁ hlog₁
      hout₁ herr₁ hdelete₁ hlo₁ hhi₁ hG₁
    simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload]
      at hG₁ hlo₁ hhi₁
    apply Func.execSat_segment
    · intro ex hex
      func_run (9) [0]
      · show (if pre.getStorVal e.currentTarget e.caller.toB256 <
            Sevm.argWord e 1 then (1 : B256) else 0) = 0
        rw [if_neg (not_lt_of_ge h_amount)]
      exact hex
    refine Func.execSat_sstore_warm_step rfl hw₁ h_static
      (M := Mem.empty) rfl
      (by simp only [Devm.gasLeft_setMach, gasStorageSet]; omega) ?_
    intro b₂ c₂ G₂ hkey₂ hoth₂ hbal₂ hcode₂ _hacc₂ hlog₂ hout₂
      herr₂ hdelete₂ hrefund₂ hc₂ hG₂
    simp only [Devm.gasLeft_setMach, gasStorageSet] at hG₂ hc₂
    apply Func.execSat_segment
    · intro ex hex
      func_run (11) [gMemory]
      · exact Devm.extCost_empty_word
      exact hex
    refine Func.execSat_log_step
      (topics := [transferEvent, e.caller.toB256, 0])
      (s := [Sevm.argWord e 1, e.caller.toB256]) rfl rfl h_static
      (M := Mem.empty.write 0 (Sevm.argWord e 1).toBytes) rfl
      (c := 1756) (payload := (Sevm.argWord e 1).toBytes)
      (M' := Mem.empty.write 0 (Sevm.argWord e 1).toBytes) ?_ ?_ ?_
      (by simp only [Devm.gasLeft_setMach]; omega) ?_
    · exact Devm.extCost_add_of_size Mem.size_write_word (by decide)
    · exact Mem.read_write_word
    · exact Mem.read_snd_eq_self (by rw [Mem.size_write_word]; decide)
    · intro b₃ G₃ hlogs₃ hstor₃ hbal₃ hcode₃ _hacc₃ hrefund₃
        hout₃ herr₃ hdelete₃ hG₃
      simp only [Devm.gasLeft_setMach] at hG₃
      apply Func.execSat_segment
      · intro ex hex
        func_run (20)
        rw [← Sevm.argWord_eq_dataWord]
        simp only [prepend]
        exact hex
      have hbal : ∀ a : Adr, b₃.getBal a = pre.getBal a := fun a =>
        (hbal₃ a).trans ((hbal₂ a).trans (hbal₁ a))
      have hcode : ∀ a : Adr, b₃.getCode a = pre.getCode a := fun a =>
        (hcode₃ a).trans ((hcode₂ a).trans (hcode₁ a))
      have hbcode : (b₃.getCode recipient).size = 0 := by
        rw [hcode recipient]
        exact h_code
      have hbsender : ¬ b₃.getBal e.currentTarget < Sevm.argWord e 1 := by
        rw [hbal e.currentTarget]
        exact h_sender
      rcases redemptionCall_runCompiled
          (e := e) (b := b₃) (G := G₃ - 24) (recipient := recipient)
          (value := Sevm.argWord e 1) h_static h_depth h_nonprecompile hbcode
          hbsender (by omega) with
            ⟨callPost, hcall, hstack, hpostgas, hcallEffect⟩
      have hcall' : Ninst.RunCompiled e
          (b₃.setMach ⟨[
            Nat.toB256 (G₃ - 24), Sevm.argWord e 0, Sevm.argWord e 1,
            0, 0, 0, 0],
            Mem.empty.write 0 (Sevm.argWord e 1).toBytes, G₃ - 24⟩)
          (.exec .call) callPost := by
        simpa only [h_recipient] using hcall
      refine Func.execSat_next hcall' ?_
      rcases callSuccessTail_runCompiled
          (fs := fs) hstack hpostgas with
        ⟨post, htail, htailError, htailOutput, htailReturnData,
          htailLogs, htailRefund, htailDelete, htailState⟩
      rcases hcallEffect.transfer with ⟨debit, hsub, hcallState⟩
      have htransferFields :=
        of_state_transfer_fields (callee := recipient) hsub
      have hcallStor : ∀ a k,
          callPost.getStorVal a k = b₃.getStorVal a k := by
        intro a k
        change (callPost.state.get a).stor.get k =
          (b₃.state.get a).stor.get k
        rw [hcallState]
        rw [htransferFields.1 a]
      have hpostStor : ∀ a k,
          post.getStorVal a k = b₃.getStorVal a k := by
        intro a k
        change (post.state.get a).stor.get k =
          (b₃.state.get a).stor.get k
        rw [htailState]
        exact hcallStor a k
      apply Func.execSat_of_runCompiledTo
        (Func.RunCompiledTo.of_runCompiled htail)
      apply hP post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact htailError.trans (hcallEffect.error.trans
          (herr₃.trans (herr₂.trans herr₁)))
      · exact htailOutput.trans (hcallEffect.output.trans
          (hout₃.trans (hout₂.trans hout₁)))
      · exact htailReturnData.trans hcallEffect.returnData
      · let l : Log :=
          ⟨e.currentTarget, [transferEvent, e.caller.toB256, 0],
            (Sevm.argWord e 1).toBytes⟩
        calc
          post.logs = callPost.logs := htailLogs
          _ = b₃.logs := hcallEffect.logs
          _ = b₂.logs ++ [l] := hlogs₃
          _ = b₁.logs ++ [l] := congrArg (fun xs => xs ++ [l]) hlog₂
          _ = pre.logs ++ [l] := congrArg (fun xs => xs ++ [l]) hlog₁
          _ = pre.logs ++
              [ordinaryTransferLog e e.caller.toB256 0
                (Sevm.argWord e 1)] := rfl
      · have hcurrent :
            (b₁.setMach ⟨[
              e.caller.toB256,
              pre.getStorVal e.currentTarget e.caller.toB256 -
                Sevm.argWord e 1], Mem.empty, G₁ - 37⟩).getStorVal
                e.currentTarget e.caller.toB256 =
              pre.getStorVal e.currentTarget e.caller.toB256 := by
          change b₁.getStorVal e.currentTarget e.caller.toB256 =
            pre.getStorVal e.currentTarget e.caller.toB256
          simpa only [Devm.getStorVal_setMach] using
            hstor₁ e.currentTarget e.caller.toB256
        have hrc :
            (b₁.setMach ⟨[
              e.caller.toB256,
              pre.getStorVal e.currentTarget e.caller.toB256 -
                Sevm.argWord e 1], Mem.empty, G₁ - 37⟩).refundCounter = 0 := by
          change b₁.refundCounter = 0
          exact hrc₁.trans h_refund
        have hb₂Refund : 0 ≤ b₂.refundCounter := by
          rw [hrefund₂, ← Sevm.argWord_eq_dataWord, hcurrent, hrc]
          exact sstoreNewRefundCounter_nonnegative_of_original_eq_current
            h_original
        calc
          0 ≤ b₂.refundCounter := hb₂Refund
          _ = b₃.refundCounter := hrefund₃.symm
          _ = callPost.refundCounter := hcallEffect.refund.symm
          _ = post.refundCounter := htailRefund.symm
      · calc
          post.accountsToDelete.isEmpty =
              callPost.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty htailDelete
          _ = b₃.accountsToDelete.isEmpty :=
            hcallEffect.accountsToDeleteEmpty
          _ = b₂.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty hdelete₃
          _ = b₁.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty hdelete₂
          _ = pre.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty hdelete₁
      · calc
          post.getStorVal e.currentTarget e.caller.toB256 =
              b₃.getStorVal e.currentTarget e.caller.toB256 :=
            hpostStor _ _
          _ = b₂.getStorVal e.currentTarget e.caller.toB256 := by
            simpa only [Devm.getStorVal_setMach] using
              hstor₃ e.currentTarget e.caller.toB256
          _ = pre.getStorVal e.currentTarget e.caller.toB256 -
              Sevm.argWord e 1 := by
            simpa only [← Sevm.argWord_eq_dataWord] using hkey₂
      · intro a k hne
        calc
          post.getStorVal a k = b₃.getStorVal a k := hpostStor a k
          _ = b₂.getStorVal a k := by
            simpa only [Devm.getStorVal_setMach] using hstor₃ a k
          _ = b₁.getStorVal a k := by
            simpa only [Devm.getStorVal_setMach] using hoth₂ a k hne
          _ = pre.getStorVal a k := by
            simpa only [Devm.getStorVal_setMach] using hstor₁ a k
      · exact ⟨b₃.state, debit, hbal, hcode, hsub,
          htailState.trans hcallState⟩

/-- The direct-holder `withdraw` body, proved by walking that body itself.  Its
recipient is the caller opcode rather than a calldata word, so this is not
inferred from `withdrawTo`. -/
theorem withdraw_execSat {fs : List Func} {e : Sevm} {pre : Devm}
    {P : Execution → Prop}
    (h_amount : Sevm.argWord e 0 ≤
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_static : e.isStatic = false)
    (h_depth : e.depth ≠ 0)
    (h_nonprecompile : e.benvStat.rules.isPrecomp e.caller = false)
    (h_code : (pre.getCode e.caller).size = 0)
    (h_sender : ¬ pre.getBal e.currentTarget < Sevm.argWord e 0)
    (h_original : getOrigStorVal e e.currentTarget e.caller.toB256 =
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_refund : pre.refundCounter = 0)
    (h_gas : 100000 ≤ pre.gasLeft)
    (hP : ∀ post : Devm,
      RedemptionCodeOutcome e pre post e.caller e.caller
        (Sevm.argWord e 0) → P (.ok post)) :
    Func.ExecSat fs e
      (pre.setMach ⟨[], Mem.empty, pre.gasLeft⟩) withdraw P := by
  simp only [withdraw]
  apply Func.execSat_segment
  · intro ex hex
    func_run (2)
    exact hex
  refine Func.execSat_sload_step rfl (by simp)
    (v := pre.getStorVal e.currentTarget e.caller.toB256) rfl
    (M := Mem.empty) ?_ ?_ ?_
  · rfl
  · simp only [Devm.gasLeft_setMach, gasColdSload]
    omega
  · intro b₁ c₁ G₁ hw₁ _hacc₁ hstor₁ hbal₁ hcode₁ hrc₁ hlog₁
      hout₁ herr₁ hdelete₁ hlo₁ hhi₁ hG₁
    simp only [Devm.gasLeft_setMach, gasWarmAccess, gasColdSload]
      at hG₁ hlo₁ hhi₁
    apply Func.execSat_segment
    · intro ex hex
      func_run (9) [0]
      · show (if pre.getStorVal e.currentTarget e.caller.toB256 <
            Sevm.argWord e 0 then (1 : B256) else 0) = 0
        rw [if_neg (not_lt_of_ge h_amount)]
      exact hex
    refine Func.execSat_sstore_warm_step rfl hw₁ h_static
      (M := Mem.empty) rfl
      (by simp only [Devm.gasLeft_setMach, gasStorageSet]; omega) ?_
    intro b₂ c₂ G₂ hkey₂ hoth₂ hbal₂ hcode₂ _hacc₂ hlog₂ hout₂
      herr₂ hdelete₂ hrefund₂ hc₂ hG₂
    simp only [Devm.gasLeft_setMach, gasStorageSet] at hG₂ hc₂
    apply Func.execSat_segment
    · intro ex hex
      func_run (11) [gMemory]
      · exact Devm.extCost_empty_word
      exact hex
    refine Func.execSat_log_step
      (topics := [transferEvent, e.caller.toB256, 0])
      (s := [Sevm.argWord e 0, e.caller.toB256]) rfl rfl h_static
      (M := Mem.empty.write 0 (Sevm.argWord e 0).toBytes) rfl
      (c := 1756) (payload := (Sevm.argWord e 0).toBytes)
      (M' := Mem.empty.write 0 (Sevm.argWord e 0).toBytes) ?_ ?_ ?_
      (by simp only [Devm.gasLeft_setMach]; omega) ?_
    · exact Devm.extCost_add_of_size Mem.size_write_word (by decide)
    · exact Mem.read_write_word
    · exact Mem.read_snd_eq_self (by rw [Mem.size_write_word]; decide)
    · intro b₃ G₃ hlogs₃ hstor₃ hbal₃ hcode₃ _hacc₃ hrefund₃
        hout₃ herr₃ hdelete₃ hG₃
      simp only [Devm.gasLeft_setMach] at hG₃
      apply Func.execSat_segment
      · intro ex hex
        func_run (20)
        exact hex
      have hbal : ∀ a : Adr, b₃.getBal a = pre.getBal a := fun a =>
        (hbal₃ a).trans ((hbal₂ a).trans (hbal₁ a))
      have hcode : ∀ a : Adr, b₃.getCode a = pre.getCode a := fun a =>
        (hcode₃ a).trans ((hcode₂ a).trans (hcode₁ a))
      have hbcode : (b₃.getCode e.caller).size = 0 := by
        rw [hcode e.caller]
        exact h_code
      have hbsender : ¬ b₃.getBal e.currentTarget < Sevm.argWord e 0 := by
        rw [hbal e.currentTarget]
        exact h_sender
      rcases redemptionCall_runCompiled
          (e := e) (b := b₃) (G := G₃ - 20) (recipient := e.caller)
          (value := Sevm.argWord e 0) h_static h_depth h_nonprecompile hbcode
          hbsender (by omega) with
            ⟨callPost, hcall, hstack, hpostgas, hcallEffect⟩
      refine Func.execSat_next hcall ?_
      rcases callSuccessTail_runCompiled
          (fs := fs) hstack hpostgas with
        ⟨post, htail, htailError, htailOutput, htailReturnData,
          htailLogs, htailRefund, htailDelete, htailState⟩
      rcases hcallEffect.transfer with ⟨debit, hsub, hcallState⟩
      have htransferFields :=
        of_state_transfer_fields (callee := e.caller) hsub
      have hcallStor : ∀ a k,
          callPost.getStorVal a k = b₃.getStorVal a k := by
        intro a k
        change (callPost.state.get a).stor.get k =
          (b₃.state.get a).stor.get k
        rw [hcallState]
        rw [htransferFields.1 a]
      have hpostStor : ∀ a k,
          post.getStorVal a k = b₃.getStorVal a k := by
        intro a k
        change (post.state.get a).stor.get k =
          (b₃.state.get a).stor.get k
        rw [htailState]
        exact hcallStor a k
      apply Func.execSat_of_runCompiledTo
        (Func.RunCompiledTo.of_runCompiled htail)
      apply hP post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact htailError.trans (hcallEffect.error.trans
          (herr₃.trans (herr₂.trans herr₁)))
      · exact htailOutput.trans (hcallEffect.output.trans
          (hout₃.trans (hout₂.trans hout₁)))
      · exact htailReturnData.trans hcallEffect.returnData
      · let l : Log :=
          ⟨e.currentTarget, [transferEvent, e.caller.toB256, 0],
            (Sevm.argWord e 0).toBytes⟩
        calc
          post.logs = callPost.logs := htailLogs
          _ = b₃.logs := hcallEffect.logs
          _ = b₂.logs ++ [l] := hlogs₃
          _ = b₁.logs ++ [l] := congrArg (fun xs => xs ++ [l]) hlog₂
          _ = pre.logs ++ [l] := congrArg (fun xs => xs ++ [l]) hlog₁
          _ = pre.logs ++
              [ordinaryTransferLog e e.caller.toB256 0
                (Sevm.argWord e 0)] := rfl
      · have hcurrent :
            (b₁.setMach ⟨[
              e.caller.toB256,
              pre.getStorVal e.currentTarget e.caller.toB256 -
                Sevm.argWord e 0], Mem.empty, G₁ - 37⟩).getStorVal
                e.currentTarget e.caller.toB256 =
              pre.getStorVal e.currentTarget e.caller.toB256 := by
          change b₁.getStorVal e.currentTarget e.caller.toB256 =
            pre.getStorVal e.currentTarget e.caller.toB256
          simpa only [Devm.getStorVal_setMach] using
            hstor₁ e.currentTarget e.caller.toB256
        have hrc :
            (b₁.setMach ⟨[
              e.caller.toB256,
              pre.getStorVal e.currentTarget e.caller.toB256 -
                Sevm.argWord e 0], Mem.empty, G₁ - 37⟩).refundCounter = 0 := by
          change b₁.refundCounter = 0
          exact hrc₁.trans h_refund
        have hb₂Refund : 0 ≤ b₂.refundCounter := by
          rw [hrefund₂, ← Sevm.argWord_eq_dataWord, hcurrent, hrc]
          exact sstoreNewRefundCounter_nonnegative_of_original_eq_current
            h_original
        calc
          0 ≤ b₂.refundCounter := hb₂Refund
          _ = b₃.refundCounter := hrefund₃.symm
          _ = callPost.refundCounter := hcallEffect.refund.symm
          _ = post.refundCounter := htailRefund.symm
      · calc
          post.accountsToDelete.isEmpty =
              callPost.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty htailDelete
          _ = b₃.accountsToDelete.isEmpty :=
            hcallEffect.accountsToDeleteEmpty
          _ = b₂.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty hdelete₃
          _ = b₁.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty hdelete₂
          _ = pre.accountsToDelete.isEmpty :=
            congrArg Std.HashSet.isEmpty hdelete₁
      · calc
          post.getStorVal e.currentTarget e.caller.toB256 =
              b₃.getStorVal e.currentTarget e.caller.toB256 :=
            hpostStor _ _
          _ = b₂.getStorVal e.currentTarget e.caller.toB256 := by
            simpa only [Devm.getStorVal_setMach] using
              hstor₃ e.currentTarget e.caller.toB256
          _ = pre.getStorVal e.currentTarget e.caller.toB256 -
              Sevm.argWord e 0 := by
            simpa only [← Sevm.argWord_eq_dataWord] using hkey₂
      · intro a k hne
        calc
          post.getStorVal a k = b₃.getStorVal a k := hpostStor a k
          _ = b₂.getStorVal a k := by
            simpa only [Devm.getStorVal_setMach] using hstor₃ a k
          _ = b₁.getStorVal a k := by
            simpa only [Devm.getStorVal_setMach] using hoth₂ a k hne
          _ = pre.getStorVal a k := by
            simpa only [Devm.getStorVal_setMach] using hstor₁ a k
      · exact ⟨b₃.state, debit, hbal, hcode, hsub,
          htailState.trans hcallState⟩

/-! ## Selector paths through the real balanced dispatcher -/

def redemptionTreeSlice (dp : DeployParams) (fuel lo len : Nat) : DispatchTree :=
  DispatchTree.build fuel ((weth10Funcs dp).drop lo |>.take len)

def redemptionDispatch26_14_13 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 26 14 13)

def redemptionDispatch25_7_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 25 7 7)

def redemptionDispatch24_4_3 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 24 4 3)

def redemptionDispatch23_0_2 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 23 0 2)

def redemptionDispatch22_2_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 22 2 1)

def redemptionDispatch24_0_4 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 24 0 4)

def redemptionDispatch22_4_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 22 4 1)

def redemptionDispatch22_6_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (redemptionTreeSlice dp 22 6 1)

theorem withdrawToSelector_eq :
    selector "withdrawTo" [.address, .uint256] = (0x205c2878 : B256) := by
  decide +kernel

theorem withdrawSelector_eq :
    selector "withdraw" [.uint256] = (0x2e1a7d4d : B256) := by
  decide +kernel

theorem totalSupplySelector_eq :
    selector "totalSupply" [] = (0x18160ddd : B256) := by decide +kernel

theorem transferFromSelector_eq :
    selector "transferFrom" [.address, .address, .uint256] =
      (0x23b872dd : B256) := by decide +kernel

theorem permitTypehashSelector_eq :
    selector "PERMIT_TYPEHASH" [] = (0x30adf81f : B256) := by decide +kernel

theorem decimalsSelector_eq :
    selector "decimals" [] = (0x313ce567 : B256) := by decide +kernel

theorem noncesSelector_eq :
    selector "nonces" [.address] = (0x7ecebe00 : B256) := by decide +kernel

def withdrawToDispatch (dp : DeployParams) : Func :=
  dup 0 ::: pushB256 (0x7ecebe00 : B256) ::: gt :::
  ((dup 0 ::: pushB256 (0x313ce567 : B256) ::: gt :::
    ((dup 0 ::: pushB256 (0x23b872dd : B256) ::: gt :::
      ((dup 0 ::: pushB256 (0x18160ddd : B256) ::: gt :::
        (redemptionDispatch23_0_2 dp <?>
          (dup 0 ::: pushB256 (0x205c2878 : B256) ::: gt :::
            (redemptionDispatch22_2_1 dp <?>
              (pushB256 (0x205c2878 : B256) ::: eq :::
                ((nonpayable withdrawTo) <?> .call fallbackSlot)))))) <?>
        redemptionDispatch24_4_3 dp)) <?>
      redemptionDispatch25_7_7 dp)) <?>
  redemptionDispatch26_14_13 dp)

def withdrawDispatch (dp : DeployParams) : Func :=
  dup 0 ::: pushB256 (0x7ecebe00 : B256) ::: gt :::
  ((dup 0 ::: pushB256 (0x313ce567 : B256) ::: gt :::
    ((dup 0 ::: pushB256 (0x23b872dd : B256) ::: gt :::
      (redemptionDispatch24_0_4 dp <?>
        (dup 0 ::: pushB256 (0x30adf81f : B256) ::: gt :::
          ((dup 0 ::: pushB256 (0x2e1a7d4d : B256) ::: gt :::
            (redemptionDispatch22_4_1 dp <?>
              (pushB256 (0x2e1a7d4d : B256) ::: eq :::
                ((nonpayable withdraw) <?> .call fallbackSlot)))) <?>
          redemptionDispatch22_6_1 dp)))) <?>
      redemptionDispatch25_7_7 dp)) <?>
  redemptionDispatch26_14_13 dp)

def withdrawToMain (dp : DeployParams) : Func :=
  calldatasize ::: Ninst.iszero :::
    (receiveEther <?> (fsig +++ withdrawToDispatch dp))

def withdrawMain (dp : DeployParams) : Func :=
  calldatasize ::: Ninst.iszero :::
    (receiveEther <?> (fsig +++ withdrawDispatch dp))

theorem withdrawToDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = withdrawToDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    redemptionTreeSlice, redemptionDispatch26_14_13, redemptionDispatch25_7_7,
    redemptionDispatch24_4_3, redemptionDispatch23_0_2,
    redemptionDispatch22_2_1, withdrawToDispatch, dispatchWith, leftmostFsig,
    withdrawToSelector_eq, totalSupplySelector_eq, transferFromSelector_eq,
    decimalsSelector_eq, noncesSelector_eq]

theorem withdrawDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = withdrawDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    redemptionTreeSlice, redemptionDispatch26_14_13, redemptionDispatch25_7_7,
    redemptionDispatch24_0_4, redemptionDispatch22_4_1,
    redemptionDispatch22_6_1, withdrawDispatch, dispatchWith, leftmostFsig,
    withdrawSelector_eq, transferFromSelector_eq, permitTypehashSelector_eq,
    decimalsSelector_eq, noncesSelector_eq]

theorem weth10Main_eq_withdrawTo (dp : DeployParams) :
    (weth10 dp).main = withdrawToMain dp := by
  simp only [weth10, weth10Main, withdrawToDispatch_eq, withdrawToMain]

theorem weth10Main_eq_withdraw (dp : DeployParams) :
    (weth10 dp).main = withdrawMain dp := by
  simp only [weth10, weth10Main, withdrawDispatch_eq, withdrawMain]

/-- Dispatcher, nonpayability guard, and actual `withdrawTo` body composed at
program altitude.  The balanced-tree path costs 182 gas including entry. -/
theorem withdrawTo_progExecSat (dp : DeployParams)
    {e : Sevm} {pre : Devm} {recipient : Adr} {P : Execution → Prop}
    (h_data : e.data.length.toB256 ≠ 0)
    (h_value : e.value = 0)
    (h_sel : Sevm.selector e = withdrawToSelector)
    (h_recipient : Sevm.argWord e 0 = recipient.toB256)
    (h_amount : Sevm.argWord e 1 ≤
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_static : e.isStatic = false)
    (h_depth : e.depth ≠ 0)
    (h_nonprecompile : e.benvStat.rules.isPrecomp recipient = false)
    (h_code : (pre.getCode recipient).size = 0)
    (h_sender : ¬ pre.getBal e.currentTarget < Sevm.argWord e 1)
    (h_original : getOrigStorVal e e.currentTarget e.caller.toB256 =
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_refund : pre.refundCounter = 0)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : redemptionExecutionGasFloor ≤ pre.gasLeft)
    (hP : ∀ post : Devm,
      RedemptionCodeOutcome e pre post e.caller recipient
        (Sevm.argWord e 1) → P (.ok post)) :
    Prog.ExecSat e pre (weth10 dp) P := by
  rw [withdrawToSelector, withdrawToSelector_eq] at h_sel
  set g := pre.gasLeft with hg
  simp only [redemptionExecutionGasFloor, redemptionSelectorDispatchGas,
    redemptionMechanizedBodyGas] at h_gas
  refine Prog.execSat_intro (G := g - 1)
    (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
    (by simp only [gJumpdest]; omega)
    (by rw [h_stack, h_mem]) ?_
  apply Func.execSat_segment
  · intro ex hex
    have h_data_nz : B256.eqCheck e.data.length.toB256 0 = 0 := by
      simp [B256.eqCheck, h_data]
    have h_value_zero : B256.eqCheck e.value 0 = 1 := by
      simp [B256.eqCheck, h_value]
    have h_fork0 :
        B256.gtCheck (0x7ecebe00 : B256) 0x205c2878 = 1 := by decide
    have h_fork1 :
        B256.gtCheck (0x313ce567 : B256) 0x205c2878 = 1 := by decide
    have h_fork2 :
        B256.gtCheck (0x23b872dd : B256) 0x205c2878 = 1 := by decide
    have h_fork3 :
        B256.gtCheck (0x18160ddd : B256) 0x205c2878 = 0 := by decide
    have h_fork4 :
        B256.gtCheck (0x205c2878 : B256) 0x205c2878 = 0 := by decide
    have h_leaf :
        B256.eqCheck (0x205c2878 : B256) 0x205c2878 = 1 := by decide
    rw [weth10Main_eq_withdrawTo]
    func_run (33) [0, (0x205c2878 : B256), 1, 1, 1, 0, 0, 1, 1]
    simpa only [weth10Main_eq_withdrawTo] using hex
  have hbody := withdrawTo_execSat
    (fs := withdrawToMain dp :: (weth10 dp).aux) (e := e)
    (pre := pre.setMach ⟨[], Mem.empty, g - 182⟩)
    (recipient := recipient) (P := P) h_recipient
    (by simpa only [Devm.getStorVal_setMach] using h_amount)
    h_static h_depth h_nonprecompile
    (by simpa only [Devm.getCode_setMach] using h_code)
    (by exact h_sender)
    (by simpa only [Devm.getStorVal_setMach] using h_original)
    (by exact h_refund)
    (by
      simp only [Devm.gasLeft_setMach]
      omega)
    (fun post heffect => hP post heffect.of_setMach)
  simpa only [Devm.setMach_setMach, Devm.gasLeft_setMach,
    weth10Main_eq_withdrawTo] using hbody

/-- Dispatcher composition for direct-holder `withdraw`; it follows its own
five comparison outcomes and then invokes the actual `withdraw` body walk. -/
theorem withdraw_progExecSat (dp : DeployParams)
    {e : Sevm} {pre : Devm} {P : Execution → Prop}
    (h_data : e.data.length.toB256 ≠ 0)
    (h_value : e.value = 0)
    (h_sel : Sevm.selector e = withdrawSelector)
    (h_amount : Sevm.argWord e 0 ≤
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_static : e.isStatic = false)
    (h_depth : e.depth ≠ 0)
    (h_nonprecompile : e.benvStat.rules.isPrecomp e.caller = false)
    (h_code : (pre.getCode e.caller).size = 0)
    (h_sender : ¬ pre.getBal e.currentTarget < Sevm.argWord e 0)
    (h_original : getOrigStorVal e e.currentTarget e.caller.toB256 =
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_refund : pre.refundCounter = 0)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : redemptionExecutionGasFloor ≤ pre.gasLeft)
    (hP : ∀ post : Devm,
      RedemptionCodeOutcome e pre post e.caller e.caller
        (Sevm.argWord e 0) → P (.ok post)) :
    Prog.ExecSat e pre (weth10 dp) P := by
  rw [withdrawSelector, withdrawSelector_eq] at h_sel
  set g := pre.gasLeft with hg
  simp only [redemptionExecutionGasFloor, redemptionSelectorDispatchGas,
    redemptionMechanizedBodyGas] at h_gas
  refine Prog.execSat_intro (G := g - 1)
    (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
    (by simp only [gJumpdest]; omega)
    (by rw [h_stack, h_mem]) ?_
  apply Func.execSat_segment
  · intro ex hex
    have h_data_nz : B256.eqCheck e.data.length.toB256 0 = 0 := by
      simp [B256.eqCheck, h_data]
    have h_value_zero : B256.eqCheck e.value 0 = 1 := by
      simp [B256.eqCheck, h_value]
    have h_fork0 :
        B256.gtCheck (0x7ecebe00 : B256) 0x2e1a7d4d = 1 := by decide
    have h_fork1 :
        B256.gtCheck (0x313ce567 : B256) 0x2e1a7d4d = 1 := by decide
    have h_fork2 :
        B256.gtCheck (0x23b872dd : B256) 0x2e1a7d4d = 0 := by decide
    have h_fork3 :
        B256.gtCheck (0x30adf81f : B256) 0x2e1a7d4d = 1 := by decide
    have h_fork4 :
        B256.gtCheck (0x2e1a7d4d : B256) 0x2e1a7d4d = 0 := by decide
    have h_leaf :
        B256.eqCheck (0x2e1a7d4d : B256) 0x2e1a7d4d = 1 := by decide
    rw [weth10Main_eq_withdraw]
    func_run (33) [0, (0x2e1a7d4d : B256), 1, 1, 0, 1, 0, 1, 1]
    simpa only [weth10Main_eq_withdraw] using hex
  have hbody := withdraw_execSat
    (fs := withdrawMain dp :: (weth10 dp).aux) (e := e)
    (pre := pre.setMach ⟨[], Mem.empty, g - 182⟩) (P := P)
    (by simpa only [Devm.getStorVal_setMach] using h_amount)
    h_static h_depth h_nonprecompile
    (by simpa only [Devm.getCode_setMach] using h_code)
    (by exact h_sender)
    (by simpa only [Devm.getStorVal_setMach] using h_original)
    (by exact h_refund)
    (by
      simp only [Devm.gasLeft_setMach]
      omega)
    (fun post heffect => hP post heffect.of_setMach)
  simpa only [Devm.setMach_setMach, Devm.gasLeft_setMach,
    weth10Main_eq_withdraw] using hbody

/-! ## Exact code execution adapters -/

theorem withdrawTo_exec (dp : DeployParams)
    {e : Sevm} {pre : Devm} {recipient : Adr}
    (h_data : e.data.length.toB256 ≠ 0)
    (h_value : e.value = 0)
    (h_sel : Sevm.selector e = withdrawToSelector)
    (h_recipient : Sevm.argWord e 0 = recipient.toB256)
    (h_amount : Sevm.argWord e 1 ≤
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_static : e.isStatic = false)
    (h_depth : e.depth ≠ 0)
    (h_nonprecompile : e.benvStat.rules.isPrecomp recipient = false)
    (h_code : (pre.getCode recipient).size = 0)
    (h_sender : ¬ pre.getBal e.currentTarget < Sevm.argWord e 1)
    (h_original : getOrigStorVal e e.currentTarget e.caller.toB256 =
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_refund : pre.refundCounter = 0)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : redemptionExecutionGasFloor ≤ pre.gasLeft)
    (h_compile : some e.code.toList = Prog.compile (weth10 dp)) :
    ∃ post,
      exec ⟨0, e, pre⟩ = .ok post ∧
      RedemptionCodeOutcome e pre post e.caller recipient
        (Sevm.argWord e 1) := by
  refine Prog.execSat_out (P := fun ex => ∃ post,
    ex = .ok post ∧
      RedemptionCodeOutcome e pre post e.caller recipient
        (Sevm.argWord e 1)) ?_ h_compile
  exact withdrawTo_progExecSat dp h_data h_value h_sel h_recipient h_amount
    h_static h_depth h_nonprecompile h_code h_sender h_original h_refund
    h_stack h_mem h_gas (fun post hpost => ⟨post, rfl, hpost⟩)

theorem withdraw_exec (dp : DeployParams)
    {e : Sevm} {pre : Devm}
    (h_data : e.data.length.toB256 ≠ 0)
    (h_value : e.value = 0)
    (h_sel : Sevm.selector e = withdrawSelector)
    (h_amount : Sevm.argWord e 0 ≤
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_static : e.isStatic = false)
    (h_depth : e.depth ≠ 0)
    (h_nonprecompile : e.benvStat.rules.isPrecomp e.caller = false)
    (h_code : (pre.getCode e.caller).size = 0)
    (h_sender : ¬ pre.getBal e.currentTarget < Sevm.argWord e 0)
    (h_original : getOrigStorVal e e.currentTarget e.caller.toB256 =
      pre.getStorVal e.currentTarget e.caller.toB256)
    (h_refund : pre.refundCounter = 0)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : redemptionExecutionGasFloor ≤ pre.gasLeft)
    (h_compile : some e.code.toList = Prog.compile (weth10 dp)) :
    ∃ post,
      exec ⟨0, e, pre⟩ = .ok post ∧
      RedemptionCodeOutcome e pre post e.caller e.caller
        (Sevm.argWord e 0) := by
  refine Prog.execSat_out (P := fun ex => ∃ post,
    ex = .ok post ∧
      RedemptionCodeOutcome e pre post e.caller e.caller
        (Sevm.argWord e 0)) ?_ h_compile
  exact withdraw_progExecSat dp h_data h_value h_sel h_amount h_static h_depth
    h_nonprecompile h_code h_sender h_original h_refund h_stack h_mem h_gas
    (fun post hpost => ⟨post, rfl, hpost⟩)

/-! ## Ordinary message-frame packaging -/

theorem processMessageCall_eq_of_exec
    {p : Prog} {msg : Msg} {benv : Benv} {child : Evm} {post : Devm}
    (hauths : msg.tenv.stat.auths = [])
    (htarget : msg.target.isNone = false)
    (hcompile : some msg.code.toList = Prog.compile p)
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (henter : (Frame.ofCall msg).enter = .run child)
    (hexec : exec child = .ok post)
    (herror : post.error = none)
    (hrefund : 0 ≤ post.refundCounter) :
    processMessageCall msg = .ok
      (post.state,
        { gasLeft := post.gasLeft
          refundCounter := post.refundCounter.toNat
          logs := post.logs
          accountsToDelete := post.accountsToDelete
          error := post.error
          returnData := post.output }) := by
  have hprocess : processMessage msg = .ok post := by
    unfold processMessage runFrame
    rw [henter]
    unfold Frame.settle Frame.settleMsg processMessage.settle
      executeCode.handleError
    simp only [hexec, herror, Frame.ofCall, Option.isSome,
      Bool.false_eq_true, if_false, bind, Except.bind]
  have hdelegation : getDelegatedCodeAddress msg.code = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg (not_delegation_of_compile hcompile)]
  have htoNat : Int.toNat? post.refundCounter =
      some post.refundCounter.toNat :=
    Int.mem_toNat?.mpr (Int.toNat_of_nonneg hrefund).symm
  unfold processMessageCall
  rw [htarget]
  unfold processMessageCall.call
  simp only [hauths, List.isEmpty, if_true, bind, Except.bind,
    hdelegation, hprocess, Except.bimap, id_eq, herror, Option.isNone,
    htoNat, Option.toExcept, Nat.cast_zero, zero_add]
  rfl

lemma B256.sub_zero_exact (x : B256) : x - 0 = x := by
  rcases x with ⟨xh, xl⟩
  change (((xh - (0 : B128)) -
    (if xl < (0 : B128) then (1 : B128) else 0),
    xl - (0 : B128))) = (xh, xl)
  have h : ¬ xl < (0 : B128) := by
    intro h
    rcases h with h | ⟨_, h⟩
    · exact UInt64.not_lt_zero h
    · exact UInt64.not_lt_zero h
  rw [if_neg h, B128.sub_zero, B128.sub_zero, B128.sub_zero]

lemma B256.add_zero_exact (x : B256) : x + 0 = x := by
  apply B256.toNat_inj
  rw [B256.toNat_add]
  rw [show (0 : B256).toNat = 0 from rfl]
  norm_num [Nat.lo_eq]
  exact B256.toNat_lt x

lemma B256.zero_le_exact (x : B256) : (0 : B256) ≤ x := by
  rw [B256.le_iff_toNat_le_toNat]
  rw [show (0 : B256).toNat = 0 from rfl]
  norm_num

lemma zero_transfer_bal {st mid : State} {caller target : Adr}
    (hsub : st.subBal caller 0 = some mid) :
    ∀ a, (mid.addBal target 0).bal a = st.bal a := by
  rcases State.of_subBal hsub with ⟨_, rfl⟩
  intro a
  unfold State.addBal
  by_cases hc : caller = a
  · subst a
    by_cases ht : target = caller
    · subst target
      show (((st.setBal caller _).setBal caller _).get caller).bal = _
      rw [State.setBal_get_self]
      show ((st.setBal caller _).get caller).bal + 0 = _
      rw [State.setBal_get_self]
      exact B256.sub_add_cancel
    · show (((st.setBal caller _).setBal target _).get caller).bal = _
      rw [State.setBal_get_ne ht]
      show ((st.setBal caller _).get caller).bal = _
      rw [State.setBal_get_self]
      change st.bal caller - 0 = st.bal caller
      exact B256.sub_zero_exact _
  · by_cases ht : target = a
    · subst a
      show (((st.setBal caller _).setBal target _).get target).bal = _
      rw [State.setBal_get_self]
      show ((st.setBal caller _).get target).bal + 0 = _
      rw [State.setBal_get_ne hc]
      change st.bal target + 0 = st.bal target
      exact B256.add_zero_exact _
    · show (((st.setBal caller _).setBal target _).get a).bal = _
      rw [State.setBal_get_ne ht]
      show ((st.setBal caller _).get a).bal = _
      rw [State.setBal_get_ne hc]
      rfl

structure MessageFrameRedemptionOutcome
    (dp : DeployParams) (ca owner recipient : Adr) (q : Nat)
    (w : State) (msg : Msg) (entry post : Devm)
    (out : MsgCallOutput) : Prop where
  process : processMessageCall msg = .ok (post.state, out)
  entryStor : ∀ a k, entry.getStorVal a k = (w.getStor a).get k
  entryBal : ∀ a, entry.getBal a = w.bal a
  entryCode : ∀ a, entry.getCode a = w.getCode a
  entryLogs : entry.logs = []
  entryOutput : entry.output = []
  codeOutcome : RedemptionCodeOutcome (initSevm msg) entry post
    owner recipient q.toB256
  outError : out.error = none
  outGasLeft : out.gasLeft = post.gasLeft
  outRefundCounter : out.refundCounter = post.refundCounter.toNat
  outLogs : out.logs = post.logs
  outReturnData : out.returnData = post.output
  outAccountsToDeleteEmpty : out.accountsToDelete.isEmpty = true

theorem Stable.withdrawTo_messageFrame_of_le
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleRedemptionMessage
      dp ca owner recipient q w msg) :
    ∃ entry post out,
      MessageFrameRedemptionOutcome
        dp ca owner recipient q w msg entry post out := by
  have hq_lt : q < 2 ^ 256 := hstable.amount_lt_modulus_of_le hq
  have hq_toNat : q.toB256.toNat = q :=
    B256.toNat_toB256_of_lt hq_lt
  have hcurrent : (initSevm msg).currentTarget = ca :=
    henv.currentTarget_eq
  have haffordable : ¬ msg.benv.state.bal msg.caller < msg.value := by
    rw [henv.value_eq]
    exact not_lt_of_ge (B256.zero_le_exact _)
  rcases Msg.benvAfterTransfer_of_affordable msg
      henv.shouldTransferValue_eq haffordable with ⟨stmid, hsub, hbt⟩
  let benv' :=
    (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile (benv := benv') hbt
    · change msg.codeAddress = some ca
      exact henv.codeAddress_eq
    · change msg.benv.stat.rules.isPrecomp ca = false
      rw [henv.rules_eq]
      exact henv.target_not_precompile
  rcases of_state_transfer_fields
      (callee := msg.currentTarget) hsub with
    ⟨htopStor, htopCode, _, _, _⟩
  have hentryStor : ∀ a k,
      child.dyna.getStorVal a k = (w.getStor a).get k := by
    intro a k
    change ((stmid.addBal msg.currentTarget msg.value).get a).stor.get k =
      (w.get a).stor.get k
    rw [htopStor a, henv.state_eq]
  have hentryCode : ∀ a,
      child.dyna.getCode a = w.getCode a := by
    intro a
    change ((stmid.addBal msg.currentTarget msg.value).get a).code =
      (w.get a).code
    rw [htopCode a, henv.state_eq]
  have hsub0 : msg.benv.state.subBal msg.caller 0 = some stmid := by
    simpa only [henv.value_eq] using hsub
  have hentryBal : ∀ a, child.dyna.getBal a = w.bal a := by
    intro a
    change (stmid.addBal msg.currentTarget msg.value).bal a = w.bal a
    rw [henv.value_eq]
    exact (zero_transfer_bal hsub0 a).trans (by rw [henv.state_eq])
  have hsta : child.sta = initSevm msg := by
    rfl
  have hdata : (initSevm msg).data = withdrawToCalldata recipient q := by
    simpa only [initSevm] using henv.data_eq
  have hargs := withdrawToCalldata_argWords
    (initSevm msg) recipient q hdata
  have hdataNonempty : (initSevm msg).data.length.toB256 ≠ 0 := by
    rw [hdata]
    norm_num [withdrawToCalldata, abiSelectorBytes_length,
      B256.length_toBytes]
    decide
  have hamount : Sevm.argWord (initSevm msg) 1 ≤
      child.dyna.getStorVal (initSevm msg).currentTarget
        (initSevm msg).caller.toB256 := by
    change Sevm.argWord (initSevm msg) 1 ≤
      child.dyna.getStorVal msg.currentTarget msg.caller.toB256
    rw [hargs.2, B256.le_iff_toNat_le_toNat, hq_toNat,
      henv.currentTarget_eq, henv.caller_eq]
    change q ≤ (child.dyna.getStorVal ca owner.toB256).toNat
    rw [hentryStor]
    exact hq
  have hrecipientCode :
      (child.dyna.getCode recipient).size = 0 := by
    rw [hentryCode, ByteArray.size_eq_length_toList,
      henv.recipient_code_free]
    rfl
  have hcapWord : q.toB256 ≤ w.bal ca := by
    rw [B256.le_iff_toNat_le_toNat, hq_toNat]
    exact hq.trans hstable.bookedBalanceNat_le_contractEth
  have hsender : ¬ child.dyna.getBal ca < q.toB256 := by
    rw [hentryBal]
    exact not_lt_of_ge hcapWord
  have horiginal :
      getOrigStorVal (initSevm msg) ca owner.toB256 =
        child.dyna.getStorVal ca owner.toB256 := by
    change (msg.benv.stat.origState.getStor ca).get owner.toB256 = _
    rw [henv.original_storage_eq, hentryStor]
  have hcompile :
      some (initSevm msg).code.toList = Prog.compile (weth10 dp) := by
    simpa only [initSevm] using henv.code_eq
  rcases withdrawTo_exec dp hdataNonempty
      (by simpa only [initSevm] using henv.value_eq)
      henv.selector_eq hargs.1 hamount
      (by simpa only [initSevm] using henv.isStatic_eq)
      (by simp only [initSevm, henv.depth_eq]; decide)
      (by simpa only [initSevm, henv.rules_eq] using
        henv.recipient_not_precompile)
      hrecipientCode
      (by
        change ¬ child.dyna.getBal msg.currentTarget <
          Sevm.argWord (initSevm msg) 1
        rw [henv.currentTarget_eq, hargs.2]
        exact hsender)
      (by simpa only [initSevm, henv.currentTarget_eq,
          henv.caller_eq] using horiginal)
      (by rfl) (by rfl) (by rfl)
      (by
        exact (redemptionExecutionGasFloor_le_runtimeCeiling q).trans
          henv.gas_bound)
      hcompile with ⟨post, hexec, houtcome⟩
  have hpostError : post.error = none := by
    exact houtcome.error.trans rfl
  let out : MsgCallOutput :=
    { gasLeft := post.gasLeft
      refundCounter := post.refundCounter.toNat
      logs := post.logs
      accountsToDelete := post.accountsToDelete
      error := post.error
      returnData := post.output }
  have hprocess : processMessageCall msg = .ok (post.state, out) := by
    apply processMessageCall_eq_of_exec
      (p := weth10 dp) (benv := benv') (child := child)
      henv.auths_eq
      (by simp only [henv.target_eq, Option.isNone]) hcompile hbt henter
      (by
        have hchildEq : child = ⟨0, initSevm msg, child.dyna⟩ := by
          apply Evm.ext
          · rfl
          · exact hsta
          · rfl
        rw [hchildEq]
        exact hexec)
      hpostError houtcome.refundNonnegative
  refine ⟨child.dyna, post, out, ?_⟩
  refine ⟨hprocess, hentryStor, hentryBal, hentryCode, rfl, rfl,
    ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [show (initSevm msg).caller = owner from henv.caller_eq,
      hargs.2] at houtcome
    exact houtcome
  · exact hpostError
  · change post.accountsToDelete.isEmpty = true
    rw [houtcome.accountsToDeleteEmpty]
    rfl

/-- The canonical direct-holder entry point executes the actual `withdraw`
dispatcher branch and body, rather than deriving its result from `withdrawTo`. -/
theorem Stable.withdraw_messageFrame_of_le
    {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleSelfRedemptionMessage dp ca owner q w msg) :
    ∃ entry post out,
      MessageFrameRedemptionOutcome
        dp ca owner owner q w msg entry post out := by
  have hq_lt : q < 2 ^ 256 := hstable.amount_lt_modulus_of_le hq
  have hq_toNat : q.toB256.toNat = q :=
    B256.toNat_toB256_of_lt hq_lt
  have hcurrent : (initSevm msg).currentTarget = ca :=
    henv.currentTarget_eq
  have haffordable : ¬ msg.benv.state.bal msg.caller < msg.value := by
    rw [henv.value_eq]
    exact not_lt_of_ge (B256.zero_le_exact _)
  rcases Msg.benvAfterTransfer_of_affordable msg
      henv.shouldTransferValue_eq haffordable with ⟨stmid, hsub, hbt⟩
  let benv' :=
    (msg.benv.withState stmid).addBal msg.currentTarget msg.value
  let child := initEvm (msg.withBenv benv')
  have henter : (Frame.ofCall msg).enter = .run child := by
    apply Frame.enter_run_of_nonprecompile (benv := benv') hbt
    · change msg.codeAddress = some ca
      exact henv.codeAddress_eq
    · change msg.benv.stat.rules.isPrecomp ca = false
      rw [henv.rules_eq]
      exact henv.target_not_precompile
  rcases of_state_transfer_fields
      (callee := msg.currentTarget) hsub with
    ⟨htopStor, htopCode, _, _, _⟩
  have hentryStor : ∀ a k,
      child.dyna.getStorVal a k = (w.getStor a).get k := by
    intro a k
    change ((stmid.addBal msg.currentTarget msg.value).get a).stor.get k =
      (w.get a).stor.get k
    rw [htopStor a, henv.state_eq]
  have hentryCode : ∀ a,
      child.dyna.getCode a = w.getCode a := by
    intro a
    change ((stmid.addBal msg.currentTarget msg.value).get a).code =
      (w.get a).code
    rw [htopCode a, henv.state_eq]
  have hsub0 : msg.benv.state.subBal msg.caller 0 = some stmid := by
    simpa only [henv.value_eq] using hsub
  have hentryBal : ∀ a, child.dyna.getBal a = w.bal a := by
    intro a
    change (stmid.addBal msg.currentTarget msg.value).bal a = w.bal a
    rw [henv.value_eq]
    exact (zero_transfer_bal hsub0 a).trans (by rw [henv.state_eq])
  have hsta : child.sta = initSevm msg := by
    rfl
  have hdata : (initSevm msg).data = withdrawCalldata q := by
    simpa only [initSevm] using henv.data_eq
  have harg := withdrawCalldata_argWord (initSevm msg) q hdata
  have hdataNonempty : (initSevm msg).data.length.toB256 ≠ 0 := by
    rw [hdata]
    norm_num [withdrawCalldata, abiSelectorBytes_length,
      B256.length_toBytes]
    decide
  have hamount : Sevm.argWord (initSevm msg) 0 ≤
      child.dyna.getStorVal (initSevm msg).currentTarget
        (initSevm msg).caller.toB256 := by
    change Sevm.argWord (initSevm msg) 0 ≤
      child.dyna.getStorVal msg.currentTarget msg.caller.toB256
    rw [harg, B256.le_iff_toNat_le_toNat, hq_toNat,
      henv.currentTarget_eq, henv.caller_eq]
    change q ≤ (child.dyna.getStorVal ca owner.toB256).toNat
    rw [hentryStor]
    exact hq
  have hownerCode : (child.dyna.getCode owner).size = 0 := by
    rw [hentryCode, ByteArray.size_eq_length_toList,
      henv.recipient_code_free]
    rfl
  have hcapWord : q.toB256 ≤ w.bal ca := by
    rw [B256.le_iff_toNat_le_toNat, hq_toNat]
    exact hq.trans hstable.bookedBalanceNat_le_contractEth
  have hsender : ¬ child.dyna.getBal ca < q.toB256 := by
    rw [hentryBal]
    exact not_lt_of_ge hcapWord
  have horiginal :
      getOrigStorVal (initSevm msg) ca owner.toB256 =
        child.dyna.getStorVal ca owner.toB256 := by
    change (msg.benv.stat.origState.getStor ca).get owner.toB256 = _
    rw [henv.original_storage_eq, hentryStor]
  have hcompile :
      some (initSevm msg).code.toList = Prog.compile (weth10 dp) := by
    simpa only [initSevm] using henv.code_eq
  rcases withdraw_exec dp hdataNonempty
      (by simpa only [initSevm] using henv.value_eq)
      henv.selector_eq hamount
      (by simpa only [initSevm] using henv.isStatic_eq)
      (by simp only [initSevm, henv.depth_eq]; decide)
      (by simpa only [initSevm, henv.rules_eq, henv.caller_eq] using
        henv.recipient_not_precompile)
      (by simpa only [initSevm, henv.caller_eq] using hownerCode)
      (by
        change ¬ child.dyna.getBal msg.currentTarget <
          Sevm.argWord (initSevm msg) 0
        rw [henv.currentTarget_eq, harg]
        exact hsender)
      (by simpa only [initSevm, henv.currentTarget_eq,
          henv.caller_eq] using horiginal)
      (by rfl) (by rfl) (by rfl)
      (by
        exact (redemptionExecutionGasFloor_le_runtimeCeiling q).trans
          henv.gas_bound)
      hcompile with ⟨post, hexec, houtcome⟩
  have hpostError : post.error = none := houtcome.error.trans rfl
  let out : MsgCallOutput :=
    { gasLeft := post.gasLeft
      refundCounter := post.refundCounter.toNat
      logs := post.logs
      accountsToDelete := post.accountsToDelete
      error := post.error
      returnData := post.output }
  have hprocess : processMessageCall msg = .ok (post.state, out) := by
    apply processMessageCall_eq_of_exec
      (p := weth10 dp) (benv := benv') (child := child)
      henv.auths_eq
      (by simp only [henv.target_eq, Option.isNone]) hcompile hbt henter
      (by
        have hchildEq : child = ⟨0, initSevm msg, child.dyna⟩ := by
          apply Evm.ext
          · rfl
          · exact hsta
          · rfl
        rw [hchildEq]
        exact hexec)
      hpostError houtcome.refundNonnegative
  refine ⟨child.dyna, post, out, ?_⟩
  refine ⟨hprocess, hentryStor, hentryBal, hentryCode, rfl, rfl,
    ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [show (initSevm msg).caller = owner from henv.caller_eq,
      harg] at houtcome
    exact houtcome
  · exact hpostError
  · change post.accountsToDelete.isEmpty = true
    rw [houtcome.accountsToDeleteEmpty]
    rfl

theorem Stable.messageRedemption_enabled_of_frame
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleRedemptionMessageCore
      dp ca owner recipient q w msg)
    (hrun : ∃ entry post out,
      MessageFrameRedemptionOutcome
        dp ca owner recipient q w msg entry post out) :
    MessageRedemptionEnabled dp ca owner recipient q w msg := by
  rcases hrun with ⟨entry, post, out, hframe⟩
  have hq_lt : q < 2 ^ 256 := hstable.amount_lt_modulus_of_le hq
  have hq_toNat : q.toB256.toNat = q :=
    B256.toNat_toB256_of_lt hq_lt
  have hcurrent : (initSevm msg).currentTarget = ca :=
    henv.currentTarget_eq
  have hrecipient_ne : recipient ≠ ca := by
    intro h
    subst recipient
    have hempty : msg.code.toList = [] := by
      rw [henv.installedCode_eq]
      exact henv.recipient_code_free
    exact Prog.compile_ne_nil
      (henv.code_eq.symm.trans (congrArg some hempty))
  rcases hframe.codeOutcome.transfer with
    ⟨callState, debit, hcallBal, hcallCode, hsub, hpostState⟩
  rw [hcurrent] at hsub
  have hcallNof : sum callState.bal < 2 ^ 256 := by
    rw [funext hcallBal, funext hframe.entryBal]
    exact hstable.sumNof
  rcases of_state_transfer_fields (callee := recipient) hsub with
    ⟨htransferStor, htransferCode, hleEth, _, hcontract⟩
  have hpostCode : ∀ a, post.state.getCode a = w.getCode a := by
    intro a
    rw [hpostState]
    change ((debit.addBal recipient q.toB256).get a).code = _
    rw [htransferCode a]
    change callState.getCode a = w.getCode a
    rw [hcallCode a, hframe.entryCode a]
  have hpostContract : post.state.bal ca = w.bal ca - q.toB256 := by
    rw [hpostState, hcontract hrecipient_ne, hcallBal ca,
      hframe.entryBal ca]
  have hpostRecipient :
      (post.state.bal recipient).toNat =
        (w.bal recipient).toNat + q := by
    rw [hpostState]
    have hcredit := of_transfer_bal_target hsub
      hrecipient_ne.symm hcallNof
    rw [hcallBal recipient, hframe.entryBal recipient, hq_toNat] at hcredit
    exact hcredit
  have hpostOther : ∀ a, a ≠ ca → a ≠ recipient →
      post.state.bal a = w.bal a := by
    intro a hca hrecipient
    rw [hpostState]
    exact (of_transfer_bal_other hsub hca.symm hrecipient.symm).trans
      ((hcallBal a).trans (hframe.entryBal a))
  have hwordLeBooked : q.toB256 ≤ (w.getStor ca).get owner.toB256 := by
    rw [B256.le_iff_toNat_le_toNat, hq_toNat]
    exact hq
  have hwordLeEth : q.toB256 ≤ w.bal ca := by
    rw [B256.le_iff_toNat_le_toNat, hq_toNat]
    exact hq.trans hstable.bookedBalanceNat_le_contractEth
  have hstorageDebit := hframe.codeOutcome.storageDebit
  rw [hcurrent] at hstorageDebit
  have hstorageOther := hframe.codeOutcome.storageOther
  rw [hcurrent] at hstorageOther
  have hdecrease : Decrease owner q.toB256
      (Stor.rest (w.getStor ca)) (Stor.rest (post.state.getStor ca)) := by
    intro a
    constructor
    · intro ha
      subst a
      change (w.getStor ca).get owner.toB256 - q.toB256 =
        (post.state.getStor ca).get owner.toB256
      exact (hstorageDebit.trans (congrArg (fun x => x - q.toB256)
        (hframe.entryStor ca owner.toB256))).symm
    · intro hne
      change (w.getStor ca).get a.toB256 =
        (post.state.getStor ca).get a.toB256
      symm
      have hnePair : (ca, a.toB256) ≠ (ca, owner.toB256) := by
        intro hp
        apply hne
        exact (Adr.toB256_inj (x := a) (y := owner)
          (congrArg Prod.snd hp)).symm
      exact (hstorageOther ca a.toB256 hnePair).trans
        (hframe.entryStor ca a.toB256)
  have hflashKey : flashMintedSlot ≠ owner.toB256 := by
    intro h
    exact flashMintedSlot_not_valid ⟨owner, h.symm⟩
  have hpostFlash :
      (post.state.getStor ca).get flashMintedSlot = 0 := by
    calc
      (post.state.getStor ca).get flashMintedSlot =
          entry.getStorVal ca flashMintedSlot :=
        hstorageOther ca flashMintedSlot (by
          intro hp
          exact hflashKey (congrArg Prod.snd hp))
      _ = (w.getStor ca).get flashMintedSlot :=
        hframe.entryStor ca flashMintedSlot
      _ = 0 := hstable.flashZero
  have hpostSum : sum post.state.bal < 2 ^ 256 := by
    rw [hpostState, of_state_transfer_sum hsub hcallNof]
    exact hcallNof
  have hpostBacked :
      Stor.Weth10Inv (post.state.getStor ca) 0 (post.state.bal ca) := by
    have hi := Stor.Weth10Inv.withdraw hstable.backed hdecrease
      hwordLeBooked hwordLeEth
      (by
        rw [hpostFlash, hstable.flashZero])
    rw [hpostContract]
    exact hi
  have hpostStable : Stable dp ca post.state :=
    ⟨by
      rw [hpostCode ca]
      exact hstable.code,
     hpostSum, hpostBacked, hpostFlash⟩
  have hqStorNat : q ≤ ((w.getStor ca).get owner.toB256).toNat := by
    exact hq
  have hqEthNat : q ≤ (w.bal ca).toNat :=
    hq.trans hstable.bookedBalanceNat_le_contractEth
  refine ⟨post.state, out, hframe.process, ?_⟩
  refine ⟨hframe.outError, ?_, ?_, ?_, ?_, hpostOther, ?_, ?_, ?_,
    hpostCode, hpostFlash, hpostStable⟩
  · unfold bookedBalanceNat Stor.rest
    change ((post.state.getStor ca).get owner.toB256).toNat + q =
      ((w.getStor ca).get owner.toB256).toNat
    change (post.getStorVal ca owner.toB256).toNat + q =
      ((w.getStor ca).get owner.toB256).toNat
    rw [hstorageDebit,
      hframe.entryStor ca owner.toB256,
      B256.toNat_sub_eq_of_le _ _ hwordLeBooked, hq_toNat]
    exact Nat.sub_add_cancel hqStorNat
  · intro a hne
    unfold bookedBalanceNat Stor.rest
    change ((post.state.getStor ca).get a.toB256).toNat =
      ((w.getStor ca).get a.toB256).toNat
    change (post.getStorVal ca a.toB256).toNat =
      ((w.getStor ca).get a.toB256).toNat
    rw [hstorageOther ca a.toB256 (by
      intro hp
      apply hne
      exact Adr.toB256_inj (x := a) (y := owner)
        (congrArg Prod.snd hp)),
      hframe.entryStor ca a.toB256]
  · rw [hpostContract, B256.toNat_sub_eq_of_le _ _ hwordLeEth]
    rw [hq_toNat]
    exact Nat.sub_add_cancel hqEthNat
  · exact hpostRecipient
  · rw [hpostState, of_state_transfer_sum hsub hcallNof]
    rw [funext hcallBal, funext hframe.entryBal]
  · rw [hframe.outLogs, hframe.codeOutcome.logs]
    rw [hframe.entryLogs]
    change [ordinaryTransferLog (initSevm msg) owner.toB256 0 q.toB256] =
      [redemptionBurnLog ca owner q]
    simp only [ordinaryTransferLog, redemptionBurnLog, hcurrent]
  · rw [hframe.outReturnData, hframe.codeOutcome.output]
    exact hframe.entryOutput

theorem Stable.messageRedemption_enabled_of_le
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleRedemptionMessage
      dp ca owner recipient q w msg) :
    MessageRedemptionEnabled dp ca owner recipient q w msg :=
  hstable.messageRedemption_enabled_of_frame hq
    henv.toAdmissibleRedemptionMessageCore
    (hstable.withdrawTo_messageFrame_of_le hq henv)

/-- A direct holder can redeem through the canonical `withdraw(q)` selector.
Its execution witness is constructed by `withdraw_messageFrame_of_le`. -/
theorem Stable.selfRedemption_enabled_of_le
    {dp : DeployParams} {ca owner : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hq : q ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleSelfRedemptionMessage dp ca owner q w msg) :
    MessageRedemptionEnabled dp ca owner owner q w msg :=
  hstable.messageRedemption_enabled_of_frame hq
    henv.toAdmissibleRedemptionMessageCore
    (hstable.withdraw_messageFrame_of_le hq henv)

/-! ## Canonical transaction construction -/

theorem Stable.preparedRedemptionMessage_exists
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (hq : q ≤ bookedBalanceNat benv.state ca owner)
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index) :
    ∃ debit msg entry messagePost messageOut,
      TransactionDebitOutcome owner
          (tx.gas * redemptionEffectiveGasPrice benv tx)
          benv.state debit ∧
      prepareMessage {benv.beginTransaction with state := debit}
          (redemptionTenv benv tx owner index) tx = .ok msg ∧
      MessageFrameRedemptionOutcome
          dp ca owner recipient q debit msg entry messagePost messageOut ∧
      MessageRedemptionExactEffect
          dp ca owner recipient q debit messagePost.state messageOut := by
  rcases henv.upfrontDebit_exists with ⟨debit, hdebit⟩
  rcases henv.type_eq with ⟨maxPriorityFee, maxFee, htype⟩
  have howner_ca : owner ≠ ca := by
    intro h
    subst owner
    have hempty : (benv.state.getCode ca).toList = [] := henv.owner_code_free
    exact Prog.compile_ne_nil
      (henv.target_code.symm.trans (congrArg some hempty))
  have hrecipient_ca : recipient ≠ ca := by
    intro h
    subst recipient
    have hempty : (benv.state.getCode ca).toList = [] :=
      henv.recipient_code_free
    exact Prog.compile_ne_nil
      (henv.target_code.symm.trans (congrArg some hempty))
  have hdebitCaBal : debit.bal ca = benv.state.bal ca :=
    hdebit.otherBalancePreserved ca howner_ca.symm
  have hdebitStable : Stable dp ca debit := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change some (debit.getCode ca).toList = Prog.compile (weth10 dp)
      rw [hdebit.codePreserved ca]
      exact henv.target_code
    · exact (Nat.le_add_right _ _).trans_lt
        (hdebit.sumDebit.trans_lt hstable.sumNof)
    · simpa [hdebit.storagePreserved ca, hdebitCaBal] using hstable.backed
    · simpa [hdebit.storagePreserved ca] using hstable.flashZero
  have hqDebit : q ≤ bookedBalanceNat debit ca owner := by
    simpa [bookedBalanceNat, hdebit.storagePreserved ca] using hq
  let msg := redemptionPreparedMessage benv tx owner ca index debit
  have hprepare :
      prepareMessage {benv.beginTransaction with state := debit}
          (redemptionTenv benv tx owner index) tx = .ok msg := by
    unfold prepareMessage msg redemptionPreparedMessage
    simp only [htype]
    rfl
  have hmsg : AdmissibleRedemptionMessage
      dp ca owner recipient q debit msg := by
    refine {
      state_eq := ?_
      rules_eq := ?_
      target_eq := ?_
      currentTarget_eq := ?_
      codeAddress_eq := ?_
      code_eq := ?_
      installedCode_eq := ?_
      caller_eq := ?_
      value_eq := ?_
      depth_eq := ?_
      shouldTransferValue_eq := ?_
      isStatic_eq := ?_
      auths_eq := ?_
      disablePrecompiles_eq := ?_
      target_not_precompile := henv.target_not_precompile
      recipient_ne_zero := henv.recipient_ne_zero
      recipient_not_precompile := henv.recipient_not_precompile
      recipient_code_free := ?_
      original_storage_eq := ?_
      target_access := ?_
      recipient_access := ?_
      owner_storage_access := ?_
      recipient_account := ?_
      gas_bound := ?_
      data_eq := ?_
      selector_eq := ?_ }
    · rfl
    · simpa only [msg, redemptionPreparedMessage,
        Benv.beginTransaction] using henv.rules_eq
    · rfl
    · rfl
    · rfl
    · change some (debit.getCode ca).toList = Prog.compile (weth10 dp)
      rw [hdebit.codePreserved ca]
      exact henv.target_code
    · rfl
    · rfl
    · simp [msg, redemptionPreparedMessage, henv.value_eq]
      decide
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rw [hdebit.codePreserved recipient]
      exact henv.recipient_code_free
    · simpa [msg, redemptionPreparedMessage, Benv.beginTransaction,
        hdebit.storagePreserved ca]
    · by_cases h : ca ∈ msg.accessedAddresses
      · exact .warm h
      · exact .cold h
    · by_cases h : recipient ∈ msg.accessedAddresses
      · exact .warm h
      · exact .cold h
    · by_cases h : (ca, owner.toB256) ∈ msg.accessedStorageKeys
      · exact .warm h
      · exact .cold h
    · by_cases h : (debit.get recipient).Empty
      · exact .empty h
      · exact .existing h
    · change redemptionRuntimeCeiling q ≤
        tx.gas - redemptionIntrinsicGas tx
      have hbudget : redemptionIntrinsicGas tx +
          redemptionRuntimeCeiling q ≤ tx.gas := by
        exact (Nat.le_max_right _ _).trans henv.gas_bound
      omega
    · simpa [msg, redemptionPreparedMessage] using henv.data_eq
    · apply henv.selector_eq (initSevm msg)
      rfl
  rcases hdebitStable.withdrawTo_messageFrame_of_le hqDebit hmsg with
    ⟨entry, messagePost, messageOut, hframe⟩
  have heffect := hdebitStable.messageRedemption_enabled_of_frame hqDebit
    hmsg.toAdmissibleRedemptionMessageCore
    ⟨entry, messagePost, messageOut, hframe⟩
  rcases heffect with ⟨effectPost, effectOut, hprocess, heffect⟩
  have hpost : effectPost = messagePost.state := by
    exact (Prod.mk.inj
      (Except.ok.inj (hprocess.symm.trans hframe.process))).1
  have hout : effectOut = messageOut := by
    exact (Prod.mk.inj
      (Except.ok.inj (hprocess.symm.trans hframe.process))).2
  subst effectPost
  subst effectOut
  exact ⟨debit, msg, entry, messagePost, messageOut,
    hdebit, hprepare, hframe, heffect⟩

theorem AdmissibleRedemptionTx.processTransaction_eq_of_message
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index)
    {debit : State} {msg : Msg} {entry messagePost : Devm}
    {messageOut : MsgCallOutput}
    (hdebit : TransactionDebitOutcome owner
      (tx.gas * redemptionEffectiveGasPrice benv tx)
      benv.state debit)
    (hprepare :
      prepareMessage {benv.beginTransaction with state := debit}
        (redemptionTenv benv tx owner index) tx = .ok msg)
    (hframe : MessageFrameRedemptionOutcome
      dp ca owner recipient q debit msg entry messagePost messageOut) :
    let usedGas := redemptionUsedGasFromMessage tx messageOut
      messagePost.refundCounter.toNat
    processTransaction benv bout tx index = .ok
      (redemptionFinalState benv tx owner messagePost.state usedGas,
        redemptionFinalBout bout tx index messageOut usedGas) := by
  have hrefund : Int.toNat? messageOut.refundCounter =
      some messagePost.refundCounter.toNat := by
    rw [hframe.outRefundCounter]
    exact Int.mem_toNat?.mpr rfl
  have hdelete : messageOut.accountsToDelete.toList = [] := by
    apply List.isEmpty_iff.mp
    rw [Std.HashSet.isEmpty_toList]
    exact hframe.outAccountsToDeleteEmpty
  rcases henv.type_eq with ⟨maxPriorityFee, maxFee, htype⟩
  unfold processTransaction
  simp only [bind, Except.bind]
  have hrules : benv.beginTransaction.stat.rules = pragueRules := by
    simpa only [Benv.beginTransaction] using henv.rules_eq
  rw [hrules, henv.validated]
  simp only [Except.mapError]
  have hchecked := henv.checked
  simp only [redemptionTxPreludeBout] at hchecked
  rw [hchecked]
  simp only [Tx.isTypeThree, Tx.accessList, TxType.accessList, Tx.auths,
    htype, Bool.false_eq_true, if_false, Nat.add_zero,
    Benv.beginTransaction]
  rw [hdebit.subBal]
  simp only [Option.toExcept]
  have hprepare' := hprepare
  simp only [redemptionTenv, redemptionIntrinsicGas,
    Benv.beginTransaction] at hprepare'
  simp only [List.map_nil, List.flatten_nil]
  rw [hprepare']
  simp only [Except.bind]
  rw [hframe.process]
  simp only [Except.mapError, Except.bind]
  rw [hrefund]
  simp only [Option.toExcept, hdelete, List.foldl_nil]
  rfl

lemma addBal_toNat_eq_add_if
    (w : State) (target a : Adr) (value : B256)
    (hbound : sum w.bal + value.toNat < 2 ^ 256) :
    ((w.addBal target value).bal a).toNat =
      (w.bal a).toNat + if a = target then value.toNat else 0 := by
  unfold State.addBal
  by_cases h : a = target
  · subst a
    change (((w.setBal target _).get target).bal).toNat = _
    rw [State.setBal_get_self]
    change (w.bal target + value).toNat = _
    have hnof : B256.Nof (w.bal target) value := by
      unfold B256.Nof
      have hle := Blanc.le_sum (f := w.bal) (k := target)
      omega
    rw [B256.toNat_add_eq_of_nof _ _ hnof]
    simp
  · change (((w.setBal target _).get a).bal).toNat = _
    rw [State.setBal_get_ne (Ne.symm h)]
    simp [h]
    rfl

theorem AdmissibleRedemptionTx.usedGas_le
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index)
    (out : MsgCallOutput) (refundCounter : Nat) :
    redemptionUsedGasFromMessage tx out refundCounter ≤ tx.gas := by
  have hfloor :=
    validateTransaction_calldataFloorGasCost_le_gas henv.validated
  unfold redemptionUsedGasFromMessage redemptionCalldataFloorGas
  apply max_le
  · omega
  · exact hfloor

theorem redemptionFinalBout_gasUsed
    (bout : BlockOutput) (tx : Tx) (index : Nat)
    (out : MsgCallOutput) (usedGas : Nat) :
    redemptionTxGasUsed bout
      (redemptionFinalBout bout tx index out usedGas) = usedGas := by
  unfold redemptionTxGasUsed redemptionFinalBout redemptionTxPreludeBout
  simp only
  omega

theorem Stable.transactionRedemption_enabled_of_le
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (hq : q ≤ bookedBalanceNat benv.state ca owner)
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index) :
    TransactionRedemptionEnabled
      dp ca owner recipient q benv bout tx index := by
  rcases hstable.preparedRedemptionMessage_exists hq henv with
    ⟨debit, msg, entry, messagePost, messageOut,
      hdebit, hprepare, hframe, heffect⟩
  let usedGas := redemptionUsedGasFromMessage tx messageOut
    messagePost.refundCounter.toNat
  let post := redemptionFinalState benv tx owner messagePost.state usedGas
  let bout' := redemptionFinalBout bout tx index messageOut usedGas
  have hrun : processTransaction benv bout tx index = .ok (post, bout') := by
    simpa only [usedGas, post, bout'] using
      henv.processTransaction_eq_of_message hdebit hprepare hframe
  have hgasUsed : redemptionTxGasUsed bout bout' = usedGas := by
    simpa only [bout'] using
      redemptionFinalBout_gasUsed bout tx index messageOut usedGas
  have hused_le : usedGas ≤ tx.gas := by
    exact henv.usedGas_le messageOut messagePost.refundCounter.toNat
  have hrecipient_ca : recipient ≠ ca := by
    intro h
    subst recipient
    have hempty : (benv.state.getCode ca).toList = [] :=
      henv.recipient_code_free
    exact Prog.compile_ne_nil
      (henv.target_code.symm.trans (congrArg some hempty))
  have hpostStor : ∀ a, post.getStor a = messagePost.state.getStor a := by
    intro a
    dsimp only [post, redemptionFinalState]
    unfold State.addBal
    change
      ((((messagePost.state.setBal owner _).setBal
        benv.stat.coinbase _).get a).stor) = _
    rw [State.setBal_get_stor, State.setBal_get_stor]
    rfl
  have hpostCode : ∀ a, post.getCode a = messagePost.state.getCode a := by
    intro a
    dsimp only [post, redemptionFinalState]
    unfold State.addBal
    change
      ((((messagePost.state.setBal owner _).setBal
        benv.stat.coinbase _).get a).code) = _
    rw [State.setBal_get_code, State.setBal_get_code]
    rfl
  have hpostStable : Stable dp ca post :=
    processTransaction_preserves_stable dp ca benv bout bout' tx index post
      hrun hstable.sumNof henv.target_not_created hstable
  let effective := redemptionEffectiveGasPrice benv tx
  let refundAmount := (tx.gas - usedGas) * effective
  let tipAmount := usedGas * (effective - benv.stat.baseFeePerGas)
  let burnAmount := usedGas * benv.stat.baseFeePerGas
  have hfeeDecomp : refundAmount + tipAmount + burnAmount =
      tx.gas * effective := by
    dsimp only [refundAmount, tipAmount, burnAmount]
    calc
      (tx.gas - usedGas) * effective +
            usedGas * (effective - benv.stat.baseFeePerGas) +
            usedGas * benv.stat.baseFeePerGas =
          (tx.gas - usedGas) * effective +
            usedGas * ((effective - benv.stat.baseFeePerGas) +
              benv.stat.baseFeePerGas) := by
        rw [Nat.mul_add, Nat.add_assoc]
      _ = (tx.gas - usedGas) * effective + usedGas * effective := by
        rw [Nat.sub_add_cancel]
        exact henv.base_fee_le_effective
      _ = ((tx.gas - usedGas) + usedGas) * effective := by
        rw [Nat.add_mul]
      _ = tx.gas * effective := by
        rw [Nat.sub_add_cancel hused_le]
  have hmessageAddress : ∀ a,
      (messagePost.state.bal a).toNat + (if a = ca then q else 0) =
        (debit.bal a).toNat + (if a = recipient then q else 0) := by
    intro a
    by_cases hca : a = ca
    · subst a
      simpa [hrecipient_ca.symm] using heffect.contractEthDebit
    · by_cases hr : a = recipient
      · subst a
        simpa [hrecipient_ca] using heffect.recipientEthCredit
      · have hbal := congrArg B256.toNat
          (heffect.otherEthUnchanged a hca hr)
        simpa [hca, hr] using hbal
  have hdebitAddress : ∀ a,
      (debit.bal a).toNat + (if a = owner then
        tx.gas * effective else 0) = (benv.state.bal a).toNat := by
    intro a
    by_cases howner : a = owner
    · subst a
      simpa [effective] using hdebit.ownerDebit
    · have hbal := congrArg B256.toNat
          (hdebit.otherBalancePreserved a howner)
      simpa [howner] using hbal
  have hcreditBudget :
      sum messagePost.state.bal + refundAmount + tipAmount < 2 ^ 256 := by
    have hsumMessage := heffect.sumPreserved
    have hsumDebit := hdebit.sumDebit
    change sum debit.bal + tx.gas * effective = sum benv.state.bal
      at hsumDebit
    have hcredits_le : refundAmount + tipAmount ≤ tx.gas * effective := by
      omega
    calc
      sum messagePost.state.bal + refundAmount + tipAmount =
          sum debit.bal + (refundAmount + tipAmount) := by omega
      _ ≤ sum debit.bal + tx.gas * effective :=
        Nat.add_le_add_left hcredits_le _
      _ = sum benv.state.bal := hsumDebit
      _ < 2 ^ 256 := hstable.sumNof
  have hrefund_lt : refundAmount < 2 ^ 256 := by omega
  have htip_lt : tipAmount < 2 ^ 256 := by omega
  have hrefundEncoded : refundAmount.toB256.toNat = refundAmount :=
    B256.toNat_toB256_of_lt hrefund_lt
  have htipEncoded : tipAmount.toB256.toNat = tipAmount :=
    B256.toNat_toB256_of_lt htip_lt
  have hrefundBound :
      sum messagePost.state.bal + refundAmount.toB256.toNat < 2 ^ 256 := by
    rw [hrefundEncoded]
    omega
  let refunded := messagePost.state.addBal owner refundAmount.toB256
  have hrefundedSum : sum refunded.bal =
      sum messagePost.state.bal + refundAmount := by
    dsimp only [refunded]
    rw [sum_addBal_eq messagePost.state owner _ hrefundBound,
      hrefundEncoded]
  have htipBound : sum refunded.bal + tipAmount.toB256.toNat < 2 ^ 256 := by
    rw [hrefundedSum, htipEncoded]
    exact hcreditBudget
  have hpostSum : sum post.bal =
      sum messagePost.state.bal + refundAmount + tipAmount := by
    change sum (refunded.addBal benv.stat.coinbase tipAmount.toB256).bal = _
    rw [sum_addBal_eq refunded benv.stat.coinbase _ htipBound,
      hrefundedSum, htipEncoded]
  have hpostAddress : ∀ a,
      (post.bal a).toNat =
        (messagePost.state.bal a).toNat +
          (if a = owner then refundAmount else 0) +
          (if a = benv.stat.coinbase then tipAmount else 0) := by
    intro a
    have hfirst := addBal_toNat_eq_add_if messagePost.state owner a
      refundAmount.toB256 hrefundBound
    have hsecond := addBal_toNat_eq_add_if refunded benv.stat.coinbase a
      tipAmount.toB256 htipBound
    change (post.bal a).toNat = _
    rw [show post = refunded.addBal benv.stat.coinbase tipAmount.toB256 by
      rfl, hsecond, hfirst, hrefundEncoded, htipEncoded]
  have heth : TransactionEthAccounting
      dp ca owner recipient q benv bout tx index post bout' := by
    refine ⟨?_, ?_⟩
    · intro a
      have hm := hmessageAddress a
      have hd := hdebitAddress a
      rw [hpostAddress a]
      unfold redemptionGasRefund redemptionPriorityFee
      rw [hgasUsed]
      dsimp only [refundAmount, tipAmount, effective]
      dsimp only [effective] at hd
      omega
    · unfold redemptionBaseFeeBurn
      rw [hgasUsed, hpostSum, heffect.sumPreserved]
      have hsumDebit := hdebit.sumDebit
      change sum debit.bal + tx.gas * effective = sum benv.state.bal
        at hsumDebit
      dsimp only [burnAmount] at hfeeDecomp
      omega
  have hreceiptEntry :
      Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index) =
        some (makeReceipt tx messageOut.error
          (bout.blockGasUsed + usedGas) messageOut.logs) := by
    dsimp only [bout', redemptionFinalBout]
    simp only [redemptionTxPreludeBout]
    change
      (bout.receiptsTrie.insert (redemptionReceiptKey index)
        (makeReceipt tx messageOut.error
          (bout.blockGasUsed + usedGas) messageOut.logs))[redemptionReceiptKey index]? = _
    rw [Std.TreeMap.getElem?_insert_self]
  refine ⟨post, bout', hrun, ?_⟩
  refine {
    trace := ?_
    receiptAt := ?_
    receiptSucceeded := ?_
    receiptLogs := ?_
    ownerDebit := ?_
    otherBookedUnchanged := ?_
    codePreserved := ?_
    flashZero := ?_
    postStable := hpostStable
    ethAccounting := heth }
  · refine ⟨redemptionIntrinsicGas tx, redemptionCalldataFloorGas tx,
      redemptionEffectiveGasPrice benv tx, debit, msg, messagePost.state,
      messageOut, ?_, henv.checked, hdebit.subBal, ?_, hframe.process,
      heffect⟩
    · simpa [redemptionIntrinsicGas, redemptionCalldataFloorGas] using
        henv.validated
    · simpa [redemptionTenv] using hprepare
  · rcases henv.type_eq with ⟨maxPriorityFee, maxFee, htype⟩
    refine ⟨(makeReceipt tx messageOut.error
      (bout.blockGasUsed + usedGas) messageOut.logs).2, ?_⟩
    rw [hreceiptEntry]
    simp [makeReceipt, htype]
  · rw [hreceiptEntry]
    simp [makeReceipt, hframe.outError]
  · rw [hreceiptEntry]
    simp [makeReceipt, heffect.burnLog]
  · calc
      bookedBalanceNat post ca owner + q =
          bookedBalanceNat messagePost.state ca owner + q := by
        unfold bookedBalanceNat
        rw [hpostStor ca]
      _ = bookedBalanceNat debit ca owner := heffect.ownerDebit
      _ = bookedBalanceNat benv.state ca owner := by
        unfold bookedBalanceNat
        rw [hdebit.storagePreserved ca]
  · intro a hne
    calc
      bookedBalanceNat post ca a =
          bookedBalanceNat messagePost.state ca a := by
        unfold bookedBalanceNat
        rw [hpostStor ca]
      _ = bookedBalanceNat debit ca a :=
        heffect.otherBookedUnchanged a hne
      _ = bookedBalanceNat benv.state ca a := by
        unfold bookedBalanceNat
        rw [hdebit.storagePreserved ca]
  · intro a
    rw [hpostCode a, heffect.codePreserved a, hdebit.codePreserved a]
  · rw [hpostStor ca]
    exact heffect.flashZero

/-! ## Boundary and anti-vacuity witnesses -/

theorem bookedBalance_insufficient_not_admitted
    {w : State} {ca owner : Adr} {q : Nat}
    (hinsufficient : bookedBalanceNat w ca owner < q) :
    ¬ q ≤ bookedBalanceNat w ca owner := by
  omega

theorem activeFlash_not_stable
    {dp : DeployParams} {ca : Adr} {w : State}
    (hactive : (w.getStor ca).get flashMintedSlot ≠ 0) :
    ¬ Stable dp ca w := by
  intro hstable
  exact hactive hstable.flashZero

theorem staticMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg} (hstatic : msg.isStatic = true) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  rw [henv.isStatic_eq] at hstatic
  cases hstatic

theorem precompileTargetMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hprecompile : pragueRules.isPrecomp ca = true) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  have h := henv.target_not_precompile
  rw [hprecompile] at h
  contradiction

theorem precompileRecipientMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hprecompile : pragueRules.isPrecomp recipient = true) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  have h := henv.recipient_not_precompile
  rw [hprecompile] at h
  contradiction

theorem zeroRecipientMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg} (hzero : recipient = 0) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  exact henv.recipient_ne_zero hzero

theorem codedRecipientMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hcoded : (w.getCode recipient).toList ≠ []) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  exact hcoded henv.recipient_code_free

theorem wrongInstalledCodeMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hcode : some (w.getCode ca).toList ≠ Prog.compile (weth10 dp)) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  apply hcode
  rw [← henv.installedCode_eq]
  exact henv.code_eq

theorem dirtyOriginalStorageMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hdirty : msg.benv.stat.origState.getStor ca ≠ w.getStor ca) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  exact hdirty henv.original_storage_eq

theorem nonemptyAuthorizationMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg} (hauth : msg.tenv.stat.auths ≠ []) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  exact hauth henv.auths_eq

theorem lowGasMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hlow : msg.gas < redemptionRuntimeCeiling q) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  exact Nat.not_le_of_lt hlow henv.gas_bound

theorem noncanonicalCalldataMessage_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {w : State} {msg : Msg}
    (hdata : msg.data ≠ withdrawToCalldata recipient q) :
    ¬ AdmissibleRedemptionMessage dp ca owner recipient q w msg := by
  intro henv
  exact hdata henv.data_eq

theorem lowGasTransaction_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hlow : tx.gas < redemptionTransactionGasBound q tx) :
    ¬ AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index := by
  intro henv
  exact Nat.not_le_of_lt hlow henv.gas_bound

theorem noncanonicalCalldataTransaction_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hdata : tx.data ≠ withdrawToCalldata recipient q) :
    ¬ AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index := by
  intro henv
  exact hdata henv.data_eq

theorem nonemptyAccessListTransaction_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {priority fee : Nat} {accessList : AccessList}
    (hne : accessList ≠ [])
    (htype : tx.type =
      .two benv.stat.chainId priority fee (some ca) accessList) :
    ¬ AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index := by
  intro henv
  rcases henv.type_eq with ⟨p, f, htwo⟩
  rw [htype] at htwo
  cases htwo
  exact hne rfl

theorem typeThreeTransaction_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {chainId : UInt64} {priority fee blobFee : Nat} {target : Adr}
    {accessList : AccessList} {blobHashes : List B256}
    (htype : tx.type =
      .three chainId priority fee target accessList blobFee blobHashes) :
    ¬ AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index := by
  intro henv
  rcases henv.type_eq with ⟨p, f, htwo⟩
  rw [htype] at htwo
  cases htwo

theorem typeFourTransaction_not_admissible
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {chainId : UInt64} {priority fee : Nat} {target : Adr}
    {accessList : AccessList} {auths : List Auth}
    (htype : tx.type =
      .four chainId priority fee target accessList auths) :
    ¬ AdmissibleRedemptionTx
      dp ca owner recipient q benv bout tx index := by
  intro henv
  rcases henv.type_eq with ⟨p, f, htwo⟩
  rw [htype] at htwo
  cases htwo

theorem outerOkWithFailedReceipt_not_redemptionEnabled
    {dp : DeployParams} {ca owner recipient : Adr} {q : Nat}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {post : State} {bout' : BlockOutput}
    (hrun : processTransaction benv bout tx index = .ok (post, bout'))
    (hfailed :
      (Std.TreeMap.get? bout'.receiptsTrie (redemptionReceiptKey index)).map
        (fun entry => entry.2.succeeded) = some false) :
    ¬ TransactionRedemptionEnabled
      dp ca owner recipient q benv bout tx index := by
  intro henabled
  rcases henabled with ⟨post', bout'', hrun', heffect⟩
  have hp : (post, bout') = (post', bout'') :=
    Except.ok.inj (hrun.symm.trans hrun')
  cases hp
  rw [heffect.receiptSucceeded] at hfailed
  contradiction

theorem Stable.zeroMessageRedemption_enabled
    {dp : DeployParams} {ca owner recipient : Adr}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (henv : AdmissibleRedemptionMessage
      dp ca owner recipient 0 w msg) :
    MessageRedemptionEnabled dp ca owner recipient 0 w msg := by
  exact hstable.messageRedemption_enabled_of_le (Nat.zero_le _) henv

theorem Stable.unitMessageRedemption_enabled
    {dp : DeployParams} {ca owner recipient : Adr}
    {w : State} {msg : Msg}
    (hstable : Stable dp ca w)
    (hbooked : 1 ≤ bookedBalanceNat w ca owner)
    (henv : AdmissibleRedemptionMessage
      dp ca owner recipient 1 w msg) :
    MessageRedemptionEnabled dp ca owner recipient 1 w msg := by
  exact hstable.messageRedemption_enabled_of_le hbooked henv

theorem Stable.zeroTransactionRedemption_enabled
    {dp : DeployParams} {ca owner recipient : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient 0 benv bout tx index) :
    TransactionRedemptionEnabled
      dp ca owner recipient 0 benv bout tx index := by
  exact hstable.transactionRedemption_enabled_of_le (Nat.zero_le _) henv

theorem Stable.unitTransactionRedemption_enabled
    {dp : DeployParams} {ca owner recipient : Adr}
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    (hstable : Stable dp ca benv.state)
    (hbooked : 1 ≤ bookedBalanceNat benv.state ca owner)
    (henv : AdmissibleRedemptionTx
      dp ca owner recipient 1 benv bout tx index) :
    TransactionRedemptionEnabled
      dp ca owner recipient 1 benv bout tx index := by
  exact hstable.transactionRedemption_enabled_of_le hbooked henv

end Weth10
end Blanc
