import Blanc.ForwardCall
import Blanc.ForwardStorageAccess
import Jaune.Machine
import Jaune.WordFacts
import Blanc.MachineDataFacts
import Blanc.RlpConcrete
import Jaune.Transaction
import Blanc.ExecutionOccurrence
import Blanc.ExecutionTrace
import Init.Data.Ord.UInt
import Blanc.DeploymentMessage
import Blanc.MessageExecution
import Blanc.TransactionForward
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionAccountingAdmissionIn
import Blanc.TransactionForwardH

/-!
# Machine, codec and transaction-forward facts

Storage-access, machine-word, concrete RLP codec, deployment-message and transaction-forward facts.
Each section names the module whose vocabulary it extends.  Nothing here mentions a contract.
-/

/-! ## From `Blanc/ForwardStorageAccess.lean` -/

namespace Blanc

open Jaune

theorem afterSstore_accessedAddresses
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accessedAddresses =
      base.accessedAddresses := by
  unfold afterSstore
  split <;> rfl

theorem afterSstore_accessedStorageKeys
    (sevm : Sevm) (base : Devm) (key value : B256) :
    (afterSstore sevm base key value).accessedStorageKeys =
      sloadAccessedStorageKeys sevm.currentTarget
        base.accessedStorageKeys key := by
  unfold afterSstore sloadAccessedStorageKeys
  split <;> rfl

/-! ### Created accounts and the machine original read

Jaune prices `SSTORE` from `Devm.getOrigStorVal`, which reads `0` at an account
created in this transaction and the transaction-start snapshot otherwise. These
laws carry that read across the selected storage steps. -/

/-! ## Selected `SLOAD`: values, warmth, and key sets

A selected `SLOAD` changes only the accessed-key set, so storage, original and
transient reads pass through it, the read key is warm afterwards, and every
other key keeps its warm or cold status. -/

end Blanc

/-! ## From `Blanc/MachineDataFacts.lean` -/

namespace Blanc

open Jaune

/-- Multiplication by one preserves an EVM word. -/
theorem B256.mul_one (x : B256) : x * (1 : B256) = x := by
  apply B256.toNat_inj
  rw [B256.toNat_mul]
  have h1 : (1 : B256).toNat = 1 := by decide
  rw [h1, Nat.mul_one, Nat.lo_eq_of_lt x.toNat_lt]

end Blanc

/-! ## From `Blanc/RlpConcrete.lean` -/

namespace Blanc.RlpConcrete

open Jaune

private theorem bytes_of_singleton_rlp (bs : Bytes) (b : UInt8)
    (small : b < 0x80) (encoded : (BLT.bytes bs).toBytes = [b]) : bs = [b] := by
  cases bs with
  | nil =>
      rw [BLT.toBytes] at encoded <;>
        try simp only [reduceCtorEq, imp_self, implies_true]
      change [0x80] = [b] at encoded
      have same := (List.cons.inj encoded).1
      rw [← same] at small
      exact False.elim ((by decide : ¬ (0x80 : UInt8) < 0x80) small)
  | cons a rest =>
      cases rest with
      | nil =>
          rw [BLT.toBytes] at encoded
          split at encoded
          · exact encoded
          · have lengths := congrArg List.length encoded
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at lengths
            omega
      | cons c rest =>
          rw [BLT.toBytes] at encoded <;>
            try simp only [List.cons.injEq, reduceCtorEq, and_false, imp_self, implies_true]
          have lengths := congrArg List.length encoded
          split at lengths <;>
            simp only [List.length_cons, List.length_nil, List.length_append] at lengths <;> omega

/-- A positive transaction index below 128 is its one-byte RLP atom. -/
theorem receipt_key_small (index : Nat) (positive : 0 < index) (small : index < 128) :
    (BLT.bytes index.toBytes).toBytes = [index.toUInt8] := by
  have byteSmall : index.toUInt8 < 0x80 := by
    change index.toUInt8.toNat < 128
    simpa only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow,
      Nat.mod_eq_of_lt (by omega : index < 256)] using small
  cases index with
  | zero => omega
  | succ n =>
      unfold Nat.toBytes
      rw [Nat.toBytes.aux]
      rw [Nat.div_eq_of_lt (by omega : n + 1 < 256),
        Nat.mod_eq_of_lt (by omega : n + 1 < 256), Nat.toBytes.aux]
      rw [BLT.toBytes, ite_eq_left byteSmall]

/-- No other natural index has the RLP receipt key of a positive index below
128. The other index is unbounded; no general codec injectivity is assumed. -/
theorem receipt_key_ne_of_small {index other : Nat}
    (positive : 0 < index) (small : index < 128) (different : other ≠ index) :
    (BLT.bytes other.toBytes).toBytes ≠ (BLT.bytes index.toBytes).toBytes := by
  intro same
  rw [receipt_key_small index positive small] at same
  have byteSmall : index.toUInt8 < 0x80 := by
    change index.toUInt8.toNat < 128
    simpa only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow,
      Nat.mod_eq_of_lt (by omega : index < 256)] using small
  have bytes := bytes_of_singleton_rlp other.toBytes index.toUInt8 byteSmall same
  have number := congrArg Bytes.toNat bytes
  rw [nat_bytes_roundtrip] at number
  simp only [Bytes.toNat, Bytes.toNat.aux, Nat.zero_mul, Nat.zero_add,
    Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow,
    Nat.mod_eq_of_lt (by omega : index < 256)] at number
  exact different number

end Blanc.RlpConcrete

/-! ## From `Blanc/DeploymentMessage.lean` -/

namespace Blanc

open Jaune

/-- A successful raw `exec` with no frame error settles as the corresponding
ordinary message result. -/
theorem processMessage_ok_of_exec
    {msg : Msg} {benv : Benv} {post : Devm}
    (htransfer : msg.benvAfterTransfer = .ok benv)
    (hcodeAddress : msg.codeAddress = .none)
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = .none)
    (hsweep : msg.benv.stat.rules.settle.touchedSweep = false) :
    processMessage msg = .ok post := by
  unfold processMessage runFrame Frame.enter Frame.ofCall
  rw [htransfer]
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress]
  unfold Frame.settle Frame.settleMsg
  simp only [Msg.withBenv, hcodeAddress] at hexec
  rw [hexec]
  simp only [Bool.false_eq_true, ↓reduceIte, processMessage.settle, executeCode.handleErrorWith_ok,
    Except.bind_ok, herror, Option.isSome_none, Devm.recordTouch_of_not_touchedSweep hsweep]

/-- The outer message result induced by a successful direct CREATE after code
charging.  Constructor families may retain their historical wrapper names,
but the projection itself is contract-neutral. -/
def directCreateMessageOutputOf (post : Devm) : MsgCallOutput :=
  { gasLeft := post.gasLeft
    refundCounter := 0
    logs := post.logs
    accountsToDelete := post.accountsToDelete
    error := post.error
    returnData := post.output
    touchedAccounts := post.meta.touchedAccounts }

/-! ## Contract-neutral protocol-deployment plumbing -/

end Blanc

/-! ## From `Blanc/TransactionForward.lean` -/

namespace Blanc

open Jaune ExecutionTrace

/-! ### The admission checks of a type-2 transaction, from stated facts -/

/-- Validation without a state-gas dimension when init-code limits are disabled.
Direct intrinsic projections keep concrete CREATE payloads out of pair conversion. -/
theorem validateTransaction_ok_of_noInitcodeLimit
    {rules : ForkRules} {tx : Tx} {sender : Adr} {f : Nat}
    (hsg : rules.stateGas = none) (hinit : rules.creation.initCodeLimit = false)
    (hfloor : (calculateIntrinsicCost rules tx sender).2 = f)
    (hgas : max (calculateIntrinsicCost rules tx sender).1 f ≤ tx.gas)
    (hnonce : tx.nonce ≠ UInt64.max)
    (hcap : checkTransactionGasCap rules.tx tx.gas = .ok ()) :
    validateTransaction rules tx sender =
      .ok ((calculateIntrinsicCost rules tx sender).1, f) := by
  have hlimit : checkInitcodeLimit rules tx.type.receiver? tx.data.length = .ok () := by
    simp only [checkInitcodeLimit, hinit, Bool.false_eq_true, ↓reduceIte]
  cases hcost : calculateIntrinsicCost rules tx sender with
  | mk i g =>
    simp only [hcost] at hfloor hgas ⊢
    subst f
    unfold validateTransaction
    simp only [hsg, hcost, Nat.not_lt.mpr hgas, ↓reduceIte]
    cases hm : rules.tx.maxGas with
    | none => simp only [hnonce, ↓reduceIte, bind, Except.bind, hlimit]
    | some m => simp only [bind, Except.bind, hlimit, hcap, hnonce, ↓reduceIte]

/-! ### A type-2 call transaction from the outcome of its message's execution -/

/-! ### The intrinsic gas of a plain call -/

/-! ### The same quantities under the deployment vocabulary

`Blanc/DeploymentMessage.lean` names the settlement of a transaction for the deployment corridor
(`deploymentEffectiveGasPrice`, `deploymentUsedGasFromMessage`, `deploymentFinalState`).  They are the
quantities of `processTransaction_call_of_exec` for a type-2 transaction; these equations tie the two
vocabularies together so that a consumer of either can use the other's lemmas. -/

end Blanc

/-! ## From `Blanc/TransactionForwardH.lean` -/

namespace Blanc

open Jaune ExecutionTrace

/-- **The creation wrapper over a successful raw creation.**  A creation message (`target`
absent) under rules without a state-gas dimension, whose target has neither code nor nonce,
settles as its `processCreateMessage` core: the same state, the core's gas, and (with no core
error) its logs, accounts to delete, touched accounts and non-negative refund counter. -/
theorem processMessageCall_create_of_message {msg : Msg} {post : Devm} {refund : Nat}
    (hsg : msg.benv.stat.rules.stateGas = none) (htarget : msg.target = none)
    (hfresh : accountHasCodeOrNonce msg.benv.state msg.currentTarget = false)
    (hcreate : processCreateMessage msg = .ok post) (herror : post.error = none)
    (hrefund : Int.toNat? post.refundCounter = some refund) :
    processMessageCall msg = .ok (post.state,
      { gasLeft := post.gasLeft, refundCounter := (refund : Int),
        logs := post.logs, accountsToDelete := post.accountsToDelete,
        error := none, returnData := post.output,
        touchedAccounts := post.meta.touchedAccounts }) := by
  unfold processMessageCall
  simp only [htarget, Option.isNone_none, ↓reduceIte]
  unfold processMessageCall.create
  rw [hsg]
  simp only [hfresh, Bool.false_eq_true, ↓reduceIte, hcreate, bind, Except.bind, Except.bimap, id,
    herror, Option.isNone_none, hrefund, Option.toExcept]

end Blanc
