import Blanc.Lift.BuilderRequest.Exit.Revert
import Blanc.Lift.BuilderRequest.Transaction
import Blanc.Lift.RequestSystem.Access
import Blanc.Lift.BuilderRequest.Exit.SystemCall

/-!
# Direct transactions to the exit contract under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

`transaction_ok` is `Submissions.transaction_ok` at this contract. The other four are the reasons a direct transaction
reverts, each through `processTransaction`: the guards reject the submission, slot 0 holds the inhibitor, the calldata has
neither form, a fee read carries value. Each of them is a `Submissions.TxReverted`, with the regular gas of `revertBound`.
-/

namespace Blanc.Lift.BuilderRequest.Exit

open Jaune

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {E t : Adr} {chainId : UInt64} {prio maxFee i f n : Nat}
  {out : B256}

/-- **A direct submission to the exit contract.** -/
abbrev transaction_ok := @Submissions.transaction_ok submissions

/-- **A direct submission's effect and access-list entries.** -/
abbrev transaction_bal := @Submissions.transaction_bal submissions

/-- **The exit system call's access-list entries, from any storage.** -/
abbrev system_call_bal := @RequestSystem.SysCall.bal _ sysCall

/-- **A direct submission the guards reject reverts.** -/
theorem transaction_not_admitted (index : Nat) (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (caller : E ≠ systemAddress) (hlen : tx.data.length = 48)
    (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess 2 (benv.state.getStor t)) 17 1 17 0 n out)
    (rejected : ¬ Admits tx.data tx.value.toB256 (out / (17 : B256))) (hgas : i + revertBound n ≤ tx.gas) :
    Submissions.TxReverted benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f (revertBound n) :=
  submissions.transaction_reverts d installed hprecomp (fun _ hentry =>
    frameReverts_not_admitted (out := out) rfl (submissions.frame_fork d hentry) caller hlen
      (by
        show Devm.getStorVal _ t 0 ≠ _
        rw [submissions.frame_read d installed hentry]
        exact off)
      (by rw [submissions.frame_excess d installed hentry]; exact wordRun)
      rejected) hgas

/-- **A direct transaction while slot 0 holds the inhibitor reverts**, whatever its calldata and value. -/
abbrev transaction_inhibited := @Submissions.transaction_inhibited submissions @frameReverts_inhibited

/-- **A direct transaction with calldata of neither form reverts.** -/
theorem transaction_badLength (index : Nat) (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (caller : E ≠ systemAddress) (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess 2 (benv.state.getStor t)) 17 1 17 0 n out)
    (other : tx.data.length.toB256 ≠ (48 : B256)) (nonzero : tx.data.length.toB256 ≠ 0)
    (hgas : i + revertBound n ≤ tx.gas) :
    Submissions.TxReverted benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f (revertBound n) :=
  submissions.transaction_reverts d installed hprecomp (fun _ hentry =>
    frameReverts_badLength (out := out) rfl (submissions.frame_fork d hentry) caller
      (by
        show Devm.getStorVal _ t 0 ≠ _
        rw [submissions.frame_read d installed hentry]
        exact off)
      (by rw [submissions.frame_excess d installed hentry]; exact wordRun)
      other nonzero) hgas

/-- **A direct fee read carrying value reverts.** -/
theorem transaction_paidRead (index : Nat) (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t)
    (caller : E ≠ systemAddress) (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess 2 (benv.state.getStor t)) 17 1 17 0 n out)
    (empty : tx.data = []) (paid : tx.value.toB256 ≠ 0) (hgas : i + revertBound n ≤ tx.gas) :
    Submissions.TxReverted benv bout tx index E (twoPrice benv.stat.baseFeePerGas prio maxFee) i f (revertBound n) :=
  submissions.transaction_reverts d installed hprecomp (fun _ hentry =>
    frameReverts_paidRead (out := out) rfl (submissions.frame_fork d hentry) caller
      (by
        show Devm.getStorVal _ t 0 ≠ _
        rw [submissions.frame_read d installed hentry]
        exact off)
      (by rw [submissions.frame_excess d installed hentry]; exact wordRun)
      empty paid) hgas

end Blanc.Lift.BuilderRequest.Exit
