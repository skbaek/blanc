import Blanc.BeaconDeposit
import Blanc.ForwardNoRawSstore

/-!
# Beacon deposit reachable error catalogue

The source model has one additional `assert_false` label, proved unreachable
and intentionally omitted from the executable.  This catalogue indexes only
the eight compiled `require` auxiliaries and locks each model reason to its
stable function-table coordinate.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- The eight model reasons that have compiled `Error(string)` auxiliaries. -/
inductive ReachableReason
  | pubkeyLength
  | withdrawalCredentialsLength
  | signatureLength
  | valueTooLow
  | valueNotGweiMultiple
  | valueTooHigh
  | depositDataRootMismatch
  | merkleTreeFull
deriving DecidableEq

/-- The source-model reason represented by one compiled auxiliary. -/
def ReachableReason.reason : ReachableReason → Reason
  | .pubkeyLength => .pubkey_length
  | .withdrawalCredentialsLength => .withdrawal_credentials_length
  | .signatureLength => .signature_length
  | .valueTooLow => .value_too_low
  | .valueNotGweiMultiple => .value_not_gwei_multiple
  | .valueTooHigh => .value_too_high
  | .depositDataRootMismatch => .deposit_data_root_mismatch
  | .merkleTreeFull => .merkle_tree_full

/-- Stable function-table coordinate of one compiled error auxiliary. -/
def ReachableReason.slot : ReachableReason → Nat
  | .pubkeyLength => pubkeyLengthErrorSlot
  | .withdrawalCredentialsLength => withdrawalLengthErrorSlot
  | .signatureLength => signatureLengthErrorSlot
  | .valueTooLow => valueTooLowErrorSlot
  | .valueNotGweiMultiple => valueNotGweiErrorSlot
  | .valueTooHigh => valueTooHighErrorSlot
  | .depositDataRootMismatch => rootMismatchErrorSlot
  | .merkleTreeFull => treeFullErrorSlot

/-- Every reachable catalogue row is distinct from the omitted terminal
`assert_false` label. -/
theorem ReachableReason.reason_ne_assertFalse (error : ReachableReason) :
    error.reason ≠ .assert_false := by
  cases error <;> simp [ReachableReason.reason]

/-- The runtime table contains the exact constant-error body at every
catalogued slot. -/
theorem reachableError_lookup (error : ReachableReason) :
    (runtime.main :: runtime.aux)[error.slot]? =
      some (Func.revWith (reasonString error.reason)) := by
  cases error <;> rfl

/-- Contract specialization of the shared constant-error guard walk. -/
theorem reachableErrorGuard_runCompiledTo
    {sevm : Sevm} {devm : Devm} {G : Nat} {w : B256}
    {stack : List B256} {img : Bytes} {otherwise : Func}
    (error : ReachableReason)
    (h_ne : w ≠ 0) (h_stack : devm.stack = w :: stack)
    (hwf : Mem.Wf devm.memory) (hr : Mem.Reads devm.memory img)
    (halign : devm.memory.size % 32 = 0)
    (h_blob : (errorData (reasonString error.reason)).length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData (reasonString error.reason))).length < 2 ^ 256)
    (h_gas : devm.gasLeft =
      G + errorGuardCost devm (reasonString error.reason))
    (h_room : devm.stack.length < 1024) :
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm devm
      ((.call error.slot) <?> otherwise)
      (.error (.revert,
        (devm.setMach ⟨stack,
          Mem.writeStoresRev devm.memory
            (bytesWords (errorData (reasonString error.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString error.reason)))) := by
  exact Func.runCompiledTo_errorGuard (reachableError_lookup error)
    h_ne h_stack hwf hr halign h_blob h_words h_gas h_room

/-- Gas-normalized form of `reachableErrorGuard_runCompiledTo` for a guard
entered from an ordinary `setMach` state.  The arbitrary `otherwise` arm is
unreachable on the nonzero flag. -/
theorem reachableErrorGuard_exact_runCompiledTo
    {sevm : Sevm} {base : Devm} {G : Nat} {w : B256}
    {stack : List B256} {img : Bytes} {otherwise : Func}
    (error : ReachableReason)
    (h_ne : w ≠ 0)
    (hwf : Mem.Wf base.memory) (hr : Mem.Reads base.memory img)
    (halign : base.memory.size % 32 = 0)
    (h_blob : (errorData (reasonString error.reason)).length < 2 ^ 256)
    (h_words : 32 *
      (bytesWords (errorData (reasonString error.reason))).length < 2 ^ 256)
    (h_room : stack.length < 1022) :
    Func.RunCompiledTo (runtime.main :: runtime.aux) sevm
      (base.setMach ⟨w :: stack, base.memory,
        G + errorGuardCost base (reasonString error.reason)⟩)
      ((.call error.slot) <?> otherwise)
      (.error (.revert,
        (base.setMach ⟨stack,
          Mem.writeStoresRev base.memory
            (bytesWords (errorData (reasonString error.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString error.reason)))) := by
  exact Func.runCompiledTo_errorGuard (reachableError_lookup error)
    h_ne rfl hwf hr halign h_blob h_words (by
      simp only [Devm.gasLeft_setMach, errorGuardCost, errorCallCost,
        errorBodyCost, Devm.extCost, Devm.memory_setMach]) (by
      simp only [Devm.stack_setMach, List.length_cons]
      omega)

/-- The selected catalogue guard and its constant-error callee contain no raw
`SSTORE`.  The nonzero flag rules out the continuation arm before the proof
enters the table body. -/
theorem reachableErrorGuard_noRawSstorePath
    {sevm : Sevm} {devm : Devm} {G : Nat} {w : B256}
    {stack : List B256} {otherwise : Func} (error : ReachableReason)
    {run : Func.RunCompiledTo (runtime.main :: runtime.aux) sevm devm
      ((.call error.slot) <?> otherwise)
      (.error (.revert,
        (devm.setMach ⟨stack,
          Mem.writeStoresRev devm.memory
            (bytesWords (errorData (reasonString error.reason))).zipIdx,
          G⟩).withOutput (errorData (reasonString error.reason))))}
    (h_ne : w ≠ 0) (h_stack : devm.stack = w :: stack) :
    Func.RunCompiledTo.NoRawSstorePath run := by
  cases run with
  | zero room pop tail =>
      have heads := h_stack.symm.trans pop.stack
      have hzero : w = 0 := List.cons.inj heads |>.1
      exact (h_ne hzero).elim
  | succ nonzero room pop tail =>
      cases tail with
      | call lookup callRoom burn errorRun =>
          have bodyEq := Option.some.inj
            (lookup.symm.trans (reachableError_lookup error))
          subst bodyEq
          exact .succ (nonzero := nonzero) (room := room) (pop := pop)
            (.call (lookup := lookup) (room := callRoom) (burn := burn)
              (Func.RunCompiledTo.NoRawSstorePath.of_revWith errorRun))

end Blanc.BeaconDeposit
