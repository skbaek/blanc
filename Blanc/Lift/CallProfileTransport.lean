import Blanc.Lift.GasErasureRun
import Blanc.Lift.ExactWalkCallChild

/-!
# Full-state transport for exact call profiles

Normalizing execution gas loses no other machine column. These lemmas preserve the complete
`Devm`, including all child-world, refund, access, state-gas and tracking metadata. They apply
to ordinary callees and identity-precompile resumes; no contract or selected opcode walk is
assumed here.
-/

namespace Blanc

open Jaune

/-- Equality modulo gas becomes literal equality after choosing a common gas value. -/
theorem Devm.EqModGas.withGasLeft_eq {a b : Devm} (h : EqModGas a b) (G : Nat) :
    a.withGasLeft G = b.withGasLeft G := by
  apply Devm.ext
  · apply Mach.ext
    · exact h.stack
    · exact h.memory
    · rfl
    · exact h.stateGas
  · apply Meta.ext
    · exact h.logs
    · exact h.refundCounter
    · exact h.output
    · exact h.accountsToDelete
    · exact h.returnData
    · exact h.error
    · exact h.accessedAddresses
    · exact h.accessedStorageKeys
    · exact h.createdAccounts
    · exact h.accountReads
    · exact h.storageReads
    · exact h.touchedAccounts
  · apply World.ext
    · exact h.state
    · exact h.transientStorage
    · exact h.storageWrites

/-- Literal equality after gas normalization proves agreement on every other column. -/
theorem Devm.EqModGas.of_normalized_eq {a b : Devm}
    (h : a.withGasLeft 0 = b.withGasLeft 0) : EqModGas a b := by
  have hz : EqModGas (a.withGasLeft 0) (b.withGasLeft 0) := h ▸ .refl _
  exact (Devm.EqModGas.withGasLeft a 0).trans
    (hz.trans (Devm.EqModGas.withGasLeft b 0).symm)

/-- Replacing stack and memory preserves full agreement modulo gas, at arbitrary residuals. -/
theorem Devm.EqModGas.st {a b : Devm} (h : EqModGas a b) (S : List B256) (M : Mem)
    (G H : Nat) : EqModGas (Lift.St a S M G) (Lift.St b S M H) := by
  apply of_normalized_eq
  change Lift.St (a.withGasLeft 0) S M 0 = Lift.St (b.withGasLeft 0) S M 0
  rw [h.withGasLeft_eq 0]

/-- Warming a callee preserves full agreement modulo gas. -/
theorem Devm.EqModGas.addAccessedAddress {a b : Devm} (h : EqModGas a b) (t : Adr) :
    EqModGas (Jaune.addAccessedAddress a t) (Jaune.addAccessedAddress b t) := by
  apply of_normalized_eq
  change Jaune.addAccessedAddress (a.withGasLeft 0) t =
    Jaune.addAccessedAddress (b.withGasLeft 0) t
  rw [h.withGasLeft_eq 0]

/-- Parent preparation changes only gas as the chosen forwarded charge changes. -/
theorem Devm.EqModGas.callSpawnParent {a b : Devm} (h : EqModGas a b)
    (ca cb ii is oi os : Nat) :
    EqModGas (Blanc.callSpawnParent a ca ii is oi os) (Blanc.callSpawnParent b cb ii is oi os) := by
  apply of_normalized_eq
  change (Blanc.callSpawnParent (a.withGasLeft 0) 0 ii is oi os).withGasLeft 0 =
    (Blanc.callSpawnParent (b.withGasLeft 0) 0 ii is oi os).withGasLeft 0
  rw [h.withGasLeft_eq 0]

/-- Resuming agreeing parents with agreeing child posts preserves every column except gas. -/
theorem Devm.EqModGas.callChildPost {a b c d : Devm} (hp : EqModGas a b) (hc : EqModGas c d)
    (oi os : Nat) : EqModGas (Lift.callChildPost a c oi os) (Lift.callChildPost b d oi os) := by
  apply of_normalized_eq
  change (Lift.callChildPost (a.withGasLeft 0) (c.withGasLeft 0) oi os).withGasLeft 0 =
    (Lift.callChildPost (b.withGasLeft 0) (d.withGasLeft 0) oi os).withGasLeft 0
  rw [hp.withGasLeft_eq 0, hc.withGasLeft_eq 0]

end Blanc

namespace Blanc.Lift.AllGasCall

open Jaune Blanc

section Cross

variable (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat) (t ii is oi : B256)

end Cross



end Blanc.Lift.AllGasCall
