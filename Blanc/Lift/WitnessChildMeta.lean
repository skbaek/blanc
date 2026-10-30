import Blanc.Lift.WitnessChild

/-!
# A frame entry's accessed sets and world, for any frame

`frameEnterS_run_meta` states, for an arbitrary frame and account shadow, that the entered
machine keeps the spawn message's accessed sets and carries the world the value transfer made.
Proving it once over variables lets a concrete witness instantiate it without the kernel
re-evaluating the concrete call preparation (a projection of a concrete `CallPrep` checked by
`rfl` forces the whole run that produced it). Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

theorem frameEnterS_run_meta {f : Frame} {acs : AcctShadow} {e : Evm}
    (h : frameEnterS f acs = .run e) :
    ∃ benv, benvAfterTransferS f.inner acs = .ok benv ∧
      e.dyna.accessedAddresses = f.inner.accessedAddresses ∧
      e.dyna.accessedStorageKeys = f.inner.accessedStorageKeys ∧
      e.dyna.state = benv.state := by
  obtain ⟨benv, hb, he⟩ := frameEnterS_run h
  exact ⟨benv, hb, by rw [he]; rfl, by rw [he]; rfl, by rw [he]; rfl⟩

end Blanc.Lift.Witness
