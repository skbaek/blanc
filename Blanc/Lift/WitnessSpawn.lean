import Blanc.Lift.WitnessChild

/-!
Frame-level spawn facts for witness runs: a machine is *spawned by* a parent machine
executing a call-family instruction when that instruction's step spawns a frame which enters
as the machine.  These lemmas read the fact off the witness engine's shadow computations
(`callPrep`, `dcallPrep`, `childStart`), so a statement about a nested execution can name
each frame's entry machine and its parent in Jaune's own terms (`Xinst.step`,
`Frame.enter`).  Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

/-- `child` is the machine of a frame that the parent machine `⟨sevm, devm⟩` spawns by
executing the call-family instruction `x`: the step spawns a frame, and that frame enters
(Jaune's `Frame.enter`, value transfer included) as `child`. -/
def SpawnedBy (sevm : Sevm) (devm : Devm) (x : Xinst) (child : Evm) : Prop :=
  ∃ f rsm, Xinst.step sevm devm x = .spawn f rsm ∧ f.enter = .run child

/-- A `CALL` computed on the shadows (`callPrep`) of an agreeing configuration, whose frame
enters on the account shadow (`frameEnterS`), spawns that machine. -/
theorem spawnedBy_of_callPrep {sevm : Sevm} {c : Cfg} {cp : CallPrep} {cevm : Evm}
    (hagree : Agree c) (hp : callPrep sevm c = some cp) (he : frameEnterS cp.f c.acs = .run cevm) :
    SpawnedBy sevm c.devm .call cevm := by
  obtain ⟨hstep, -, -, -, -, -, -, hst⟩ := callPrep_spec hp hagree.2.1 hagree.2.2.2
  refine ⟨cp.f, _, hstep, ?_⟩
  rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst]; exact hagree.2.2.2)]
  exact he

/-- The machine a code `CALL`'s child starts with (`childStart`) is spawned by that `CALL`. -/
theorem spawnedBy_of_childStart {sevm : Sevm} {c cc : Cfg} {f0 : SFunc} {cevm : Evm}
    (hagree : Agree c) (hs : childStart sevm c f0 = some (cevm, cc)) :
    SpawnedBy sevm c.devm .call cevm := by
  unfold childStart at hs
  split at hs
  · rename_i cp hp
    split at hs
    · rename_i cevm' he
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, -⟩ := hs
      exact spawnedBy_of_callPrep hagree hp he
    · cases hs
  · cases hs

/-- A `DELEGATECALL` computed on the shadows (`dcallPrep`), whose frame enters on the
account shadow, spawns that machine. -/
theorem spawnedBy_of_dcallPrep {sevm : Sevm} {devm : Devm} {adrs : List Adr} {acs : AcctShadow}
    {cp : CallPrep} {cevm : Evm} (h : dcallPrep sevm devm adrs acs = some cp)
    (hA : ∀ a, a ∈ devm.accessedAddresses ↔ a ∈ adrs) (hC : AcctAgree devm.state acs)
    (he : frameEnterS cp.f acs = .run cevm) :
    SpawnedBy sevm devm .delegatecall cevm := by
  obtain ⟨hstep, -, -, -, -, -, -, hst, -⟩ := dcallPrep_spec h hA hC
  refine ⟨cp.f, _, hstep, ?_⟩
  rw [frame_enter_eq_B, frameEnterB_eq_S (by rw [hst]; exact hC)]
  exact he

end Blanc.Lift.Witness
