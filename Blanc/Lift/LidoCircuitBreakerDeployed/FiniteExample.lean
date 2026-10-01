import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteUpdate

/-!
# Concrete applicability of finite Lido observations

One target (`1`) starts with pauser `2`, and is updated to pauser `3`.
The probe list includes reserved address `0` explicitly. The initial raw
storage is constructed, not assumed to have a global registry witness.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc Blanc.LidoCircuitBreaker

def exampleEntries : List LidoCircuitBreaker.Entry := [(1, 2)]
def exampleProbes : List B256 := [0, 1, 2, 3]
def exampleInitialWrites : List (B256 × B256) :=
  [(assignmentSlot 1, 2), (arrayEntrySlot 1, 1), (indexSlot 1, 1),
    (arrayLengthSlot, 1), (countSlot 2, 1)]
def exampleStorage : Stor := applyRegistryRawWrites Stor.empty exampleInitialWrites

private theorem exampleProbes_valid : ∀ p ∈ exampleProbes, canonicalAddress p := by
  intro p hp
  simp only [exampleProbes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> unfold canonicalAddress <;> decide

/-- The actual nonempty raw pre-state follows from a finite construction check.
The proof transports chronological writes, avoiding evaluation of an entire
concrete storage tree. -/
theorem exampleRegistryOn_of_check
    (hcheck : SlotFootprint.checkFaithfulOn solKey (registryQueries exampleProbes 1)
      (exampleInitialWrites.map Prod.fst) = true) :
    RegistryOn (solRegistryStorage exampleStorage) exampleEntries exampleProbes := by
  have htarget : nonzeroCanonicalAddress (1 : B256) := by
    constructor
    · decide
    · unfold canonicalAddress; decide
  have hnew : nonzeroCanonicalAddress (2 : B256) := by
    constructor
    · decide
    · unfold canonicalAddress; decide
  have hlogical : RegistryWitness
      { read := fun key => exampleInitialWrites.foldl
          (fun cur w => if w.1 = key then w.2 else cur) 0 } exampleEntries := by
    apply RegistryWitness.applyFreshWritesOfReadEffect emptyWitness htarget hnew (by rfl)
    intro key; rfl
  apply (registryOn_of_modelWitness hlogical exampleProbes_valid).of_read_eq
  intro key hk
  change key ∈ registryQueries exampleProbes 1 at hk
  have hobs := registryQueries_observable exampleProbes_valid hk
  have hwobs : ∀ w ∈ exampleInitialWrites, RegistryObservable 1 w.1 := by
    intro w hw
    apply registryQueries_observable exampleProbes_valid
    simp only [exampleInitialWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;>
      simp only [registryQueries, List.range_one, List.map_cons, zero_add,
        show Nat.toB256 1 = (1 : B256) from rfl, List.map_nil, exampleProbes, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false, true_or, or_true]
  have hclean : ∀ w ∈ exampleInitialWrites,
      RegistryAddressFamily 1 w.1 → addressSlotReadWord w.2 = w.2 := by
    intro w hw _
    simp only [exampleInitialWrites, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> rfl
  unfold exampleStorage
  rw [solRegistryStorage_applyRegistryRawWrites_at (by norm_num : 1 < 2 ^ 252)
    (fun t ht => SlotFootprint.checkFaithfulOn_eq_true.mp hcheck t ht key hk)
    hwobs hclean hobs]
  have hzero : (solRegistryStorage Stor.empty).read key = 0 := by
    have hz : addressSlotReadWord 0 = 0 := rfl
    simp only [solRegistryStorage, Nat.reducePow, Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
      Std.TreeMap.getD_emptyc, hz, ite_self]
  rw [hzero]

/-- Concrete separation for the constructed five-write pre-state, discharged
by kernel reduction of the executable finite checker. -/
theorem exampleInitialCheck :
    SlotFootprint.checkFaithfulOn solKey (registryQueries exampleProbes 1)
      (exampleInitialWrites.map Prod.fst) = true := by
  decide +kernel

/-- The update's three logical writes and two raw heartbeat writes pass the
same finite query checks. The constructor's two raw writes also pass for these
probes. All three results are kernel computations, not external digests. -/
theorem exampleSeparationChecks :
    SlotFootprint.checkFaithfulOn solKey (registryQueries exampleProbes exampleEntries.length)
      ((nonzeroWrites exampleEntries 1 3 2).map Prod.fst) = true ∧
    SlotFootprint.checkApartOn solKey (registryQueries exampleProbes exampleEntries.length)
      [mapSlot 2 2, mapSlot 3 2] = true ∧
    SlotFootprint.checkApartOn solKey (registryQueries exampleProbes 0) [0, 1] = true := by
  decide +kernel

/-- A concrete nonempty raw pre-state simultaneously satisfies every finite
state, coverage, closure and separation requirement of the nonzero update.
This certifies applicability of those premises; it does not assert an
empty-constructor-to-update execution history or supply a successful call. -/
theorem exampleApplicable :
    checkRegistryOn (solRegistryStorage exampleStorage) exampleEntries exampleProbes = true ∧
    checkLiveCovered exampleEntries exampleProbes = true ∧
    findEntry exampleEntries 1 = some (0, 2) ∧
    ((1 : B256) ∈ exampleProbes ∧ (2 : B256) ∈ exampleProbes ∧ (3 : B256) ∈ exampleProbes) ∧
    (3 : B256) ≠ 0 ∧
    SlotFootprint.checkFaithfulOn solKey (registryQueries exampleProbes exampleEntries.length)
      ((nonzeroWrites exampleEntries 1 3 2).map Prod.fst) = true ∧
    SlotFootprint.checkApartOn solKey (registryQueries exampleProbes exampleEntries.length)
      [mapSlot 2 2, mapSlot 3 2] = true := by
  exact ⟨checkRegistryOn_eq_true.mpr (exampleRegistryOn_of_check exampleInitialCheck),
    by decide, by decide, by decide, by decide,
    exampleSeparationChecks.1, exampleSeparationChecks.2.1⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
