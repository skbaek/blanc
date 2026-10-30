import Blanc.Lift.LidoCircuitBreakerDeployed.LiveObservation

/-!
# A kernel-checked finite registry observation of the live CircuitBreaker

`Live.words` (generated, `LiveObservation.lean`) lists the raw storage words of the deployed
CircuitBreaker at block 26,141,229 that the finite registry observation reads: the array
length, every live array cell, and the assignment/index/count words of every probe.
`lido_live_registryOn` states that any raw storage agreeing with those words carries the finite
observation `RegistryOn` for the live entries at the probes. The check is a kernel decision on
the observed words (`checkRegistryOn` and query coverage), replacing an external script check;
the only premise is the one-block storage observation itself.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed.Live

open Jaune Blanc.LidoCircuitBreaker

/-- The Registry decode of `solRegistryStorage`, over an arbitrary raw-slot reader. -/
def solRegistryRead (get : B256 → B256) (key : B256) : B256 :=
  let region := key.toNat / 2 ^ 252
  let payload := Nat.toB256 (key.toNat % 2 ^ 252)
  if region = assignmentRegion then
    addressSlotReadWord (get (mapSlot payload 3))
  else if region = indexRegion then
    get (mapSlot payload 4)
  else if region = countRegion then
    get (mapSlot payload 6)
  else if region = arrayRegion then
    if payload = 0 then get 5
    else addressSlotReadWord
      (get (registryArrayBase + (payload - 1)))
  else 0

theorem solRegistryStorage_read (s : Stor) (key : B256) :
    (solRegistryStorage s).read key = solRegistryRead s.get key := rfl

/-- The decode reads exactly the raw slot `solKey` names. -/
theorem solRegistryRead_congr {get get' : B256 → B256} {key : B256}
    (h : get (solKey key) = get' (solKey key)) :
    solRegistryRead get key = solRegistryRead get' key := by
  simp only [solRegistryRead, solKey] at h ⊢
  split_ifs at h ⊢ <;> first | rfl | rw [h]

/-- The observed word at a slot (zero when unobserved). -/
def obsGet (slot : B256) : B256 :=
  ((words.find? (fun w => w.1 == slot)).map Prod.snd).getD 0

/-- The finite registry check on the observed words, by kernel evaluation. -/
theorem check_observed :
    checkRegistryOn ⟨solRegistryRead obsGet⟩ entries probes = true := by
  decide +kernel

/-- Every raw slot the finite observation reads is among the observed slots. -/
theorem queries_observed :
    (registryQueries probes entries.length).all
      (fun key => words.any (fun w => w.1 == solKey key)) = true := by
  decide +kernel

theorem obsGet_of_observed {s : Stor} (hobs : ∀ w ∈ words, s.get w.1 = w.2) {slot : B256}
    (hmem : words.any (fun w => w.1 == slot) = true) : s.get slot = obsGet slot := by
  unfold obsGet
  cases hfind : words.find? (fun w => w.1 == slot) with
  | none =>
      rw [List.find?_eq_none] at hfind
      obtain ⟨w, hw, hw'⟩ := List.any_eq_true.mp hmem
      exact absurd hw' (hfind w hw)
  | some w =>
      have hw := List.mem_of_find?_eq_some hfind
      have heq : w.1 = slot := by simpa only [beq_iff_eq] using List.find?_some hfind
      simp only [Option.map_some, Option.getD_some]
      rw [← heq]
      exact hobs w hw

/-- **The live finite registry observation.** Any raw storage of the CircuitBreaker agreeing
with the observed words at block 26,141,229 carries the finite registry observation for the
live entries (whole array) at the probes. -/
theorem lido_live_registryOn (s : Stor) (hobs : ∀ w ∈ words, s.get w.1 = w.2) :
    RegistryOn (solRegistryStorage s) entries probes := by
  apply (checkRegistryOn_eq_true.mp check_observed).of_read_eq
  intro key hk
  rw [solRegistryStorage_read]
  apply solRegistryRead_congr
  exact obsGet_of_observed hobs (List.all_eq_true.mp queries_observed key hk)

end Blanc.Lift.LidoCircuitBreakerDeployed.Live
