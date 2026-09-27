import Blanc.Lift.LidoCircuitBreakerDeployed.Writers

/-!
# L2 for the whole `registerPauser(t, 0)` frame

The whole-frame corollary of `L2.lean` (decision D1): a successful run of the
deployed `registerPauser` wrapper with `np = 0` (calldata word 36) leaves the
L2 removal effects of `t` (calldata word 4) on the frame's final storage, the
same facts `l2_entry32_found`/`l2_entry32_absent` state right after entry 32.
The only later writes are entry 22's `heartbeatExpiry` stores, which are
`ForeignApart` by the frame's `lidoA` premise and so miss every raw slot L2
reads (each is the raw slot of a Registry-observable key at bound `2 ^ 160`).
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

/-- An off-Registry write misses the raw slot of every observed key. -/
theorem foreign_get {s : Stor} {w v key : B256} (hfa : ForeignApart (2 ^ 160) w)
    (hk : RegistryObservable (2 ^ 160) key) : (s.set w v).get (solKey key) = s.get (solKey key) :=
  Stor.get_set_ne s (hfa key hk).symm v

/-- The L2 removal effects of `setPauser(t, 0)` on a raw storage, relative to the
pre-call witness `entries`. -/
def L2Post (entries : List Entry) (t : B256) (s : Stor) : Prop :=
  nonzeroCanonicalAddress t ∧
  addressSlotReadWord (s.get (mapSlot t 3)) = 0 ∧
  s.get (mapSlot t 4) = 0 ∧
  (∃ entries', RegistryWitness (solRegistryStorage s) entries' ∧ t ∉ entries'.map Prod.fst) ∧
  match findEntry entries t with
  | some (index, _) =>
      addressSlotReadWord (s.get (registryArraySlot (entries.length - 1))) = 0 ∧
      s.get 5 = Nat.toB256 (entries.length - 1) ∧
      (index + 1 < entries.length →
        addressSlotReadWord (s.get (registryArraySlot index)) = sourceLastTarget entries ∧
        s.get (mapSlot (sourceLastTarget entries) 4) = Nat.toB256 (index + 1)) ∧
      (index + 1 = entries.length → sourceLastTarget entries = t)
  | none =>
      addressSlotReadWord (s.get (registryArraySlot entries.length)) = 0 ∧
      s.get 5 = Nat.toB256 entries.length

theorem L2Post.set_foreign {entries : List Entry} {t : B256} {s : Stor} {w v : B256}
    (hvalid : ∀ e ∈ entries, nonzeroCanonicalAddress e.1)
    (hlen : entries.length < 2 ^ 160)
    (hfa : ForeignApart (2 ^ 160) w) (h : L2Post entries t s) :
    L2Post entries t (s.set w v) := by
  have ht : canonicalAddress t := h.1.2
  have hlt : entries.length < 2 ^ 252 := by
    have : (2 : Nat) ^ 160 < 2 ^ 252 := by norm_num
    omega
  have gA : (s.set w v).get (mapSlot t 3) = s.get (mapSlot t 3) := by
    rw [← solKey_assignmentSlot ht]; exact foreign_get hfa (Or.inl ⟨t, ht, rfl⟩)
  have gI : ∀ {p}, canonicalAddress p → (s.set w v).get (mapSlot p 4) = s.get (mapSlot p 4) := by
    intro p hp
    rw [← solKey_indexSlot hp]; exact foreign_get hfa (Or.inr (Or.inl ⟨p, hp, rfl⟩))
  have gL : (s.set w v).get 5 = s.get 5 := by
    rw [← solKey_arrayLengthSlot]; exact foreign_get hfa (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have gArr : ∀ {i}, i < 2 ^ 160 →
      (s.set w v).get (registryArraySlot i) = s.get (registryArraySlot i) := by
    intro i hi
    have hk := solKey_arrayEntrySlot (index := i) (by omega)
    rw [← hk]
    exact foreign_get hfa (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, hi, rfl⟩))))
  obtain ⟨htn, ha, hi, ⟨e', hwe, hne⟩, hrest⟩ := h
  refine ⟨htn, by rw [gA]; exact ha, by rw [gI ht]; exact hi,
    ⟨e', RegistryWitness.of_foreign_set_160 hfa hwe, hne⟩, ?_⟩
  cases hf : findEntry entries t with
  | none =>
    rw [hf] at hrest
    obtain ⟨h1, h2⟩ := hrest
    exact ⟨by rw [gArr hlen]; exact h1, by rw [gL]; exact h2⟩
  | some val =>
    obtain ⟨index, old⟩ := val
    rw [hf] at hrest
    obtain ⟨h1, h2, h3, h4⟩ := hrest
    have hidx := findEntry_index_lt hf
    refine ⟨by rw [gArr (by omega)]; exact h1, by rw [gL]; exact h2, fun hnl => ?_, h4⟩
    obtain ⟨h31, h32⟩ := h3 hnl
    obtain ⟨lastE, hlastE⟩ := last_some_of_length_pos entries (by omega)
    have hsrc : sourceLastTarget entries = lastE.1 := by simp [sourceLastTarget, hlastE]
    refine ⟨by rw [gArr (by omega)]; exact h31, ?_⟩
    have hmc : canonicalAddress (sourceLastTarget entries) := by
      rw [hsrc]
      exact (hvalid lastE (last_mem_of_last entries hlastE)).2
    rw [gI hmc]; exact h32

/-- **L2, whole `registerPauser(t, 0)` frame.**  A successful run of the
deployed `registerPauser` wrapper whose second argument word is zero leaves, on
the frame's final storage, the removal effects of its first argument `t`
(`L2Post`): relative to the frame-entry witness `entries`, `t`'s assignment and
index cleared and `t` absent from the post witness, and (found) the vacated
tail's address cleared, length `n - 1`, the moved element at the hole with its
index repaired unless hole = tail, or (absent) the pushed slot cleared and the
length unchanged. -/
theorem l2_registerPauser_zero {sevm : Sevm} {d : Devm} {o : Outcome} {w : SFunc}
    {entries : List Entry}
    (hfork : CoveredFork sevm.benvStat.fork) (hw : prog[59]? = some w)
    (hA : EntryAt lidoA sevm d) (hmem : MemOK d.memory)
    (hwit : RegistryWitness (solRegistryStorage (Devm.getStor d sevm.currentTarget)) entries)
    (hnp0 : Sevm.dataWord sevm 36 = 0) (run : SFunc.Run prog sevm d w o) :
    L2Post entries (Sevm.dataWord sevm 4) (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
  have hlen : entries.length < 2 ^ 160 := by
    have := hwit.entries_length_le
    have : 0 < 2 ^ 160 := by norm_num
    omega
  have hAe := hA entries hwit
  refine registerPauser_wrapper_foreign (Φ := L2Post entries (Sevm.dataWord sevm 4))
    (fun hfa h => h.set_foreign hwit.targetsValid hlen hfa) hfork hw hA hmem hwit ?_ run
  intro ht _ ht0 b' M' G' base post hs hm r
  rw [hnp0] at r
  have htn : nonzeroCanonicalAddress (Sevm.dataWord sevm 4) := ⟨ht0, ht⟩
  have hk := hAe.2 htn
  have hw' : RegistryWitness (solRegistryStorage (Devm.getStor b' sevm.currentTarget)) entries := by
    rw [hs]; exact hwit
  cases hf : findEntry entries (Sevm.dataWord sevm 4) with
  | none =>
    simp only [setPauserKeys, hf, ↓reduceIte] at hk
    obtain ⟨hwp, hnm, ha, hi, htail, hl⟩ :=
      l2_entry32_absent hfork hm.1 hm.2 hw' htn hf (hk.bound_mono (by omega)) r
    refine ⟨htn, ha, hi, ⟨entries, hwp, hnm⟩, ?_⟩
    simp only [hf]
    exact ⟨htail, hl⟩
  | some val =>
    obtain ⟨index, old⟩ := val
    simp only [setPauserKeys, hf, ↓reduceIte] at hk
    obtain ⟨hwp, hnm, ha, hi, htail, hl, hmv, hal⟩ :=
      l2_entry32_found hfork hm.1 hm.2 hw' htn hf (hk.bound_mono (by omega)) r
    refine ⟨htn, ha, hi, ⟨_, hwp, hnm⟩, ?_⟩
    simp only [hf]
    exact ⟨htail, hl, hmv, hal⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
