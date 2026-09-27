import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryLayout

/-!
# Preservation of Lido Registry Witness under Foreign Writes

This module defines `ForeignApart`, capturing when a raw storage slot does not
collide with any slot observed by the deployed Lido Registry layout up to a given
bound. It proves that writing to such a foreign slot preserves the `RegistryWitness`
invariants on the deployed storage projection `solRegistryStorage`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc Blanc.LidoCircuitBreaker

/-- A raw Solidity storage slot `w` that is disjoint from the deployed storage
slots of all logical keys observed by a registry witness up to `bound`. This
serves as a per-written-slot collision premise ensuring that a foreign write to
slot `w` does not disturb any storage location mapped from the registry's observed
keys, avoiding any need for global Keccak injectivity. -/
def ForeignApart (bound : Nat) (w : B256) : Prop :=
  ∀ k, RegistryObservable bound k → solKey k ≠ w

/-- Monotonicity of registry observation with respect to the array bound: any
logical key observed under a smaller bound `b` is also observed under any larger
bound `b'`. The assignment, index, count, and array length slots are independent
of the bound, while array entry indices strictly below `b` remain strictly below `b'`. -/
theorem RegistryObservable.mono {b b' : Nat} {k : B256}
    (h : RegistryObservable b k) (hle : b ≤ b') :
    RegistryObservable b' k := by
  rcases h with
    ⟨probe, hp, rfl⟩ | ⟨probe, hp, rfl⟩ | ⟨probe, hp, rfl⟩ |
      rfl | ⟨i, hi, rfl⟩
  · exact Or.inl ⟨probe, hp, rfl⟩
  · exact Or.inr (Or.inl ⟨probe, hp, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨probe, hp, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, by omega, rfl⟩)))

/-- Faithfulness of registry key mappings is antitone in the bound: if written
keys in `T` have no collisions with any logical keys observed up to a larger
bound `b'`, then they have no collisions with logical keys observed up to a
smaller bound `b ≤ b'`. -/
theorem RegistryKeysFaithful.bound_mono {b b' : Nat} {T : List B256}
    (h : RegistryKeysFaithful b' T) (hle : b ≤ b') :
    RegistryKeysFaithful b T :=
  fun t ht k hk heq => h t ht k (hk.mono hle) heq

/-- Separation of a foreign slot is antitone in the bound: if raw slot `w`
is disjoint from all registry slots observed up to bound `b'`, it is also disjoint
from all registry slots observed up to any smaller bound `b ≤ b'`. -/
theorem ForeignApart.bound_mono {b b' : Nat} {w : B256}
    (h : ForeignApart b' w) (hle : b ≤ b') :
    ForeignApart b w :=
  fun k hk => h k (hk.mono hle)

/-- A raw storage write to a foreign slot `w` preserves the registry witness.
Because `w` is apart from all observed registry keys up to `bound`, reading any
observed slot in the updated storage `s.set w v` returns the same value as in
`s`, transporting all nine invariant fields of the witness unchanged. -/
theorem RegistryWitness.of_foreign_set {s : Stor} {entries : List Entry} {bound : Nat} {w v : B256}
    (hlength : bound < 2 ^ 252) (hbound : entries.length ≤ bound)
    (hapart : ForeignApart bound w)
    (h : RegistryWitness (solRegistryStorage s) entries) :
    RegistryWitness (solRegistryStorage (s.set w v)) entries := by
  have hread : ∀ key, RegistryObservable bound key →
      (solRegistryStorage (s.set w v)).read key = (solRegistryStorage s).read key := by
    intro key hkey
    apply solRegistryStorage_read_congr hlength hkey
    exact Stor.get_set_ne s (hapart key hkey).symm v
  exact {
    targetsNodup := h.targetsNodup
    targetsValid := h.targetsValid
    pausersValid := h.pausersValid
    lengthWord := by
      rw [hread arrayLengthSlot (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
      exact h.lengthWord
    arrayWords := by
      intro probe hprobe
      rw [hread _ (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨probe, by omega, rfl⟩))))]
      exact h.arrayWords probe hprobe
    assignments := by
      intro probe hprobe
      rw [hread _ (Or.inl ⟨probe, hprobe, rfl⟩)]
      exact h.assignments probe hprobe
    indices := by
      intro probe hprobe
      rw [hread _ (Or.inr (Or.inl ⟨probe, hprobe, rfl⟩))]
      exact h.indices probe hprobe
    counts := by
      intro probe hprobe
      rw [hread _ (Or.inr (Or.inr (Or.inl ⟨probe, hprobe, rfl⟩)))]
      exact h.counts probe hprobe
    zeroCount := by
      have hzero : canonicalAddress (0 : B256) := by
        unfold canonicalAddress
        change (0 : Nat) < 2 ^ 160
        norm_num
      rw [hread _ (Or.inr (Or.inr (Or.inl ⟨0, hzero, rfl⟩)))]
      exact h.zeroCount
  }

/-- A raw storage write to a foreign slot `w` preserves the registry witness at
the canonical bound `2 ^ 160`. The bound on the number of entries is derived
directly from the pre-state witness via `RegistryWitness.entries_length_le`,
discharging the entry-count premise automatically. -/
theorem RegistryWitness.of_foreign_set_160 {s : Stor} {entries : List Entry} {w v : B256}
    (hapart : ForeignApart (2 ^ 160) w)
    (h : RegistryWitness (solRegistryStorage s) entries) :
    RegistryWitness (solRegistryStorage (s.set w v)) entries := by
  have hbound : entries.length ≤ 2 ^ 160 := by
    have hle := h.entries_length_le
    omega
  have hlength : 2 ^ 160 < 2 ^ 252 := by
    norm_num
  exact of_foreign_set hlength hbound hapart h

end Blanc.Lift.LidoCircuitBreakerDeployed
