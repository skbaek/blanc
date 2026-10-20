import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.InvWalkOps

/-!
# Indexed loads from three carried words

`pickWord3` selects a word from a three-word layout. `word3_indexAddr` relates the EVM
address arithmetic to its natural offset without wrap. `ri_mloadWord3` inverts an indexed
load over the shared `Words` carrier and preserves an already aligned allocation.
-/

namespace Blanc.Lift

open Jaune

/-- Select one of three words; callers establish that the index is below three. -/
def pickWord3 (n : Nat) (a0 a1 a2 : B256) : B256 :=
  if n = 0 then a0 else if n = 1 then a1 else a2

/-- The word address of a three-element array, with enough room to avoid wrapping. -/
theorem word3_indexAddr {i bw : B256} (hi : i.toNat < 3) (hb : bw.toNat < 2 ^ 255) :
    (Bytes.toB256 [0x20] * i + bw).toNat = bw.toNat + 32 * i.toNat := by
  have h32 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  rw [B256.toNat_add, B256.toNat_mul, h32]
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- Read one of three consecutive carried words without extending aligned memory. -/
theorem ri_mloadWord3 {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    {LW : List (Nat × B256)} {base : Nat} {a i a0 a1 a2 : B256}
    (hW : Words M LW) (hal : M.size % 32 = 0)
    (h0 : (base, a0) ∈ LW) (h1 : (base + 32, a1) ∈ LW) (h2 : (base + 64, a2) ∈ LW)
    (hi : i.toNat < 3) (ha : a.toNat = base + 32 * i.toNat)
    (h : Ninst.Run sevm (St b (a :: S) M G) (.reg .mload) d) :
    ∃ G', d = St b (pickWord3 i.toNat a0 a1 a2 :: S) M G' := by
  obtain ⟨G', rfl⟩ := ri_mload h
  unfold pickWord3
  have he : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 := by omega
  rcases he with e | e | e <;> rw [e] at ha ⊢ <;>
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, ↓reduceIte,
      OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero] at ha ⊢
  · obtain ⟨hv, hM⟩ := hW.read hal h0
    rw [ha, hv, hM]
    exact ⟨G', rfl⟩
  · obtain ⟨hv, hM⟩ := hW.read hal h1
    rw [ha, hv, hM]
    exact ⟨G', rfl⟩
  · obtain ⟨hv, hM⟩ := hW.read hal h2
    rw [ha, hv, hM]
    exact ⟨G', rfl⟩

end Blanc.Lift
