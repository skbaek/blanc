import JauneConsensus.SSZ.Container

/-!
# SSZ serialization facts for consensus containers

Contract-neutral equations for Jaune's consensus SSZ: little-endian `uint64` bytes against
Jaune's big-endian `UInt64.toBytes`, the byte vector, and lists of fixed-size elements.
-/

namespace Blanc.ConsensusSsz

open Jaune JauneConsensus

/-- Little-endian `uint64` bytes are Jaune's big-endian bytes reversed. -/
theorem leBytes_eight_eq_reverse_toBytes (x : UInt64) :
    leBytes 8 x.toNat = x.toBytes.reverse := by
  have hx := x.toNat_lt
  simp only [leBytes, UInt64.toBytes, UInt32.toBytes, UInt16.toBytes, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow, dvd_refl, Nat.mod_mod_of_dvd, UInt64.toUInt16_toUInt32, UInt64.toUInt8_toUInt16, UInt64.toNat_toUInt8, UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, UInt64.toNat_toUInt16, UInt16.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, Nat.reduceMul, UInt32.toUInt8_toUInt16, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt64.toNat_toUInt32, UInt32.reduceToNat, UInt32.toNat_toUInt16, UInt64.toNat_shiftRight, UInt64.reduceToNat] <;> omega

/-- Little-endian decoding inverts little-endian encoding modulo the width. -/
theorem leNat_leBytes (n v : Nat) : leNat (leBytes n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp only [leBytes, leNat, pow_zero, Nat.mod_one]
  | succ n ih =>
    simp only [leBytes, leNat, ih]
    rw [Nat.pow_succ', Nat.mod_mul]
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.reducePow, dvd_refl, Nat.mod_mod_of_dvd]

/-- `uint64` serialization is injective. -/
theorem leBytes_eight_injective {x y : U64} (h : leBytes 8 x.toNat = leBytes 8 y.toNat) :
    x = y := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have h' := congrArg leNat h
  rw [leNat_leBytes, leNat_leBytes, Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hx),
    Nat.mod_eq_of_lt (by simpa only [Nat.reducePow] using hy)] at h'
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  exact congrArg U64.mk (UInt64.toNat_inj.mp h')

/-- An address's 20 bytes determine it. -/
theorem adr_toBytes_injective {a b : Adr} (h : a.toBytes = b.toBytes) : a = b := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  obtain ⟨b₁, b₂, b₃⟩ := b
  simp only [Adr.toBytes, B128.toBytes] at h
  obtain ⟨h₁, h⟩ := List.append_inj h rfl
  obtain ⟨h₂, h₃⟩ := List.append_inj h rfl
  have e₁ := congrArg Bytes.toUInt32 h₁
  have e₂ := congrArg Bytes.toUInt64 h₂
  have e₃ := congrArg Bytes.toUInt64 h₃
  rw [toUInt32_toBytes, toUInt32_toBytes] at e₁
  rw [UInt64.toUInt64_toBytes, UInt64.toUInt64_toBytes] at e₂ e₃
  subst e₁ e₂ e₃
  rfl

/-- A sequence of fixed-size elements serializes to the concatenation of its elements. -/
theorem serializeSeq_of_fixedSize {α : Type} [Ssz α] {k : Nat}
    (hk : Ssz.fixedSize? α = some k) (xs : Array α) :
    serializeSeq xs = xs.toList.flatMap serialize := by
  rw [serializeSeq_eq, seqParts, hk]
  exact serializeParts_fixed serialize xs.toList

/-- A byte vector serializes to its bytes. -/
theorem serialize_byteVector {n : Nat} (v : SszVector UInt8 n) :
    serialize v = v.toArray.toList := by
  change serializeSeq v.toArray = _
  rw [serializeSeq_of_fixedSize (k := 1) rfl]
  induction v.toArray.toList with
  | nil => rfl
  | cons b bs ih => simp only [List.flatMap_cons, ih]; rfl

/-- A list of fixed-size elements serializes to the concatenation of its elements. -/
theorem serialize_sszList_of_fixedSize {α : Type} [Ssz α] {k n : Nat}
    (hk : Ssz.fixedSize? α = some k) (l : SszList α n) :
    serialize l = l.toArray.toList.flatMap serialize :=
  serializeSeq_of_fixedSize hk l.toArray

/-- Jaune's four-byte constructor is the big-endian four-byte decoder. -/
theorem uint32_ofBytes_eq_toUInt32 (a b c d : UInt8) :
    UInt32.ofBytes a b c d = Bytes.toUInt32 [a, b, c, d] := by
  rw [UInt32.ofBytes_eq_halves]
  rfl

/-- Twenty bytes split 4 + 8 + 8 decode to the address of the three big-endian limbs. -/
theorem toAdr?_append {l₁ l₂ l₃ : Bytes} (h₁ : l₁.length = 4) (h₂ : l₂.length = 8)
    (h₃ : l₃.length = 8) :
    Bytes.toAdr? (l₁ ++ l₂ ++ l₃) = some ⟨l₁.toUInt32, l₂.toUInt64, l₃.toUInt64⟩ := by
  match l₁, l₂, l₃, h₁, h₂, h₃ with
  | [_, _, _, _], [_, _, _, _, _, _, _, _], [_, _, _, _, _, _, _, _], _, _, _ =>
    simp only [List.cons_append, List.nil_append, Bytes.toAdr?, uint32_ofBytes_eq_toUInt32,
      UInt64.ofBytes_eq_toUInt64]

/-- An address's 20 bytes decode back to it. -/
theorem toAdr?_toBytes (a : Adr) : Bytes.toAdr? a.toBytes = some a := by
  obtain ⟨a₁, a₂, a₃⟩ := a
  simp only [Adr.toBytes, B128.toBytes, ← List.append_assoc]
  rw [toAdr?_append (UInt32.length_toBytes _) (UInt64.length_toBytes _)
    (UInt64.length_toBytes _), toUInt32_toBytes, UInt64.toUInt64_toBytes,
    UInt64.toUInt64_toBytes]

end Blanc.ConsensusSsz
