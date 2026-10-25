import Blanc.Lift.Usdc.InitReachV1
import Blanc.Lift.Usdc.InitV1ConcreteBounds
import Jaune.MulDiv

/-!
# FiatTokenV1 initializer key bounds

The helper's actual old-header arithmetic and reached-key ranges, followed by the
initializer exclusion using the separately checked fixed header hashes. Conditional
numerical interfaces remain available; fixed Keccak proofs are imported, not repeated.
-/

namespace Blanc.Lift.Usdc.InitV1KeyBounds

open Jaune Blanc Blanc.Lift
open OldInitializerV1Staging

/-- V1's decoded old length is bounded for every stored header, including malformed ones. -/
theorem oldLength_le (old : B256) :
    ((Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& old) =? 0) -
      Bytes.toB256 [1] &&& old) / Bytes.toB256 [2]).toNat ≤ 2 ^ 255 - 1 := by
  have bound := B256.toNat_lt (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& old) =? 0) -
    Bytes.toB256 [1] &&& old)
  rw [B256.toNat_div (by decide), show (Bytes.toB256 [2]).toNat = 2 from rfl]
  omega

/-- The old clearing count is at most 2^250 without any header-format premise. -/
theorem oldWords_le (old : B256) :
    ((Bytes.toB256 [31] +
      (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& old) =? 0) -
        Bytes.toB256 [1] &&& old) / Bytes.toB256 [2]) / Bytes.toB256 [32]).toNat ≤
      2 ^ 250 := by
  let decoded := (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& old) =? 0) -
    Bytes.toB256 [1] &&& old) / Bytes.toB256 [2]
  have length : decoded.toNat ≤ 2 ^ 255 - 1 := oldLength_le old
  have safe : B256.Nof (Bytes.toB256 [31]) decoded := by
    change 31 + decoded.toNat < 2 ^ 256
    omega
  change ((Bytes.toB256 [31] + decoded) / Bytes.toB256 [32]).toNat ≤ 2 ^ 250
  rw [B256.toNat_div (by decide), B256.toNat_add_eq_of_nof _ _ safe,
    show (Bytes.toB256 [31]).toNat = 31 from rfl,
    show (Bytes.toB256 [32]).toNat = 32 from rfl]
  omega

/-- The original old endpoint lies below the explicit hash-base margin. -/
theorem oldEnd_le (H old : B256) (base : H.toNat + 2 ^ 251 < 2 ^ 256) :
    (H + (Bytes.toB256 [31] +
      (Bytes.toB256 [1, 0] * ((Bytes.toB256 [1] &&& old) =? 0) -
        Bytes.toB256 [1] &&& old) / Bytes.toB256 [2]) / Bytes.toB256 [32]).toNat ≤
      H.toNat + 2 ^ 250 := by
  have words := oldWords_le old
  rw [B256.toNat_add_eq_of_nof _ _ (by
    unfold B256.Nof
    omega)]
  omega

/-- The numerical classifier shared by actual helper and initializer range consumers. -/
theorem range_key_ne_implSlot {L slot key value : B256}
    (length : L.toNat ≤ 2 ^ 160) (header : slot ≠ implSlot)
    (base : slot.toBytes.keccak.toNat + 2 ^ 251 < 2 ^ 256)
    (control : implSlot.toNat < slot.toBytes.keccak.toNat ∨
      slot.toBytes.keccak.toNat + 2 ^ 251 ≤ implSlot.toNat)
    (kind : key = slot ∨ (∃ j < (L.toNat + 31) / 32,
      key = slot.toBytes.keccak + j.toB256) ∨
      value = 0 ∧ InitReachV1.ClearRange slot ((L.toNat + 31) / 32) key) :
    key ≠ implSlot := by
  let H := slot.toBytes.keccak
  have words : (L.toNat + 31) / 32 ≤ 2 ^ 155 := by omega
  have index : ∀ i ≤ 2 ^ 155, (H + i.toB256).toNat = H.toNat + i := by
    intro i hi
    have small : i < 2 ^ 256 := by omega
    rw [B256.toNat_add_eq_of_nof _ _ (by
      unfold B256.Nof
      rw [B256.toNat_toB256_of_lt small]
      change H.toNat + 2 ^ 251 < 2 ^ 256 at base
      omega), B256.toNat_toB256_of_lt small]
  have separate : ∀ {key : B256}, H.toNat ≤ key.toNat →
      key.toNat < H.toNat + 2 ^ 251 → key ≠ implSlot := by
    intro key lower upper eq
    have same := congrArg B256.toNat eq
    change implSlot.toNat < H.toNat ∨ H.toNat + 2 ^ 251 ≤ implSlot.toNat at control
    rcases control with before | after
    · omega
    · omega
  rcases kind with fixed | ⟨j, hj, rfl⟩ | ⟨-, old, i, hi, lower, upper⟩
  · exact fixed ▸ header
  · have hj' : j ≤ 2 ^ 155 := by omega
    apply separate
    · rw [index j hj']
      omega
    · rw [index j hj']
      omega
  · have hi' : i ≤ 2 ^ 155 := by omega
    rw [index i hi'] at lower
    have oldEnd := oldEnd_le H old base
    apply separate (by omega)
    dsimp only [H] at oldEnd ⊢
    omega

/-- Every helper store avoids the implementation slot under explicit numerical base
bounds, or the helper reaches its original continuation. The fixed hashes are not
instantiated, and the endpoint uses the actual stored old header. -/
theorem helper46_reach_ne_implSlot
    {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {K : List SFunc} {b : Devm} {L D slot r : B256} {S : List B256} {M : Mem} {G : Nat}
    (hnw : D.toNat + L.toNat < 2 ^ 256)
    (length : L.toNat ≤ 2 ^ 160) (header : slot ≠ implSlot)
    (base : slot.toBytes.keccak.toNat + 2 ^ 251 < 2 ^ 256)
    (control : implSlot.toNat < slot.toBytes.keccak.toNat ∨
      slot.toBytes.keccak.toNat + 2 ^ 251 ≤ implSlot.toNat)
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St b (L :: D :: slot :: r :: S) M G, ImplV1.t_2e8a_c46, K⟩ T)
    (hT : AtSstore T) :
    (∃ key value rest, T.d.stack = key :: value :: rest ∧ key ≠ implSlot) ∨
      ∃ f K' b' M' G', K = f :: K' ∧
        SolcStorageReturn.Keeps (M.write 0 slot.toBytes) M' ∧
        Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
          ⟨St b' (slot :: S) M' G', f, K'⟩ T := by
  rcases InitReachV1.helper46_reach_range eraseQ hnw run hT with
    ⟨key, value, rest, stack, kind⟩ | returned
  · refine .inl ⟨key, value, rest, stack, ?_⟩
    apply range_key_ne_implSlot length header base control (value := value)
    rcases kind with fixed | payload | ⟨zero, i, hi, lower, upper⟩
    · exact .inl fixed
    · exact .inr (.inl payload)
    · exact .inr (.inr ⟨zero, b.getStorVal sevm.currentTarget slot, i, hi, lower, upper⟩)
  · exact .inr returned

/-- The range and actual stage-derived caps suffice under the finite numerical family. -/
theorem boundedRange_ne_implSlot {sevm : Sevm} {T : Conf}
    (bounds : ∀ slot ∈ ([4, 5, 7] : List B256), slot ≠ implSlot ∧
      slot.toBytes.keccak.toNat + 2 ^ 251 < 2 ^ 256 ∧
      (implSlot.toNat < slot.toBytes.keccak.toNat ∨
        slot.toBytes.keccak.toNat + 2 ^ 251 ≤ implSlot.toNat))
    (range : InitReachV1.BoundedRange sevm T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  intro key value rest stack
  obtain ⟨ranges, cap1, cap2, cap3⟩ := range
  have string (slot L : B256) (member : slot ∈ ([4, 5, 7] : List B256))
      (cap : L.toNat ≤ 2 ^ 160)
      (kind : key = slot ∨ (∃ j < (L.toNat + 31) / 32,
        key = slot.toBytes.keccak + j.toB256) ∨
        value = 0 ∧ InitReachV1.ClearRange slot ((L.toNat + 31) / 32) key) :
      key ≠ implSlot := by
    obtain ⟨header, base, control⟩ := bounds slot member
    exact range_key_ne_implSlot cap header base control kind
  rcases ranges key value rest stack with allowed | ⟨zero, clear⟩
  · rcases allowed with fixed | payload | payload | payload
    · have off : implSlot ∉ ([0, 1, 2, 4, 5, 6, 7, 8] : List B256) := by decide
      intro same
      exact off (same ▸ fixed)
    · exact string 4 (lenAt sevm head1) (by decide) cap1 (.inr (.inl payload))
    · exact string 5 (lenAt sevm head2) (by decide) cap2 (.inr (.inl payload))
    · exact string 7 (lenAt sevm head3) (by decide) cap3 (.inr (.inl payload))
  · rcases clear with clear | clear | clear
    · exact string 4 (lenAt sevm head1) (by decide) cap1 (.inr (.inr ⟨zero, clear⟩))
    · exact string 5 (lenAt sevm head2) (by decide) cap2 (.inr (.inr ⟨zero, clear⟩))
    · exact string 7 (lenAt sevm head3) (by decide) cap3 (.inr (.inr ⟨zero, clear⟩))

/-- The actual V1 initializer reach avoids the implementation slot. All three length
caps come from the actual wrapper staging; only the finite numerical bounds remain inputs. -/
theorem initV1_reach_ne_implSlot
    {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (bounds : ∀ slot ∈ ([4, 5, 7] : List B256), slot ≠ implSlot ∧
      slot.toBytes.keccak.toNat + 2 ^ 251 < 2 ^ 256 ∧
      (implSlot.toNat < slot.toBytes.keccak.toNat ∨
        slot.toBytes.keccak.toNat + 2 ^ 251 ≤ implSlot.toNat))
    (hs : Blanc.Sevm.selector sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St d [] Mem.empty G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  exact boundedRange_ne_implSlot bounds (InitReachV1.initV1_reach_range eraseQ hs run hT)

/-- Concrete V1 initializer exclusion, using the checked fixed header hashes and the
actual stage-derived length caps. No numerical bound or cap is supplied by the caller. -/
theorem initV1_reach_ne_implSlot_concrete
    {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : Blanc.Sevm.selector sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) ImplV1.cert.prog sevm
      ⟨St d [] Mem.empty G, ImplV1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  exact initV1_reach_ne_implSlot eraseQ (fun _ member => InitV1ConcreteBounds.bounds member)
    hs run hT

end Blanc.Lift.Usdc.InitV1KeyBounds
