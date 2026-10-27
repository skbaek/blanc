import Blanc.Lift.Usdc.InitReachV1
import Blanc.Lift.Usdc.InitV1ConcreteBounds
import Blanc.Lift.Usdc.InitReachV2
import Blanc.Lift.Usdc.InitReachV2_1
import Blanc.Lift.Usdc.InitReachV2_2
import Jaune.MulDiv

/-!
# USDC initialize key bounds across runtime versions

The helper's actual old-header arithmetic and reached-key ranges, followed by the
V1 and modern initialize exclusions using the same separately checked fixed header hashes. Conditional
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
    unfold StrStore.oldEnd at upper
    omega

/-- Natural decoded lengths reuse the same fixed header bounds. -/
theorem range_nat_key_ne_implSlot {L : Nat} {slot key value : B256}
    (member : slot ∈ ([4, 5, 7] : List B256)) (cap : L ≤ 2 ^ 160)
    (kind : key = slot ∨ (∃ j < (L + 31) / 32,
      key = slot.toBytes.keccak + j.toB256) ∨
      value = 0 ∧ StrStore.ClearRange slot ((L + 31) / 32) key) : key ≠ implSlot := by
  obtain ⟨header, base, control⟩ := InitV1ConcreteBounds.bounds member
  have small : L < 2 ^ 256 := by omega
  apply range_key_ne_implSlot (L := L.toB256) (value := value)
    (by rw [B256.toNat_toB256_of_lt small]; exact cap) header base control
  simpa only [B256.toNat_toB256_of_lt small] using kind

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

namespace Blanc.Lift.Usdc.Init06

open Jaune Blanc Blanc.Lift InitV1KeyBounds

/-- The common three-string initializer ranges avoid the implementation slot.
The finite header hashes and old-header bounds are reused from the V1 proof. -/
theorem initRange_ne_implSlot {L1 L2 L3 : Nat} {T : Conf}
    (cap1 : L1 ≤ 2 ^ 160) (cap2 : L2 ≤ 2 ^ 160) (cap3 : L3 ≤ 2 ^ 160)
    (range : InitRange L1 L2 L3 T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  intro key value rest stack
  have string (slot : B256) (L : Nat) (member : slot ∈ ([4, 5, 7] : List B256))
      (cap : L ≤ 2 ^ 160)
      (kind : key = slot ∨ (∃ j < (L + 31) / 32,
        key = slot.toBytes.keccak + j.toB256) ∨
        value = 0 ∧ StrStore.ClearRange slot ((L + 31) / 32) key) : key ≠ implSlot := by
    exact range_nat_key_ne_implSlot member cap kind
  rcases range key value rest stack with allowed | ⟨zero, clear⟩
  · rcases allowed with fixed | payload | payload | payload
    · have off : implSlot ∉ ([0, 1, 2, 4, 5, 6, 7, 8] : List B256) := by decide
      intro same
      exact off (same ▸ fixed)
    · exact string 4 L1 (by decide) cap1 (.inr (.inl payload))
    · exact string 5 L2 (by decide) cap2 (.inr (.inl payload))
    · exact string 7 L3 (by decide) cap3 (.inr (.inl payload))
  · rcases clear with clear | clear | clear
    · exact string 4 L1 (by decide) cap1 (.inr (.inr ⟨zero, clear⟩))
    · exact string 5 L2 (by decide) cap2 (.inr (.inr ⟨zero, clear⟩))
    · exact string 7 L3 (by decide) cap3 (.inr (.inr ⟨zero, clear⟩))

/-- Capped frame-local initializer ranges need no caller-supplied numeric bounds. -/
theorem initRange06_ne_implSlot {sevm : Sevm} {T : Conf} (range : InitRange06 sevm T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  exact initRange_ne_implSlot (Nat.min_le_right _ _) (Nat.min_le_right _ _)
    (Nat.min_le_right _ _) range

/-- V2 initialize avoids the implementation slot, including zero-clearing stores. -/
theorem init_reach_V2_ne_implSlot
    {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : initSelWord sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) ImplV2.cert.prog sevm
      ⟨St d [] Mem.empty G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  exact initRange06_ne_implSlot (init_reach_V2_range eraseQ hs run hT)

/-- V2_1 initialize avoids the implementation slot, including zero-clearing stores. -/
theorem init_reach_V2_1_ne_implSlot
    {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : initSelWord sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) ImplV2_1.cert.prog sevm
      ⟨St d [] Mem.empty G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  exact initRange06_ne_implSlot (init_reach_V2_1_range eraseQ hs run hT)

/-- V2_2 initialize avoids the implementation slot, including zero-clearing stores. -/
theorem init_reach_V2_2_ne_implSlot
    {Q : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (eraseQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    (hs : initSelWord sevm = 0x3357162b) {d : Devm} {G : Nat}
    (run : Reach (FreePtr.PotStep Q) Impl.cert.prog sevm
      ⟨St d [] Mem.empty G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  exact initRange06_ne_implSlot (init_reach_V2_2_range eraseQ hs run hT)

end Blanc.Lift.Usdc.Init06

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift

/-- The actual name range and fixed slots of `initializeV2` avoid the implementation slot. -/
theorem InitRangeV2Len.ne_implSlot {n : Nat} {T : Conf} (cap : n ≤ 2 ^ 160)
    (range : InitRangeV2Len n T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  intro key value rest stack
  rcases range key value rest stack with allowed | clear
  · rcases allowed with fixed | fixed | fixed | payload
    · exact fixed ▸ (by decide : (4 : B256) ≠ implSlot)
    · exact fixed ▸ (by decide : (15 : B256) ≠ implSlot)
    · exact fixed ▸ (by decide : (18 : B256) ≠ implSlot)
    · exact InitV1KeyBounds.range_nat_key_ne_implSlot (value := value)
        (by decide : (4 : B256) ∈ [4, 5, 7]) cap (.inr (.inl payload))
  · exact InitV1KeyBounds.range_nat_key_ne_implSlot
      (by decide : (4 : B256) ∈ [4, 5, 7]) cap (.inr (.inr clear))

theorem InitRangeV2.ne_implSlot {sevm : Sevm} {T : Conf} (range : InitRangeV2 sevm T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot := by
  apply InitRangeV2Len.ne_implSlot (n := min (CdStrWrap.cdLen sevm) (2 ^ 32)) ?_ range
  exact (Nat.min_le_right _ _).trans (Nat.pow_le_pow_right (by decide) (by decide))

/-- Every actual `initializeV2` store avoids the implementation slot, including clearing. -/
theorem InitReachV2.initV2_reach_ne_implSlot
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P ImplV2.cert.prog sevm ⟨St d [] M G, ImplV2.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot :=
  (InitReachV2.initV2_reach_range erase sel run hT).ne_implSlot

/-- Every actual `initializeV2` store avoids the implementation slot, including clearing. -/
theorem InitReachV2_1.initV2_reach_ne_implSlot
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P ImplV2_1.cert.prog sevm ⟨St d [] M G, ImplV2_1.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot :=
  (InitReachV2_1.initV2_reach_range erase sel run hT).ne_implSlot

/-- Every actual `initializeV2` store avoids the implementation slot, including clearing. -/
theorem InitReachV2_2.initV2_reach_ne_implSlot
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0xd608ea64) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest → key ≠ implSlot :=
  (InitReachV2_2.initV2_reach_range erase sel run hT).ne_implSlot

namespace InitReachV2_2

/-- The only nonliteral, nonstring keys remaining in the V2.2 migration. -/
def MigrationKey (sevm : Sevm) (key : B256) : Prop :=
  LoopKeys sevm (arrPtr sevm) (min (arrLen sevm).toNat (2 ^ 32)) key ∨
    key = mapSlot (sevm.currentTarget.toB256 &&& addrMask) 9 ∨
    key = mapSlot sevm.currentTarget.toB256 3

/-- Symbol headers, payloads, clearing and the version word avoid the implementation
slot. Any remaining store is one of the migration's actual decoded mapping keys. -/
theorem InitRange22.ne_implSlot_or_mapping {sevm : Sevm} {T : Conf}
    (range : InitRange22 sevm T) :
    ∀ key value rest, T.d.stack = key :: value :: rest →
      key ≠ implSlot ∨ MigrationKey sevm key := by
  intro key value rest stack
  have cap : min (strLen sevm) (2 ^ 32) ≤ 2 ^ 160 :=
    (Nat.min_le_right _ _).trans (Nat.pow_le_pow_right (by decide) (by decide))
  rcases range key value rest stack with allowed | clear
  · rcases allowed with fixed | payload | loop | own9 | own3 | version
    · exact .inl (fixed ▸ (by decide : (5 : B256) ≠ implSlot))
    · exact .inl (InitV1KeyBounds.range_nat_key_ne_implSlot (value := value)
        (by decide : (5 : B256) ∈ [4, 5, 7]) cap (.inr (.inl payload)))
    · exact .inr (.inl loop)
    · exact .inr (.inr (.inl own9))
    · exact .inr (.inr (.inr own3))
    · exact .inl (version ▸ (by decide : (18 : B256) ≠ implSlot))
  · exact .inl (InitV1KeyBounds.range_nat_key_ne_implSlot
      (by decide : (5 : B256) ∈ [4, 5, 7]) cap (.inr (.inr clear)))

/-- The actual V2.2 initializer prefix reduces slot exclusion to its mapping stores. -/
theorem initV2_2_reach_ne_implSlot_or_mapping
    {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {T : Conf}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0x430239b4) {d : Devm} {M : Mem} {G : Nat}
    (run : Reach P Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest →
      key ≠ implSlot ∨ MigrationKey sevm key :=
  (initV2_2_reach_range erase sel run hT).ne_implSlot_or_mapping

/-- Numerical string ranges and version18 are disjoint from the implementation
slot; the only remaining case retains its actually executed mapping hash. -/
theorem BodySource22.ne_implSlot_or_source
    {P : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    {sevm : Sevm} {T : Conf} {sLen : Nat} (cap : sLen ≤ 2 ^ 160)
    (source : BodySource22 P observe sevm sLen T) :
    ∀ key value rest, T.d.stack = key :: value :: rest →
      key ≠ implSlot ∨ MigrationSource P observe sevm key := by
  intro key value rest stack
  rcases source with ⟨key', value', rest', stack', range⟩ | other
  · rw [stack] at stack'
    simp only [List.cons.injEq] at stack'
    obtain ⟨rfl, rfl, rfl⟩ := stack'
    exact .inl (InitV1KeyBounds.range_nat_key_ne_implSlot
      (by decide : (5 : B256) ∈ [4, 5, 7]) cap range)
  · rcases other key value rest stack with version | mapping
    · exact .inl (version ▸ (by decide : (18 : B256) ≠ implSlot))
    · exact .inr mapping

/-- Original initializer entry reduces implementation-slot exclusion to an
observed successful mapping hash, including zero writes. -/
theorem initV2_2_source_ne_implSlot_or_source
    {P : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    {sevm : Sevm} {T : Conf}
    (erase : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (sel : initSelWord sevm = 0x430239b4) {d : Devm} {M : Mem} {G : Nat}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (run : ObservedReach P observe Impl.cert.prog sevm ⟨St d [] M G, Impl.t_0000_c0, []⟩ T)
    (hT : AtSstore T) :
    ∀ key value rest, T.d.stack = key :: value :: rest →
      key ≠ implSlot ∨ MigrationSource P observe sevm key :=
  (initV2_2_source erase sel hsg run hT).ne_implSlot_or_source
    ((Nat.min_le_right _ _).trans (Nat.pow_le_pow_right (by decide) (by decide)))


/-- An actual successful migration store is off the implementation slot or
names the successful original hash occurrence that computed its mapping key. -/
theorem initV2_2_successfulSstore_source {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = Impl.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none) (empty : root.devm.stack = [])
    (selected : initSelWord root.sevm = 0x430239b4)
    (chain : Exec.Deriv.ParentPrefix root node)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot ∨ ∃ (account : Adr) (base : B256),
      (base = 3 ∨ base = 9) ∧ write.key = mapSlot account.toB256 base ∧
        ∃ hashPc, KeccakBefore root node (account.toB256.toBytes ++ base.toBytes) hashPc := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas Impl.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  change ObservedReach (StepIn root) (Cursor.RawEdgeAt Impl.code Impl.cert root node)
    Impl.cert.prog root.sevm ⟨root.devm, Impl.t_0000_c0, []⟩ (κ.conf node.devm) at reach
  rw [St.self empty rfl] at reach
  rcases initV2_2_source_ne_implSlot_or_source (fun h => StepIn.toRun h) selected hsg reach target
      write.key write.value rest stack with safe | ⟨account, at3 | at9⟩
  · exact .inl safe
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      at3.2.actual
    exact .inr ⟨account, 3, .inl rfl, at3.1, _, occ, next, rfl,
      instruction, result, before, edge, after, hashStack, read⟩
  · obtain ⟨occ, next, here, instruction, result, before, edge, after, _, _, hashStack, read⟩ :=
      at9.2.actual
    exact .inr ⟨account, 9, .inr rfl, at9.1, _, occ, next, rfl,
      instruction, result, before, edge, after, hashStack, read⟩


end InitReachV2_2

end Blanc.Lift.Usdc
