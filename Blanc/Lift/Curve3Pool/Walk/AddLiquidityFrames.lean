import Blanc.Lift.Curve3Pool.Walk.AddLiquidityKit

/-!
# `add_liquidity`'s frame saves and restores, on the actual derivation

Before each `get_D_mem` call the body pushes its live memory `[0x140, top)` onto the stack word
by word (a counter in memory), and after the call pops it back. `svWords img lo n` is the stack
the save leaves after `n` words (the word at `lo + 32 (n - 1)` on top). The restore puts every
saved word back and keeps every other word except the counter's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

/-- The words `[lo, lo + 32 n)` of `img` as a frame save leaves them on the stack. -/
def svWords (img : Bytes) (lo : Nat) : Nat → List B256
  | 0 => []
  | n + 1 => Bytes.toB256 (img.sliceD (lo + 32 * n) 32 0) :: svWords img lo n

theorem svWords_succ (img : Bytes) (lo n : Nat) :
    svWords img lo (n + 1) = Bytes.toB256 (img.sliceD (lo + 32 * n) 32 0) :: svWords img lo n :=
  rfl

theorem svWords_writeAt {img xs : Bytes} {lo n o : Nat} (h : lo + 32 * n ≤ o) :
    svWords (Bytes.writeAt img o xs) lo n = svWords img lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [svWords_succ, svWords_succ, ih (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]

theorem al_lt_of_ltCheck {x y : B256} (h : B256.ltCheck x y ≠ 0) : x < y := by
  unfold B256.ltCheck at h
  split_ifs at h with e
  · exact e
  · exact absurd rfl h

/-- **The frame save before `get_D_mem` at `0xf96`**: from `0x140` the loop pushes the words up to
`0x360` (counter at `0x360`), leaving them on the stack, the lowest deepest. -/
theorem xa_al_save1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    (hcode : sevm.code = code) :
    ∀ k n (S : List B256) (M : Mem) (img : Bytes) (G : Nat), n + k + 1 = 17 →
      Mem.Reads M img → Mem.Wf M → M.size % 32 = 0 → WordAt img 0x360 (Nat.toB256 (0x140 + 32 * n)) →
      XAt sevm post 0xf96 (St b (svWords img 0x140 n ++ S) M G) L →
      ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
        (∀ o w, WordAt img o w → (o + 32 ≤ 0x360 ∨ 0x360 + 32 ≤ o) → WordAt img' o w) ∧
        XAt sevm post 0xfb8 (St b (svWords img 0x140 17 ++ S) M' G') L := by
  intro k
  induction k with
  | zero =>
    intro n S M img G hn hR hW hA hc h
    xjd 0xf97
    xs 0xf9a (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xf9b (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [hc.read] at h
    xma 0xf9c (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * n) (B256.toNat_toB256_of_lt (by omega)))
    xs 0xf9e (.push [0x20] (by decide)) ri_push
    xs 0xfa1 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xfa2 (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [hc.read] at h
    xs 0xfa3 (.reg .add) ri_add
    rw [toB256_add_0x20 (by omega)] at h
    xs 0xfa6 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xfa7 (.reg .mstore) (ri_mstore_imgAtA (o := 0x360) rfl)
    xs 0xfaa (.push [0x03, 0x60] (by decide)) ri_push
    xs 0xfad (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xfae (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0xfaf (.reg .lt) ri_lt
    xs 0xfb0 (.reg .iszero) ri_iszero
    xs 0xfb3 (.push [0x0f, 0xb8] (by decide)) ri_push
    xji 0xfb4 0xfb8 hw
    · exact absurd (al_lt_of_ltCheck (eqCheck_eq_zero hw)) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]
        rw [show (Bytes.toB256 [0x03, 0x60]).toNat = 0x360 by decide]; omega)
    clear hw
    rw [← List.cons_append, ← svWords_succ,
      show n + 1 = 17 by omega] at h
    exact ⟨_, _, _, hR, hW, hA, fun o w hw ho => WordAt.write_other hw (by
      simp only [B256.length_toBytes]; omega), h⟩
  | succ k ih =>
    intro n S M img G hn hR hW hA hc h
    xjd 0xf97
    xs 0xf9a (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xf9b (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [hc.read] at h
    xma 0xf9c (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * n) (B256.toNat_toB256_of_lt (by omega)))
    xs 0xf9e (.push [0x20] (by decide)) ri_push
    xs 0xfa1 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xfa2 (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [hc.read] at h
    xs 0xfa3 (.reg .add) ri_add
    rw [toB256_add_0x20 (by omega)] at h
    xs 0xfa6 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xfa7 (.reg .mstore) (ri_mstore_imgAtA (o := 0x360) rfl)
    xs 0xfaa (.push [0x03, 0x60] (by decide)) ri_push
    xs 0xfad (.push [0x03, 0x60] (by decide)) ri_push
    xma 0xfae (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0xfaf (.reg .lt) ri_lt
    xs 0xfb0 (.reg .iszero) ri_iszero
    xs 0xfb3 (.push [0x0f, 0xb8] (by decide)) ri_push
    xji 0xfb4 0xfb8 hw
    · clear hw
      xs 0xfb7 (.push [0x0f, 0x96] (by decide)) ri_push
      xjmp 0xf96
      rw [← List.cons_append, ← svWords_succ, ← svWords_writeAt (img := img) (o := 0x360)
        (xs := (Nat.toB256 (0x140 + 32 * n + 32)).toBytes) (by omega)] at h
      obtain ⟨M', img', G', hR', hW', hA', hk, h⟩ := ih (n + 1) S _ _ _ (by omega) hR hW hA
        (by rw [show 0x140 + 32 * (n + 1) = 0x140 + 32 * n + 32 by omega]; exact WordAt.write_self _ _ _)
        h
      refine ⟨M', img', G', hR', hW', hA', fun o w hw ho => hk o w (WordAt.write_other hw (by
        simp only [B256.length_toBytes]; omega)) ho, ?_⟩
      rw [svWords_writeAt (by omega)] at h
      exact h
    · exact absurd (ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]
        rw [show (Bytes.toB256 [0x03, 0x60]).toNat = 0x360 by decide]; omega)

/-- **The frame save before `get_D_mem` at `0x133d`**: from `0x140` the loop pushes the words up to
`0x920` (counter at `0x920`), leaving them on the stack, the lowest deepest. -/
theorem xa_al_save2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    (hcode : sevm.code = code) :
    ∀ k n (S : List B256) (M : Mem) (img : Bytes) (G : Nat), n + k + 1 = 63 →
      Mem.Reads M img → Mem.Wf M → M.size % 32 = 0 → WordAt img 0x920 (Nat.toB256 (0x140 + 32 * n)) →
      XAt sevm post 0x133d (St b (svWords img 0x140 n ++ S) M G) L →
      ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
        (∀ o w, WordAt img o w → (o + 32 ≤ 0x920 ∨ 0x920 + 32 ≤ o) → WordAt img' o w) ∧
        XAt sevm post 0x135f (St b (svWords img 0x140 63 ++ S) M' G') L := by
  intro k
  induction k with
  | zero =>
    intro n S M img G hn hR hW hA hc h
    xjd 0x133e
    xs 0x1341 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x1342 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [hc.read] at h
    xma 0x1343 (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * n) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x1345 (.push [0x20] (by decide)) ri_push
    xs 0x1348 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x1349 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [hc.read] at h
    xs 0x134a (.reg .add) ri_add
    rw [toB256_add_0x20 (by omega)] at h
    xs 0x134d (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x134e (.reg .mstore) (ri_mstore_imgAtA (o := 0x920) rfl)
    xs 0x1351 (.push [0x09, 0x20] (by decide)) ri_push
    xs 0x1354 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x1355 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x1356 (.reg .lt) ri_lt
    xs 0x1357 (.reg .iszero) ri_iszero
    xs 0x135a (.push [0x13, 0x5f] (by decide)) ri_push
    xji 0x135b 0x135f hw
    · exact absurd (al_lt_of_ltCheck (eqCheck_eq_zero hw)) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]
        rw [show (Bytes.toB256 [0x09, 0x20]).toNat = 0x920 by decide]; omega)
    clear hw
    rw [← List.cons_append, ← svWords_succ,
      show n + 1 = 63 by omega] at h
    exact ⟨_, _, _, hR, hW, hA, fun o w hw ho => WordAt.write_other hw (by
      simp only [B256.length_toBytes]; omega), h⟩
  | succ k ih =>
    intro n S M img G hn hR hW hA hc h
    xjd 0x133e
    xs 0x1341 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x1342 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [hc.read] at h
    xma 0x1343 (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * n) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x1345 (.push [0x20] (by decide)) ri_push
    xs 0x1348 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x1349 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [hc.read] at h
    xs 0x134a (.reg .add) ri_add
    rw [toB256_add_0x20 (by omega)] at h
    xs 0x134d (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x134e (.reg .mstore) (ri_mstore_imgAtA (o := 0x920) rfl)
    xs 0x1351 (.push [0x09, 0x20] (by decide)) ri_push
    xs 0x1354 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x1355 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x1356 (.reg .lt) ri_lt
    xs 0x1357 (.reg .iszero) ri_iszero
    xs 0x135a (.push [0x13, 0x5f] (by decide)) ri_push
    xji 0x135b 0x135f hw
    · clear hw
      xs 0x135e (.push [0x13, 0x3d] (by decide)) ri_push
      xjmp 0x133d
      rw [← List.cons_append, ← svWords_succ, ← svWords_writeAt (img := img) (o := 0x920)
        (xs := (Nat.toB256 (0x140 + 32 * n + 32)).toBytes) (by omega)] at h
      obtain ⟨M', img', G', hR', hW', hA', hk, h⟩ := ih (n + 1) S _ _ _ (by omega) hR hW hA
        (by rw [show 0x140 + 32 * (n + 1) = 0x140 + 32 * n + 32 by omega]; exact WordAt.write_self _ _ _)
        h
      refine ⟨M', img', G', hR', hW', hA', fun o w hw ho => hk o w (WordAt.write_other hw (by
        simp only [B256.length_toBytes]; omega)) ho, ?_⟩
      rw [svWords_writeAt (by omega)] at h
      exact h
    · exact absurd (ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]
        rw [show (Bytes.toB256 [0x09, 0x20]).toNat = 0x920 by decide]; omega)

/-- **The frame save before `get_D_mem` at `0x1644`**: from `0x140` the loop pushes the words up to
`0xa40` (counter at `0xaa0`), leaving them on the stack, the lowest deepest. -/
theorem xa_al_save3 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame}
    (hcode : sevm.code = code) :
    ∀ k n (S : List B256) (M : Mem) (img : Bytes) (G : Nat), n + k + 1 = 72 →
      Mem.Reads M img → Mem.Wf M → M.size % 32 = 0 → WordAt img 0xaa0 (Nat.toB256 (0x140 + 32 * n)) →
      XAt sevm post 0x1644 (St b (svWords img 0x140 n ++ S) M G) L →
      ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
        (∀ o w, WordAt img o w → (o + 32 ≤ 0xaa0 ∨ 0xaa0 + 32 ≤ o) → WordAt img' o w) ∧
        XAt sevm post 0x1666 (St b (svWords img 0x140 72 ++ S) M' G') L := by
  intro k
  induction k with
  | zero =>
    intro n S M img G hn hR hW hA hc h
    xjd 0x1645
    xs 0x1648 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x1649 (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [hc.read] at h
    xma 0x164a (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * n) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x164c (.push [0x20] (by decide)) ri_push
    xs 0x164f (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x1650 (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [hc.read] at h
    xs 0x1651 (.reg .add) ri_add
    rw [toB256_add_0x20 (by omega)] at h
    xs 0x1654 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x1655 (.reg .mstore) (ri_mstore_imgAtA (o := 0xaa0) rfl)
    xs 0x1658 (.push [0x0a, 0x40] (by decide)) ri_push
    xs 0x165b (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x165c (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x165d (.reg .lt) ri_lt
    xs 0x165e (.reg .iszero) ri_iszero
    xs 0x1661 (.push [0x16, 0x66] (by decide)) ri_push
    xji 0x1662 0x1666 hw
    · exact absurd (al_lt_of_ltCheck (eqCheck_eq_zero hw)) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]
        rw [show (Bytes.toB256 [0x0a, 0x40]).toNat = 0xa40 by decide]; omega)
    clear hw
    rw [← List.cons_append, ← svWords_succ,
      show n + 1 = 72 by omega] at h
    exact ⟨_, _, _, hR, hW, hA, fun o w hw ho => WordAt.write_other hw (by
      simp only [B256.length_toBytes]; omega), h⟩
  | succ k ih =>
    intro n S M img G hn hR hW hA hc h
    xjd 0x1645
    xs 0x1648 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x1649 (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [hc.read] at h
    xma 0x164a (.reg .mload) (ri_mload_imgAtA (o := 0x140 + 32 * n) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x164c (.push [0x20] (by decide)) ri_push
    xs 0x164f (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x1650 (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [hc.read] at h
    xs 0x1651 (.reg .add) ri_add
    rw [toB256_add_0x20 (by omega)] at h
    xs 0x1654 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x1655 (.reg .mstore) (ri_mstore_imgAtA (o := 0xaa0) rfl)
    xs 0x1658 (.push [0x0a, 0x40] (by decide)) ri_push
    xs 0x165b (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x165c (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x165d (.reg .lt) ri_lt
    xs 0x165e (.reg .iszero) ri_iszero
    xs 0x1661 (.push [0x16, 0x66] (by decide)) ri_push
    xji 0x1662 0x1666 hw
    · clear hw
      xs 0x1665 (.push [0x16, 0x44] (by decide)) ri_push
      xjmp 0x1644
      rw [← List.cons_append, ← svWords_succ, ← svWords_writeAt (img := img) (o := 0xaa0)
        (xs := (Nat.toB256 (0x140 + 32 * n + 32)).toBytes) (by omega)] at h
      obtain ⟨M', img', G', hR', hW', hA', hk, h⟩ := ih (n + 1) S _ _ _ (by omega) hR hW hA
        (by rw [show 0x140 + 32 * (n + 1) = 0x140 + 32 * n + 32 by omega]; exact WordAt.write_self _ _ _)
        h
      refine ⟨M', img', G', hR', hW', hA', fun o w hw ho => hk o w (WordAt.write_other hw (by
        simp only [B256.length_toBytes]; omega)) ho, ?_⟩
      rw [svWords_writeAt (by omega)] at h
      exact h
    · exact absurd (ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq hw)) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)]
        rw [show (Bytes.toB256 [0x0a, 0x40]).toNat = 0xa40 by decide]; omega)

/-- **The frame restore after `get_D_mem` at `0x1005`** (counter at `0x360`): the loop pops the saved
words back over `0x140…`, top word first. -/
theorem xa_al_restore1 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {src : Bytes}
    (hcode : sevm.code = code) :
    ∀ m (S : List B256) (M : Mem) (img : Bytes) (G : Nat), m + 1 ≤ 17 →
      Mem.Reads M img → Mem.Wf M → M.size % 32 = 0 → WordAt img 0x360 (Nat.toB256 (0x140 + 32 * m)) →
      XAt sevm post 0x1005 (St b (svWords src 0x140 (m + 1) ++ S) M G) L →
      ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
        (∀ j, j ≤ m → WordAt img' (0x140 + 32 * j)
          (Bytes.toB256 (src.sliceD (0x140 + 32 * j) 32 0))) ∧
        (∀ o w, WordAt img o w → (o + 32 ≤ 0x140 ∨ 0x140 + 32 * (m + 1) ≤ o) →
          (o + 32 ≤ 0x360 ∨ 0x360 + 32 ≤ o) → WordAt img' o w) ∧
        XAt sevm post 0x1028 (St b S M' G') L := by
  intro m
  induction m with
  | zero =>
    intro S M img G hm hR hW hA hc h
    rw [svWords_succ, List.cons_append] at h
    xjd 0x1006
    xs 0x1009 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x100a (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [hc.read] at h
    xma 0x100b (.reg .mstore) (ri_mstore_imgAtA (o := 0x140 + 32 * 0) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x100d (.push [0x20] (by decide)) ri_push
    xs 0x1010 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x1011 (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [(hc.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
    xs 0x1012 (.reg .sub) ri_sub
    rw [toB256_sub_0x20 (by omega) (by omega)] at h
    xs 0x1015 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x1016 (.reg .mstore) (ri_mstore_imgAtA (o := 0x360) rfl)
    xs 0x1019 (.push [0x01, 0x40] (by decide)) ri_push
    xs 0x101c (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x101d (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x101e (.reg .lt) ri_lt
    xs 0x101f (.reg .iszero) ri_iszero
    xs 0x1020 (.reg .iszero) ri_iszero
    xs 0x1023 (.push [0x10, 0x28] (by decide)) ri_push
    xji 0x1024 0x1028 hw
    · exact absurd (ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq (eqCheck_eq_zero hw))) (by
        rw [not_not, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by decide]; omega)
    simp only [svWords, List.nil_append] at h
    refine ⟨_, _, _, hR, hW, hA, fun j hj => ?_, fun o w hw h1 h2 => ?_, h⟩
    · obtain rfl : j = 0 := by omega
      exact WordAt.write_other (WordAt.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
    · exact WordAt.write_other (WordAt.write_other hw (by simp only [B256.length_toBytes]; omega))
        (by simp only [B256.length_toBytes]; omega)
  | succ m ih =>
    intro S M img G hm hR hW hA hc h
    rw [svWords_succ, List.cons_append] at h
    xjd 0x1006
    xs 0x1009 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x100a (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [hc.read] at h
    xma 0x100b (.reg .mstore) (ri_mstore_imgAtA (o := 0x140 + 32 * (m + 1)) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x100d (.push [0x20] (by decide)) ri_push
    xs 0x1010 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x1011 (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [(hc.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
    xs 0x1012 (.reg .sub) ri_sub
    rw [toB256_sub_0x20 (by omega) (by omega)] at h
    xs 0x1015 (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x1016 (.reg .mstore) (ri_mstore_imgAtA (o := 0x360) rfl)
    xs 0x1019 (.push [0x01, 0x40] (by decide)) ri_push
    xs 0x101c (.push [0x03, 0x60] (by decide)) ri_push
    xma 0x101d (.reg .mload) (ri_mload_imgAtA (o := 0x360) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x101e (.reg .lt) ri_lt
    xs 0x101f (.reg .iszero) ri_iszero
    xs 0x1020 (.reg .iszero) ri_iszero
    xs 0x1023 (.push [0x10, 0x28] (by decide)) ri_push
    xji 0x1024 0x1028 hw
    · clear hw
      xs 0x1027 (.push [0x10, 0x05] (by decide)) ri_push
      xjmp 0x1005
      obtain ⟨M', img', G', hR', hW', hA', hj, hk, h⟩ := ih S _ _ _ (by omega) hR hW hA
        (by rw [show 0x140 + 32 * (m + 1) - 32 = 0x140 + 32 * m by omega]
            exact WordAt.write_self _ _ _) h
      refine ⟨M', img', G', hR', hW', hA', fun j hj' => ?_, fun o w hw h1 h2 => ?_, h⟩
      · rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
        · exact hj j (by omega)
        · exact hk _ _ (WordAt.write_other (WordAt.write_self _ _ _) (by
            simp only [B256.length_toBytes]; omega)) (by omega) (by omega)
      · exact hk o w (WordAt.write_other (WordAt.write_other hw (by
          simp only [B256.length_toBytes]; omega)) (by simp only [B256.length_toBytes]; omega))
          (by omega) h2
    · exact absurd (al_lt_of_ltCheck (eqCheck_eq_zero (eqCheck_ne_zero_eq hw))) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by decide]; omega)

/-- **The frame restore after `get_D_mem` at `0x13ac`** (counter at `0x920`): the loop pops the saved
words back over `0x140…`, top word first. -/
theorem xa_al_restore2 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {src : Bytes}
    (hcode : sevm.code = code) :
    ∀ m (S : List B256) (M : Mem) (img : Bytes) (G : Nat), m + 1 ≤ 63 →
      Mem.Reads M img → Mem.Wf M → M.size % 32 = 0 → WordAt img 0x920 (Nat.toB256 (0x140 + 32 * m)) →
      XAt sevm post 0x13ac (St b (svWords src 0x140 (m + 1) ++ S) M G) L →
      ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
        (∀ j, j ≤ m → WordAt img' (0x140 + 32 * j)
          (Bytes.toB256 (src.sliceD (0x140 + 32 * j) 32 0))) ∧
        (∀ o w, WordAt img o w → (o + 32 ≤ 0x140 ∨ 0x140 + 32 * (m + 1) ≤ o) →
          (o + 32 ≤ 0x920 ∨ 0x920 + 32 ≤ o) → WordAt img' o w) ∧
        XAt sevm post 0x13cf (St b S M' G') L := by
  intro m
  induction m with
  | zero =>
    intro S M img G hm hR hW hA hc h
    rw [svWords_succ, List.cons_append] at h
    xjd 0x13ad
    xs 0x13b0 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13b1 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [hc.read] at h
    xma 0x13b2 (.reg .mstore) (ri_mstore_imgAtA (o := 0x140 + 32 * 0) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x13b4 (.push [0x20] (by decide)) ri_push
    xs 0x13b7 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13b8 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [(hc.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
    xs 0x13b9 (.reg .sub) ri_sub
    rw [toB256_sub_0x20 (by omega) (by omega)] at h
    xs 0x13bc (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13bd (.reg .mstore) (ri_mstore_imgAtA (o := 0x920) rfl)
    xs 0x13c0 (.push [0x01, 0x40] (by decide)) ri_push
    xs 0x13c3 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13c4 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x13c5 (.reg .lt) ri_lt
    xs 0x13c6 (.reg .iszero) ri_iszero
    xs 0x13c7 (.reg .iszero) ri_iszero
    xs 0x13ca (.push [0x13, 0xcf] (by decide)) ri_push
    xji 0x13cb 0x13cf hw
    · exact absurd (ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq (eqCheck_eq_zero hw))) (by
        rw [not_not, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by decide]; omega)
    simp only [svWords, List.nil_append] at h
    refine ⟨_, _, _, hR, hW, hA, fun j hj => ?_, fun o w hw h1 h2 => ?_, h⟩
    · obtain rfl : j = 0 := by omega
      exact WordAt.write_other (WordAt.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
    · exact WordAt.write_other (WordAt.write_other hw (by simp only [B256.length_toBytes]; omega))
        (by simp only [B256.length_toBytes]; omega)
  | succ m ih =>
    intro S M img G hm hR hW hA hc h
    rw [svWords_succ, List.cons_append] at h
    xjd 0x13ad
    xs 0x13b0 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13b1 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [hc.read] at h
    xma 0x13b2 (.reg .mstore) (ri_mstore_imgAtA (o := 0x140 + 32 * (m + 1)) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x13b4 (.push [0x20] (by decide)) ri_push
    xs 0x13b7 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13b8 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [(hc.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
    xs 0x13b9 (.reg .sub) ri_sub
    rw [toB256_sub_0x20 (by omega) (by omega)] at h
    xs 0x13bc (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13bd (.reg .mstore) (ri_mstore_imgAtA (o := 0x920) rfl)
    xs 0x13c0 (.push [0x01, 0x40] (by decide)) ri_push
    xs 0x13c3 (.push [0x09, 0x20] (by decide)) ri_push
    xma 0x13c4 (.reg .mload) (ri_mload_imgAtA (o := 0x920) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x13c5 (.reg .lt) ri_lt
    xs 0x13c6 (.reg .iszero) ri_iszero
    xs 0x13c7 (.reg .iszero) ri_iszero
    xs 0x13ca (.push [0x13, 0xcf] (by decide)) ri_push
    xji 0x13cb 0x13cf hw
    · clear hw
      xs 0x13ce (.push [0x13, 0xac] (by decide)) ri_push
      xjmp 0x13ac
      obtain ⟨M', img', G', hR', hW', hA', hj, hk, h⟩ := ih S _ _ _ (by omega) hR hW hA
        (by rw [show 0x140 + 32 * (m + 1) - 32 = 0x140 + 32 * m by omega]
            exact WordAt.write_self _ _ _) h
      refine ⟨M', img', G', hR', hW', hA', fun j hj' => ?_, fun o w hw h1 h2 => ?_, h⟩
      · rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
        · exact hj j (by omega)
        · exact hk _ _ (WordAt.write_other (WordAt.write_self _ _ _) (by
            simp only [B256.length_toBytes]; omega)) (by omega) (by omega)
      · exact hk o w (WordAt.write_other (WordAt.write_other hw (by
          simp only [B256.length_toBytes]; omega)) (by simp only [B256.length_toBytes]; omega))
          (by omega) h2
    · exact absurd (al_lt_of_ltCheck (eqCheck_eq_zero (eqCheck_ne_zero_eq hw))) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by decide]; omega)

/-- **The frame restore after `get_D_mem` at `0x16b3`** (counter at `0xaa0`): the loop pops the saved
words back over `0x140…`, top word first. -/
theorem xa_al_restore3 {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {src : Bytes}
    (hcode : sevm.code = code) :
    ∀ m (S : List B256) (M : Mem) (img : Bytes) (G : Nat), m + 1 ≤ 72 →
      Mem.Reads M img → Mem.Wf M → M.size % 32 = 0 → WordAt img 0xaa0 (Nat.toB256 (0x140 + 32 * m)) →
      XAt sevm post 0x16b3 (St b (svWords src 0x140 (m + 1) ++ S) M G) L →
      ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
        (∀ j, j ≤ m → WordAt img' (0x140 + 32 * j)
          (Bytes.toB256 (src.sliceD (0x140 + 32 * j) 32 0))) ∧
        (∀ o w, WordAt img o w → (o + 32 ≤ 0x140 ∨ 0x140 + 32 * (m + 1) ≤ o) →
          (o + 32 ≤ 0xaa0 ∨ 0xaa0 + 32 ≤ o) → WordAt img' o w) ∧
        XAt sevm post 0x16d6 (St b S M' G') L := by
  intro m
  induction m with
  | zero =>
    intro S M img G hm hR hW hA hc h
    rw [svWords_succ, List.cons_append] at h
    xjd 0x16b4
    xs 0x16b7 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16b8 (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [hc.read] at h
    xma 0x16b9 (.reg .mstore) (ri_mstore_imgAtA (o := 0x140 + 32 * 0) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x16bb (.push [0x20] (by decide)) ri_push
    xs 0x16be (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16bf (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [(hc.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
    xs 0x16c0 (.reg .sub) ri_sub
    rw [toB256_sub_0x20 (by omega) (by omega)] at h
    xs 0x16c3 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16c4 (.reg .mstore) (ri_mstore_imgAtA (o := 0xaa0) rfl)
    xs 0x16c7 (.push [0x01, 0x40] (by decide)) ri_push
    xs 0x16ca (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16cb (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x16cc (.reg .lt) ri_lt
    xs 0x16cd (.reg .iszero) ri_iszero
    xs 0x16ce (.reg .iszero) ri_iszero
    xs 0x16d1 (.push [0x16, 0xd6] (by decide)) ri_push
    xji 0x16d2 0x16d6 hw
    · exact absurd (ltCheck_eq_zero_not_lt (eqCheck_ne_zero_eq (eqCheck_eq_zero hw))) (by
        rw [not_not, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by decide]; omega)
    simp only [svWords, List.nil_append] at h
    refine ⟨_, _, _, hR, hW, hA, fun j hj => ?_, fun o w hw h1 h2 => ?_, h⟩
    · obtain rfl : j = 0 := by omega
      exact WordAt.write_other (WordAt.write_self _ _ _) (by simp only [B256.length_toBytes]; omega)
    · exact WordAt.write_other (WordAt.write_other hw (by simp only [B256.length_toBytes]; omega))
        (by simp only [B256.length_toBytes]; omega)
  | succ m ih =>
    intro S M img G hm hR hW hA hc h
    rw [svWords_succ, List.cons_append] at h
    xjd 0x16b4
    xs 0x16b7 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16b8 (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [hc.read] at h
    xma 0x16b9 (.reg .mstore) (ri_mstore_imgAtA (o := 0x140 + 32 * (m + 1)) (B256.toNat_toB256_of_lt (by omega)))
    xs 0x16bb (.push [0x20] (by decide)) ri_push
    xs 0x16be (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16bf (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [(hc.write_other (by simp only [B256.length_toBytes]; omega)).read] at h
    xs 0x16c0 (.reg .sub) ri_sub
    rw [toB256_sub_0x20 (by omega) (by omega)] at h
    xs 0x16c3 (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16c4 (.reg .mstore) (ri_mstore_imgAtA (o := 0xaa0) rfl)
    xs 0x16c7 (.push [0x01, 0x40] (by decide)) ri_push
    xs 0x16ca (.push [0x0a, 0xa0] (by decide)) ri_push
    xma 0x16cb (.reg .mload) (ri_mload_imgAtA (o := 0xaa0) rfl)
    rw [(WordAt.write_self _ _ _).read] at h
    xs 0x16cc (.reg .lt) ri_lt
    xs 0x16cd (.reg .iszero) ri_iszero
    xs 0x16ce (.reg .iszero) ri_iszero
    xs 0x16d1 (.push [0x16, 0xd6] (by decide)) ri_push
    xji 0x16d2 0x16d6 hw
    · clear hw
      xs 0x16d5 (.push [0x16, 0xb3] (by decide)) ri_push
      xjmp 0x16b3
      obtain ⟨M', img', G', hR', hW', hA', hj, hk, h⟩ := ih S _ _ _ (by omega) hR hW hA
        (by rw [show 0x140 + 32 * (m + 1) - 32 = 0x140 + 32 * m by omega]
            exact WordAt.write_self _ _ _) h
      refine ⟨M', img', G', hR', hW', hA', fun j hj' => ?_, fun o w hw h1 h2 => ?_, h⟩
      · rcases Nat.lt_or_eq_of_le hj' with hlt | rfl
        · exact hj j (by omega)
        · exact hk _ _ (WordAt.write_other (WordAt.write_self _ _ _) (by
            simp only [B256.length_toBytes]; omega)) (by omega) (by omega)
      · exact hk o w (WordAt.write_other (WordAt.write_other hw (by
          simp only [B256.length_toBytes]; omega)) (by simp only [B256.length_toBytes]; omega))
          (by omega) h2
    · exact absurd (al_lt_of_ltCheck (eqCheck_eq_zero (eqCheck_ne_zero_eq hw))) (by
        rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega),
          show (Bytes.toB256 [0x01, 0x40]).toNat = 0x140 by decide]; omega)


end Blanc.Lift.Curve3Pool
