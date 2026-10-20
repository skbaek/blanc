import Blanc.Lift.Curve3Pool.Walk.ExchangeMid

/-!
# `exchange`, part 5: around the call of `get_y`

* `xa_ex_args` (`0x2777` → `get_y`'s entry `0x18a4`): after the frame save, `i`, `j`, `x` and
  `xp` staged at `0x800 … 0x8a0`, pushed, and the return tag `0x27cd`; the memory's logical size
  is word-aligned there (the last `MLOAD` rounds it up), as `get_y`'s spec asks;
* `xa_ex_afterY` (`0x27cd` → the frame restore at `0x27d9`): `y` parked at `0x900`, the restore
  counter set to `0x7c0`;
* `ExFrame.of_restore`: the frame words read back after the save/restore round trip.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

set_option hygiene false in
/-- As `xmo`, for `ri_mload_imgAl` (also yields `hA`, the aligned size). -/
macro "xmA " pc:term:max n:term:max ri:term:max : tactic => `(tactic| (
  replace h := xa_nextAt (n := $n) (pc' := $pc) (atN hcode (by kernel_rfl)) (by nofun)
    (by rfl) h
  obtain ⟨_, s, h⟩ := h
  have e := $ri hR hW s
  clear s hR hW
  obtain ⟨M, _, rfl, hR, hW, hA⟩ := e))

/-- **`get_y`'s arguments** (`0x2777` → `0x18a4`). -/
theorem xa_ex_args {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {S : List B256} {xw X0 X1 X2 : B256}
    (hcode : sevm.code = code) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (hx : WordAt img 0x7a0 xw) (h0 : WordAt img 0x200 X0) (h1 : WordAt img 0x220 X1)
    (h2 : WordAt img 0x240 X2)
    (h : XAt sevm post 0x2777 (St b S M G) L) :
    ∃ M' img' G', Mem.Reads M' img' ∧ Mem.Wf M' ∧ M'.size % 32 = 0 ∧
      (∀ o v, WordAt img o v → o + 32 ≤ 0x800 ∨ 0x8c0 ≤ o → WordAt img' o v) ∧
      XAt sevm post 0x18a4 (St b (Nat.toB256 0x27cd :: exI sevm :: exJ sevm :: xw :: X0 :: X1 ::
        X2 :: S) M' G') L := by
  xs 0x2779 (.push [0x04] (by decide)) ri_push
  xs 0x277a (.reg .calldataload) ri_calldataload
  xs 0x277d (.push [0x08, 0x00] (by decide)) ri_push
  xmo 0x277e (.reg .mstore) (ri_mstore_imgAt (o := 0x800) rfl)
  xs 0x2780 (.push [0x24] (by decide)) ri_push
  xs 0x2781 (.reg .calldataload) ri_calldataload
  xs 0x2784 (.push [0x08, 0x20] (by decide)) ri_push
  xmo 0x2785 (.reg .mstore) (ri_mstore_imgAt (o := 0x820) rfl)
  xs 0x2788 (.push [0x07, 0xa0] (by decide)) ri_push
  xmo 0x2789 (.reg .mload) (ri_mload_imgAt (o := 0x7a0) rfl)
  rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide),
    Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by decide), hx.read] at h
  xs 0x278c (.push [0x08, 0x40] (by decide)) ri_push
  xmo 0x278d (.reg .mstore) (ri_mstore_imgAt (o := 0x840) rfl)
  xs 0x2790 (.push [0x08, 0x60] (by decide)) ri_push
  xs 0x2793 (.push [0x02, 0x00] (by decide)) ri_push
  xs 0x2794 (.reg (.dup 0)) (ri_dup (by rfl))
  xmo 0x2795 (.reg .mload) (ri_mload_imgAt (o := 0x200) rfl)
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [h0.read] at h
  xs 0x2796 (.reg (.dup 2)) (ri_dup (by rfl))
  xmo 0x2797 (.reg .mstore) (ri_mstore_imgAt (o := 0x860) rfl)
  xs 0x2798 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x279a (.push [0x20] (by decide)) ri_push
  xs 0x279b (.reg .add) ri_add
  xmo 0x279c (.reg .mload) (ri_mload_imgAt (o := 0x220) (by decide))
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [h1.read] at h
  xs 0x279d (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x279f (.push [0x20] (by decide)) ri_push
  xs 0x27a0 (.reg .add) ri_add
  xmo 0x27a1 (.reg .mstore) (ri_mstore_imgAt (o := 0x880) (by decide))
  xs 0x27a2 (.reg (.dup 0)) (ri_dup (by rfl))
  xs 0x27a4 (.push [0x40] (by decide)) ri_push
  xs 0x27a5 (.reg .add) ri_add
  xmo 0x27a6 (.reg .mload) (ri_mload_imgAt (o := 0x240) (by decide))
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint] at h
  rw [h2.read] at h
  xs 0x27a7 (.reg (.dup 2)) (ri_dup (by rfl))
  xs 0x27a9 (.push [0x40] (by decide)) ri_push
  xs 0x27aa (.reg .add) ri_add
  xmo 0x27ab (.reg .mstore) (ri_mstore_imgAt (o := 0x8a0) (by decide))
  xs 0x27ac (.reg .pop) ri_pop
  xs 0x27ad (.reg .pop) ri_pop
  xs 0x27b0 (.push [0x08, 0xa0] (by decide)) ri_push
  xmo 0x27b1 (.reg .mload) (ri_mload_imgAt (o := 0x8a0) rfl)
  xs 0x27b4 (.push [0x08, 0x80] (by decide)) ri_push
  xmo 0x27b5 (.reg .mload) (ri_mload_imgAt (o := 0x880) rfl)
  xs 0x27b8 (.push [0x08, 0x60] (by decide)) ri_push
  xmo 0x27b9 (.reg .mload) (ri_mload_imgAt (o := 0x860) rfl)
  xs 0x27bc (.push [0x08, 0x40] (by decide)) ri_push
  xmo 0x27bd (.reg .mload) (ri_mload_imgAt (o := 0x840) rfl)
  xs 0x27c0 (.push [0x08, 0x20] (by decide)) ri_push
  xmo 0x27c1 (.reg .mload) (ri_mload_imgAt (o := 0x820) rfl)
  xs 0x27c4 (.push [0x08, 0x00] (by decide)) ri_push
  xmA 0x27c5 (.reg .mload) (ri_mload_imgAl (o := 0x800) rfl)
  xs 0x27c7 (.push [0x06] (by decide)) ri_push
  xpc 0x27c8
  xs 0x27c9 (.reg .add) ri_add
  xs 0x27cc (.push [0x18, 0xa4] (by decide)) ri_push
  xjmp 0x18a4
  simp (disch := decide) only [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_self]
    at h
  rw [show Nat.toB256 0x27c7 + Bytes.toB256 [6] = Nat.toB256 0x27cd by decide] at h
  refine ⟨_, _, _, hR, hW, hA, fun o v hv ho => ?_, h⟩
  refine WordAt.write_other (WordAt.write_other (WordAt.write_other (WordAt.write_other
    (WordAt.write_other (WordAt.write_other hv ?_) ?_) ?_) ?_) ?_) ?_ <;>
    simp only [B256.length_toBytes] <;> omega

/-- **After `get_y`** (`0x27cd` → `0x27d9`): `y` at `0x900`, the restore counter at `0x7c0`. -/
theorem xa_ex_afterY {sevm : Sevm} {post b : Devm} {L : List Exec.Frame} {G : Nat} {M : Mem}
    {img : Bytes} {S : List B256} {y : B256}
    (hcode : sevm.code = code) (hR : Mem.Reads M img) (hW : Mem.Wf M)
    (h : XAt sevm post 0x27cd (St b (y :: S) M G) L) :
    ∃ M' G', Mem.Reads M' (Bytes.writeAt (Bytes.writeAt img 0x900 y.toBytes) 0x7e0
        (Nat.toB256 (0x140 + 32 * 52)).toBytes) ∧ Mem.Wf M' ∧
      XAt sevm post 0x27d9 (St b S M' G') L := by
  xjd 0x27ce
  xs 0x27d1 (.push [0x09, 0x00] (by decide)) ri_push
  xmo 0x27d2 (.reg .mstore) (ri_mstore_imgAt (o := 0x900) rfl)
  xs 0x27d5 (.push [0x07, 0xc0] (by decide)) ri_push
  xs 0x27d8 (.push [0x07, 0xe0] (by decide)) ri_push
  xmo 0x27d9 (.reg .mstore) (ri_mstore_imgAt (o := 0x7e0) rfl)
  exact ⟨_, _, hR, hW, h⟩

/-- A word of an image is the word its 32 bytes read as. -/
theorem WordAt.self (img : Bytes) (o : Nat) : WordAt img o (Bytes.toB256 (img.sliceD o 32 0)) :=
  (Blanc.Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)).symm

/-- The frame words after the save/restore round trip: a word of the frame `[0x140, 0x7e0)`
before the save reads the same after the restore. -/
theorem WordAt.of_restore {img img' : Bytes} {o : Nat} {v : B256}
    (hr : ∀ m, m < 52 + 1 → WordAt img' (0x140 + 32 * m)
      (Bytes.toB256 (img.sliceD (0x140 + 32 * m) 32 0)))
    (hv : WordAt img o v) (m : Nat) (hm : m < 53) (ho : o = 0x140 + 32 * m) : WordAt img' o v := by
  subst ho
  have e := hr m hm
  rwa [hv.read] at e

theorem ExFrame.of_restore {img img' : Bytes} {B X : Nat → B256} {D C : B256}
    (hF : ExFrame img B X D C)
    (hr : ∀ m, m < 52 + 1 → WordAt img' (0x140 + 32 * m)
      (Bytes.toB256 (img.sliceD (0x140 + 32 * m) 32 0))) : ExFrame img' B X D C :=
  ⟨fun k hk => WordAt.of_restore hr (hF.rate k hk) k (by omega) rfl,
    fun k hk => WordAt.of_restore hr (hF.old k hk) (k + 3) (by omega) (by omega),
    fun k hk => WordAt.of_restore hr (hF.xp k hk) (k + 6) (by omega) (by omega),
    WordAt.of_restore hr hF.dx 18 (by omega) rfl, WordAt.of_restore hr hF.coin 19 (by omega) rfl⟩

end Blanc.Lift.Curve3Pool
