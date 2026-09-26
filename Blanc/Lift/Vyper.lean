import Blanc.Lift.MapSlot
import Blanc.Lift.InvWalkOps
import Blanc.Lift.WalkSteps

/-!
# Vyper 0.2.x front end: the frame prologue and mapping slots

Vyper 0.2.x runtimes (no internal calls) start every frame past the `CALLDATASIZE < 4` test with a
fixed prologue: `mstore(0x1c, calldataload(0))`, so that `mload(0)` is the selector, and five
clamp constants at `0x20 … 0xa0` (`2^160` for address arguments at `0x20`; the `int128` and
`decimal` bounds at `0x40 … 0xa0`).  The walks carry them in memory:

* `vyPrologue f`: the prologue as a lifted tree before `f`; `ric_vyPrologue` (inverted, over any
  memory) and `rx_vyPrologue` (forward from empty memory, 75 gas);
* `vyMem M w`: memory after it; `VyClamps img`: the five constants in a memory image, which
  word writes outside `0x20 … 0xc0` keep (`VyClamps.writeAt`);
* `mapSlot slot key` (`MapSlot.lean`) is Vyper's `HashMap` slot `keccak(slot ‖ key)`, and
  `vySlot_read` the scratch window `mstore(0xe0, key); mstore(0xc0, slot)` hashes.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The clamp constants, as the prologue pushes them -/

/-- `2^160`, the address clamp at `0x20`. -/
abbrev vyC20 : Bytes := [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
/-- `2^127 - 1` at `0x40`. -/
abbrev vyC40 : Bytes := [0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff]
/-- `-2^127` at `0x60`. -/
abbrev vyC60 : Bytes := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00]
/-- The largest `decimal` at `0x80`. -/
abbrev vyC80 : Bytes := [0x01, 0x2a, 0x05, 0xf1, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
  0xff, 0xff, 0xff, 0xff, 0xfd, 0xab, 0xf4, 0x1c, 0x00]
/-- The smallest `decimal` at `0xa0`. -/
abbrev vyCa0 : Bytes := [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe,
  0xd5, 0xfa, 0x0e, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00]

/-- A word the address clamp admits is an address word. -/
theorem B256.toAdr_toB256_of_lt {x : B256} (h : x.toNat < 2 ^ 160) : x.toAdr.toB256 = x := by
  obtain ⟨⟨h1, h2⟩, l⟩ := x
  have e := B256.toNat_eq ((h1, h2), l)
  rw [B128.toNat_eq] at e
  simp only [] at e
  have hl := B128.toNat_lt (x := l)
  have hh1 : h1.toNat = 0 := by
    rcases Nat.eq_zero_or_pos h1.toNat with h0 | h0
    · exact h0
    · exfalso
      have : 2 ^ 64 * 2 ^ 128 ≤ (h1.toNat * 2 ^ 64 + h2.toNat) * 2 ^ 128 :=
        Nat.mul_le_mul_right _ (Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ h0))
      omega
  have hh2 : h2.toNat < 2 ^ 32 := by
    by_contra hc
    have : 2 ^ 32 * 2 ^ 128 ≤ (h1.toNat * 2 ^ 64 + h2.toNat) * 2 ^ 128 :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have e1 : h1 = 0 := UInt64.toNat_inj.mp (by rw [hh1]; rfl)
  have e2 : h2.toUInt32.toUInt64 = h2 := UInt64.toNat_inj.mp (by
    rw [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32, Nat.mod_eq_of_lt hh2])
  show ((⟨0, h2.toUInt32.toUInt64⟩, l) : B256) = ((h1, h2), l)
  rw [e1, e2]
  rfl

/-- The address clamp word, `2^160`. -/
theorem vyC20_toB256 : (Bytes.toB256 vyC20).toNat = 2 ^ 160 := by decide

/-- The prologue, before the tree `f`. -/
def vyPrologue (f : SFunc) : SFunc :=
  .next (.push [0x00] (by decide)) (.next (.reg .calldataload) (.next (.push [0x1c] (by decide))
  (.next (.reg .mstore)
  (.next (.push vyC20 (by decide)) (.next (.push [0x20] (by decide)) (.next (.reg .mstore)
  (.next (.push vyC40 (by decide)) (.next (.push [0x40] (by decide)) (.next (.reg .mstore)
  (.next (.push vyC60 (by decide)) (.next (.push [0x60] (by decide)) (.next (.reg .mstore)
  (.next (.push vyC80 (by decide)) (.next (.push [0x80] (by decide)) (.next (.reg .mstore)
  (.next (.push vyCa0 (by decide)) (.next (.push [0xa0] (by decide)) (.next (.reg .mstore)
    f))))))))))))))))))

/-- Memory after the prologue over `M`, with `w` the calldata's first word. -/
def vyMem (M : Mem) (w : B256) : Mem :=
  ((((((M.write 28 w.toBytes).write 32 (Bytes.toB256 vyC20).toBytes).write 64
    (Bytes.toB256 vyC40).toBytes).write 96 (Bytes.toB256 vyC60).toBytes).write 128
    (Bytes.toB256 vyC80).toBytes).write 160 (Bytes.toB256 vyCa0).toBytes)

/-- Its image over an image `img` of `M`. -/
def vyImg (img : Bytes) (w : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img 28
    w.toBytes) 32 (Bytes.toB256 vyC20).toBytes) 64 (Bytes.toB256 vyC40).toBytes) 96
    (Bytes.toB256 vyC60).toBytes) 128 (Bytes.toB256 vyC80).toBytes) 160
    (Bytes.toB256 vyCa0).toBytes

theorem vyMem_reads {M : Mem} {img : Bytes} (hwf : Mem.Wf M) (h : Mem.Reads M img) (w : B256) :
    Mem.Reads (vyMem M w) (vyImg img w) := by
  unfold vyMem vyImg
  refine Mem.Reads.write (Mem.Wf.write (Mem.Wf.write (Mem.Wf.write (Mem.Wf.write (Mem.Wf.write
    hwf _ _) _ _) _ _) _ _) _ _) ?_ _ _
  refine Mem.Reads.write (Mem.Wf.write (Mem.Wf.write (Mem.Wf.write (Mem.Wf.write
    hwf _ _) _ _) _ _) _ _) ?_ _ _
  refine Mem.Reads.write (Mem.Wf.write (Mem.Wf.write (Mem.Wf.write hwf _ _) _ _) _ _) ?_ _ _
  refine Mem.Reads.write (Mem.Wf.write (Mem.Wf.write hwf _ _) _ _) ?_ _ _
  refine Mem.Reads.write (Mem.Wf.write hwf _ _) ?_ _ _
  exact Mem.Reads.write hwf h _ _

theorem vyMem_wf {M : Mem} (hwf : Mem.Wf M) (w : B256) : Mem.Wf (vyMem M w) :=
  (((((hwf.write _ _).write _ _).write _ _).write _ _).write _ _).write _ _

/-- From empty memory the prologue leaves six words. -/
theorem vyMem_empty_size (w : B256) : (vyMem Mem.empty w).size = 192 := by
  simp only [vyMem, Mem.size_write_word_at]
  rfl

/-! ## The constants as a carried memory invariant -/

/-- The five clamp constants in a memory image. -/
def VyClamps (img : Bytes) : Prop :=
  img.sliceD 32 32 0 = (Bytes.toB256 vyC20).toBytes ∧
  img.sliceD 64 32 0 = (Bytes.toB256 vyC40).toBytes ∧
  img.sliceD 96 32 0 = (Bytes.toB256 vyC60).toBytes ∧
  img.sliceD 128 32 0 = (Bytes.toB256 vyC80).toBytes ∧
  img.sliceD 160 32 0 = (Bytes.toB256 vyCa0).toBytes

/-- A word write outside `0x20 … 0xc0` keeps the constants. -/
theorem VyClamps.writeAt {img : Bytes} (h : VyClamps img) {n : Nat} (hn : n + 32 ≤ 32 ∨ 192 ≤ n)
    (v : B256) : VyClamps (Bytes.writeAt img n v.toBytes) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rwa [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]

theorem vyImg_clamps (img : Bytes) (w : B256) : VyClamps (vyImg img w) := by
  unfold vyImg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega),
      Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega),
      Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega),
      Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
    exact sliceD_word_same _ _ _
  · rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega),
      Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega),
      Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
    exact sliceD_word_same _ _ _
  · rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega),
      Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
    exact sliceD_word_same _ _ _
  · rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _ (by omega)]
    exact sliceD_word_same _ _ _
  · exact sliceD_word_same _ _ _

/-- The address clamp an image with the constants yields to `MLOAD 0x20`. -/
theorem VyClamps.clamp {img : Bytes} (h : VyClamps img) :
    Bytes.toB256 (img.sliceD 32 32 0) = Bytes.toB256 vyC20 := by
  rw [h.1, B256.toB256_toBytes]

/-! ## The prologue, inverted and forward -/

section Walks

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

/-- **The prologue, inverted.** -/
theorem ric_vyPrologue (run : SFunc.RunCut fs sevm C (St b S M G) (vyPrologue f) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b S (vyMem M (Sevm.dataWord sevm 0)) G') f r := by
  unfold vyPrologue at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_mstore s1
  exact ⟨G19, run⟩

/-- **The prologue, forward** from empty memory: 75 gas (57 for the instructions, 18 for six
words of memory). -/
theorem rx_vyPrologue {o : Outcome} (hroom : S.length + 2 < 1024)
    (k : SFunc.RunExact fs sevm (St b S (vyMem Mem.empty (Sevm.dataWord sevm 0)) G) f o) :
    SFunc.RunExact fs sevm (St b S Mem.empty (G + 75)) (vyPrologue f) o := by
  unfold vyPrologue
  refine rx_push rfl (by omega) ?_
  refine rx_calldataload (by omega) ?_
  refine rx_push rfl (by first | omega | (simp; omega)) ?_
  refine rx_mstore (c := 9) ?_ rfl ?_
  · rw [St.extCost_eq rfl]; decide
  refine rx_push rfl (by omega) ?_
  refine rx_push rfl (by first | omega | (simp; omega)) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq (n := 64) (by simp [Mem.size_write_word_at]; rfl)]; decide
  refine rx_push rfl (by omega) ?_
  refine rx_push rfl (by first | omega | (simp; omega)) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · rw [St.extCost_eq (n := 64) (by simp [Mem.size_write_word_at]; rfl)]; decide
  refine rx_push rfl (by omega) ?_
  refine rx_push rfl (by first | omega | (simp; omega)) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · rw [St.extCost_eq (n := 96) (by simp [Mem.size_write_word_at]; rfl)]; decide
  refine rx_push rfl (by omega) ?_
  refine rx_push rfl (by first | omega | (simp; omega)) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · rw [St.extCost_eq (n := 128) (by simp [Mem.size_write_word_at]; rfl)]; decide
  refine rx_push rfl (by omega) ?_
  refine rx_push rfl (by first | omega | (simp; omega)) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · rw [St.extCost_eq (n := 160) (by simp [Mem.size_write_word_at]; rfl)]; decide
  exact k

end Walks


/-! ## The two argument guards every function body starts with -/

section Guards

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f g ok : SFunc}

/-- The non-payable guard's tree: `CALLVALUE ISZERO PUSH2 ok JUMPI`, reverting on fall-through. -/
def vyNonpayable (h l : UInt8) (fail ok : SFunc) : SFunc :=
  .next (.reg .callvalue) (.next (.reg .iszero) (.next (.push [h, l] (by simp))
    (.branch fail (.dest ok))))

/-- An address argument's clamp: `PUSH1 p CALLDATALOAD PUSH1 0x20 MLOAD DUP2 LT PUSH2 ok JUMPI`,
reverting on fall-through, then `JUMPDEST POP` before `ok`. -/
def vyAddrArg (p h l : UInt8) (fail ok : SFunc) : SFunc :=
  .next (.push [p] (by simp)) (.next (.reg .calldataload) (.next (.push [0x20] (by decide))
    (.next (.reg .mload) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [h, l] (by simp))
      (.branch fail (.dest (.next (.reg .pop) ok)))))))))

theorem rx_vyNonpayable {o : Outcome} {h l : UInt8} {fail : SFunc} (hv : sevm.value = 0)
    (hroom : S.length + 2 < 1024) (k : SFunc.RunExact fs sevm (St b S M G) ok o) :
    SFunc.RunExact fs sevm (St b S M (G + 19)) (vyNonpayable h l fail ok) o := by
  unfold vyNonpayable
  rw [show G + 19 = G + 1 + 10 + 3 + 3 + 2 by omega]
  refine rx_callvalue (by omega) ?_
  rw [hv]
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  exact rx_branch_succ (by decide) (rx_dest k)

theorem ric_vyNonpayable {C : List Nat} {r : Seg} {h l : UInt8} {fail : SFunc}
    (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b S M G) (vyNonpayable h l fail ok) r) :
    sevm.value = 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b S M G') ok r := by
  unfold vyNonpayable at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_callvalue s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G4, run⟩ | ⟨hw, G4, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G5, run⟩ := ric_dest run
  refine ⟨?_, G5, run⟩
  by_contra hne
  exact hw (by simp [B256.eqCheck, hne])

/-- **An address argument's clamp, forward** (34 gas), over a memory image with the clamp
constants, word-aligned and covering `0x40`. -/
theorem rx_vyAddrArg {o : Outcome} {img : Bytes} {p h l : UInt8} {fail : SFunc}
    (hr : Mem.Reads M img) (hc : VyClamps img) (hs : M.size % 32 = 0) (hsz : 64 ≤ M.size)
    (harg : (Sevm.dataWord sevm (Bytes.toB256 [p])).toNat < 2 ^ 160) (hroom : S.length + 3 < 1024)
    (k : SFunc.RunExact fs sevm (St b S M G) ok o) :
    SFunc.RunExact fs sevm (St b S M (G + 34)) (vyAddrArg p h l fail ok) o := by
  unfold vyAddrArg
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  rw [show G + 34 = G + 2 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 by omega]
  refine rx_push rfl (by omega) ?_
  refine rx_calldataload (by omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mload (c := 3) ?_ (v := Bytes.toB256 vyC20) ?_ ?_ (by simp; omega) ?_
  · rw [St, Devm.extCost_zero_of_le hs (by rw [h20]; omega)]; rfl
  · rw [h20, hr.read, hc.clamp]
  · rw [h20]; exact read_covered rfl hs (by omega)
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_lt (v := 1) ?_ (by simp; omega) ?_
  · simp only [B256.ltCheck, B256.lt_iff_toNat_lt_toNat, vyC20_toB256, harg, ite_true]
  refine rx_push rfl (by simp; omega) ?_
  exact rx_branch_succ (by decide) (rx_dest (rx_pop k))

/-- **An address argument's clamp, inverted.** -/
theorem ric_vyAddrArg {C : List Nat} {r : Seg} {img : Bytes} {p h l : UInt8} {fail : SFunc}
    (hf : fail.noOk = true) (hr : Mem.Reads M img) (hc : VyClamps img) (hs : M.size % 32 = 0)
    (hsz : 64 ≤ M.size)
    (run : SFunc.RunCut fs sevm C (St b S M G) (vyAddrArg p h l fail ok) r) :
    (Sevm.dataWord sevm (Bytes.toB256 [p])).toNat < 2 ^ 160 ∧
      ∃ G', SFunc.RunCut fs sevm C (St b S M G') ok r := by
  unfold vyAddrArg at run
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mload s1
  rw [h20, hr.read, hc.clamp, read_covered rfl hs (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := Sevm.dataWord sevm (Bytes.toB256 [p])) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨hw, G8, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_pop s1
  refine ⟨?_, G10, run⟩
  by_contra hne
  apply hw
  simp only [B256.ltCheck, B256.lt_iff_toNat_lt_toNat, vyC20_toB256]
  rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]

end Guards

/-! ## Mapping slots -/

/-- Vyper's scratch window for `HashMap` slots: after `mstore(0xe0, key); mstore(0xc0, slot)`,
`keccak(0xc0, 0x40)` hashes `slot ‖ key`, so the digest is `mapSlot slot key`. -/
theorem vySlot_read (μ : Mem) (slot key : B256) :
    ((((μ.write 224 key.toBytes).write 192 slot.toBytes).read 192 64).1) =
      slot.toBytes ++ key.toBytes :=
  Mem.read_two_word_writes_at_raw_right_first μ 192 slot key

theorem vySlot_keccak (μ : Mem) (slot key : B256) :
    (((μ.write 224 key.toBytes).write 192 slot.toBytes).read 192 64).1.keccak = mapSlot slot key := by
  rw [vySlot_read]; rfl

end Blanc.Lift
