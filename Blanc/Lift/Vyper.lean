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
* `vyMem M w`: memory after it; `VyClamps img`: the five constants in a memory image
  (`vyImg_clamps` establishes it, `VyClamps.clamp` reads the address clamp);
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

/-- `x != 0` compiles to `XOR` with zero. -/
theorem B256.xor_zero (x : B256) : x ^^^ 0 = x := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
  show ((⟨⟨a ^^^ 0, b ^^^ 0⟩, ⟨c ^^^ 0, d ^^^ 0⟩⟩ : B256)) = _
  simp

/-- `x != y` compiles to `XOR`: the word is zero exactly when the operands agree. -/
theorem B256.xor_eq_zero_iff (x y : B256) : x ^^^ y = 0 ↔ x = y := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
  obtain ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ := y
  change ((((a ^^^ a', b ^^^ b'), (c ^^^ c', d ^^^ d')) : (UInt64 × UInt64) × (UInt64 × UInt64)) =
    ((0, 0), (0, 0))) ↔ (((a, b), (c, d)) : (UInt64 × UInt64) × (UInt64 × UInt64)) =
    ((a', b'), (c', d'))
  simp only [Prod.mk.injEq, UInt64.xor_eq_zero_iff]

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

/-- `mload(0)` after the prologue is the selector: the calldata's first word shifted down 224
bits. -/
theorem vyImg_selector (w : B256) : Bytes.toB256 ((vyImg [] w).sliceD 0 32 0) = w >>> 224 := by
  unfold vyImg
  rw [Bytes.sliceD_writeAt_before _ _ 0 32 160 (by omega),
    Bytes.sliceD_writeAt_before _ _ 0 32 128 (by omega),
    Bytes.sliceD_writeAt_before _ _ 0 32 96 (by omega),
    Bytes.sliceD_writeAt_before _ _ 0 32 64 (by omega),
    Bytes.sliceD_writeAt_before _ _ 0 32 32 (by omega), shiftRight_224_eq_toB256_take_four]
  have hw : w.toBytes = w.toBytes.take 4 ++ w.toBytes.drop 4 := (List.take_append_drop 4 _).symm
  have e : (Bytes.writeAt [] 28 w.toBytes).sliceD 0 32 0 =
      List.replicate 28 0 ++ w.toBytes.take 4 := by
    simp only [Bytes.writeAt, List.sliceD, List.drop_zero, List.drop_nil, List.append_nil]
    rw [List.takeD_eq_take _ (by simp [B256.length_toBytes]), hw]
    simp [List.takeD]
  rw [e]
  simp [Bytes.toB256_zero_cons]

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


/-! ## Mapping slots and checked storage updates, as trees -/

section Stores

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f : SFunc} {r : Seg}

/-- The `HashMap` slot sequence: from `[key, slot]`, `mstore(0xe0, key); mstore(0xc0, slot);
keccak(0xc0, 0x40)`, then `f`. -/
def vySlot (f : SFunc) : SFunc :=
  .next (.push [0xe0] (by simp)) (.next (.reg .mstore) (.next (.push [0xc0] (by simp))
    (.next (.reg .mstore) (.next (.push [0x40] (by simp)) (.next (.push [0xc0] (by simp))
      (.next (.reg .keccak256) f))))))

/-- The memory the slot sequence leaves. -/
def vySlotMem (M : Mem) (slot key : B256) : Mem :=
  (((M.write 224 key.toBytes).write 192 slot.toBytes).read 192 64).2

theorem vySlotMem_wf {M : Mem} (h : Mem.Wf M) (slot key : B256) : Mem.Wf (vySlotMem M slot key) :=
  ((h.write _ _).write _ _).extend _ _

/-- **The slot sequence, inverted.** -/
theorem ric_vySlot {key slot : B256}
    (run : SFunc.RunCut fs sevm C (St b (key :: slot :: S) M G) (vySlot f) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (mapSlot slot key :: S) (vySlotMem M slot key) G') f r := by
  have he0 : (Bytes.toB256 [0xe0]).toNat = 224 := by decide
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 192 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  unfold vySlot at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_keccak s1
  rw [he0, hc0, h40, vySlot_keccak] at run
  exact ⟨G7, run⟩

/-- A checked `self.x -= v` with the slot on the stack and `v` the calldata word at `p`:
`DUP1 SLOAD PUSH1 p CALLDATALOAD DUP1 DUP3 LT ISZERO PUSH2 ok JUMPI` (reverting on fall-through),
`JUMPDEST DUP1 DUP3 SUB SWAP1 POP SWAP1 POP DUP2 SSTORE POP`. -/
def vySubStore (p h l : UInt8) (fail rest : SFunc) : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg .sload) (.next (.push [p] (by simp))
    (.next (.reg .calldataload) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt)
      (.next (.reg .iszero) (.next (.push [h, l] (by simp)) (.branch fail
        (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .sub)
          (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop)
            (.next (.reg (.dup 1)) (.next (.reg .sstore) (.next (.reg .pop) rest))))))))))))))))))))

/-- A checked `self.x += v`: `DUP1 SLOAD PUSH1 p CALLDATALOAD DUP2 DUP2 DUP4 ADD LT ISZERO PUSH2
ok JUMPI` (the sum wrapped below the old value reverts), `JUMPDEST DUP1 DUP3 ADD SWAP1 POP SWAP1
POP DUP2 SSTORE POP`. -/
def vyAddStore (p h l : UInt8) (fail rest : SFunc) : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg .sload) (.next (.push [p] (by simp))
    (.next (.reg .calldataload) (.next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3))
      (.next (.reg .add) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [h, l] (by simp))
        (.branch fail (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .add)
          (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop)
            (.next (.reg (.dup 1)) (.next (.reg .sstore) (.next (.reg .pop)
              rest))))))))))))))))))))))

/-- The sum of two words does not wrap exactly when it is not below the first. -/
theorem B256.nof_iff_not_add_lt (y v : B256) :
    y.toNat + v.toNat < 2 ^ 256 ↔ ¬ (y + v < y) := by
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_add]
  have hy := B256.toNat_lt y
  have hv := B256.toNat_lt v
  unfold Nat.lo
  constructor
  · intro h; rw [Nat.mod_eq_of_lt h]; omega
  · intro h
    by_contra hc
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega

/-- **A checked subtraction store, inverted**: the stored word covered the calldata word, and
the slot now holds the difference. -/
theorem ric_vySubStore {slot : B256} {p h l : UInt8} {fail rest : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (slot :: S) M G) (vySubStore p h l fail rest) r) :
    Sevm.dataWord sevm (Bytes.toB256 [p]) ≤ b.getStorVal sevm.currentTarget slot ∧
      ∃ G', SFunc.RunCut fs sevm C
        (St (afterSstore sevm (afterSload sevm b slot) slot
          (b.getStorVal sevm.currentTarget slot - Sevm.dataWord sevm (Bytes.toB256 [p]))) S M G')
        rest r := by
  unfold vySubStore at run
  set x := b.getStorVal sevm.currentTarget slot
  set v := Sevm.dataWord sevm (Bytes.toB256 [p])
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_dup (w := slot) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_dup (w := v) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G10, run⟩ | ⟨hw, G10, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G11, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_dup (w := v) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_swap (S' := v :: (x - v) :: x ::
    slot :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_swap (S' := x :: (x - v) ::
    slot :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_dup (w := slot) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_pop s1
  refine ⟨?_, G21, run⟩
  have h0 := eq_zero_of_iszero_ne_zero hw
  have := toNat_ge_of_ltCheck_eq_zero h0
  exact B256.le_iff_toNat_le_toNat.mpr this

/-- **A checked addition store, inverted**: the sum did not wrap, and the slot now holds it. -/
theorem ric_vyAddStore {slot : B256} {p h l : UInt8} {fail rest : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (slot :: S) M G) (vyAddStore p h l fail rest) r) :
    (b.getStorVal sevm.currentTarget slot).toNat +
        (Sevm.dataWord sevm (Bytes.toB256 [p])).toNat < 2 ^ 256 ∧
      ∃ G', SFunc.RunCut fs sevm C
        (St (afterSstore sevm (afterSload sevm b slot) slot
          (b.getStorVal sevm.currentTarget slot + Sevm.dataWord sevm (Bytes.toB256 [p]))) S M G')
        rest r := by
  unfold vyAddStore at run
  set x := b.getStorVal sevm.currentTarget slot
  set v := Sevm.dataWord sevm (Bytes.toB256 [p])
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_dup (w := slot) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup (w := v) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G12, run⟩ | ⟨hw, G12, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G13, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup (w := v) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_swap (S' := v :: (x + v) :: x ::
    slot :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_swap (S' := x :: (x + v) ::
    slot :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup (w := slot) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_pop s1
  refine ⟨?_, G23, run⟩
  have h0 := eq_zero_of_iszero_ne_zero hw
  rw [B256.nof_iff_not_add_lt]
  intro hlt
  simp [B256.ltCheck, hlt] at h0
  exact absurd h0 (by decide)

end Stores
section StoresForward

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome}

/-- **The slot sequence, forward**, over a memory of at most eight words (`c1` the first store's
charge: 9 from six words, 3 from eight). -/
theorem rx_vySlot {n c1 : Nat} (hM : M.size = n) (hn : n ≤ 256) (h32 : n % 32 = 0)
    (hc1 : gVerylow + (calculateMemoryGasCost (memExtSize n 224 32) - calculateMemoryGasCost n)
      = c1) {slot key : B256} (hroom : S.length + 2 < 1024)
    (k : SFunc.RunExact fs sevm
      (St b (mapSlot slot key :: S) ((M.write 224 key.toBytes).write 192 slot.toBytes) G) f o) :
    SFunc.RunExact fs sevm (St b (key :: slot :: S) M (G + 42 + 3 + 3 + 3 + 3 + c1 + 3))
      (vySlot f) o := by
  have he0 : (Bytes.toB256 [0xe0]).toNat = 224 := by decide
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 192 := by decide
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hs1 : (M.write 224 key.toBytes).size = 256 := by
    rw [Mem.size_write_word_at, hM]
    split_ifs with h
    · omega
    · rfl
  have hs2 : ((M.write 224 key.toBytes).write 192 slot.toBytes).size = 256 := by
    rw [Mem.size_write_word_at, hs1]; rfl
  unfold vySlot
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mstore (c := c1) ?_ (M' := M.write 224 key.toBytes) (by rw [he0]) ?_
  · rw [he0, St.extCost_eq hM]; exact hc1
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mstore (c := 3) ?_ (M' := (M.write 224 key.toBytes).write 192 slot.toBytes)
    (by rw [hc0]) ?_
  · rw [hc0, St, Devm.extCost_zero_of_le (by rw [hs1]) (by rw [hs1]; omega)]; rfl
  refine rx_push rfl (by omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_keccak (c := 42) ?_ ?_ ?_ (by omega) k
  · rw [hc0, h40, St, Devm.extCost_zero_of_le (by rw [hs2]) (by rw [hs2])]; decide
  · rw [hc0, h40]; exact vySlot_keccak M slot key
  · rw [hc0, h40]
    exact Mem.read_snd_eq_self (by rw [hs2]; rfl)

/-- **A checked subtraction store, forward.** -/
theorem rx_vySubStore {slot : B256} {p h l : UInt8} {fail rest : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hle : Sevm.dataWord sevm (Bytes.toB256 [p]) ≤ b.getStorVal sevm.currentTarget slot)
    (hG : gCallStipend < G + 2) (hroom : S.length + 6 < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSstore sevm (afterSload sevm b slot) slot
        (b.getStorVal sevm.currentTarget slot - Sevm.dataWord sevm (Bytes.toB256 [p]))) S M G)
      rest o) :
    let x := b.getStorVal sevm.currentTarget slot
    let v := Sevm.dataWord sevm (Bytes.toB256 [p])
    SFunc.RunExact fs sevm (St b (slot :: S) M (G + 2 + sstoreCost sevm (afterSload sevm b slot) slot (x - v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b slot + 3))
      (vySubStore p h l fail rest) o := by
  intro x v
  unfold vySubStore
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_sload_sel hfork (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_calldataload (by simp; omega) ?_
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_lt (v := 0) ?_ (by simp; omega) ?_
  · simp only [B256.ltCheck]
    rw [ite_eq_right_iff]
    intro hlt
    rw [B256.lt_iff_toNat_lt_toNat] at hlt
    have := B256.le_iff_toNat_le_toNat.mp hle
    omega
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_succ (by decide) (rx_dest ?_)
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_sub (by simp; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_sstore hfork (by omega) hstatic ?_
  exact rx_pop k

/-- **A checked addition store, forward.** -/
theorem rx_vyAddStore {slot : B256} {p h l : UInt8} {fail rest : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hnof : (b.getStorVal sevm.currentTarget slot).toNat +
      (Sevm.dataWord sevm (Bytes.toB256 [p])).toNat < 2 ^ 256)
    (hG : gCallStipend < G + 2) (hroom : S.length + 7 < 1024)
    (k : SFunc.RunExact fs sevm
      (St (afterSstore sevm (afterSload sevm b slot) slot
        (b.getStorVal sevm.currentTarget slot + Sevm.dataWord sevm (Bytes.toB256 [p]))) S M G)
      rest o) :
    let x := b.getStorVal sevm.currentTarget slot
    let v := Sevm.dataWord sevm (Bytes.toB256 [p])
    SFunc.RunExact fs sevm (St b (slot :: S) M (G + 2 + sstoreCost sevm (afterSload sevm b slot) slot (x + v) + 3 + 2 + 3 + 2 + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + sloadCost sevm b slot + 3))
      (vyAddStore p h l fail rest) o := by
  intro x v
  unfold vyAddStore
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_sload_sel hfork (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_calldataload (by simp; omega) ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_dup (n := 3) rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_lt (v := 0) ?_ (by simp; omega) ?_
  · simp only [B256.ltCheck]
    rw [ite_eq_right_iff]
    intro hlt
    exact absurd hlt ((B256.nof_iff_not_add_lt _ _).mp hnof)
  refine rx_iszero (v := 1) (by simp [B256.eqCheck]) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_succ (by decide) (rx_dest ?_)
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_pop ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_sstore hfork (by omega) hstatic ?_
  exact rx_pop k

end StoresForward

/-! ## The string load loop (storage to memory)

Vyper 0.2 copies a stored `String[n]` into memory with one loop: the stack is
`cap :: 0x120 :: lp :: dst :: base :: R` (`lp` the length word plus 32), and the counter `i`
lives in memory at `0x120`.  The head tests `32 i ≤ lp`; the body copies storage word `base + i`
to memory `dst + 32 i`, stores `i + 1` at `0x120`, and loops back to its entry `k` unless the
counter reached `cap`, when it falls through to `exitT`.  A failing test jumps to entry `j`.
The forward steps: `rx_vyLoadStep` (an iteration that loops back), `rx_vyLoadLast` (one that
falls through), `rx_vyLoadExit` (the failing test). -/

/-- The load loop's head tree (see the section note). -/
def vyLoadLoopTree (e0 e1 x0 x1 r0 r1 : UInt8) (j k : Nat) (exitT : SFunc) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.push [0x01, 0x20] (by decide)) (.next (.reg .mload)
  (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .gt) (.next (.reg .iszero)
  (.next (.push [e0, e1] (by simp)) (.branch (.next (.push [x0, x1] (by simp)) (.jump j))
  (.dest (.next (.push [0x01, 0x20] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 5))
  (.next (.reg .add) (.next (.reg .sload) (.next (.push [0x01, 0x20] (by decide))
  (.next (.reg .mload) (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg (.dup 5))
  (.next (.reg .add) (.next (.reg .mstore)
  (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide))
  (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore)
  (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero)
  (.next (.push [r0, r1] (by simp)) (.branchTo exitT k)))))))))))))))))))))))))))))))))))

/-- The load loop's stack. -/
def vyLoadStack (cap lp dst base : B256) (R : List B256) : List B256 :=
  cap :: 0x120 :: lp :: dst :: base :: R

section LoadLoop

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
  {cap lp dst base : B256} {R : List B256} {e0 e1 x0 x1 r0 r1 : UInt8} {j k : Nat}
  {exitT : SFunc}

theorem vy_mul32 {i : Nat} (h : 32 * i < 2 ^ 256) :
    Bytes.toB256 [0x20] * Nat.toB256 i = Nat.toB256 (32 * i) := by
  apply B256.toNat_inj
  rw [B256.toNat_mul, B256.toNat_toB256_of_lt (by omega), B256.toNat_toB256_of_lt h,
    show (Bytes.toB256 [0x20]).toNat = 32 by decide, Nat.lo_eq_of_lt h]

/-- One pass of the head and the body up to the counter's `EQ` test. -/
private theorem rx_vyLoadBody (hfork : CoveredFork sevm.benvStat.fork) (hroom : R.length + 12 < 1024) {i : Nat}
    (hi : 32 * i ≤ lp.toNat) (hwf : Mem.Wf M) {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0)
    (hs1 : 0x140 ≤ s) (hs2 : s ≤ dst.toNat + 32 * i + 32) (hd32 : dst.toNat % 32 = 0)
    (hd : 0x140 ≤ dst.toNat) (hbig : dst.toNat + 32 * i + 32 < 2 ^ 256)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes)
    (kk : SFunc.RunExact fs sevm
      (St (afterSload sevm b (base + Nat.toB256 i))
        (B256.eqCheck cap (Nat.toB256 (i + 1)) :: vyLoadStack cap lp dst base R)
        ((M.write (dst.toNat + 32 * i)
          (b.getStorVal sevm.currentTarget (base + Nat.toB256 i)).toBytes).write 0x120
          (Nat.toB256 (i + 1)).toBytes) G)
      (.next (.reg .iszero) (.next (.push [r0, r1] (by simp)) (.branchTo exitT k))) o) :
    SFunc.RunExact fs sevm (St b (vyLoadStack cap lp dst base R) M
      (G + 101 + sloadCost sevm b (base + Nat.toB256 i) +
        (calculateMemoryGasCost (dst.toNat + 32 * i + 32) - calculateMemoryGasCost s)))
      (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  set v := b.getStorVal sevm.currentTarget (base + Nat.toB256 i)
  set ce := calculateMemoryGasCost (dst.toNat + 32 * i + 32) - calculateMemoryGasCost s
  set M1 := M.write (dst.toNat + 32 * i) v.toBytes
  have h120 : (0x120 : B256).toNat = 0x120 := by decide
  have hp120 : Bytes.toB256 [0x01, 0x20] = 0x120 := by decide
  have hi' : Bytes.toB256 (M.read 0x120 32).1 = Nat.toB256 i := by
    rw [hctr, B256.toB256_toBytes]
  have hM : (M.read 0x120 32).2 = M := read_covered hs hs32 (by omega)
  have h32i := vy_mul32 (i := i) (by omega)
  have hdn : (dst + Nat.toB256 (32 * i)).toNat = dst.toNat + 32 * i := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have hgt : B256.gtCheck (Nat.toB256 (32 * i)) lp = 0 := by
    rw [B256.gtCheck, ite_eq_right_iff]
    intro h
    rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)] at h
    omega
  have hM1s : M1.size = dst.toNat + 32 * i + 32 := by
    rw [Mem.size_write_word_aligned (by rw [hs]; exact hs32) (by omega), hs]; omega
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hctr1 : (M1.read 0x120 32).1 = (Nat.toB256 i).toBytes := by
    rw [((Mem.reads_data M).write hwf _ _).read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      ← (Mem.reads_data M).read, hctr]
  have hM1 : (M1.read 0x120 32).2 = M1 := read_covered hM1s (by omega) (by omega)
  have hone := one_add_toB256 (h := i) (by omega)
  rw [show G + 101 + sloadCost sevm b (base + Nat.toB256 i) + ce =
    G + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + (3 + ce) + 3 + 3 + 5 + 3 + 3 + 3 +
      sloadCost sevm b (base + Nat.toB256 i) + 3 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 +
      3 + 3 + 1 by omega]
  unfold vyLoadLoopTree vyLoadStack
  unfold vyLoadStack at kk
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120]; exact hi') (by rw [h120]; exact hM)
    (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mul h32i (by simp; omega) ?_
  refine rx_gt hgt (by simp; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_succ (by decide) (rx_dest ?_)
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120]; exact hi') (by rw [h120]; exact hM)
    (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl
  refine rx_dup (n := 5) rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_sload_sel (k' := base + Nat.toB256 i) hfork (by simp; omega) ?_
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120]; exact hi') (by rw [h120]; exact hM)
    (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mul h32i (by simp; omega) ?_
  refine rx_dup (n := 5) rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_mstore (c := 3 + ce) ?_ (M' := M1) (by rw [hdn]) ?_
  · rw [hdn, St.extCost_eq hs, memExtSize_word_aligned hs32 (by omega), Nat.max_eq_right hs2]
    rfl
  refine rx_dest ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120, hctr1, B256.toB256_toBytes])
    (by rw [h120]; exact hM1) (by simp; omega) ?_
  · rw [h120, St.extCost_eq hM1s, memExtSize_of_le (by omega) (by omega), Nat.sub_self]; rfl
  refine rx_push rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  rw [hone]
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_dup (n := 3) rfl (by simp; omega) ?_
  refine rx_mstore (c := 3) ?_ (M' := M1.write 0x120 (Nat.toB256 (i + 1)).toBytes)
    (by rw [h120]) ?_
  · rw [h120, St.extCost_eq hM1s, memExtSize_of_le (by omega) (by omega), Nat.sub_self]; rfl
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  exact rx_eq rfl (by simp; omega) kk

/-- **An iteration that loops back**: `32 i ≤ lp`, the counter `i + 1` has not reached `cap`. -/
theorem rx_vyLoadStep (hfork : CoveredFork sevm.benvStat.fork) (hroom : R.length + 12 < 1024)
    {i : Nat} (hi : 32 * i ≤ lp.toNat) (hcap : cap ≠ Nat.toB256 (i + 1)) (hwf : Mem.Wf M) {s : Nat}
    (hs : M.size = s) (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s) {d : Nat} (hdd : dst.toNat = d)
    (hs2 : s ≤ d + 32 * i + 32) (hd32 : d % 32 = 0) (hd : 0x140 ≤ d) (hbig : d + 32 * i + 32 < 2 ^ 256)
    {ce : Nat} (hce : calculateMemoryGasCost (d + 32 * i + 32) - calculateMemoryGasCost s = ce)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes) {gk : SFunc} (hk : fs[k]? = some gk)
    (kk : SFunc.RunExact fs sevm
      (St (afterSload sevm b (base + Nat.toB256 i)) (vyLoadStack cap lp dst base R)
        ((M.write (d + 32 * i)
          (b.getStorVal sevm.currentTarget (base + Nat.toB256 i)).toBytes).write 0x120
          (Nat.toB256 (i + 1)).toBytes) G) gk o) :
    SFunc.RunExact fs sevm (St b (vyLoadStack cap lp dst base R) M
      (G + 117 + sloadCost sevm b (base + Nat.toB256 i) + ce))
      (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  subst hdd hce
  rw [show G + 117 = G + 10 + 3 + 3 + 101 by omega]
  refine rx_vyLoadBody hfork hroom hi hwf hs hs32 hs1 hs2 hd32 hd hbig hctr ?_
  refine rx_iszero (v := 1) ?_ (by simp [vyLoadStack]; omega) ?_
  · simp [B256.eqCheck, hcap]
  refine rx_push rfl (by simp [vyLoadStack]; omega) ?_
  exact rx_branchTo_succ (by decide) hk kk

/-- **An iteration that falls through**: `32 i ≤ lp`, the counter `i + 1` reached `cap`. -/
theorem rx_vyLoadLast (hfork : CoveredFork sevm.benvStat.fork) (hroom : R.length + 12 < 1024)
    {i : Nat} (hi : 32 * i ≤ lp.toNat) (hcap : cap = Nat.toB256 (i + 1)) (hwf : Mem.Wf M) {s : Nat}
    (hs : M.size = s) (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s) {d : Nat} (hdd : dst.toNat = d)
    (hs2 : s ≤ d + 32 * i + 32) (hd32 : d % 32 = 0) (hd : 0x140 ≤ d) (hbig : d + 32 * i + 32 < 2 ^ 256)
    {ce : Nat} (hce : calculateMemoryGasCost (d + 32 * i + 32) - calculateMemoryGasCost s = ce)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes)
    (kk : SFunc.RunExact fs sevm
      (St (afterSload sevm b (base + Nat.toB256 i)) (vyLoadStack cap lp dst base R)
        ((M.write (d + 32 * i)
          (b.getStorVal sevm.currentTarget (base + Nat.toB256 i)).toBytes).write 0x120
          (Nat.toB256 (i + 1)).toBytes) G) exitT o) :
    SFunc.RunExact fs sevm (St b (vyLoadStack cap lp dst base R) M
      (G + 117 + sloadCost sevm b (base + Nat.toB256 i) + ce))
      (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  subst hdd hce
  rw [show G + 117 = G + 10 + 3 + 3 + 101 by omega]
  refine rx_vyLoadBody hfork hroom hi hwf hs hs32 hs1 hs2 hd32 hd hbig hctr ?_
  refine rx_iszero (v := 0) ?_ (by simp [vyLoadStack]; omega) ?_
  · simp [B256.eqCheck, hcap]
  refine rx_push rfl (by simp [vyLoadStack]; omega) ?_
  exact rx_branchTo_zero kk

/-- **The failing test**: `32 i > lp`, on to entry `j`. -/
theorem rx_vyLoadExit (hroom : R.length + 12 < 1024) {i : Nat} (hi : lp.toNat < 32 * i)
    (hi' : 32 * i < 2 ^ 256) {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes) {gj : SFunc} (hj : fs[j]? = some gj)
    (kk : SFunc.RunExact fs sevm (St b (vyLoadStack cap lp dst base R) M G) gj o) :
    SFunc.RunExact fs sevm (St b (vyLoadStack cap lp dst base R) M (G + 48))
      (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  have h120 : (0x120 : B256).toNat = 0x120 := by decide
  have hp120 : Bytes.toB256 [0x01, 0x20] = 0x120 := by decide
  have hM : (M.read 0x120 32).2 = M := read_covered hs hs32 (by omega)
  have hgt : B256.gtCheck (Nat.toB256 (32 * i)) lp = 1 := by
    rw [B256.gtCheck, ite_eq_left_iff]
    intro h
    exact absurd (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hi']; exact hi) h
  rw [show G + 48 = G + 8 + 3 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 1 by omega]
  unfold vyLoadLoopTree vyLoadStack
  unfold vyLoadStack at kk
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120, hctr, B256.toB256_toBytes])
    (by rw [h120]; exact hM) (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mul (vy_mul32 hi') (by simp; omega) ?_
  refine rx_gt hgt (by simp; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_zero ?_
  refine rx_push rfl (by simp; omega) ?_
  exact rx_jump hj kk

/-- **One pass of the load loop, inverted**: either the test fails and the run goes on at
entry `j`, or storage word `base + i` was copied to memory `dst + 32 i`, the counter bumped,
and the run goes on at `exitT` (the counter reached `cap`) or back at entry `k`. -/
theorem ric_vyLoadIter (hfork : CoveredFork sevm.benvStat.fork) {C : List Nat} {r : Seg}
    {i : Nat} {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s) {d : Nat}
    (hdd : dst.toNat = d) (hs2 : s ≤ d + 32 * i + 32) (hd32 : d % 32 = 0) (hd : 0x140 ≤ d)
    (hbig : d + 32 * i + 32 < 2 ^ 256) (hwf : Mem.Wf M)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes) {gk gj : SFunc}
    (hk : fs[k]? = some gk) (hkC : k ∉ C) (hj : fs[j]? = some gj) (hjC : j ∉ C)
    (run : SFunc.RunCut fs sevm C (St b (vyLoadStack cap lp dst base R) M G)
      (vyLoadLoopTree e0 e1 x0 x1 r0 r1 j k exitT) r) :
    (lp.toNat < 32 * i ∧
      ∃ G', SFunc.RunCut fs sevm C (St b (vyLoadStack cap lp dst base R) M G') gj r) ∨
    (32 * i ≤ lp.toNat ∧ ∃ G', SFunc.RunCut fs sevm C
      (St (afterSload sevm b (base + Nat.toB256 i)) (vyLoadStack cap lp dst base R)
        ((M.write (d + 32 * i)
          (b.getStorVal sevm.currentTarget (base + Nat.toB256 i)).toBytes).write 0x120
          (Nat.toB256 (i + 1)).toBytes) G')
      (if cap = Nat.toB256 (i + 1) then exitT else gk) r) := by
  subst hdd
  set v := b.getStorVal sevm.currentTarget (base + Nat.toB256 i)
  set M1 := M.write (dst.toNat + 32 * i) v.toBytes
  have h120 : (Bytes.toB256 [0x01, 0x20]).toNat = 0x120 := by decide
  have h120' : (0x120 : B256).toNat = 0x120 := by decide
  have hi' : Bytes.toB256 (M.read 0x120 32).1 = Nat.toB256 i := by
    rw [hctr, B256.toB256_toBytes]
  have hM : (M.read 0x120 32).2 = M := read_covered hs hs32 (by omega)
  have h32i := vy_mul32 (i := i) (by omega)
  have hdn : (dst + Nat.toB256 (32 * i)).toNat = dst.toNat + 32 * i := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have hM1s : M1.size = dst.toNat + 32 * i + 32 := by
    rw [Mem.size_write_word_aligned (by rw [hs]; exact hs32) (by omega), hs]; omega
  have hctr1 : Bytes.toB256 (M1.read 0x120 32).1 = Nat.toB256 i := by
    rw [((Mem.reads_data M).write hwf _ _).read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      ← (Mem.reads_data M).read, hctr, B256.toB256_toBytes]
  have hM1 : (M1.read 0x120 32).2 = M1 := read_covered hM1s (by omega) (by omega)
  have hone := one_add_toB256 (h := i) (by omega)
  unfold vyLoadLoopTree vyLoadStack at run
  unfold vyLoadStack
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mload s1
  rw [h120, hM, hi'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_mul s1
  rw [h32i] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hw, G10, run⟩ | ⟨hw, G10, run⟩
  · left
    refine ⟨?_, ?_⟩
    · by_contra hc
      apply absurd hw
      have : B256.gtCheck (Nat.toB256 (32 * i)) lp = 0 := by
        rw [B256.gtCheck, ite_eq_right_iff]
        intro h
        rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)] at h
        omega
      rw [this]; decide
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
    exact ric_jump hjC hj run
  right
  refine ⟨?_, ?_⟩
  · by_contra hc
    apply hw
    have : B256.gtCheck (Nat.toB256 (32 * i)) lp = 1 := by
      rw [B256.gtCheck, ite_eq_left_iff]
      intro h
      exact absurd (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat,
        B256.toNat_toB256_of_lt (by omega)]; omega) h
    rw [this]; decide
  obtain ⟨G11, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mload s1
  rw [h120, hM, hi'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_dup (n := 5) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_mload s1
  rw [h120, hM, hi'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_mul s1
  rw [h32i] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup (n := 5) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_mstore s1
  rw [hdn] at run
  obtain ⟨G24, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_mload s1
  rw [h120', hM1, hctr1] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_add s1
  rw [hone] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_dup (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_dup (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_mstore s1
  rw [h120'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_push s1
  rcases ric_branchTo hkC hk run with ⟨hw, G36, run⟩ | ⟨hw, G36, run⟩
  · have hc : cap = Nat.toB256 (i + 1) := by
      by_contra hc
      simp only [B256.eqCheck, hc, ↓reduceIte] at hw
      exact absurd hw (by decide)
    exact ⟨G36, by rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact run⟩
  · have hc : cap ≠ Nat.toB256 (i + 1) := by
      intro hc
      simp only [B256.eqCheck, hc, ↓reduceIte] at hw
      exact hw (by decide)
    exact ⟨G36, by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; exact run⟩

end LoadLoop

/-! ## The string store loop (memory to storage)

The setter's side of the string copy: stack `cap :: 0x120 :: lp :: base :: src :: R`, counter
`i` at `0x120`; while `32 i ≤ lp` it stores the memory word at `src + 32 i` to storage slot
`base + i`, bumps the counter, and loops back to its entry `k` unless the counter reached `cap`
(then `exitT`); a failing test jumps to entry `j`.  Forward: `rx_vyStoreStep`, `rx_vyStoreLast`,
`rx_vyStoreExit`; inverted: `ric_vyStoreIter` (one pass, either way out). -/

/-- The store loop's head tree (see the section note). -/
def vyStoreLoopTree (e0 e1 x0 x1 r0 r1 : UInt8) (j k : Nat) (exitT : SFunc) : SFunc :=
  .dest (.next (.reg (.dup 2)) (.next (.push [0x01, 0x20] (by decide)) (.next (.reg .mload)
  (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .gt) (.next (.reg .iszero)
  (.next (.push [e0, e1] (by simp)) (.branch (.next (.push [x0, x1] (by simp)) (.jump j))
  (.dest (.next (.push [0x01, 0x20] (by decide)) (.next (.reg .mload)
  (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg (.dup 5)) (.next (.reg .add)
  (.next (.reg .mload) (.next (.push [0x01, 0x20] (by decide)) (.next (.reg .mload)
  (.next (.reg (.dup 5)) (.next (.reg .add) (.next (.reg .sstore)
  (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide))
  (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore)
  (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero)
  (.next (.push [r0, r1] (by simp)) (.branchTo exitT k)))))))))))))))))))))))))))))))))))

/-- The store loop's stack. -/
def vyStoreStack (cap lp base src : B256) (R : List B256) : List B256 :=
  cap :: 0x120 :: lp :: base :: src :: R

/-- An `SSTORE`'s selected charge is at most a cold access plus a fresh set. -/
theorem sstoreCost_le (sevm : Sevm) (d : Devm) (key value : B256) :
    sstoreCost sevm d key value ≤ gasColdSload + gasStorageSet := by
  have hv : sstoreValueCost (getOrigStorVal sevm sevm.currentTarget key)
      (d.getStorVal sevm.currentTarget key) value ≤ gasStorageSet := by
    rw [sstoreValueCost]
    split_ifs <;> decide +kernel
  unfold sstoreCost
  split <;> omega

section StoreLoop

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
  {cap lp base src : B256} {R : List B256} {e0 e1 x0 x1 r0 r1 : UInt8} {j k : Nat}
  {exitT : SFunc}

/-- One pass of the head and the body up to the counter's `EQ` test. -/
private theorem rx_vyStoreBody (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hroom : R.length + 12 < 1024) {i : Nat}
    (hi : 32 * i ≤ lp.toNat) {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s)
    {sn : Nat} (hsn : src.toNat = sn) (hsrc : sn + 32 * i + 32 ≤ s) (hbig : s < 2 ^ 256)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes) (hG : gCallStipend < G)
    (kk : SFunc.RunExact fs sevm
      (St (afterSstore sevm b (base + Nat.toB256 i) (Bytes.toB256 (M.read (sn + 32 * i) 32).1))
        (B256.eqCheck cap (Nat.toB256 (i + 1)) :: vyStoreStack cap lp base src R)
        (M.write 0x120 (Nat.toB256 (i + 1)).toBytes) G)
      (.next (.reg .iszero) (.next (.push [r0, r1] (by simp)) (.branchTo exitT k))) o) :
    SFunc.RunExact fs sevm (St b (vyStoreStack cap lp base src R) M
      (G + 101 + sstoreCost sevm b (base + Nat.toB256 i)
        (Bytes.toB256 (M.read (sn + 32 * i) 32).1)))
      (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  subst hsn
  set w := Bytes.toB256 (M.read (src.toNat + 32 * i) 32).1
  set sc := sstoreCost sevm b (base + Nat.toB256 i) w
  have h120 : (0x120 : B256).toNat = 0x120 := by decide
  have hp120 : Bytes.toB256 [0x01, 0x20] = 0x120 := by decide
  have hi' : Bytes.toB256 (M.read 0x120 32).1 = Nat.toB256 i := by
    rw [hctr, B256.toB256_toBytes]
  have hM : (M.read 0x120 32).2 = M := read_covered hs hs32 (by omega)
  have h32i := vy_mul32 (i := i) (by omega)
  have hsa : (src + Nat.toB256 (32 * i)).toNat = src.toNat + 32 * i := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have hgt : B256.gtCheck (Nat.toB256 (32 * i)) lp = 0 := by
    rw [B256.gtCheck, ite_eq_right_iff]
    intro h
    rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)] at h
    omega
  have hM1 : (M.write 0x120 (Nat.toB256 (i + 1)).toBytes).size = s := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hs]; omega), hs]
  have hone := one_add_toB256 (h := i) (by omega)
  have hc0 : gVerylow + (calculateMemoryGasCost s - calculateMemoryGasCost s) = 3 := by
    rw [Nat.sub_self]; rfl
  rw [show G + 101 + sc = G + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 1 + sc + 3 + 3 + 3 + 3 + 3 +
    3 + 3 + 5 + 3 + 3 + 3 + 1 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 1 by omega]
  unfold vyStoreLoopTree vyStoreStack
  unfold vyStoreStack at kk
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120]; exact hi')
    (by rw [h120]; exact hM) (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega)]; exact hc0
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mul h32i (by simp; omega) ?_
  refine rx_gt hgt (by simp; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_succ (by decide) (rx_dest ?_)
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120]; exact hi')
    (by rw [h120]; exact hM) (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega)]; exact hc0
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mul h32i (by simp; omega) ?_
  refine rx_dup (n := 5) rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_mload (c := 3) (v := w) ?_ (by rw [hsa]) (by rw [hsa]; exact read_covered hs hs32 hsrc)
    (by simp; omega) ?_
  · rw [hsa, St.extCost_eq hs, memExtSize_of_le hs32 hsrc]; exact hc0
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120]; exact hi')
    (by rw [h120]; exact hM) (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega)]; exact hc0
  refine rx_dup (n := 5) rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_sstore hfork (by omega) hstatic ?_
  refine rx_dest ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120]; exact hi')
    (by rw [h120]; exact hM) (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega)]; exact hc0
  refine rx_push rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  rw [hone]
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_dup (n := 3) rfl (by simp; omega) ?_
  refine rx_mstore (c := 3) ?_ (M' := M.write 0x120 (Nat.toB256 (i + 1)).toBytes)
    (by rw [h120]) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega)]; exact hc0
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  exact rx_eq rfl (by simp; omega) kk

/-- **A store iteration that loops back.** -/
theorem rx_vyStoreStep (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hroom : R.length + 12 < 1024) {i : Nat} (hi : 32 * i ≤ lp.toNat)
    (hcap : cap ≠ Nat.toB256 (i + 1)) {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0)
    (hs1 : 0x140 ≤ s) {sn : Nat} (hsn : src.toNat = sn) (hsrc : sn + 32 * i + 32 ≤ s)
    (hbig : s < 2 ^ 256) (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes)
    (hG : gCallStipend < G) {gk : SFunc} (hk : fs[k]? = some gk)
    (kk : SFunc.RunExact fs sevm
      (St (afterSstore sevm b (base + Nat.toB256 i) (Bytes.toB256 (M.read (sn + 32 * i) 32).1))
        (vyStoreStack cap lp base src R) (M.write 0x120 (Nat.toB256 (i + 1)).toBytes) G) gk o) :
    SFunc.RunExact fs sevm (St b (vyStoreStack cap lp base src R) M
      (G + 117 + sstoreCost sevm b (base + Nat.toB256 i)
        (Bytes.toB256 (M.read (sn + 32 * i) 32).1)))
      (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  rw [show G + 117 = G + 10 + 3 + 3 + 101 by omega]
  refine rx_vyStoreBody hfork hstatic hroom hi hs hs32 hs1 hsn hsrc hbig hctr (by omega) ?_
  refine rx_iszero (v := 1) ?_ (by simp [vyStoreStack]; omega) ?_
  · simp [B256.eqCheck, hcap]
  refine rx_push rfl (by simp [vyStoreStack]; omega) ?_
  exact rx_branchTo_succ (by decide) hk kk

/-- **A store iteration that falls through** (the counter reached `cap`). -/
theorem rx_vyStoreLast (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hroom : R.length + 12 < 1024) {i : Nat} (hi : 32 * i ≤ lp.toNat)
    (hcap : cap = Nat.toB256 (i + 1)) {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0)
    (hs1 : 0x140 ≤ s) {sn : Nat} (hsn : src.toNat = sn) (hsrc : sn + 32 * i + 32 ≤ s)
    (hbig : s < 2 ^ 256) (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes)
    (hG : gCallStipend < G)
    (kk : SFunc.RunExact fs sevm
      (St (afterSstore sevm b (base + Nat.toB256 i) (Bytes.toB256 (M.read (sn + 32 * i) 32).1))
        (vyStoreStack cap lp base src R) (M.write 0x120 (Nat.toB256 (i + 1)).toBytes) G) exitT o) :
    SFunc.RunExact fs sevm (St b (vyStoreStack cap lp base src R) M
      (G + 117 + sstoreCost sevm b (base + Nat.toB256 i)
        (Bytes.toB256 (M.read (sn + 32 * i) 32).1)))
      (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  rw [show G + 117 = G + 10 + 3 + 3 + 101 by omega]
  refine rx_vyStoreBody hfork hstatic hroom hi hs hs32 hs1 hsn hsrc hbig hctr (by omega) ?_
  refine rx_iszero (v := 0) ?_ (by simp [vyStoreStack]; omega) ?_
  · simp [B256.eqCheck, hcap]
  refine rx_push rfl (by simp [vyStoreStack]; omega) ?_
  exact rx_branchTo_zero kk

/-- **The store loop's failing test**: `32 i > lp`, on to entry `j`. -/
theorem rx_vyStoreExit (hroom : R.length + 12 < 1024) {i : Nat} (hi : lp.toNat < 32 * i)
    (hi' : 32 * i < 2 ^ 256) {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes) {gj : SFunc} (hj : fs[j]? = some gj)
    (kk : SFunc.RunExact fs sevm (St b (vyStoreStack cap lp base src R) M G) gj o) :
    SFunc.RunExact fs sevm (St b (vyStoreStack cap lp base src R) M (G + 48))
      (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT) o := by
  have h120 : (0x120 : B256).toNat = 0x120 := by decide
  have hp120 : Bytes.toB256 [0x01, 0x20] = 0x120 := by decide
  have hM : (M.read 0x120 32).2 = M := read_covered hs hs32 (by omega)
  have hgt : B256.gtCheck (Nat.toB256 (32 * i)) lp = 1 := by
    rw [B256.gtCheck, ite_eq_left_iff]
    intro h
    exact absurd (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hi']; exact hi) h
  rw [show G + 48 = G + 8 + 3 + 10 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 + 1 by omega]
  unfold vyStoreLoopTree vyStoreStack
  unfold vyStoreStack at kk
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_push hp120 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Nat.toB256 i) ?_ (by rw [h120, hctr, B256.toB256_toBytes])
    (by rw [h120]; exact hM) (by simp; omega) ?_
  · rw [h120, St.extCost_eq hs, memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mul (vy_mul32 hi') (by simp; omega) ?_
  refine rx_gt hgt (by simp; omega) ?_
  refine rx_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_branch_zero ?_
  refine rx_push rfl (by simp; omega) ?_
  exact rx_jump hj kk

/-- **One pass of the store loop, inverted**: either the test fails and the run goes on at
entry `j`, or word `i` was stored, the counter bumped, and the run goes on at `exitT` (the
counter reached `cap`) or back at entry `k`. -/
theorem ric_vyStoreIter (hfork : CoveredFork sevm.benvStat.fork) {C : List Nat} {r : Seg}
    {i : Nat} {s : Nat} (hs : M.size = s) (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s) {sn : Nat}
    (hsn : src.toNat = sn) (hsrc : sn + 32 * i + 32 ≤ s) (hbig : s < 2 ^ 256)
    (hctr : (M.read 0x120 32).1 = (Nat.toB256 i).toBytes) {gk gj : SFunc}
    (hk : fs[k]? = some gk) (hkC : k ∉ C) (hj : fs[j]? = some gj) (hjC : j ∉ C)
    (run : SFunc.RunCut fs sevm C (St b (vyStoreStack cap lp base src R) M G)
      (vyStoreLoopTree e0 e1 x0 x1 r0 r1 j k exitT) r) :
    (lp.toNat < 32 * i ∧
      ∃ G', SFunc.RunCut fs sevm C (St b (vyStoreStack cap lp base src R) M G') gj r) ∨
    (32 * i ≤ lp.toNat ∧ sevm.isStatic = false ∧ ∃ G', SFunc.RunCut fs sevm C
      (St (afterSstore sevm b (base + Nat.toB256 i) (Bytes.toB256 (M.read (sn + 32 * i) 32).1))
        (vyStoreStack cap lp base src R) (M.write 0x120 (Nat.toB256 (i + 1)).toBytes) G')
      (if cap = Nat.toB256 (i + 1) then exitT else gk) r) := by
  subst hsn
  have h120 : (Bytes.toB256 [0x01, 0x20]).toNat = 0x120 := by decide
  have h120' : (0x120 : B256).toNat = 0x120 := by decide
  have hi' : Bytes.toB256 (M.read 0x120 32).1 = Nat.toB256 i := by
    rw [hctr, B256.toB256_toBytes]
  have hM : (M.read 0x120 32).2 = M := read_covered hs hs32 (by omega)
  have h32i := vy_mul32 (i := i) (by omega)
  have hsa : (src + Nat.toB256 (32 * i)).toNat = src.toNat + 32 * i := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have hone := one_add_toB256 (h := i) (by omega)
  unfold vyStoreLoopTree vyStoreStack at run
  unfold vyStoreStack
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (n := 2) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mload s1
  rw [h120, hM, hi'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_mul s1
  rw [h32i] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hw, G10, run⟩ | ⟨hw, G10, run⟩
  · left
    refine ⟨?_, ?_⟩
    · by_contra hc
      apply absurd hw
      have : B256.gtCheck (Nat.toB256 (32 * i)) lp = 0 := by
        rw [B256.gtCheck, ite_eq_right_iff]
        intro h
        rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt (by omega)] at h
        omega
      rw [this]; decide
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
    exact ric_jump hjC hj run
  right
  refine ⟨?_, ?_⟩
  · by_contra hc
    apply hw
    have : B256.gtCheck (Nat.toB256 (32 * i)) lp = 1 := by
      rw [B256.gtCheck, ite_eq_left_iff]
      intro h
      exact absurd (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat,
        B256.toNat_toB256_of_lt (by omega)]; omega) h
    rw [this]; decide
  obtain ⟨G11, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_mload s1
  rw [h120, hM, hi'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_mul s1
  rw [h32i] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup (n := 5) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_mload s1
  rw [hsa, read_covered hs hs32 hsrc] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_mload s1
  rw [h120, hM, hi'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_dup (n := 5) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  refine ⟨ri_sstore_nonstatic hfork s1, ?_⟩
  obtain ⟨G23, rfl⟩ := ri_sstore hfork s1
  obtain ⟨G24, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_mload s1
  rw [h120', hM, hi'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_add s1
  rw [hone] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_dup (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_dup (n := 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_mstore s1
  rw [h120'] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_dup (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_push s1
  rcases ric_branchTo hkC hk run with ⟨hw, G36, run⟩ | ⟨hw, G36, run⟩
  · have hc : cap = Nat.toB256 (i + 1) := by
      by_contra hc
      simp only [B256.eqCheck, hc, ↓reduceIte] at hw
      exact absurd hw (by decide)
    exact ⟨G36, by rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]; exact run⟩
  · have hc : cap ≠ Nat.toB256 (i + 1) := by
      intro hc
      simp only [B256.eqCheck, hc, ↓reduceIte] at hw
      exact hw (by decide)
    exact ⟨G36, by rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]; exact run⟩

end StoreLoop

/-- A read of a window a write misses sees the memory before the write. -/
theorem Mem.read_write_disjoint {M : Mem} (hwf : Mem.Wf M) (n : Nat) (xs : Bytes) {a len : Nat}
    (h : n + xs.length ≤ a ∨ a + len ≤ n) : ((M.write n xs).read a len).1 = (M.read a len).1 := by
  rw [((Mem.reads_data M).write hwf n xs).read, (Mem.reads_data M).read]
  rcases h with h | h
  · exact Bytes.sliceD_writeAt_after _ _ _ _ _ h
  · exact Bytes.sliceD_writeAt_before _ _ _ _ _ h

/-- The store loop's set-up: `mstore(0xc0, sl); keccak(0xc0, 0x20)` for the base, the length
word at `src` plus 32, the counter `0` at `0x120`, the cap `cp`. -/
def vyStoreHead (s0 s1 sl cp : UInt8) (loopT : SFunc) : SFunc :=
  .next (.push [s0, s1] (by simp)) (.next (.reg (.dup 0)) (.next (.push [sl] (by simp))
  (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide))
  (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.push [0x20] (by decide))
  (.next (.reg (.dup 2)) (.next (.reg .mload) (.next (.reg .add)
  (.next (.push [0x01, 0x20] (by decide)) (.next (.push [0x00] (by decide))
  (.next (.push [cp] (by simp)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3))
  (.next (.reg .mstore) (.next (.reg .add) loopT))))))))))))))))))

section StoreHead

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {o : Outcome} {s0 s1 sl cp : UInt8} {loopT : SFunc}

/-- **The store loop's set-up, forward** (90 gas over a memory already covering `0x140`). -/
theorem rx_vyStoreHead (hroom : S.length + 8 < 1024) {s sn : Nat} (hs : M.size = s)
    (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s) (hwf : Mem.Wf M)
    (hsn : (Bytes.toB256 [s0, s1]).toNat = sn) (hsn1 : 0xe0 ≤ sn) (hsn2 : sn + 32 ≤ s)
    (kk : SFunc.RunExact fs sevm
      (St b (vyStoreStack (Bytes.toB256 [cp] + Nat.toB256 0)
          (Bytes.toB256 (M.read sn 32).1 + Bytes.toB256 [0x20]) (Bytes.toB256 [sl]).toBytes.keccak
          (Bytes.toB256 [s0, s1]) (Bytes.toB256 [s0, s1] :: S))
        ((M.write 0xc0 (Bytes.toB256 [sl]).toBytes).write 0x120 (Nat.toB256 0).toBytes) G)
      loopT o) :
    SFunc.RunExact fs sevm (St b S M (G + 90)) (vyStoreHead s0 s1 sl cp loopT) o := by
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 0xc0 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h120 : (0x120 : B256).toNat = 0x120 := by decide
  set M1 := M.write 0xc0 (Bytes.toB256 [sl]).toBytes
  have hM1 : M1.size = s := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hs]; omega), hs]
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hL : (M1.read sn 32).1 = (M.read sn 32).1 :=
    Mem.read_write_disjoint hwf _ _ (by rw [B256.length_toBytes]; omega)
  have hx : ∀ n (hn : n = s), gVerylow + (calculateMemoryGasCost (memExtSize s 0xc0 32) -
      calculateMemoryGasCost n) = 3 := by
    intro n hn; subst hn; rw [memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl
  rw [show G + 90 = G + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 36 + 3 + 3 + 3 + 3 + 3 + 3 + 3
    by omega]
  unfold vyStoreHead
  refine rx_push rfl (by omega) ?_
  refine rx_dup (n := 0) rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_mstore (c := 3) ?_ (M' := M1) (by rw [hc0]) ?_
  · rw [hc0, St.extCost_eq hs]; exact hx s rfl
  refine rx_push rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_keccak (c := 36) ?_ (by rw [hc0, h20, Mem.read_write_word_of_wf hwf])
    (by rw [hc0, h20]; exact read_covered hM1 (by omega) (by omega)) (by simp; omega) ?_
  · rw [hc0, h20, St, Devm.extCost_zero_of_le (by rw [hM1]; exact hs32) (by rw [hM1]; omega)]
    decide
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_mload (c := 3) (v := Bytes.toB256 (M.read sn 32).1) ?_ (by rw [hsn, hL])
    (by rw [hsn]; exact read_covered hM1 (by omega) hsn2) (by simp; omega) ?_
  · rw [hsn, St.extCost_eq hM1, memExtSize_of_le hs32 hsn2, Nat.sub_self]; rfl
  refine rx_add (by simp; omega) ?_
  refine rx_push (w := 0x120) (by decide) (by simp; omega) ?_
  refine rx_push (w := Nat.toB256 0) (by decide) (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_dup (n := 3) rfl (by simp; omega) ?_
  refine rx_mstore (c := 3) ?_ (by rw [h120]) ?_
  · rw [h120, St.extCost_eq hM1, memExtSize_of_le hs32 (by omega), Nat.sub_self]; rfl
  exact rx_add (by simp; omega) kk

/-- **The store loop's set-up, inverted.** -/
theorem ric_vyStoreHead {C : List Nat} {r : Seg} {s sn : Nat} (hs : M.size = s)
    (hs32 : s % 32 = 0) (hs1 : 0x140 ≤ s) (hwf : Mem.Wf M)
    (hsn : (Bytes.toB256 [s0, s1]).toNat = sn) (hsn1 : 0xe0 ≤ sn) (hsn2 : sn + 32 ≤ s)
    (run : SFunc.RunCut fs sevm C (St b S M G) (vyStoreHead s0 s1 sl cp loopT) r) :
    ∃ G', SFunc.RunCut fs sevm C
      (St b (vyStoreStack (Bytes.toB256 [cp] + Bytes.toB256 [0x00])
          (Bytes.toB256 (M.read sn 32).1 + Bytes.toB256 [0x20]) (Bytes.toB256 [sl]).toBytes.keccak
          (Bytes.toB256 [s0, s1]) (Bytes.toB256 [s0, s1] :: S))
        ((M.write 0xc0 (Bytes.toB256 [sl]).toBytes).write 0x120 (Nat.toB256 0).toBytes) G')
      loopT r := by
  have hc0 : (Bytes.toB256 [0xc0]).toNat = 0xc0 := by decide
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h120 : (Bytes.toB256 [0x01, 0x20]).toNat = 0x120 := by decide
  have hp120 : Bytes.toB256 [0x01, 0x20] = 0x120 := by decide
  have h0 : Bytes.toB256 [0x00] = Nat.toB256 0 := by decide
  set M1 := M.write 0xc0 (Bytes.toB256 [sl]).toBytes
  have hM1 : M1.size = s := by
    rw [Mem.size_write_of_le (by rw [B256.length_toBytes, hs]; omega), hs]
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hL : (M1.read sn 32).1 = (M.read sn 32).1 :=
    Mem.read_write_disjoint hwf _ _ (by rw [B256.length_toBytes]; omega)
  unfold vyStoreHead at run
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (n := 0) rfl s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_mstore s1'
  rw [hc0] at run
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_keccak s1'
  rw [hc0, h20, Mem.read_write_word_of_wf hwf,
    read_covered hM1 (by omega) (by omega)] at run
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (n := 2) rfl s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_mload s1'
  rw [hsn, hL, read_covered hM1 (by omega) hsn2] at run
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_add s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup (n := 1) rfl s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup (n := 3) rfl s1'
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_mstore s1'
  rw [h120, h0] at run
  obtain ⟨d1, s1', run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_add s1'
  rw [hp120] at run
  exact ⟨G19, run⟩

end StoreHead

/-! ## A stored `String` view (storage to returned ABI string)

A Vyper 0.2 view of a stored `String[32 (cp - 1)]` at slot `sl`: the non-payable guard, the
string's base `keccak(sl)` via `mstore(0xc0, sl); keccak(0xc0, 0x20)`, the length word plus 32,
the counter `0` at `0x120`, and the load loop `loopT` (stack `vyLoadStack`, destination
`0x180`).  The join after the loop zero-pads with `CALLDATACOPY` from `CALLDATASIZE`
(`sliceD_data_end`) to `ceil32` (`ceil32_eq`). -/

/-- The string view's body up to its load loop `loopT`. -/
def vyStrView (h0 h1 sl cp : UInt8) (fail loopT : SFunc) : SFunc :=
  .next (.reg .callvalue) (.next (.reg .iszero) (.next (.push [h0, h1] (by simp))
  (.branch fail (.dest (.next (.push [sl] (by simp)) (.next (.reg (.dup 0))
  (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide))
  (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.push [0x01, 0x80] (by decide))
  (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .sload) (.next (.reg .add)
  (.next (.push [0x01, 0x20] (by decide)) (.next (.push [0x00] (by decide))
  (.next (.push [cp] (by simp)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3))
  (.next (.reg .mstore) (.next (.reg .add) loopT)))))))))))))))))))))))

/-- `ceil32` as a subtraction of the residue. -/
theorem ceil32_eq (L : Nat) : ceil32 L = L + 31 - (L + 31) % 32 := by
  unfold ceil32
  rcases h : L % 32 with _ | m
  · simp only; omega
  · simp only; omega

/-- Reading calldata from its own size reads zeros. -/
theorem sliceD_data_end (bs : Bytes) (z : Nat) : bs.sliceD bs.length z 0 = List.replicate z 0 := by
  unfold List.sliceD
  rw [List.drop_length]
  induction z with
  | zero => rfl
  | succ z ih => simp [List.takeD, ih, List.replicate_succ]

end Blanc.Lift
