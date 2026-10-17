import Blanc.Lift.IdentityCall
import Blanc.Lift.BalanceDiffCall

/-!
# Vyper 0.2.x `raw_call(…, max_outsize=32)` and its optional-return test

Vyper 0.2.x compiles `_response = raw_call(coin, data, max_outsize=32)` followed by
`if len(_response) > 0: assert convert(_response, bool)` to one fixed instruction sequence
after the `CALL` (output window one word at `L + 32`):

* `PUSH2 ok JUMPI` — revert unless the call succeeded;
* `len = min(RETURNDATASIZE, 32)` — the short side jumps to a join entry, the long side falls
  into an inlined copy of it (`vyRawCallTail`);
* the join (`vyRawCallJoin`): `mstore(L, len)`, an identity-precompile copy of
  `L[0 : 32 + len]` to `B` (`IdentityCall.lean`), and `if mload(B) > 0:` the tested tail
  (`vyRawCallCheck`): load the copied word at `B + 32`, assert `0 ≤ len ≤ 32` (signed), divide
  by `256^(32 - len)` and assert the quotient nonzero.

Only `L`, `B` and the jump destinations vary between sites (`VyRawSite`).  The test passes
exactly when `RawCallOk returnData`: no data, or the first `min(len, 32)` bytes are a nonzero
big-endian number (any nonzero value passes; data longer than 32 bytes is accepted).  The
bytes the output window keeps beyond the returned prefix are read into the tested word but
divided away.

* `ric_vyRawCallTail` / `ric_vyRawCall`: inversion — flag `≠ 0`, `RawCallOk`, and the
  continuation over the identity copy's base with memory changed only in `[L, L + 32)` and
  `[B, B + 64)`;
* `rxc_vyRawCallTail`: the forward twin, at gas `rawTailCost (min len 32)`, with memory
  `vyRawMem`;
* the join and the tested tail have their own `ric_`/`rxc_` lemmas;
* supporting facts: `Bytes.toNat_toB256_of_length` (a word's number is its bytes'
  big-endian number), `Mem.write_getD_inside`, `Mem.read_fst_of_getD` (byte-level memory
  without `Mem.Wf`), `Mem.AgreeOutside.comp` / `.widen`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

theorem Bytes.toNat_aux_eq (xs : Bytes) (acc : Nat) :
    Bytes.toNat.aux acc xs = acc * 256 ^ xs.length + Bytes.toNat.aux 0 xs := by
  induction xs generalizing acc with
  | nil => simp only [Bytes.toNat.aux, List.length_nil, pow_zero, mul_one, add_zero]
  | cons x xs ih =>
    simp only [Bytes.toNat.aux, List.length_cons, zero_mul, zero_add]
    rw [ih, ih x.toNat, pow_succ]
    ring

theorem Bytes.toNat_append (xs ys : Bytes) :
    Bytes.toNat (xs ++ ys) = Bytes.toNat xs * 256 ^ ys.length + Bytes.toNat ys := by
  have h : ∀ acc, Bytes.toNat.aux acc (xs ++ ys) = Bytes.toNat.aux (Bytes.toNat.aux acc xs) ys := by
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih => intro acc; exact ih _
  unfold Bytes.toNat
  rw [h, Bytes.toNat_aux_eq]

theorem UInt16.toNat_toBytes' (x : UInt16) : Bytes.toNat x.toBytes = x.toNat := by
  have hx := x.toNat_lt
  simp only [Bytes.toNat, UInt16.toBytes, Bytes.toNat.aux, zero_mul, UInt16.toNat_toUInt8,
    UInt16.toNat_shiftRight, UInt16.reduceToNat, Nat.reduceMod, Nat.reducePow, zero_add,
    Nat.shiftRight_eq_div_pow] at hx ⊢
  omega

theorem UInt32.toNat_toBytes' (x : UInt32) : Bytes.toNat x.toBytes = x.toNat := by
  have hx := x.toNat_lt
  rw [UInt32.toBytes, Bytes.toNat_append, UInt16.toNat_toBytes', UInt16.toNat_toBytes']
  simp only [UInt32.toNat_toUInt16, UInt32.toNat_shiftRight, UInt32.reduceToNat, Nat.reduceMod,
    Nat.reducePow, Nat.shiftRight_eq_div_pow, UInt16.toBytes, List.length_cons, List.length_nil]
    at hx ⊢
  omega

theorem UInt64.toNat_toBytes' (x : UInt64) : Bytes.toNat x.toBytes = x.toNat := by
  have hx := x.toNat_lt
  rw [UInt64.toBytes, Bytes.toNat_append, UInt32.toNat_toBytes', UInt32.toNat_toBytes']
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod,
    Nat.reducePow, Nat.shiftRight_eq_div_pow, UInt32.toBytes, UInt16.toBytes, List.length_append,
    List.length_cons, List.length_nil] at hx ⊢
  omega

theorem B128.toNat_eq_toBytes (x : B128) : x.toNat = Bytes.toNat x.toBytes := by
  rcases x with ⟨a, c⟩
  change (a.toNat <<< 64 ||| c.toNat) = Bytes.toNat (a.toBytes ++ c.toBytes)
  rw [Bytes.toNat_append, UInt64.toNat_toBytes', UInt64.toNat_toBytes',
    ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt c), Nat.shiftLeft_eq]
  simp only [UInt64.toBytes, UInt32.toBytes, UInt16.toBytes, List.length_append,
    List.length_cons, List.length_nil]
  norm_num only

/-- A word's number is the big-endian number of its 32 bytes. -/
theorem B256.toNat_eq_toBytes (x : B256) : x.toNat = Bytes.toNat x.toBytes := by
  rcases x with ⟨a, c⟩
  have hc := B128.toNat_eq_toBytes c
  change (a.toNat <<< 128 ||| c.toNat) = Bytes.toNat (B128.toBytes a ++ B128.toBytes c)
  rw [Bytes.toNat_append, ← B128.toNat_eq_toBytes, ← hc,
    ← Nat.shiftLeft_add_eq_or_of_lt (B128.toNat_lt (x := c)), Nat.shiftLeft_eq]
  simp only [B128.toBytes, UInt64.toBytes, UInt32.toBytes, UInt16.toBytes, List.length_append,
    List.length_cons, List.length_nil]
  norm_num only

/-- The word of 32 bytes has their big-endian number. -/
theorem Bytes.toNat_toB256_of_length {xs : Bytes} (h : xs.length = 32) :
    (Bytes.toB256 xs).toNat = Bytes.toNat xs := by
  rw [B256.toNat_eq_toBytes, Bytes.toBytes_toB256_of_length h]

theorem Bytes.toNat_replicate_zero (m : Nat) : Bytes.toNat (List.replicate m 0) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ', Bytes.toNat_append, ih]
    rfl

theorem Bytes.toB256_replicate_zero_append (m : Nat) (xs : Bytes) :
    Bytes.toB256 (List.replicate m 0 ++ xs) = Bytes.toB256 xs := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.cons_append, Bytes.toB256_zero_cons, ih]

/-- A word of at most 32 bytes has their big-endian number. -/
theorem Bytes.toNat_toB256_of_le {xs : Bytes} (h : xs.length ≤ 32) :
    (Bytes.toB256 xs).toNat = Bytes.toNat xs := by
  rw [← Bytes.toB256_replicate_zero_append (32 - xs.length),
    Bytes.toNat_toB256_of_length (by rw [List.length_append, List.length_replicate]; omega),
    Bytes.toNat_append, Bytes.toNat_replicate_zero, zero_mul, zero_add]

/-- A two-byte push is below `2^16`. -/
theorem toNat_push2_lt (a c : UInt8) : (Bytes.toB256 [a, c]).toNat < 2 ^ 16 := by
  rw [Bytes.toNat_toB256_of_le (by simp only [List.length_cons, List.length_nil]; omega)]
  exact lt_of_lt_of_le (Bytes.toNat_lt _) (by simp only [List.length_cons, List.length_nil]; norm_num only)

/-! ## Memory, byte by byte (no `Mem.Wf`) -/

/-- A byte inside a write window reads as the payload's. -/
theorem Mem.write_getD_inside (μ : Mem) (n : Nat) {ys : Bytes} {i : Nat} (hi : i < ys.length) :
    (μ.write n ys).data.getD (n + i) 0 = ys.getD i 0 := by
  have hne : ys ≠ [] := by
    intro h; rw [h, List.length_nil] at hi; exact Nat.not_lt_zero _ hi
  obtain ⟨A, hdata, hA, -, -, -⟩ := Mem.write_base μ n hne
  rw [hdata, Array.getD_writeD 0 _ A n (n + i) hA, ite_eq_left (by omega),
    Nat.add_sub_cancel_left]

/-- A read's bytes are the backing array's. -/
theorem Mem.read_fst_getD (μ : Mem) (i k : Nat) {j : Nat} (hj : j < k) :
    (μ.read i k).1.getD j 0 = μ.data.getD (i + j) 0 := by
  simp only [Mem.read, Array.sliceD_eq_map]
  rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; exact hj),
    List.getElem_map, List.getElem_range]

/-- A read is determined by the backing array's bytes. -/
theorem Mem.read_fst_of_getD (μ : Mem) (i : Nat) {xs : Bytes}
    (h : ∀ j, j < xs.length → μ.data.getD (i + j) 0 = xs.getD j 0) :
    (μ.read i xs.length).1 = xs := by
  apply List.ext_getElem
  · simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  · intro j h1 h2
    have e := Mem.read_fst_getD μ i xs.length h2
    rw [List.getD_eq_getElem _ _ h1, h j h2, List.getD_eq_getElem _ _ h2] at e
    exact e

/-- A memory with the same bytes that did not shrink agrees with the old one everywhere. -/
theorem Mem.agreeOutside_of_data {μ μ' : Mem} (hd : μ'.data = μ.data) (hs : μ.size ≤ μ'.size)
    (lo hi : Nat) : Mem.AgreeOutside μ μ' lo hi :=
  ⟨hs, fun _ _ _ => by rw [hd]⟩

/-- Agreement outside a window survives a further agreement outside the same window. -/
theorem Mem.AgreeOutside.comp {μ μ' μ'' : Mem} {lo hi : Nat} (h1 : Mem.AgreeOutside μ μ' lo hi)
    (h2 : Mem.AgreeOutside μ' μ'' lo hi) : Mem.AgreeOutside μ μ'' lo hi :=
  ⟨le_trans h1.1 h2.1, fun i hi hout => (h2.2 i (lt_of_lt_of_le hi h1.1) hout).trans
    (h1.2 i hi hout)⟩

/-- Agreement outside a window is agreement outside any larger window. -/
theorem Mem.AgreeOutside.widen {μ μ' : Mem} {lo hi lo' hi' : Nat}
    (h : Mem.AgreeOutside μ μ' lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    Mem.AgreeOutside μ μ' lo' hi' :=
  ⟨h.1, fun i hi hout => h.2 i hi (by omega)⟩

/-- `SGT`, inverted, value forgotten. -/
theorem ri_sgt {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {x y : B256}
    {d : Devm} (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .sgt) d) :
    ∃ z G', d = St b (z :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact ⟨_, St.of_diff (Devm.diffBurn_of_applyBinary run)⟩

/-- The first `n` bytes of a 32-byte window, as a number: the window's number shifted down by
the other `32 - n` bytes. -/
theorem Bytes.toNat_append_div {xs ys : Bytes} {n : Nat} (hy : ys.length = 32 - n) :
    Bytes.toNat (xs ++ ys) / 256 ^ (32 - n) = Bytes.toNat xs := by
  rw [Bytes.toNat_append, hy, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (hy ▸ Bytes.toNat_lt ys), zero_add]

/-! ## The pattern -/

/-- **Vyper's `raw_call(…, max_outsize=32)` success test**: no data, or the first
`min(len, 32)` bytes read as a nonzero number (any nonzero value passes; data longer than 32
bytes is accepted). -/
def RawCallOk (rd : Bytes) : Prop :=
  rd.length = 0 ∨ Bytes.toNat (rd.take (min rd.length 32)) ≠ 0

/-- The immediates that vary between `raw_call` sites: the length word's slot `L`, the copy
buffer `B` (both two-byte pushes), and the eight two-byte jump destinations in order. -/
structure VyRawSite where
  lh : UInt8
  ll : UInt8
  bh : UInt8
  bl : UInt8
  j1h : UInt8
  j1l : UInt8
  j2h : UInt8
  j2l : UInt8
  j3h : UInt8
  j3l : UInt8
  j4h : UInt8
  j4l : UInt8
  j5h : UInt8
  j5l : UInt8
  j6h : UInt8
  j6l : UInt8
  j7h : UInt8
  j7l : UInt8
  j8h : UInt8
  j8l : UInt8

/-- The tested tail: `if len > 0: assert convert(slice(buf, 32, len) … ) != 0` — loads the copied
word at `B + 32`, asserts `0 ≤ len ≤ 32` (signed), divides by `256^(32 - len)` and asserts the
quotient nonzero; then `K`. -/
def vyRawCallCheck (p : VyRawSite) (f3 f4 f5 K : SFunc) : SFunc :=
  .next (.push [p.bh, p.bl] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide))
  (.next (.reg .add) (.next (.reg .mload) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 2))
  (.next (.reg .mload) (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide))
  (.next (.reg (.swap 0)) (.next (.reg .sgt) (.next (.reg .iszero) (.next (.push [p.j6h, p.j6l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch f3 (.dest (.next (.reg (.dup 0)) (.next (.reg (.swap 1)) (.next (.reg (.swap 0))
  (.next (.reg .slt) (.next (.reg .iszero) (.next (.push [p.j7h, p.j7l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch f4 (.dest (.next (.reg (.dup 0)) (.next (.push [0x20] (by decide)) (.next (.reg .sub)
  (.next (.push [0x01, 0x00] (by decide)) (.next (.reg .exp) (.next (.reg (.dup 2))
  (.next (.reg .div) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0))
  (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg .iszero)
  (.next (.reg .iszero) (.next (.push [p.j8h, p.j8l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch f5 (.dest K)))))))))))))))))))))))))))))))))))))))))

/-- The join (an entry of its own, also inlined on the fall-through): `len` to `L`, the identity
copy of `L[0 : 32 + len]` to `B`, and the `len > 0` test guarding `vyRawCallCheck`. -/
def vyRawCallJoin (p : VyRawSite) (f2 f3 f4 f5 K : SFunc) : SFunc :=
  .dest (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop)
  (.next (.push [p.lh, p.ll] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.next (.reg .mstore) (.next (.push [p.lh, p.ll] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.next (.reg (.dup 0)) (.next (.reg .mload) (.next (.push [0x20] (by decide)) (.next (.reg .add)
  (.next (.reg (.dup 0)) (.next (.push [p.bh, p.bl] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.next (.reg (.dup 2))
  (.next (.reg (.dup 4)) (.next (.push [0x00] (by decide)) (.next (.push [0x04] (by decide))
  (.next (.reg .gas) (.next (.exec .call) (.next (.push [p.j4h, p.j4l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch f2 (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.push [0x00] (by decide))
  (.next (.push [p.bh, p.bl] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.next (.reg .mload) (.next (.reg .gt) (.next (.reg .iszero)
  (.next (.push [p.j5h, p.j5l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch (vyRawCallCheck p f3 f4 f5 K) K)))))))))))))))))))))))))))))))

/-- **The `raw_call(…, max_outsize=32)` tail** after the `CALL` node: the flag test, `len =
min(RETURNDATASIZE, 32)` (the short side jumps to the join entry `k`, the long side falls into
an inlined copy), then `vyRawCallJoin`. -/
def vyRawCallTail (p : VyRawSite) (k : Nat) (f1 f2 f3 f4 f5 K : SFunc) : SFunc :=
  .next (.push [p.j1h, p.j1l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.branch f1 (.dest (.next (.push [0x20] (by decide))
  (.next (.reg .returndatasize) (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .gt)
  (.next (.reg .iszero) (.next (.push [p.j2h, p.j2l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff]))
  (.branch (.next (.reg (.dup 0)) (.next (.push [p.j3h, p.j3l] (by simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceLeDiff])) (.jump k)))
    (.dest (.next (.reg (.dup 1)) (vyRawCallJoin p f2 f3 f4 f5 K)))))))))))))

/-- The quotient the tested tail computes: the window's word over `256 ^ (32 - len)` is the
number of the window's first `len` bytes. -/
theorem rawCheck_quot {len w : B256} {xs : Bytes} (hn1 : 1 ≤ len.toNat) (hn32 : len.toNat ≤ 32)
    (hxs : xs.length = 32) (hw : w = Bytes.toB256 xs) :
    (w / B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x20] - len)).toNat =
      Bytes.toNat (xs.take len.toNat) := by
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have h256 : (Bytes.toB256 [0x01, 0x00]).toNat = 256 := by decide
  have hsub : (Bytes.toB256 [0x20] - len).toNat = 32 - len.toNat := by
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by rw [h20]; exact hn32)), h20]
  have hlt : 256 ^ (32 - len.toNat) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num only) (show 32 - len.toNat ≤ 31 by omega))
      (by norm_num only)
  have he : (B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x20] - len)).toNat =
      256 ^ (32 - len.toNat) := by
    rw [B256.bexp_eq, h256, hsub, Nat.mod_eq_of_lt hlt, B256.toNat_toB256_of_lt hlt]
  have he0 : B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x20] - len) ≠ 0 := by
    intro h0
    have := congrArg B256.toNat h0
    rw [he] at this
    exact absurd this (by positivity)
  rw [B256.toNat_div he0, he, hw, Bytes.toNat_toB256_of_length hxs,
    ← List.take_append_drop len.toNat xs, List.take_append_drop,
    ← Bytes.toNat_append_div (xs := xs.take len.toNat) (ys := xs.drop len.toNat)
      (by rw [List.length_drop, hxs]), List.take_append_drop]

section Inv

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg}

/-- **The tested tail, inverted.**  With `len` (`1 ≤ len ≤ 32`) at `B` and the first `len`
returned bytes at `B + 32`: those bytes are a nonzero number. -/
theorem ric_vyRawCallCheck {p : VyRawSite} {f3 f4 f5 K : SFunc} {len : B256} {rd : Bytes}
    (hf3 : f3.noOk = true) (hf4 : f4.noOk = true) (hf5 : f5.noOk = true)
    (hn1 : 1 ≤ len.toNat) (hn32 : len.toNat ≤ 32) (hnrd : len.toNat ≤ rd.length)
    (hlen : ∀ j, j < 32 →
      M.data.getD ((Bytes.toB256 [p.bh, p.bl]).toNat + j) 0 = len.toBytes.getD j 0)
    (hrd : ∀ j, j < len.toNat →
      M.data.getD ((Bytes.toB256 [p.bh, p.bl]).toNat + 32 + j) 0 = rd.getD j 0)
    (run : SFunc.RunCut fs sevm C (St b S M G) (vyRawCallCheck p f3 f4 f5 K) r) :
    Bytes.toNat (rd.take len.toNat) ≠ 0 ∧
      ∃ M' G', M'.data = M.data ∧ M.size ≤ M'.size ∧ SFunc.RunCut fs sevm C (St b S M' G') K r := by
  set Bw := Bytes.toB256 [p.bh, p.bl] with hBw
  set n := len.toNat with hn
  have hB : Bw.toNat < 2 ^ 16 := toNat_push2_lt p.bh p.bl
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  unfold vyRawCallCheck at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (n := 0) (w := Bw) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_mload s1
  have h32B : (Bytes.toB256 [0x20] + Bw).toNat = Bw.toNat + 32 := by
    rw [B256.toNat_add, h20, Nat.lo_eq_of_lt (by omega)]; omega
  rw [h32B] at run
  set w := Bytes.toB256 (M.read (Bw.toNat + 32) 32).1 with hw
  set M4 := (M.read (Bw.toNat + 32) 32).2 with hM4
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup (n := 2) (w := Bw) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mload s1
  have hv : Bytes.toB256 (M4.read Bw.toNat 32).1 = len := by
    have e : (M4.read Bw.toNat len.toBytes.length).1 = len.toBytes :=
      Mem.read_fst_of_getD M4 Bw.toNat (fun j hj => hlen j (by rw [B256.length_toBytes] at hj; exact hj))
    rw [B256.length_toBytes] at e
    rw [e, B256.toB256_toBytes]
  rw [hv] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup (n := 0) (w := len) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_swap (S' := len :: Bytes.toB256 [0x20] :: len :: Bytes.toB256 [0x00] ::
    w :: Bw :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨z1, G12, rfl⟩ := ri_sgt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G15, run⟩ | ⟨-, G15, run⟩
  · exact (run.false_of_noOk hf3).elim
  obtain ⟨G16, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_dup (n := 0) (w := len) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_swap (S' := Bytes.toB256 [0x00] :: len :: len :: w :: Bw :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_swap (S' := len :: Bytes.toB256 [0x00] :: len :: w :: Bw :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨z2, G20, rfl⟩ := ri_slt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G23, run⟩ | ⟨-, G23, run⟩
  · exact (run.false_of_noOk hf4).elim
  obtain ⟨G24, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_dup (n := 0) (w := len) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_exp s1
  set e := B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x20] - len) with he
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_dup (n := 2) (w := w) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_div s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_swap (S' := len :: (w / e) :: w :: Bw :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_swap (S' := w :: (w / e) :: Bw :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_swap (S' := Bw :: (w / e) :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G41, run⟩ | ⟨hq, G41, run⟩
  · exact (run.false_of_noOk hf5).elim
  obtain ⟨G42, run⟩ := ric_dest run
  refine ⟨?_, _, G42, ?_, ?_, run⟩
  · have hxs : (M.read (Bw.toNat + 32) 32).1.length = 32 := by
      simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
    have htake : (M.read (Bw.toNat + 32) 32).1.take n = rd.take n := by
      apply List.ext_getElem
      · rw [List.length_take, List.length_take, hxs]; omega
      · intro j h1 h2
        rw [List.length_take] at h1
        have e1 := Mem.read_fst_getD M (Bw.toNat + 32) 32 (j := j) (by omega)
        rw [List.getElem_take, List.getElem_take, ← List.getD_eq_getElem _ 0,
          ← List.getD_eq_getElem _ 0, e1, hrd j (by omega)]
    have hq0 : w / e ≠ 0 := by
      intro h0
      apply hq
      rw [h0]
      decide
    rw [← htake, ← rawCheck_quot hn1 hn32 hxs hw]
    exact fun h => hq0 (B256.toNat_inj _ _ (by rw [h]; rfl))
  · rfl
  · show M.size ≤ memExtSize (memExtSize M.size (Bw.toNat + 32) 32) Bw.toNat 32
    exact le_trans (memExtSize_ge _ _ _) (memExtSize_ge _ _ _)

/-- **The join, inverted.**  From `[len, rds, c, …]` with `len ≤ 32` and the first `len` returned
bytes at `L + 32`: either `len = 0`, or those bytes are a nonzero number; the continuation `K`
runs over a base the identity copy `ShaCallPost`-relates to `b`, with memory changed only in
`[L, L + 32)` and then in `[B, B + 64)`. -/
theorem ric_vyRawCallJoin {p : VyRawSite} {f2 f3 f4 f5 K : SFunc} {len rds c : B256}
    {rd : Bytes} (hid : IdReady sevm b)
    (hf2 : f2.noOk = true) (hf3 : f3.noOk = true) (hf4 : f4.noOk = true) (hf5 : f5.noOk = true)
    (hn32 : len.toNat ≤ 32) (hnrd : len.toNat ≤ rd.length)
    (hrd : ∀ j, j < len.toNat → (Bytes.toB256 [p.lh, p.ll]).toNat + 32 + j < M.size ∧
      M.data.getD ((Bytes.toB256 [p.lh, p.ll]).toNat + 32 + j) 0 = rd.getD j 0)
    (run : SFunc.RunCut fs sevm C (St b (len :: rds :: c :: S) M G)
      (vyRawCallJoin p f2 f3 f4 f5 K) r) :
    (len.toNat = 0 ∨ Bytes.toNat (rd.take len.toNat) ≠ 0) ∧
      ∃ b' rd' M1 M' G', ShaCallPost b b' rd' ∧
        Mem.AgreeOutside M M1 (Bytes.toB256 [p.lh, p.ll]).toNat
          ((Bytes.toB256 [p.lh, p.ll]).toNat + 32) ∧
        Mem.AgreeOutside M1 M' (Bytes.toB256 [p.bh, p.bl]).toNat
          ((Bytes.toB256 [p.bh, p.bl]).toNat + 64) ∧
        SFunc.RunCut fs sevm C (St b' S M' G') K r := by
  set Lw := Bytes.toB256 [p.lh, p.ll] with hLw
  set Bw := Bytes.toB256 [p.bh, p.bl] with hBw
  set n := len.toNat with hn
  have hL : Lw.toNat < 2 ^ 16 := toNat_push2_lt p.lh p.ll
  have hB : Bw.toNat < 2 ^ 16 := toNat_push2_lt p.bh p.bl
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  unfold vyRawCallJoin at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_swap (S' := rds :: len :: c :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_swap (S' := c :: len :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_mstore s1
  set M1 := M.write Lw.toNat len.toBytes with hM1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup (n := 0) (w := Lw) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mload s1
  rw [hM1, Mem.read_write_word_self, B256.toB256_toBytes, ← hM1] at run
  set M1' := (M1.read Lw.toNat 32).2 with hM1'
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_add s1
  set nw := Bytes.toB256 [0x20] + len with hnw
  have hnw' : nw.toNat = n + 32 := by
    rw [hnw, B256.toNat_add, h20, Nat.lo_eq_of_lt (by omega)]; omega
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_dup (n := 0) (w := nw) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_dup (n := 2) (w := nw) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_dup (n := 4) (w := Lw) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨gw, G19, rfl⟩ := ri_gas s1
  rw [show Bytes.toB256 [0x04] = 4 by decide, show Bytes.toB256 [0x00] = 0 by decide] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  rcases ri_call_identity hid s1 with h0 | ⟨b', G20, hpost, rfl⟩
  · rw [St.self (d := d1) h0 rfl] at run
    obtain ⟨d2, s2, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s2
    rcases ric_branch run with ⟨-, G22, run⟩ | ⟨hw, -⟩
    · exact (run.false_of_noOk hf2).elim
    · exact absurd rfl hw
  set input := (M1'.read Lw.toNat nw.toNat).1 with hinput
  set M2 := (M1'.extends [(Lw.toNat, nw.toNat), (Bw.toNat, nw.toNat)]).write Bw.toNat
    (input.take nw.toNat) with hM2
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hw, -⟩ | ⟨-, G22, run⟩
  · exact absurd hw (by decide)
  obtain ⟨G23, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_mload s1
  -- the copy, byte by byte
  have hinlen : input.length = n + 32 := by
    rw [hinput, ← hnw']
    simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  have hcopy : ∀ j, j < n + 32 → M2.data.getD (Bw.toNat + j) 0 = M1.data.getD (Lw.toNat + j) 0 := by
    intro j hj
    rw [hM2, Mem.write_getD_inside _ _ (by rw [List.length_take, hnw', hinlen]; omega),
      List.getD_eq_getElem _ _ (by rw [List.length_take, hnw', hinlen]; omega),
      List.getElem_take, ← List.getD_eq_getElem _ 0, hinput,
      Mem.read_fst_getD _ _ _ (by rw [hnw']; exact hj)]
    rfl
  have hlenB : ∀ j, j < 32 → M2.data.getD (Bw.toNat + j) 0 = len.toBytes.getD j 0 := by
    intro j hj
    rw [hcopy j (by omega), hM1, Mem.write_getD_inside _ _ (by rw [B256.length_toBytes]; exact hj)]
  have hrdB : ∀ j, j < n → M2.data.getD (Bw.toNat + 32 + j) 0 = rd.getD j 0 := by
    intro j hj
    rw [Nat.add_assoc, hcopy (32 + j) (by omega), hM1, ← Nat.add_assoc,
      (Mem.write_agree M Lw.toNat len.toBytes).2 _ (hrd j hj).1
        (by rw [B256.length_toBytes]; omega)]
    exact (hrd j hj).2
  have hv : Bytes.toB256 (M2.read Bw.toNat 32).1 = len := by
    have e : (M2.read Bw.toNat len.toBytes.length).1 = len.toBytes :=
      Mem.read_fst_of_getD M2 Bw.toNat (fun j hj => hlenB j (by rw [B256.length_toBytes] at hj; exact hj))
    rw [B256.length_toBytes] at e
    rw [e, B256.toB256_toBytes]
  rw [hv] at run
  set M3 := (M2.read Bw.toNat 32).2 with hM3
  -- memory agreement
  have hag1 : Mem.AgreeOutside M M1 Lw.toNat (Lw.toNat + 32) := by
    have h := Mem.write_agree M Lw.toNat len.toBytes
    rwa [B256.length_toBytes] at h
  have hagE : Mem.AgreeOutside M1 (M1'.extends [(Lw.toNat, nw.toNat), (Bw.toNat, nw.toNat)])
      Bw.toNat (Bw.toNat + 64) :=
    Mem.agreeOutside_of_data (μ := M1)
      (μ' := M1'.extends [(Lw.toNat, nw.toNat), (Bw.toNat, nw.toNat)]) rfl
      (le_trans (memExtSize_ge M1.size Lw.toNat 32) (memExtsSize_ge _ _)) _ _
  have hag2 : Mem.AgreeOutside M1 M2 Bw.toNat (Bw.toNat + 64) := by
    refine hagE.comp ((Mem.write_agree _ _ _).widen (le_refl _) ?_)
    rw [List.length_take, hnw', hinlen]; omega
  have hag3 : Mem.AgreeOutside M1 M3 Bw.toNat (Bw.toNat + 64) :=
    hag2.comp (Mem.agreeOutside_of_data (μ := M2) (μ' := M3) rfl
      (memExtSize_ge M2.size Bw.toNat 32) _ _)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G32, run⟩ | ⟨hz, G32, run⟩
  · -- `len > 0`: the tested tail
    have hpos : 1 ≤ n := by
      by_contra h0
      have hl0 : len = 0 := B256.toNat_inj _ _ (by rw [← hn]; show n = 0; omega)
      apply absurd hz
      rw [hl0]
      decide
    obtain ⟨hne, M', G', hd, hs, run⟩ := ric_vyRawCallCheck (M := M3) (rd := rd) hf3 hf4 hf5 hpos hn32 hnrd
      (fun j hj => hlenB j hj) (fun j hj => hrdB j hj) run
    refine ⟨.inr hne, b', input, M1, M', G', hpost, hag1,
      hag3.comp (Mem.agreeOutside_of_data hd hs _ _), run⟩
  · -- `len = 0`: straight to `K`
    have hl0 : n = 0 := by
      by_contra h0
      apply hz
      have hgt : len > Bytes.toB256 [0x00] := by
        rw [GT.gt, B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide]
        omega
      simp only [B256.gtCheck, hgt, ↓reduceIte]
      decide
    exact ⟨.inl hl0, b', input, M1, M3, G32, hpost, hag1, hag3, run⟩

theorem rawCallOk_of {rd : Bytes} {n : Nat} (hn : n = min rd.length 32)
    (h : n = 0 ∨ Bytes.toNat (rd.take n) ≠ 0) : RawCallOk rd := by
  rcases h with h | h
  · exact .inl (by omega)
  · exact .inr (hn ▸ h)

/-- The returned prefix the output window holds, byte by byte. -/
theorem rawCall_window {M M0 : Mem} {o : Nat} {rd : Bytes} (hM : M = M0.write o (rd.take 32))
    {n : Nat} (hn : n = min rd.length 32) :
    ∀ j, j < n → o + j < M.size ∧ M.data.getD (o + j) 0 = rd.getD j 0 := by
  intro j hj
  have hlen : (rd.take 32).length = n := by rw [List.length_take, hn, Nat.min_comm]
  have hne : rd.take 32 ≠ [] := by
    intro h; rw [h, List.length_nil] at hlen; omega
  obtain ⟨-, -, -, -, hfit, -⟩ := Mem.write_base M0 o hne
  rw [hlen] at hfit
  subst hM
  refine ⟨by omega, ?_⟩
  rw [Mem.write_getD_inside _ _ (by omega), List.getD_eq_getElem _ _ (by omega), List.getElem_take,
    ← List.getD_eq_getElem _ 0]

/-- **The `raw_call(…, max_outsize=32)` tail, inverted.**  From the state after the `CALL`
(flag on top; when it is set, the output window at `L + 32` holds the returned prefix, as
`MutableCallPost` states): the call succeeded and its returned data passes `RawCallOk`; the
continuation `K` (the tree at the tail's last `JUMPDEST`) runs over a base the identity copy
`ShaCallPost`-relates to `b`, with memory changed only in `[L, L + 32)` and then in
`[B, B + 64)`. -/
theorem ric_vyRawCallTail {p : VyRawSite} {k : Nat} {f1 f2 f3 f4 f5 K : SFunc} {flag : B256}
    (hid : IdReady sevm b) (hf1 : f1.noOk = true) (hf2 : f2.noOk = true)
    (hf3 : f3.noOk = true) (hf4 : f4.noOk = true) (hf5 : f5.noOk = true)
    (hk : fs[k]? = some (vyRawCallJoin p f2 f3 f4 f5 K)) (hkC : k ∉ C)
    (hrdlt : b.returnData.length < 2 ^ 256)
    (hM : flag ≠ 0 → ∃ M0 : Mem, M = M0.write ((Bytes.toB256 [p.lh, p.ll]).toNat + 32)
      (b.returnData.take 32))
    (run : SFunc.RunCut fs sevm C (St b (flag :: S) M G) (vyRawCallTail p k f1 f2 f3 f4 f5 K) r) :
    flag ≠ 0 ∧ RawCallOk b.returnData ∧
      ∃ b' rd' M1 M' G', ShaCallPost b b' rd' ∧
        Mem.AgreeOutside M M1 (Bytes.toB256 [p.lh, p.ll]).toNat
          ((Bytes.toB256 [p.lh, p.ll]).toNat + 32) ∧
        Mem.AgreeOutside M1 M' (Bytes.toB256 [p.bh, p.bl]).toNat
          ((Bytes.toB256 [p.bh, p.bl]).toNat + 64) ∧
        SFunc.RunCut fs sevm C (St b' S M' G') K r := by
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  set rd := b.returnData with hrd
  have hrds : (Nat.toB256 rd.length).toNat = rd.length := B256.toNat_toB256_of_lt hrdlt
  unfold vyRawCallTail at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G2, run⟩ | ⟨hflag, G2, run⟩
  · exact (run.false_of_noOk hf1).elim
  obtain ⟨M0, hM0⟩ := hM hflag
  obtain ⟨G3, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_returndatasize s1
  rw [← hrd] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (n := 0) (w := Nat.toB256 rd.length) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (n := 2) (w := Bytes.toB256 [0x20]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hz, G11, run⟩ | ⟨hz, G11, run⟩
  · -- short reply: `len = RETURNDATASIZE`, through the join entry
    have hlt : rd.length < 32 := by
      by_contra hge
      apply absurd hz
      have : ¬ (Bytes.toB256 [0x20] > Nat.toB256 rd.length) := by
        rw [GT.gt, B256.lt_iff_toNat_lt_toNat, hrds, h20]; omega
      simp only [B256.gtCheck, this, ↓reduceIte]
      decide
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_dup (n := 0) (w := Nat.toB256 rd.length) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1
    obtain ⟨G14, run⟩ := ric_jump hkC hk run
    have hn : (Nat.toB256 rd.length).toNat = min rd.length 32 := by rw [hrds]; omega
    obtain ⟨hok, rest⟩ := ric_vyRawCallJoin hid hf2 hf3 hf4 hf5 (by omega) (by omega)
      (rawCall_window hM0 hn) run
    exact ⟨hflag, rawCallOk_of hn hok, rest⟩
  · -- long reply: `len = 32`, falling into the inlined join
    have hge : 32 ≤ rd.length := by
      by_contra hlt
      apply hz
      have : Bytes.toB256 [0x20] > Nat.toB256 rd.length := by
        rw [GT.gt, B256.lt_iff_toNat_lt_toNat, hrds, h20]; omega
      simp only [B256.gtCheck, this, ↓reduceIte]
      decide
    obtain ⟨G12, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G13, rfl⟩ := ri_dup (n := 1) (w := Bytes.toB256 [0x20]) rfl s1
    have hn : (Bytes.toB256 [0x20]).toNat = min rd.length 32 := by rw [h20]; omega
    obtain ⟨hok, rest⟩ := ric_vyRawCallJoin hid hf2 hf3 hf4 hf5 (by omega) (by omega)
      (rawCall_window hM0 hn) run
    exact ⟨hflag, rawCallOk_of hn hok, rest⟩

/-- **A `raw_call(…, max_outsize=32)` site, inverted from its `CALL` node**: the step to the
call's successor `d` (its caller-visible post state `MutableCallPost`, the returned data bounded),
and — given the identity premises over `d` — `ric_vyRawCallTail`'s conclusions. -/
theorem ric_vyRawCall {p : VyRawSite} {k : Nat} {f1 f2 f3 f4 f5 K : SFunc}
    {g c v ii is oi os : B256} (hfork : CoveredFork sevm.benvStat.fork)
    (hf1 : f1.noOk = true) (hf2 : f2.noOk = true)
    (hf3 : f3.noOk = true) (hf4 : f4.noOk = true) (hf5 : f5.noOk = true)
    (hk : fs[k]? = some (vyRawCallJoin p f2 f3 f4 f5 K)) (hkC : k ∉ C)
    (hoi : oi.toNat = (Bytes.toB256 [p.lh, p.ll]).toNat + 32) (hos : os.toNat = 32)
    (run : SFunc.RunCut fs sevm C (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G)
      (.next (.exec .call) (vyRawCallTail p k f1 f2 f3 f4 f5 K)) r) :
    ∃ flag d, Ninst.Run sevm (St b (g :: c :: v :: ii :: is :: oi :: os :: S) M G) (.exec .call) d ∧
      MutableCallPost b d S M ii is oi os flag ∧ d.returnData.length < 2 ^ 256 ∧
      (IdReady sevm d → flag ≠ 0 ∧ RawCallOk d.returnData ∧
        ∃ b' rd' M1 M' G', ShaCallPost d b' rd' ∧
          Mem.AgreeOutside d.memory M1 (Bytes.toB256 [p.lh, p.ll]).toNat
            ((Bytes.toB256 [p.lh, p.ll]).toNat + 32) ∧
          Mem.AgreeOutside M1 M' (Bytes.toB256 [p.bh, p.bl]).toNat
            ((Bytes.toB256 [p.bh, p.bl]).toNat + 64) ∧
          SFunc.RunCut fs sevm C (St b' S M' G') K r) := by
  obtain ⟨d, s0, run⟩ := ric_next run
  obtain ⟨flag, hpost⟩ := ri_call_post hfork s0
  have hlt := ReturnDataBound.call_returnData_length_lt s0 hfork
  refine ⟨flag, d, s0, hpost, hlt, fun hid => ?_⟩
  rw [St.self (d := d) hpost.stack rfl] at run
  refine ric_vyRawCallTail hid hf1 hf2 hf3 hf4 hf5 hk hkC hlt (fun hflag => ?_) run
  obtain ⟨hmem, -⟩ := hpost.settled hflag
  exact ⟨_, by rw [hmem, hoi, hos]⟩

end Inv

/-! ## Forward -/

/-- The length checks and the exponent's byte count, for every length a `raw_call` result can
have. -/
theorem rawLen_facts : ∀ n, n ≤ 32 →
    B256.sgtCheck (Nat.toB256 n) (Bytes.toB256 [0x20]) = 0 ∧
      B256.sltCheck (Nat.toB256 n) (Bytes.toB256 [0x00]) = 0 ∧
      (Bytes.toB256 [0x20] - Nat.toB256 n).bytecount = (if n = 32 then 0 else 1) := by
  decide

/-- The tested tail's gas: 137 plus `EXP`'s charge on the exponent `32 - len`. -/
def rawCheckCost (n : Nat) : Nat := 137 + (10 + 50 * if n = 32 then 0 else 1)

/-- The memory the join leaves over a word-aligned memory covering both windows: `len` at `L`,
then the identity copy of `L[0 : 32 + len]` at `B`. -/
def vyRawMem (M : Mem) (L B n : Nat) : Mem :=
  (M.write L (Nat.toB256 n).toBytes).write B ((M.write L (Nat.toB256 n).toBytes).read L (n + 32)).1

/-- The join's gas: 98 for its own steps, the identity call, and the tested tail when
`len > 0`. -/
def rawJoinCost (n : Nat) : Nat :=
  98 + (100 + 0 + idCost (n + 32)) + (if n = 0 then 0 else rawCheckCost n)

/-- The whole tail's gas, by the reply's clamped length `n = min(RETURNDATASIZE, 32)`: the
short side jumps to the join entry (58), the long side falls in (48). -/
def rawTailCost (n : Nat) : Nat := (if n < 32 then 58 else 48) + rawJoinCost n

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg}

/-- **The tested tail, forward**: over a word-aligned memory covering `[B, B + 64)` that holds
`len` at `B` and the first `len` returned bytes at `B + 32`, a nonzero number in those bytes
passes the test. -/
theorem rxc_vyRawCallCheck {p : VyRawSite} {f3 f4 f5 K : SFunc} {n : Nat} {rd : Bytes}
    (hn1 : 1 ≤ n) (hn32 : n ≤ 32) (hnrd : n ≤ rd.length) (hok : Bytes.toNat (rd.take n) ≠ 0)
    (hlen : ∀ j, j < 32 →
      M.data.getD ((Bytes.toB256 [p.bh, p.bl]).toNat + j) 0 = (Nat.toB256 n).toBytes.getD j 0)
    (hrd : ∀ j, j < n →
      M.data.getD ((Bytes.toB256 [p.bh, p.bl]).toNat + 32 + j) 0 = rd.getD j 0)
    (h32 : M.size % 32 = 0) (hcov : (Bytes.toB256 [p.bh, p.bl]).toNat + 64 ≤ M.size)
    (hroom : S.length + 6 < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b S M G) K r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + rawCheckCost n)) (vyRawCallCheck p f3 f4 f5 K) r := by
  set Bw := Bytes.toB256 [p.bh, p.bl] with hBw
  set len := Nat.toB256 n with hlenw
  have hB : Bw.toNat < 2 ^ 16 := toNat_push2_lt p.bh p.bl
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have hnlen : len.toNat = n := B256.toNat_toB256_of_lt (by omega)
  obtain ⟨hsgt, hslt, hbc⟩ := rawLen_facts n hn32
  set ce := 10 + 50 * (if n = 32 then 0 else 1) with hce
  rw [show G + rawCheckCost n = G + ce + 137 by rw [rawCheckCost]; omega]
  have h32B : (Bytes.toB256 [0x20] + Bw).toNat = Bw.toNat + 32 := by
    rw [B256.toNat_add, h20, Nat.lo_eq_of_lt (by omega)]; omega
  set w := Bytes.toB256 (M.read (Bw.toNat + 32) 32).1 with hw
  have hv : Bytes.toB256 (M.read Bw.toNat 32).1 = len := by
    have e : (M.read Bw.toNat len.toBytes.length).1 = len.toBytes :=
      Mem.read_fst_of_getD M Bw.toNat (fun j hj => hlen j (by rw [B256.length_toBytes] at hj; exact hj))
    rw [B256.length_toBytes] at e
    rw [e, B256.toB256_toBytes]
  set e := B256.bexp (Bytes.toB256 [0x01, 0x00]) (Bytes.toB256 [0x20] - len) with he
  have hq : (w / e).toNat = Bytes.toNat (rd.take n) := by
    have hxs : (M.read (Bw.toNat + 32) 32).1.length = 32 := by
      simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
    have htake : (M.read (Bw.toNat + 32) 32).1.take n = rd.take n := by
      apply List.ext_getElem
      · rw [List.length_take, List.length_take, hxs]; omega
      · intro j h1 h2
        rw [List.length_take] at h1
        have e1 := Mem.read_fst_getD M (Bw.toNat + 32) 32 (j := j) (by omega)
        rw [List.getElem_take, List.getElem_take, ← List.getD_eq_getElem _ 0,
          ← List.getD_eq_getElem _ 0, e1, hrd j (by omega)]
    rw [← htake, ← hnlen]
    exact rawCheck_quot (by omega) (by omega) hxs hw
  have hq0 : w / e ≠ 0 := by
    intro h0; apply hok; rw [← hq, h0]; rfl
  have hmB : (M.read Bw.toNat 32).2 = M := Mem.read_snd_eq_self (memExtSize_of_le h32 (by omega))
  have hmB2 : (M.read (Bw.toNat + 32) 32).2 = M :=
    Mem.read_snd_eq_self (memExtSize_of_le h32 (by omega))
  unfold vyRawCallCheck
  refine rxc_push (G := G + ce + 134) rfl (by omega) ?_
  refine rxc_dup (G := G + ce + 131) (n := 0) (w := Bw) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + ce + 128) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_add (G := G + ce + 125) (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_mload (G := G + ce + 122) (c := 3) (v := w) ?_ (by rw [h32B]) (by rw [h32B]; exact hmB2) (by (try simp only [List.length_cons]); omega) ?_
  · rw [St, Devm.extCost_zero_of_le h32 (by rw [h32B]; omega)]; rfl
  refine rxc_push (G := G + ce + 119) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_dup (G := G + ce + 116) (n := 2) (w := Bw) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_mload (G := G + ce + 113) (c := 3) (v := len) ?_ hv hmB (by (try simp only [List.length_cons]); omega) ?_
  · rw [St, Devm.extCost_zero_of_le h32 (by omega)]; rfl
  refine rxc_dup (G := G + ce + 110) (n := 0) (w := len) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + ce + 107) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_swap (G := G + ce + 104) (n := 0)
    (S' := len :: Bytes.toB256 [0x20] :: len :: Bytes.toB256 [0x00] :: w :: Bw :: S) rfl ?_
  refine rxc_binary (G := G + ce + 101) (fn := B256.sgtCheck) (c := gVerylow) (v := 0)
    (by rintro ⟨⟩) (fun _ => rfl) hsgt (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_iszero (G := G + ce + 98) (v := 1) (by decide) (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + ce + 95) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_branch_succ (G := G + ce + 85) (by decide) (rxc_dest ?_)
  refine rxc_dup (G := G + ce + 81) (n := 0) (w := len) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_swap (G := G + ce + 78) (n := 1)
    (S' := Bytes.toB256 [0x00] :: len :: len :: w :: Bw :: S) rfl ?_
  refine rxc_swap (G := G + ce + 75) (n := 0)
    (S' := len :: Bytes.toB256 [0x00] :: len :: w :: Bw :: S) rfl ?_
  refine rxc_binary (G := G + ce + 72) (fn := B256.sltCheck) (c := gVerylow) (v := 0)
    (by rintro ⟨⟩) (fun _ => rfl) hslt (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_iszero (G := G + ce + 69) (v := 1) (by decide) (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + ce + 66) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_branch_succ (G := G + ce + 56) (by decide) (rxc_dest ?_)
  refine rxc_dup (G := G + ce + 52) (n := 0) (w := len) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + ce + 49) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_sub' (G := G + ce + 46) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + ce + 43) rfl (by (try simp only [List.length_cons]); omega) ?_
  rw [show G + ce + 43 = G + 43 + ce by omega]
  refine rxc_exp' (G := G + 43) (c := ce) ?_ (by (try simp only [List.length_cons]); omega) ?_
  · show gExp + gExpbyte * (Bytes.toB256 [0x20] - Nat.toB256 n).bytecount = ce
    rw [hbc]; rfl
  refine rxc_dup (G := G + 40) (n := 2) (w := w) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_div (G := G + 35) (v := w / e) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_swap (G := G + 32) (n := 0) (S' := len :: (w / e) :: w :: Bw :: S) rfl ?_
  refine rxc_pop (G := G + 30) ?_
  refine rxc_swap (G := G + 27) (n := 0) (S' := w :: (w / e) :: Bw :: S) rfl ?_
  refine rxc_pop (G := G + 25) ?_
  refine rxc_swap (G := G + 22) (n := 0) (S' := Bw :: (w / e) :: S) rfl ?_
  refine rxc_pop (G := G + 20) ?_
  refine rxc_iszero (G := G + 17) (v := 0) (by simp only [B256.eqCheck, hq0, ↓reduceIte]) (by omega) ?_
  refine rxc_iszero (G := G + 14) (v := 1) (by decide) (by omega) ?_
  refine rxc_push (G := G + 11) rfl (by (try simp only [List.length_cons]); omega) ?_
  exact rxc_branch_succ (G := G + 1) (by decide) (rxc_dest k)

/-- **The join, forward**: over a word-aligned memory covering `[L, L + 64)` and
`[B, B + 64)` with the first `len` returned bytes at `L + 32`, and a `raw_call` result that
passes (`len = 0`, or a nonzero number), the join runs to `K` over the identity copy's base,
with the memory `vyRawMem`. -/
theorem rxc_vyRawCallJoin {p : VyRawSite} {f2 f3 f4 f5 K : SFunc} {n : Nat} {rd : Bytes}
    {rds c : B256} (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0)
    (hn32 : n ≤ 32) (hnrd : n ≤ rd.length) (hok : n = 0 ∨ Bytes.toNat (rd.take n) ≠ 0)
    (hrd : ∀ j, j < n →
      M.data.getD ((Bytes.toB256 [p.lh, p.ll]).toNat + 32 + j) 0 = rd.getD j 0)
    (h32 : M.size % 32 = 0) (hcovL : (Bytes.toB256 [p.lh, p.ll]).toNat + 64 ≤ M.size)
    (hcovB : (Bytes.toB256 [p.bh, p.bl]).toNat + 64 ≤ M.size)
    (hG : 1444 ≤ G) (hbound : G + 1000 < 2 ^ 256) (hroom : S.length + 10 < 1024)
    (k : ∀ b' rd', ShaCallPost b b' rd' → SFunc.RunExactCut fs sevm C
      (St b' S (vyRawMem M (Bytes.toB256 [p.lh, p.ll]).toNat (Bytes.toB256 [p.bh, p.bl]).toNat n)
        G) K r) :
    SFunc.RunExactCut fs sevm C (St b (Nat.toB256 n :: rds :: c :: S) M (G + rawJoinCost n))
      (vyRawCallJoin p f2 f3 f4 f5 K) r := by
  set Lw := Bytes.toB256 [p.lh, p.ll] with hLw
  set Bw := Bytes.toB256 [p.bh, p.bl] with hBw
  set len := Nat.toB256 n with hlenw
  have hL : Lw.toNat < 2 ^ 16 := toNat_push2_lt p.lh p.ll
  have hB : Bw.toNat < 2 ^ 16 := toNat_push2_lt p.bh p.bl
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  have hnlen : len.toNat = n := B256.toNat_toB256_of_lt (by omega)
  set nw := Bytes.toB256 [0x20] + len with hnw
  have hnw' : nw.toNat = n + 32 := by
    rw [hnw, B256.toNat_add, h20, hnlen, Nat.lo_eq_of_lt (by omega)]; omega
  set X := if n = 0 then 0 else rawCheckCost n with hX
  set ic := 100 + 0 + idCost nw.toNat with hic
  rw [show G + rawJoinCost n = G + X + ic + 98 by rw [rawJoinCost, hic, hnw']; omega]
  set M1 := M.write Lw.toNat len.toBytes with hM1
  have hs1 : M1.size = M.size := by
    rw [hM1, Mem.size_write_word_at, ite_eq_left (by omega)]
  set input := (M1.read Lw.toNat nw.toNat).1 with hinput
  have hinlen : input.length = n + 32 := by
    rw [hinput, ← hnw']
    simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  set M2 := M1.write Bw.toNat input with hM2
  have hs2 : M2.size = M.size := by
    rw [hM2, Mem.size_write_of_le (by rw [hinlen, hs1]; omega), hs1]
  have hmem2 : M2 = vyRawMem M Lw.toNat Bw.toNat n := by
    rw [hM2, hinput, hnw', hM1, hlenw]; rfl
  have hcopy : ∀ j, j < n + 32 →
      M2.data.getD (Bw.toNat + j) 0 = M1.data.getD (Lw.toNat + j) 0 := by
    intro j hj
    rw [hM2, Mem.write_getD_inside _ _ (by rw [hinlen]; omega),
      List.getD_eq_getElem _ _ (by rw [hinlen]; omega), ← List.getD_eq_getElem _ 0, hinput,
      Mem.read_fst_getD _ _ _ (by rw [hnw']; exact hj)]
  have hlenB : ∀ j, j < 32 → M2.data.getD (Bw.toNat + j) 0 = len.toBytes.getD j 0 := by
    intro j hj
    rw [hcopy j (by omega), hM1, Mem.write_getD_inside _ _ (by rw [B256.length_toBytes]; exact hj)]
  have hrdB : ∀ j, j < n → M2.data.getD (Bw.toNat + 32 + j) 0 = rd.getD j 0 := by
    intro j hj
    rw [Nat.add_assoc, hcopy (32 + j) (by omega), hM1, ← Nat.add_assoc,
      (Mem.write_agree M Lw.toNat len.toBytes).2 _ (by omega)
        (by rw [B256.length_toBytes]; omega)]
    exact hrd j hj
  have hv : Bytes.toB256 (M2.read Bw.toNat 32).1 = len := by
    have e : (M2.read Bw.toNat len.toBytes.length).1 = len.toBytes :=
      Mem.read_fst_of_getD M2 Bw.toNat (fun j hj => hlenB j (by rw [B256.length_toBytes] at hj; exact hj))
    rw [B256.length_toBytes] at e
    rw [e, B256.toB256_toBytes]
  have hcovI : memExtsSize M1.size [(Lw.toNat, nw.toNat), (Bw.toNat, nw.toNat)] = M1.size := by
    simp only [memExtsSize]
    rw [hs1, memExtSize_of_le h32 (by rw [hnw']; omega), memExtSize_of_le h32 (by rw [hnw']; omega)]
  have hXle : X ≤ 197 := by
    rw [hX]; split_ifs
    · omega
    · rw [rawCheckCost]; split_ifs <;> omega
  have hidc : idCost nw.toNat ≤ 21 := by
    rw [hnw', idCost]
    have : ceilDiv (n + 32) 32 ≤ 2 := by unfold ceilDiv; split_ifs <;> omega
    omega
  unfold vyRawCallJoin
  refine rxc_dest (G := G + X + ic + 97) ?_
  refine rxc_swap (G := G + X + ic + 94) (n := 0) (S' := rds :: len :: c :: S) rfl ?_
  refine rxc_pop (G := G + X + ic + 92) ?_
  refine rxc_swap (G := G + X + ic + 89) (n := 0) (S' := c :: len :: S) rfl ?_
  refine rxc_pop (G := G + X + ic + 87) ?_
  refine rxc_push (G := G + X + ic + 84) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_mstore (G := G + X + ic + 81) (c := 3) (M' := M1) ?_ rfl ?_
  · rw [St, Devm.extCost_zero_of_le h32 (by rw [← hLw]; omega)]; rfl
  refine rxc_push (G := G + X + ic + 78) rfl (by omega) ?_
  refine rxc_dup (G := G + X + ic + 75) (n := 0) (w := Lw) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_mload (G := G + X + ic + 72) (c := 3) (v := len) ?_
    (by rw [hM1, Mem.read_write_word_self, B256.toB256_toBytes])
    (Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs1]; exact h32) (by rw [hs1]; omega))) (by (try simp only [List.length_cons]); omega) ?_
  · rw [St, Devm.extCost_zero_of_le (by rw [hs1]; exact h32) (by rw [hs1]; omega)]; rfl
  refine rxc_push (G := G + X + ic + 69) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_add (G := G + X + ic + 66) (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_dup (G := G + X + ic + 63) (n := 0) (w := nw) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + X + ic + 60) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_dup (G := G + X + ic + 57) (n := 2) (w := nw) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_dup (G := G + X + ic + 54) (n := 4) (w := Lw) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + X + ic + 51) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_push (G := G + X + ic + 48) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_gas (G := G + X + ic + 46) (by (try simp only [List.length_cons]); omega) ?_
  rw [show Bytes.toB256 [0x04] = 4 by decide, show Bytes.toB256 [0x00] = 0 by decide]
  refine rxc_call_identity (G := G + X + ic + 46) hid hdepth rfl
    (Devm.extCost_covered hcovI) (by omega) (by omega) (by (try simp only [List.length_cons]); omega) ?_
  intro b' hpost
  rw [show G + X + ic + 46 - (100 + 0 + idCost nw.toNat) = G + X + 46 by omega,
    Mem.extends_covered hcovI, ← hinput, List.take_of_length_le (by rw [hinlen, hnw']), ← hM2]
  have hmB : (M2.read Bw.toNat 32).2 = M2 :=
    Mem.read_snd_eq_self (memExtSize_of_le (by rw [hs2]; exact h32) (by rw [hs2]; omega))
  refine rxc_push (G := G + X + 43) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_branch_succ (G := G + X + 33) (by decide) (rxc_dest ?_)
  refine rxc_pop (G := G + X + 30) ?_
  refine rxc_pop (G := G + X + 28) ?_
  refine rxc_push (G := G + X + 25) rfl (by omega) ?_
  refine rxc_push (G := G + X + 22) rfl (by (try simp only [List.length_cons]); omega) ?_
  refine rxc_mload (G := G + X + 19) (c := 3) (v := len) ?_ hv hmB (by (try simp only [List.length_cons]); omega) ?_
  · rw [St, Devm.extCost_zero_of_le (by rw [hs2]; exact h32) (by rw [hs2, ← hBw]; omega)]; rfl
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · -- `len = 0`: straight to `K`
    have hX0 : X = 0 := by rw [hX, ite_eq_left h0]
    have hl0 : len = 0 := by rw [hlenw, h0]; rfl
    refine rxc_binary (G := G + X + 16) (fn := B256.gtCheck) (c := gVerylow) (v := 0)
      (by rintro ⟨⟩) (fun _ => rfl) (by rw [hl0]; decide) (by omega) ?_
    refine rxc_iszero (G := G + X + 13) (v := 1) (by decide) (by omega) ?_
    refine rxc_push (G := G + X + 10) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_branch_succ (G := G + X) (by decide) ?_
    rw [hX0, Nat.add_zero, hmem2]
    exact k b' _ hpost
  · -- `len > 0`: the tested tail
    have hX1 : X = rawCheckCost n := by rw [hX, ite_eq_right (by omega)]
    have hgt : len > Bytes.toB256 [0x00] := by
      rw [GT.gt, B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x00]).toNat = 0 by decide, hnlen]
      exact hpos
    refine rxc_binary (G := G + X + 16) (fn := B256.gtCheck) (c := gVerylow) (v := 1)
      (by rintro ⟨⟩) (fun _ => rfl) (by simp only [B256.gtCheck, hgt, ↓reduceIte]) (by omega) ?_
    refine rxc_iszero (G := G + X + 13) (v := 0) (by decide) (by omega) ?_
    refine rxc_push (G := G + X + 10) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_branch_zero (G := G + X) ?_
    rw [hX1]
    refine rxc_vyRawCallCheck hpos hn32 hnrd (hok.resolve_left (by omega)) hlenB hrdB
      (by rw [hs2]; exact h32) (by rw [hs2]; exact hcovB) (by omega) ?_
    rw [hmem2]
    exact k b' _ hpost

/-- **The `raw_call(…, max_outsize=32)` tail, forward**: after a successful `CALL` whose returned
data passes `RawCallOk` and whose returned prefix sits at `L + 32`, over a word-aligned memory
covering `[L, L + 64)` and `[B, B + 64)`, the tail runs to `K` over the identity copy's base, at
gas `rawTailCost (min len 32)`. -/
theorem rxc_vyRawCallTail {p : VyRawSite} {k : Nat} {f1 f2 f3 f4 f5 K : SFunc} {flag : B256}
    (hid : IdReady sevm b) (hdepth : sevm.depth ≠ 0) (hflag : flag ≠ 0)
    (hk : fs[k]? = some (vyRawCallJoin p f2 f3 f4 f5 K)) (hkC : k ∉ C)
    (hrdlt : b.returnData.length < 2 ^ 256) (hok : RawCallOk b.returnData)
    (hrd : ∀ j, j < min b.returnData.length 32 →
      M.data.getD ((Bytes.toB256 [p.lh, p.ll]).toNat + 32 + j) 0 = b.returnData.getD j 0)
    (h32 : M.size % 32 = 0) (hcovL : (Bytes.toB256 [p.lh, p.ll]).toNat + 64 ≤ M.size)
    (hcovB : (Bytes.toB256 [p.bh, p.bl]).toNat + 64 ≤ M.size)
    (hG : 1444 ≤ G) (hbound : G + 1000 < 2 ^ 256) (hroom : S.length + 10 < 1024)
    (kk : ∀ b' rd', ShaCallPost b b' rd' → SFunc.RunExactCut fs sevm C
      (St b' S (vyRawMem M (Bytes.toB256 [p.lh, p.ll]).toNat (Bytes.toB256 [p.bh, p.bl]).toNat
        (min b.returnData.length 32)) G) K r) :
    SFunc.RunExactCut fs sevm C (St b (flag :: S) M (G + rawTailCost (min b.returnData.length 32)))
      (vyRawCallTail p k f1 f2 f3 f4 f5 K) r := by
  have h20 : (Bytes.toB256 [0x20]).toNat = 32 := by decide
  set rd := b.returnData with hrdd
  set n := min rd.length 32 with hn
  have hrds : (Nat.toB256 rd.length).toNat = rd.length := B256.toNat_toB256_of_lt hrdlt
  have hok' : n = 0 ∨ Bytes.toNat (rd.take n) ≠ 0 := by
    rcases hok with h | h
    · exact .inl (by omega)
    · exact .inr h
  set J := rawJoinCost n with hJ
  unfold vyRawCallTail
  by_cases hshort : rd.length < 32
  · rw [show G + rawTailCost n = G + J + 58 by rw [rawTailCost, ite_eq_left (by omega)]; omega]
    have hnl : n = rd.length := by omega
    have hgt : Bytes.toB256 [0x20] > Nat.toB256 rd.length := by
      rw [GT.gt, B256.lt_iff_toNat_lt_toNat, hrds, h20]; exact hshort
    refine rxc_push (G := G + J + 55) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_branch_succ (G := G + J + 45) hflag (rxc_dest ?_)
    refine rxc_push (G := G + J + 41) rfl (by omega) ?_
    refine rxc_returndatasize (G := G + J + 39) (by (try simp only [List.length_cons]); omega) ?_
    rw [← hrdd]
    refine rxc_dup (G := G + J + 36) (n := 0) (w := Nat.toB256 rd.length) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_dup (G := G + J + 33) (n := 2) (w := Bytes.toB256 [0x20]) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_binary (G := G + J + 30) (fn := B256.gtCheck) (c := gVerylow) (v := 1)
      (by rintro ⟨⟩) (fun _ => rfl) (by simp only [B256.gtCheck, hgt, ↓reduceIte]) (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_iszero (G := G + J + 27) (v := 0) (by decide) (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_push (G := G + J + 24) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_branch_zero (G := G + J + 14) ?_
    refine rxc_dup (G := G + J + 11) (n := 0) (w := Nat.toB256 rd.length) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_push (G := G + J + 8) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_jump (G := G + J) hk hkC ?_
    rw [← hnl]
    exact rxc_vyRawCallJoin hid hdepth (by omega) (by omega) hok' hrd h32 hcovL hcovB hG hbound
      (by omega) kk
  · rw [show G + rawTailCost n = G + J + 48 by rw [rawTailCost, ite_eq_right (by omega)]; omega]
    have hn32 : n = 32 := by omega
    have hgt : ¬ Bytes.toB256 [0x20] > Nat.toB256 rd.length := by
      rw [GT.gt, B256.lt_iff_toNat_lt_toNat, hrds, h20]; omega
    refine rxc_push (G := G + J + 45) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_branch_succ (G := G + J + 35) hflag (rxc_dest ?_)
    refine rxc_push (G := G + J + 31) rfl (by omega) ?_
    refine rxc_returndatasize (G := G + J + 29) (by (try simp only [List.length_cons]); omega) ?_
    rw [← hrdd]
    refine rxc_dup (G := G + J + 26) (n := 0) (w := Nat.toB256 rd.length) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_dup (G := G + J + 23) (n := 2) (w := Bytes.toB256 [0x20]) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_binary (G := G + J + 20) (fn := B256.gtCheck) (c := gVerylow) (v := 0)
      (by rintro ⟨⟩) (fun _ => rfl) (by simp only [B256.gtCheck, hgt, ↓reduceIte]) (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_iszero (G := G + J + 17) (v := 1) (by decide) (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_push (G := G + J + 14) rfl (by (try simp only [List.length_cons]); omega) ?_
    refine rxc_branch_succ (G := G + J + 4) (by decide) (rxc_dest ?_)
    refine rxc_dup (G := G + J) (n := 1) (w := Bytes.toB256 [0x20]) rfl (by (try simp only [List.length_cons]); omega) ?_
    rw [show Bytes.toB256 [0x20] = Nat.toB256 n by rw [hn32]; decide]
    exact rxc_vyRawCallJoin hid hdepth (by omega) (by omega) hok' hrd h32 hcovL hcovB hG hbound
      (by omega) kk

end Fwd

end Blanc.Lift
