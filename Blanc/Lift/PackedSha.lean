import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.CopyLoop

/-!
# `sha256(abi.encodePacked(a, b))` of two words, as solc 0.6 compiles it

solc 0.6 compiles `sha256(abi.encodePacked(a, b))` for two `bytes32` words into a fixed
shape, which this module lifts once:

* **pack** (`pack2Tree`): `a` and `b` stored at `fp + 0x20` and `fp + 0x40`, the length
  `0x40` at `fp`, the free pointer bumped to `fp' = fp + 0x60`, and the operands of a copy of
  the 64 packed bytes from `fp + 0x20` to `fp'`;
* **copy** (`mcpyTree`): the older solc word-copy loop, which counts the remaining length down
  by 32 (`while (len >= 32) { mstore(dst, mload(src)); … }`), here two passes;
* **merge** (`mergeTree`): the partial last word `(src & ~mask) | (dst & mask)`, with nothing
  left over (the mask is all ones, so the destination word is stored back unchanged — but the
  `MLOAD` of it extends memory by a word);
* **call** (`shaCallTree`): `STATICCALL` of the precompile at address 2 over the 64 bytes at
  `fp'`, output over its first word, the success test, the `RETURNDATASIZE ≥ 32` test.

`packed_sha_pair` is the gas-exact cut run of all four from the two words on the stack to the
call's continuation, with the hash `sha256 (a ‖ b)` at `fp'` and the free pointer at `fp'`.
The trees take the code's own push immediates and entry indices as parameters.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The shapes -/

/-- The all-ones word `2^256 - 32` solc pushes to count down by a word. -/
def minus32Push : Bytes :=
  [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xe0]

/-- The all-ones word. -/
def onesPush : Bytes := List.replicate 32 0xff

/-- The copy body, ending in the back-edge `JUMP` to entry `k`. -/
def mcpyBody (r0 r1 : UInt8) (k : Nat) : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg .mload) (.next (.reg (.dup 2)) (.next (.reg .mstore)
    (.next (.push minus32Push (by decide)) (.next (.reg (.swap 0)) (.next (.reg (.swap 2))
      (.next (.reg .add) (.next (.reg (.swap 1)) (.next (.push [0x20] (by decide))
        (.next (.reg (.swap 1)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.swap 1))
          (.next (.reg .add) (.next (.push [r0, r1] (by simp)) (.jump k))))))))))))))))

/-- The copy loop head: the `len < 32` test, the body on failure, `exit` otherwise. -/
def mcpyTree (e0 e1 r0 r1 : UInt8) (k : Nat) (exit : SFunc) : SFunc :=
  .dest (.next (.push [0x20] (by decide)) (.next (.reg (.dup 3)) (.next (.reg .lt)
    (.next (.push [e0, e1] (by simp)) (.branch (mcpyBody r0 r1 k) exit)))))

/-- The partial-word merge at the copy's end, then `K`. -/
def mergeTree (K : SFunc) : SFunc :=
  .dest (.next (.reg .mload) (.next (.reg (.dup 1)) (.next (.reg .mload)
    (.next (.push [0x20] (by decide)) (.next (.reg (.swap 3)) (.next (.reg (.dup 4))
      (.next (.reg .sub) (.next (.push [0x01, 0x00] (by decide)) (.next (.reg .exp)
        (.next (.push onesPush (by decide)) (.next (.reg .add) (.next (.reg (.dup 0))
          (.next (.reg .not) (.next (.reg (.swap 0)) (.next (.reg (.swap 2)) (.next (.reg .and)
            (.next (.reg (.swap 1)) (.next (.reg .and) (.next (.reg .or) (.next (.reg (.swap 0))
              (.next (.reg .mstore) K)))))))))))))))))))))

/-- The precompile call over the packed bytes and its two checks; `T` continues. -/
def shaCallTree (c0 c1 v0 v1 : UInt8) (fail1 fail2 T : SFunc) : SFunc :=
  .next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg (.swap 1))
    (.next (.reg (.swap 0)) (.next (.reg (.swap 3)) (.next (.reg .add) (.next (.reg (.swap 4))
      (.next (.reg .pop) (.next (.reg (.swap 1)) (.next (.reg (.swap 2)) (.next (.reg .pop)
        (.next (.reg .pop) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .sub)
          (.next (.reg (.dup 1)) (.next (.reg (.dup 5)) (.next (.reg .gas)
            (.next (.exec .staticcall) (.next (.reg .iszero) (.next (.reg (.dup 0))
              (.next (.reg .iszero) (.next (.push [c0, c1] (by simp)) (.branch fail1
    (.dest (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop)
      (.next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.reg .returndatasize)
        (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt)
          (.next (.reg .iszero) (.next (.push [v0, v1] (by simp))
            (.branch fail2 T))))))))))))))))))))))))))))))))))))

/-- The packing of the two words on the stack, ending in the copy's operands and `X`. -/
def pack2Tree (X : SFunc) : SFunc :=
  .next (.push [0x40] (by decide)) (.next (.reg .mload) (.next (.push [0x20] (by decide))
    (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg (.dup 1))
      (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add)
        (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .mstore)
          (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg (.swap 2))
            (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop)
              (.next (.push [0x40] (by decide)) (.next (.reg .mload)
                (.next (.push [0x20] (by decide)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3))
                  (.next (.reg .sub) (.next (.reg .sub) (.next (.reg (.dup 1))
                    (.next (.reg .mstore) (.next (.reg (.swap 0))
                      (.next (.push [0x40] (by decide)) (.next (.reg .mstore)
                        (.next (.push [0x40] (by decide)) (.next (.reg .mload)
                          (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg (.dup 0))
                            (.next (.reg .mload) (.next (.reg (.swap 0))
                              (.next (.push [0x20] (by decide)) (.next (.reg .add)
                                (.next (.reg (.swap 0)) (.next (.reg (.dup 0))
                                  (.next (.reg (.dup 3)) (.next (.reg (.dup 3))
                                    X)))))))))))))))))))))))))))))))))))))))))))

/-! ## Words, charges and images -/

/-- The 32 bytes of `sha256 (a ‖ b)`. -/
abbrev hashPairBytes (a b : B256) : Bytes := (Bytes.sha256 (a.toBytes ++ b.toBytes)).toBytes

theorem word_of_toNat {x : B256} {n : Nat} (h : x.toNat = n) (hn : n < 2 ^ 256) :
    x = Nat.toB256 n := by
  apply B256.toNat_inj; rw [h, B256.toNat_toB256_of_lt hn]

theorem toNat_toB256' {n : Nat} (hn : n < 2 ^ 256) : (Nat.toB256 n).toNat = n :=
  B256.toNat_toB256_of_lt hn

theorem minus32_eq : Bytes.toB256 minus32Push = Nat.toB256 (2 ^ 256 - 32) := by decide

theorem add_minus32 {l : Nat} (h1 : 32 ≤ l) (h2 : l < 2 ^ 256) :
    Nat.toB256 l + Bytes.toB256 minus32Push = Nat.toB256 (l - 32) := by
  rw [minus32_eq]
  apply word_of_toNat _ (by omega)
  rw [B256.toNat_add, toNat_toB256' h2, toNat_toB256' (by omega), Nat.lo]
  omega

theorem push20_add {a : Nat} (h : a + 32 < 2 ^ 256) :
    Bytes.toB256 [0x20] + Nat.toB256 a = Nat.toB256 (a + 32) := by
  rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, toB256_add_toB256 (by omega),
    Nat.add_comm]

theorem add_push20 {a : Nat} (h : a + 32 < 2 ^ 256) :
    Nat.toB256 a + Bytes.toB256 [0x20] = Nat.toB256 (a + 32) := by
  rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, toB256_add_toB256 (by omega)]

theorem lt_toB256 {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    B256.ltCheck (Nat.toB256 a) (Nat.toB256 b) = if a < b then 1 else 0 := by
  have e : Nat.toB256 a < Nat.toB256 b ↔ a < b := by
    rw [B256.lt_iff_toNat_lt_toNat, toNat_toB256' ha, toNat_toB256' hb]
  rw [B256.ltCheck]
  by_cases h : a < b <;> simp [h, e]

/-- A word access inside an aligned memory costs nothing beyond the base 3. -/
theorem charge_covered {b : Devm} {S : List B256} {M : Mem} {G n i : Nat} (hs : M.size = n)
    (hn : n % 32 = 0) (hi : i + 32 ≤ n) :
    gVerylow + (St b S M G).extCost [⟨i, 32⟩] = 3 := by
  rw [St.extCost_eq hs, memExtSize_of_le hn hi, Nat.sub_self]; rfl

/-- A word access at an aligned offset: 3 and the expansion to the window's end. -/
theorem charge_word {b : Devm} {S : List B256} {M : Mem} {G n i : Nat} (hs : M.size = n)
    (hn : n % 32 = 0) (hi : i % 32 = 0) :
    gVerylow + (St b S M G).extCost [⟨i, 32⟩] =
      3 + (calculateMemoryGasCost (max n (i + 32)) - calculateMemoryGasCost n) := by
  rw [St.extCost_eq hs, memExtSize_word_aligned hn hi]; rfl

theorem read_covered {M : Mem} {n i : Nat} (hs : M.size = n) (hn : n % 32 = 0)
    (hi : i + 32 ≤ n) : (M.read i 32).2 = M :=
  Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le hn hi)

theorem read_ext_size {M : Mem} {n i : Nat} (hs : M.size = n) (hn : n % 32 = 0)
    (hi : i % 32 = 0) : (M.read i 32).2.size = max n (i + 32) := by
  show memExtSize M.size i 32 = _
  rw [hs, memExtSize_word_aligned hn hi]

theorem read_word {M : Mem} {img : Bytes} (hr : Mem.Reads M img) (i : Nat) {w : B256}
    (h : img.sliceD i 32 0 = w.toBytes) : Bytes.toB256 (M.read i 32).1 = w := by
  rw [hr.read, h, B256.toB256_toBytes]

theorem toBytes_read (M : Mem) (i : Nat) :
    (Bytes.toB256 (M.read i 32).1).toBytes = (M.read i 32).1 :=
  Bytes.toBytes_toB256_of_length (by
    show (Array.sliceD _ _ _ _).length = 32; rw [Array.sliceD_eq_map]; simp)

/-- Writing an image's own window back changes no byte of it. -/
theorem Bytes.getD_writeAt_self (bs : Bytes) (n k i : Nat) :
    (Bytes.writeAt bs n (bs.sliceD n k 0)).getD i 0 = bs.getD i 0 := by
  rw [Bytes.getD_writeAt, List.length_sliceD]
  split_ifs with h
  · rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega)]; congr 1; omega
  · rfl

theorem Mem.Reads.write_self {μ : Mem} {bs : Bytes} (hwf : Mem.Wf μ) (h : Mem.Reads μ bs)
    (n : Nat) : Mem.Reads (μ.write n (bs.sliceD n 32 0)) bs := by
  intro i
  rw [h.write hwf n _ i, Bytes.getD_writeAt_self]

/-! ### Bitwise facts of the merge with nothing left over -/

theorem ones_eq : Bytes.toB256 onesPush = B256.max := by decide

theorem bexp_256_32 : B256.bexp (Bytes.toB256 [0x01, 0x00]) (Nat.toB256 32) = 0 := by
  decide +kernel

theorem ones_add_zero : Bytes.toB256 (255 :: List.replicate 31 255) + 0 = B256.max := by
  decide +kernel

theorem b256_and_zero (x : B256) : (x &&& 0) = 0 := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.and_zero

theorem b256_or_zero (x : B256) : (x ||| 0) = x := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.or_zero

theorem b256_max_and (x : B256) : (B256.max &&& x) = x := by
  rcases x with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  have h : ∀ u : UInt64, (0xffffffffffffffff : UInt64) &&& u = u := fun u => by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, show (0xffffffffffffffff : UInt64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (UInt64.toNat_lt u)]
  apply Prod.ext <;> apply Prod.ext <;> exact h _

/-! ## The copy loop -/

section Copy

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 : UInt8} {k : Nat} {X T : SFunc}

/-- **One copy pass** (`len ≥ 32`) from the head through the back-edge goto into entry `k`:
79 gas and the destination word's expansion. -/
theorem mcpy_iter {s d l n n' : Nat} (hl : 32 ≤ l) (hl' : l < 2 ^ 256) (hs : M.size = n)
    (hn' : max n (d + 32) = n')
    (hn : n % 32 = 0) (hsrc : s + 32 ≤ n) (hd : d % 32 = 0) (hsl : s + 64 < 2 ^ 256)
    (hdl : d + 64 < 2 ^ 256) (hR : R.length < 1000)
    (hk : fs[k]? = some T) (hkC : k ∉ C)
    (kont : SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 (s + 32) :: Nat.toB256 (d + 32) :: Nat.toB256 (l - 32) :: R)
        (M.write d (M.read s 32).1) G) T r) :
    SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M
        (G + (76 + (3 + (calculateMemoryGasCost n' - calculateMemoryGasCost n)))))
      (mcpyTree e0 e1 r0 r1 k X) r := by
  subst hn'
  rw [show G + (76 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)))
    = G + 44 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)) + 32
    by omega]
  unfold mcpyTree mcpyBody
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_lt (v := 0) ?_ (by simp; omega) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 hl' (by norm_num)]
    simp [show ¬ l < 32 by omega]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_zero ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Bytes.toB256 (M.read s 32).1) ?_
    (by rw [toNat_toB256' (by omega)]) ?_ (by simp; omega) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs hn hsrc
  · rw [toNat_toB256' (by omega)]; exact read_covered hs hn hsrc
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_mstore (M' := M.write d (M.read s 32).1) ?_ ?_ ?_
  · rw [toNat_toB256' (by omega)]; exact charge_word hs hn hd
  · rw [toNat_toB256' (by omega), toBytes_read]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_add' (add_minus32 hl hl') (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_add' (push20_add (by omega)) (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_add' (push20_add (by omega)) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  exact rxc_jump hk hkC kont

/-- **The copy's exit test** (`len < 32`): 23 gas, then `X`. -/
theorem mcpy_exit {s d l : Nat} (hl : l < 32) (hR : R.length < 1000)
    (kont : SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M G) X r) :
    SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 l :: R) M (G + 23))
      (mcpyTree e0 e1 r0 r1 k X) r := by
  unfold mcpyTree
  refine rxc_dest ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_lt (v := 1) ?_ (by simp; omega) ?_
  · rw [show Bytes.toB256 [0x20] = Nat.toB256 32 by decide, lt_toB256 (by omega) (by norm_num)]
    simp [hl]
  refine rxc_push rfl (by simp; omega) ?_
  exact rxc_branch_succ (by decide) kont

/-- **The merge with nothing left over**: the destination word is read (extending memory by
the word at `d`) and stored back.  121 gas and the expansion. -/
theorem merge0 {s d n n' : Nat} {K : SFunc} (hs : M.size = n) (hn : n % 32 = 0)
    (hn' : max n (d + 32) = n')
    (hsrc : s + 32 ≤ n) (hd : d % 32 = 0) (hsl : s < 2 ^ 256) (hdl : d < 2 ^ 256)
    (hR : R.length < 1000)
    (kont : SFunc.RunExactCut fs sevm C
      (St b (Bytes.toB256 [0x20] :: R) ((M.read d 32).2.write d (M.read d 32).1) G) K r) :
    SFunc.RunExactCut fs sevm C
      (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 0 :: R) M
        (G + (118 + (3 + (calculateMemoryGasCost n' - calculateMemoryGasCost n)))))
      (mergeTree K) r := by
  subst hn'
  rw [show G + (118 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)))
    = G + 111 + (3 + (calculateMemoryGasCost (max n (d + 32)) - calculateMemoryGasCost n)) + 7
    by omega]
  have hs' : (M.read d 32).2.size = max n (d + 32) := read_ext_size hs hn hd
  unfold mergeTree
  refine rxc_dest ?_
  refine rxc_mload (c := 3) (v := Bytes.toB256 (M.read s 32).1) ?_
    (by rw [toNat_toB256' hsl]) ?_ (by simp; omega) ?_
  · rw [toNat_toB256' hsl]; exact charge_covered hs hn hsrc
  · rw [toNat_toB256' hsl]; exact read_covered hs hn hsrc
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mload_ext (v := Bytes.toB256 (M.read d 32).1) (M' := (M.read d 32).2) ?_
    (by rw [toNat_toB256' hdl]) (by rw [toNat_toB256' hdl]) (by simp; omega) ?_
  · rw [toNat_toB256' hdl]; exact charge_word hs hn hd
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_dup (n := 4) rfl (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 32) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_exp' (c := 60) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (v := B256.max) (by rw [bexp_256_32]; exact ones_add_zero) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_not (v := 0) B256.not_max (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_and (b256_and_zero _) (by simp; omega) ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_and (b256_max_and _) (by simp; omega) ?_
  refine rxc_or (b256_or_zero _) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_mstore (M' := (M.read d 32).2.write d (M.read d 32).1) ?_ ?_ kont
  · rw [toNat_toB256' hdl]; exact charge_covered hs' (by omega) (by omega)
  · rw [toNat_toB256' hdl, toBytes_read]

end Copy

/-! ## The whole site -/

theorem push20_add' {a c : Nat} (h : a + 32 = c) (hc : c < 2 ^ 256) :
    Bytes.toB256 [0x20] + Nat.toB256 a = Nat.toB256 c := by
  subst h; exact push20_add hc

theorem add_toB256' {a b c : Nat} (h : a + b = c) (hc : c < 2 ^ 256) :
    Nat.toB256 a + Nat.toB256 b = Nat.toB256 c := by
  subst h; exact toB256_add_toB256 hc

theorem sub_toB256' {a b c : Nat} (hb : b ≤ a) (h : a - b = c) (ha : a < 2 ^ 256) :
    Nat.toB256 a - Nat.toB256 b = Nat.toB256 c := by
  subst h; exact toB256_sub_toB256 hb ha

theorem memExtsSize_two_covered {n i j : Nat} (hn : n % 32 = 0) (hi : i + 64 ≤ n)
    (hj : j + 32 ≤ n) : memExtsSize n [⟨i, 64⟩, ⟨j, 32⟩] = n := by
  simp only [memExtsSize]
  rw [memExtSize_of_le hn hi, memExtSize_of_le hn hj]

/-- The image after the packing: `a` and `b` at `fp + 0x20` and `fp + 0x40`, the length at
`fp`, and the free pointer `fp + 0x60`. -/
def packImg (img : Bytes) (f : Nat) (a b : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img (f + 32) a.toBytes) (f + 64)
    b.toBytes) f (Nat.toB256 64).toBytes) 64 (Nat.toB256 (f + 96)).toBytes

/-- The image after the copy of two words `w1`, `w2` to `d`. -/
def copyImg2 (img : Bytes) (d : Nat) (w1 w2 : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt img d w1.toBytes) (d + 32) w2.toBytes

section Site

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {r : Seg}
  {R : List B256} {M : Mem} {G : Nat} {e0 e1 r0 r1 c0 c1 v0 v1 : UInt8} {k : Nat}
  {fail1 fail2 T : SFunc}

theorem packImg_word64 {img : Bytes} {f : Nat} {a b : B256} (_hf : 96 ≤ f) :
    (packImg img f a b).sliceD 64 32 0 = (Nat.toB256 (f + 96)).toBytes := by
  rw [packImg]
  have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img (f + 32)
    a.toBytes) (f + 64) b.toBytes) f (Nat.toB256 64).toBytes) (Nat.toB256 (f + 96)).toBytes 64
  rwa [B256.length_toBytes] at this

theorem packImg_len {img : Bytes} {f : Nat} {a b : B256} (hf : 96 ≤ f) :
    (packImg img f a b).sliceD f 32 0 = (Nat.toB256 64).toBytes := by
  rw [packImg, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega)]
  have := Bytes.sliceD_writeAt (Bytes.writeAt (Bytes.writeAt img (f + 32)
    a.toBytes) (f + 64) b.toBytes) (Nat.toB256 64).toBytes f
  rwa [B256.length_toBytes] at this

theorem packImg_a {img : Bytes} {f : Nat} {a b : B256} (hf : 96 ≤ f) :
    (packImg img f a b).sliceD (f + 32) 32 0 = a.toBytes := by
  rw [packImg, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
  have := Bytes.sliceD_writeAt img a.toBytes (f + 32)
  rwa [B256.length_toBytes] at this

theorem packImg_b {img : Bytes} {f : Nat} {a b : B256} (hf : 96 ≤ f) :
    (packImg img f a b).sliceD (f + 64) 32 0 = b.toBytes := by
  rw [packImg, Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega),
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega)]
  have := Bytes.sliceD_writeAt (Bytes.writeAt img (f + 32) a.toBytes) b.toBytes (f + 64)
  rwa [B256.length_toBytes] at this

theorem copyImg2_word64 {img : Bytes} {d : Nat} {w1 w2 : B256} (hd : 96 ≤ d) :
    (copyImg2 img d w1 w2).sliceD 64 32 0 = img.sliceD 64 32 0 := by
  rw [copyImg2, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
    Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]

theorem copyImg2_input {img : Bytes} {d : Nat} {w1 w2 : B256} :
    (copyImg2 img d w1 w2).sliceD d 64 0 = w1.toBytes ++ w2.toBytes := by
  rw [copyImg2]
  exact Bytes.read_two_word_writes_at _ _ _ _

/-- **Copy, merge and call**: from the copy loop's head with two words `w1`, `w2` at `s` and
`s + 0x20` to be copied to the free pointer `d = s + 0x40`, the two passes (the first inlined,
the second through entry `k`), the exit test, the merge, and the precompile call over the
copied 64 bytes with its checks.  598 gas and the expansion to `d + 0x60`.  The stack under the
copy's operands carries the length `0x40`, three words the tail discards around the free pointer `d`, and the
precompile's address.  The successor world is `ShaCallPost`-related, and the continuation `T` starts with
the returned size and `d` on the stack. -/
theorem copy_sha {img : Bytes} {n s d : Nat} {w1 w2 x1 x3 x4 : B256}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (hdn : d ≤ n) (hnd : n ≤ d + 32) (hsd : s + 64 = d) (hd32 : d % 32 = 0) (hd96 : 96 ≤ s)
    (hdb : d + 1000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 d).toBytes)
    (hw1 : img.sliceD s 32 0 = w1.toBytes) (hw2 : img.sliceD (s + 32) 32 0 = w2.toBytes)
    (hR : R.length < 900)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hG : G + 1000 < 2 ^ 256) :
    ∃ b' M' img', ShaCallPost b b' (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      Mem.Wf M' ∧ Mem.Reads M' img' ∧ M'.size = d + 96 ∧
      img'.sliceD 64 32 0 = (Nat.toB256 d).toBytes ∧
      img'.sliceD d 32 0 = (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes ∧
      ∀ r, SFunc.RunExactCut fs sevm C (St b' (Nat.toB256 32 :: Nat.toB256 d :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (Nat.toB256 s :: Nat.toB256 d :: Nat.toB256 64 :: Nat.toB256 64 :: x1 ::
          Nat.toB256 d :: x3 :: x4 :: 2 :: R) M
          (G + (598 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost n))))
        (mcpyTree e0 e1 r0 r1 k (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))) r := by
  have m3 := calculateMemoryGasCost_mono (show n ≤ d + 32 by omega)
  have m4 := calculateMemoryGasCost_mono (show d + 32 ≤ d + 64 by omega)
  have m5 := calculateMemoryGasCost_mono (show d + 64 ≤ d + 96 by omega)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hw1' : (M.read s 32).1 = w1.toBytes := by rw [hr.read, hw1]
  set M5 := M.write d (M.read s 32).1 with hM5
  have hwf5 : Mem.Wf M5 := hwf.write _ _
  have hr5 : Mem.Reads M5 (Bytes.writeAt img d w1.toBytes) := by
    rw [hM5, hw1']; exact hr.write hwf _ _
  have hs5 : M5.size = d + 32 := by
    rw [hM5, hw1', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hw2' : (M5.read (s + 32) 32).1 = w2.toBytes := by
    rw [hr5.read, Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw2]
  set M6 := M5.write (d + 32) (M5.read (s + 32) 32).1 with hM6
  have hwf6 : Mem.Wf M6 := hwf5.write _ _
  have hr6 : Mem.Reads M6 (copyImg2 img d w1 w2) := by
    rw [hM6, hw2']; exact hr5.write hwf5 _ _
  have hs6 : M6.size = d + 64 := by
    rw [hM6, hw2', Mem.size_write_word_aligned (by omega) (by omega)]; omega
  set M7 := (M6.read (d + 64) 32).2.write (d + 64) (M6.read (d + 64) 32).1 with hM7
  have hs6' : (M6.read (d + 64) 32).2.size = d + 96 := by
    rw [read_ext_size hs6 (by omega) (by omega)]; omega
  have hwf7 : Mem.Wf M7 := (hwf6.extend _ _).write _ _
  have hr7 : Mem.Reads M7 (copyImg2 img d w1 w2) := by
    rw [hM7, hr6.read]
    exact Mem.Reads.write_self (hwf6.extend _ _) (hr6.extend _ _) _
  have hs7 : M7.size = d + 96 := by
    rw [hM7, ← toBytes_read, Mem.size_write_word_aligned (by omega) (by omega), hs6']; omega
  have hin : (M7.read d 64).1 = w1.toBytes ++ w2.toBytes := by
    rw [hr7.read, copyImg2_input]
  have hF : (Nat.toB256 d).toNat = d := toNat_toB256' (by omega)
  obtain ⟨b', hpost, hstep⟩ := staticcall_sha_step (sevm := sevm) (b := b)
    (iiw := Nat.toB256 d) (oiw := Nat.toB256 d) (S := Nat.toB256 (d + 64) :: 2 :: R)
    (M := M7) (G := G + 62)
    (by rw [hF, hs7]; exact memExtsSize_two_covered (by omega) (by omega) (by omega))
    hnodeleg hwarm hpre hfork hdepth (by omega) (by simp; omega) (by omega)
  rw [hF, hin] at hpost hstep
  set M8 := M7.write d (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes with hM8
  have hwf8 : Mem.Wf M8 := hwf7.write _ _
  have hr8 := hr7.write hwf7 d (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes
  have hs8 : M8.size = d + 96 := by
    rw [hM8, Mem.size_write_word_aligned (by omega) (by omega), hs7]; omega
  have hw7 : (copyImg2 img d w1 w2).sliceD 64 32 0 = (Nat.toB256 d).toBytes := by
    rw [copyImg2_word64 (by omega), hfp]
  have hw8 : (Bytes.writeAt (copyImg2 img d w1 w2) d
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes).sliceD 64 32 0 =
      (Nat.toB256 d).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hw7]
  have hh8 : (Bytes.writeAt (copyImg2 img d w1 w2) d
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes).sliceD d 32 0 =
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes := by
    have := Bytes.sliceD_writeAt (copyImg2 img d w1 w2)
      (Bytes.sha256 (w1.toBytes ++ w2.toBytes)).toBytes d
    rwa [B256.length_toBytes] at this
  have hrd : b'.returnData.length.toB256 = Nat.toB256 32 := by
    rw [hpost.returnData, B256.length_toBytes]
  refine ⟨b', M8, _, hpost, hwf8, hr8, hs8, hw8, hh8, fun r kont => ?_⟩
  rw [show G + (598 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost n)) =
    G + 62 + 184 + 50
      + (118 + (3 + (calculateMemoryGasCost (d + 96) - calculateMemoryGasCost (d + 64)))) + 23
      + (76 + (3 + (calculateMemoryGasCost (d + 64) - calculateMemoryGasCost (d + 32))))
      + (76 + (3 + (calculateMemoryGasCost (d + 32) - calculateMemoryGasCost n))) by omega]
  -- the copy: two passes and the exit test
  refine mcpy_iter (s := s) (d := d) (l := 64) (n := n) (n' := d + 32)
    (by omega) (by omega) hs (by omega) hn (by omega) (by omega) (by omega) (by omega)
    (by simp; omega) hk hkC ?_
  refine mcpy_iter (s := s + 32) (d := d + 32) (l := 32) (n := d + 32) (n' := d + 64)
    (by omega) (by omega) hs5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by simp; omega) hk hkC ?_
  refine mcpy_exit (s := s + 64) (d := d + 64) (l := 0) (by omega) (by simp; omega) ?_
  refine merge0 (s := s + 64) (d := d + 64) (n := d + 64) (n' := d + 96) hs6 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by simp; omega) ?_
  -- the call
  unfold shaCallTree
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 d) ?_
    (by rw [h40]; exact read_word hr7 64 hw7) ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs7 (by omega) (by omega)
  · rw [h40]; exact read_covered hs7 (by omega) (by omega)
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_swap (n := 3) rfl ?_
  refine rxc_add' (add_toB256' (c := d + 64) (by omega) (by omega)) (by simp; omega) ?_
  refine rxc_swap (n := 4) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (n := 1) rfl ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 64) (by omega) (by omega) (by omega)) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 5) rfl (by simp; omega) ?_
  refine rxc_gas (by simp; omega) ?_
  refine .next hstep ?_
  refine rxc_iszero (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  refine rxc_dest ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 d) ?_
    (by rw [h40]; exact read_word hr8 64 hw8) ?_ (by omega) ?_
  · rw [h40]; exact charge_covered hs8 (by omega) (by omega)
  · rw [h40]; exact read_covered hs8 (by omega) (by omega)
  refine rxc_returndatasize (by simp; omega) ?_
  rw [hrd]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_lt (v := 0) (by decide) (by simp; omega) ?_
  refine rxc_iszero (v := 1) (by decide) (by simp; omega) ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_branch_succ (by decide) ?_
  exact kont

/-- **`sha256(abi.encodePacked(a, b))`** with `b` on top of `a` (and the precompile's address
`2` below them), the free pointer at `f` (word-aligned, past the scratch words) and memory of
size `n ≤ f + 0x60`: the packing, then `copy_sha` from `f + 0x20` to `f + 0x60`.  727 gas and
the expansion to `f + 0xc0`. -/
theorem packed_sha_pair {img : Bytes} {n f : Nat} {a bw : B256}
    (hk : fs[k]? = some (mcpyTree e0 e1 r0 r1 k
      (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
    (hkC : k ∉ C)
    (hwf : Mem.Wf M) (hr : Mem.Reads M img) (hs : M.size = n) (hn : n % 32 = 0)
    (h96 : 96 ≤ n) (hnf : n ≤ f + 96) (hf32 : f % 32 = 0) (hf96 : 96 ≤ f)
    (hfb : f + 2000 < 2 ^ 256) (hfp : img.sliceD 64 32 0 = (Nat.toB256 f).toBytes)
    (hR : R.length < 900)
    (hnodeleg : getDelegatedCodeAddress (b.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ b.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork sevm.benvStat.fork) (hdepth : sevm.depth ≠ 0)
    (hG : G + 1000 < 2 ^ 256) :
    ∃ b' M' img', ShaCallPost b b' (hashPairBytes a bw) ∧ Mem.Wf M' ∧
      Mem.Reads M' img' ∧ M'.size = f + 192 ∧
      img'.sliceD 64 32 0 = (Nat.toB256 (f + 96)).toBytes ∧
      img'.sliceD (f + 96) 32 0 = (Bytes.sha256 (a.toBytes ++ bw.toBytes)).toBytes ∧
      ∀ r, SFunc.RunExactCut fs sevm C
        (St b' (Nat.toB256 32 :: Nat.toB256 (f + 96) :: R) M' G) T r →
      SFunc.RunExactCut fs sevm C
        (St b (bw :: a :: 2 :: R) M
          (G + (727 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n))))
        (pack2Tree (mcpyTree e0 e1 r0 r1 k (mergeTree (shaCallTree c0 c1 v0 v1 fail1 fail2 T))))
        r := by
  set s1 := max n (f + 64) with hs1_def
  have m1 := calculateMemoryGasCost_mono (show n ≤ s1 by omega)
  have m2 := calculateMemoryGasCost_mono (show s1 ≤ f + 96 by omega)
  have m3 := calculateMemoryGasCost_mono (show f + 96 ≤ f + 192 by omega)
  have h40 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  set M1 := M.write (f + 32) a.toBytes with hM1
  set M2 := M1.write (f + 64) bw.toBytes with hM2
  set M3 := M2.write f (Nat.toB256 64).toBytes with hM3
  set M4 := M3.write 64 (Nat.toB256 (f + 96)).toBytes with hM4
  have hs1 : M1.size = s1 := by
    rw [hM1, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs2 : M2.size = f + 96 := by
    rw [hM2, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs3 : M3.size = f + 96 := by
    rw [hM3, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hs4 : M4.size = f + 96 := by
    rw [hM4, Mem.size_write_word_aligned (by omega) (by omega)]; omega
  have hwf1 : Mem.Wf M1 := hwf.write _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hwf4 : Mem.Wf M4 := hwf3.write _ _
  have hr1 := hr.write hwf (f + 32) a.toBytes
  have hr2 := hr1.write hwf1 (f + 64) bw.toBytes
  have hr3 := hr2.write hwf2 f (Nat.toB256 64).toBytes
  have hr4 : Mem.Reads M4 (packImg img f a bw) := hr3.write hwf3 64 _
  have hfp2 : (Bytes.writeAt (Bytes.writeAt img (f + 32) a.toBytes) (f + 64)
      bw.toBytes).sliceD 64 32 0 = (Nat.toB256 f).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), hfp]
  obtain ⟨b', M', img', hpost, hwf', hr', hs', hw', hh', hrun⟩ :=
    copy_sha (fs := fs) (sevm := sevm) (C := C) (b := b) (R := R) (M := M4) (G := G)
      (T := T) (fail1 := fail1) (fail2 := fail2) (n := f + 96) (s := f + 32) (d := f + 96)
      (x1 := Nat.toB256 (f + 32)) (x3 := Nat.toB256 (f + 96))
      (x4 := Nat.toB256 f)
      hk hkC hwf4 hr4 hs4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (packImg_word64 hf96) (packImg_a hf96) (packImg_b hf96) hR hnodeleg hwarm hpre
      hfork hdepth hG
  refine ⟨b', M', img', hpost, hwf', hr', by omega, hw', hh', fun r kont => ?_⟩
  have hc := hrun r kont
  rw [show G + (727 + (calculateMemoryGasCost (f + 192) - calculateMemoryGasCost n)) =
    G + (598 + (calculateMemoryGasCost (f + 96 + 96) - calculateMemoryGasCost (f + 96))) + 90
      + (3 + (calculateMemoryGasCost (f + 96) - calculateMemoryGasCost s1)) + 12
      + (3 + (calculateMemoryGasCost s1 - calculateMemoryGasCost n)) + 21 by
    rw [show f + 96 + 96 = f + 192 by omega]; omega]
  unfold pack2Tree
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_ (by rw [h40]; exact read_word hr 64 hfp) ?_
    (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs hn (by omega)
  · rw [h40]; exact read_covered hs hn (by omega)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (M' := M1) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs hn (by omega)]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add' (a := f + 32) (c := f + 64) rfl (by omega)) (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (M' := M2) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega), charge_word hs1 (by omega) (by omega),
      show max s1 (f + 64 + 32) = f + 96 by omega]
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add' (a := f + 64) (c := f + 96) rfl (by omega)) (by simp; omega) ?_
  refine rxc_swap (n := 2) rfl ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_pop ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 f) ?_
    (by rw [h40]; exact read_word hr2 64 hfp2) ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs2 (by omega) (by omega)
  · rw [h40]; exact read_covered hs2 (by omega) (by omega)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_sub' (sub_toB256' (c := 96) (by omega) (by omega) (by omega)) (by simp; omega) ?_
  refine rxc_sub' (v := Nat.toB256 64) (by decide) (by simp; omega) ?_
  refine rxc_dup (n := 1) rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M3) ?_ (by rw [toNat_toB256' (by omega)]) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs2 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mstore (c := 3) (M' := M4) ?_ (by rw [h40]) ?_
  · rw [h40]; exact charge_covered hs3 (by omega) (by omega)
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 (f + 96)) ?_
    (by rw [h40]; exact read_word hr4 64 (packImg_word64 hf96)) ?_ (by simp; omega) ?_
  · rw [h40]; exact charge_covered hs4 (by omega) (by omega)
  · rw [h40]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 2) rfl (by simp; omega) ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_mload (c := 3) (v := Nat.toB256 64) ?_
    (by rw [toNat_toB256' (by omega)]; exact read_word hr4 f (packImg_len hf96)) ?_
    (by simp; omega) ?_
  · rw [toNat_toB256' (by omega)]; exact charge_covered hs4 (by omega) (by omega)
  · rw [toNat_toB256' (by omega)]; exact read_covered hs4 (by omega) (by omega)
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_push rfl (by simp; omega) ?_
  refine rxc_add' (push20_add (a := f) (by omega)) (by simp; omega) ?_
  refine rxc_swap (n := 0) rfl ?_
  refine rxc_dup (n := 0) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  refine rxc_dup (n := 3) rfl (by simp; omega) ?_
  exact hc

end Site

end Blanc.Lift
