import Blanc.Lift.BeaconDeposit.Prog
import Blanc.Lift.CopyLoop
import Blanc.BeaconDepositModel

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- solc's `PUSH31 0xff…ff`: the mask whose complement keeps a word's top byte. -/
def m31 : B256 := Bytes.toB256 (List.replicate 31 0xff)

/-- The stored byte of one `MSTORE8` step: `BYTE 0` of the byte shifted to the top and masked,
is the byte. -/
theorem byte_roundtrip (u : UInt8) :
    ((List.getD (((~~~ m31) &&& (u.toB256 <<< (Bytes.toB256 [0xf8]).toNat)).toBytes)
      (Bytes.toB256 [0x00]).toNat 0).toB256).2.2.toUInt8 = u := by
  have key : ∀ n : Fin 256,
      ((List.getD (((~~~ m31) &&& ((UInt8.ofNat n.val).toB256 <<< (Bytes.toB256 [0xf8]).toNat)).toBytes)
        (Bytes.toB256 [0x00]).toNat 0).toB256).2.2.toUInt8 = UInt8.ofNat n.val := by decide +kernel
  have := key ⟨u.toNat, u.toNat_lt⟩
  simpa using this

theorem shl192_eq (a b c d : UInt64) :
    B256.shiftLeft (((a, b) : B128), ((c, d) : B128)) 192 = (((d, 0) : B128), (0 : B128)) := by
  simp only [B256.shiftLeft]
  norm_num
  change (B128.shiftLeft ((c, d) : B128) 64, (0 : B128)) = _
  simp only [B128.shiftLeft]
  norm_num
  rfl

theorem shl192_eq' (v : B256) : v <<< 192 = (((v.2.2, 0) : B128), (0 : B128)) := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
  exact shl192_eq a b c d

/-- `BYTE (7 - i)` of `v << 192` is `le64 v`'s byte `i`. -/
theorem shl192_byte (v : B256) (i : Nat) (hi : i < 8) :
    (v <<< 192).toBytes.getD (7 - i) 0 = (Blanc.BeaconDeposit.le64 v.toNat).getD i 0 := by
  rw [shl192_eq']
  have hN : v.toNat = (v.1.1.toNat * 2 ^ 64 + v.1.2.toNat) * 2 ^ 128 +
      (v.2.1.toNat * 2 ^ 64 + v.2.2.toNat) := by
    rw [B256.toNat_eq, B128.toNat_eq, B128.toNat_eq]
  have hd := UInt64.toNat_lt v.2.2
  apply UInt8.toNat_inj.mp
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
  all_goals first
    | omega
    | simp [B256.toBytes, B128.toBytes, UInt64.toBytes, UInt32.toBytes, UInt16.toBytes,
        Blanc.BeaconDeposit.le64, hN, Nat.shiftRight_eq_div_pow] <;> omega

/-! ## Memory arithmetic -/

/-- A window of at most one word at an aligned offset over an aligned image extends it to the
word's end, or not at all. -/
theorem memExtSize_aligned_small {m i sz : Nat} (hm : m % 32 = 0) (hi : i % 32 = 0)
    (h0 : 0 < sz) (h32 : sz ≤ 32) : memExtSize m i sz = max m (i + 32) := by
  unfold memExtSize
  rw [ite_eq_right (by omega)]
  unfold ceilDiv
  rw [ite_eq_left hm]
  by_cases h : (i + sz) % 32 = 0
  · rw [ite_eq_left h]; omega
  · rw [ite_eq_right h]; omega

theorem sliceD_length_self (xs : Bytes) (k : Nat) :
    xs.sliceD xs.length k 0 = List.replicate k 0 := by
  rw [List.sliceD, List.drop_length, Blanc.List.takeD_nil_eq_replicate]

/-- Overwriting a range with a payload of the same length forgets the first payload. -/
theorem Bytes.writeAt_writeAt_same (bs : Bytes) (q : Nat) (xs ys : Bytes)
    (h : xs.length = ys.length) :
    Bytes.writeAt (Bytes.writeAt bs q xs) q ys = Bytes.writeAt bs q ys := by
  apply List.ext_getD' 0
  · simp only [Bytes.length_writeAt']; omega
  · intro k
    simp only [Bytes.getD_writeAt]
    by_cases h1 : q ≤ k ∧ k < q + ys.length
    · rw [ite_eq_left h1, ite_eq_left h1]
    · rw [ite_eq_right h1, ite_eq_right h1, ite_eq_right (by omega)]

/-! ## The code's pieces

Entry 25 (pc `0x14ba`) is `to_little_endian_64(uint64)`: allocate `new bytes(8)` (length word at
the free pointer, pointer advanced by 64, the payload zero-filled by a `CALLDATACOPY` from the end
of calldata), shift the value to the top of a word, then eight steps each storing one byte with
`MSTORE8` behind a bounds guard (`INVALID` on failure), and return the pointer.  Its tree is a
prefix, eight guard halves (`leHalf1`) and eight store halves (`leHalf2`), and a tail. -/

/-- One step's guard: `BYTE c` of the shifted value, moved to the top byte, and the check
`ib < length` (a `JUMPI` over `INVALID`). -/
def leHalf1 (c ib d0 d1 : UInt8) (T : SFunc) : SFunc :=
  .next (.reg (.dup 0)) (.next (.push [c] (by simp)) (.next (.reg .byte)
    (.next (.push [0xf8] (by decide)) (.next (.reg .shl) (.next (.reg (.dup 2))
      (.next (.push [ib] (by simp)) (.next (.reg (.dup 1)) (.next (.reg .mload)
        (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [d0, d1] (by simp))
          (.branch .undefined T))))))))))))

/-- One step's store: `MSTORE8` of the top byte at `p + 32 + ib`. -/
def leHalf2 (K : SFunc) : SFunc :=
  .dest (.next (.push [0x20] (by decide)) (.next (.reg .add) (.next (.reg .add)
    (.next (.reg (.swap 0)) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)) (.next (.reg .not) (.next (.reg .and)
        (.next (.reg (.swap 0)) (.next (.reg (.dup 1)) (.next (.push [0x00] (by decide))
          (.next (.reg .byte) (.next (.reg (.swap 0)) (.next (.reg .mstore8)
            (.next (.reg .pop) K))))))))))))))

/-- The prefix: allocation, zero fill, and `v << 192`. -/
def lePrefix (K : SFunc) : SFunc :=
  .dest (.next (.push [0x40] (by decide)) (.next (.reg (.dup 0)) (.next (.reg .mload)
    (.next (.push [0x08] (by decide)) (.next (.reg (.dup 0)) (.next (.reg (.dup 2))
      (.next (.reg .mstore) (.next (.reg (.dup 1)) (.next (.reg (.dup 3)) (.next (.reg .add)
        (.next (.reg (.swap 0)) (.next (.reg (.swap 2)) (.next (.reg .mstore)
          (.next (.push [0x60] (by decide)) (.next (.reg (.swap 1))
            (.next (.push [0x20] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .add)
              (.next (.reg (.dup 1)) (.next (.reg (.dup 0)) (.next (.reg .calldatasize)
                (.next (.reg (.dup 3)) (.next (.reg .calldatacopy) (.next (.reg .add)
                  (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg .pop)
                    (.next (.reg (.swap 0)) (.next (.reg .pop)
                      (.next (.push [0xc0] (by decide)) (.next (.reg (.dup 2))
                        (.next (.reg (.swap 0)) (.next (.reg .shl) K)))))))))))))))))))))))))))))))))

/-- The tail: drop the shifted value and the argument, return the pointer. -/
def leTail : SFunc :=
  .next (.reg .pop) (.next (.reg (.swap 1)) (.next (.reg (.swap 0)) (.next (.reg .pop) .ret)))

theorem t_14ba_eq : t_14ba_c25 = lePrefix (leHalf1 7 0 0x14 0xf4
    (leHalf2 (leHalf1 6 1 0x15 0x37 (leHalf2 (leHalf1 5 2 0x15 0x7a (leHalf2 (leHalf1 4 3 0x15 0xbd
      (leHalf2 (leHalf1 3 4 0x16 0x00 (leHalf2 (leHalf1 2 5 0x16 0x43 (leHalf2 (leHalf1 1 6 0x16 0x86
        (leHalf2 (leHalf1 0 7 0x16 0xc9 (leHalf2 leTail)))))))))))))))) := rfl

/-- The value one step moves to the top byte. -/
def leB (v : B256) (i : Nat) : B256 :=
  ((Blanc.BeaconDeposit.le64 v.toNat).getD i 0).toB256 <<< (Bytes.toB256 [0xf8]).toNat

section Walk

variable {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome} {v ret pB : B256} {rest : List B256}
  {M : Mem} {S : Nat}

theorem le_half1 {c ib d0 d1 : UInt8} {T : SFunc} {i : Nat} {imgM : Bytes} (hi : i < 8)
    (hc : (Bytes.toB256 [c]).toNat = 7 - i) (hib : (Bytes.toB256 [ib]).toNat = i)
    (hroom : rest.length < 1000) (hr : Mem.Reads M imgM)
    (h8 : imgM.sliceD pB.toNat 32 0 = (8 : B256).toBytes) (hs : M.size = S) (hS : S % 32 = 0)
    (hpS : pB.toNat + 32 ≤ S)
    (k : SFunc.RunExact prog sevm
      (St b (Bytes.toB256 [ib] :: pB :: leB v i :: (v <<< 192) :: pB :: v :: ret :: rest) M G)
      T o) :
    SFunc.RunExact prog sevm (St b ((v <<< 192) :: pB :: v :: ret :: rest) M (G + 46))
      (leHalf1 c ib d0 d1 T) o := by
  unfold leHalf1
  refine rx_dup1 (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_byte (v := ((Blanc.BeaconDeposit.le64 v.toNat).getD i 0).toB256) ?_
    (by simp; omega) ?_
  · rw [hc, shl192_byte v i hi]
  refine rx_push rfl (by simp; omega) ?_
  refine rx_shl (v := leB v i) rfl (by simp; omega) ?_
  refine rx_dup (n := 2) rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_mload (c := 3) (v := 8) ?_ ?_ ?_ (by simp; omega) ?_
  · rw [St.extCost_eq hs, memExtSize_of_le hS hpS, Nat.sub_self]; rfl
  · rw [hr.read, h8, B256.toB256_toBytes]
  · exact Mem.read_snd_eq_self (by rw [hs]; exact memExtSize_of_le hS hpS)
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_lt (v := 1) ?_ (by simp; omega) ?_
  · rw [B256.ltCheck, ite_eq_left]
    rw [B256.lt_iff_toNat_lt_toNat, hib]
    exact (by show i < 8; omega)
  refine rx_push rfl (by simp; omega) ?_
  exact rx_branch_succ (by decide) k

theorem le_half2 {K : SFunc} {ib : UInt8} {i : Nat} (hi : i < 8)
    (hib : (Bytes.toB256 [ib]).toNat = i) (hroom : rest.length < 1000) (hs : M.size = S)
    (hS : S % 32 = 0) (hpS : pB.toNat + 64 ≤ S) (hp : pB.toNat + 64 < 2 ^ 256)
    (k : SFunc.RunExact prog sevm (St b ((v <<< 192) :: pB :: v :: ret :: rest)
      (M.write (pB.toNat + 32 + i) [(Blanc.BeaconDeposit.le64 v.toNat).getD i 0]) G) K o) :
    SFunc.RunExact prog sevm
      (St b (Bytes.toB256 [ib] :: pB :: leB v i :: (v <<< 192) :: pB :: v :: ret :: rest) M
        (G + 42)) (leHalf2 K) o := by
  have hA : (Bytes.toB256 [0x20] + Bytes.toB256 [ib] + pB).toNat = pB.toNat + 32 + i := by
    rw [B256.toNat_add, B256.toNat_add, hib, show (Bytes.toB256 [0x20]).toNat = 32 by decide]
    rw [Nat.lo_eq_of_lt (a := 32 + i) (by omega), Nat.lo_eq_of_lt (by omega)]
    omega
  unfold leHalf2
  refine rx_dest ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_swap1 ?_
  refine rx_push (w := m31) rfl (by simp; omega) ?_
  refine rx_not rfl (by simp; omega) ?_
  refine rx_and rfl (by simp; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup (n := 1) rfl (by simp; omega) ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_byte rfl (by simp; omega) ?_
  refine rx_swap1 ?_
  refine rx_mstore8 (c := 3)
    (M' := M.write (pB.toNat + 32 + i) [(Blanc.BeaconDeposit.le64 v.toNat).getD i 0]) ?_ ?_ ?_
  · rw [St.extCost_eq hs, hA, memExtSize_of_le hS (by omega), Nat.sub_self]; rfl
  · rw [hA, leB, byte_roundtrip]
  exact rx_pop k

end Walk

/-! ## The eight byte stores -/

/-- Writing one byte inside an earlier write is a `List.set` of its payload. -/
theorem Bytes.writeAt_writeAt_set (bs : Bytes) (q : Nat) (L : Bytes) (i : Nat) (x : UInt8)
    (hi : i < L.length) :
    Bytes.writeAt (Bytes.writeAt bs q L) (q + i) [x] = Bytes.writeAt bs q (L.set i x) := by
  apply List.ext_getD' 0
  · simp only [Bytes.length_writeAt', List.length_set, List.length_cons, List.length_nil]; omega
  · intro k
    simp only [Bytes.getD_writeAt, List.length_set, List.length_cons, List.length_nil]
    by_cases h1 : q + i ≤ k ∧ k < q + i + 1
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
      have hk : k - q = i := by omega
      rw [hk, show k - (q + i) = 0 by omega]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [ite_eq_right h1]
      by_cases h2 : q ≤ k ∧ k < q + L.length
      · rw [ite_eq_left h2, ite_eq_left h2]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
        rw [ite_eq_right (by omega)]
      · rw [ite_eq_right h2, ite_eq_right h2]

/-- The memory after the first `i` byte stores at `q + 0, …, q + (i - 1)`. -/
def leMem (M : Mem) (q : Nat) (v : B256) : Nat → Mem
  | 0 => M
  | i + 1 => (leMem M q v i).write (q + i) [(Blanc.BeaconDeposit.le64 v.toNat).getD i 0]

/-- The byte image after the first `i` byte stores. -/
def leBytes (img : Bytes) (q : Nat) (v : B256) : Nat → Bytes
  | 0 => img
  | i + 1 => Bytes.writeAt (leBytes img q v i) (q + i) [(Blanc.BeaconDeposit.le64 v.toNat).getD i 0]

/-- What the byte stores keep: a well-formed memory of fixed size, reading as its image, with
the length word at `p`. -/
def LeInv (M : Mem) (img : Bytes) (S p : Nat) : Prop :=
  Mem.Wf M ∧ Mem.Reads M img ∧ M.size = S ∧ img.sliceD p 32 0 = (8 : B256).toBytes

theorem LeInv.write {M : Mem} {img : Bytes} {S p q : Nat} (h : LeInv M img S p)
    (hq : p + 32 ≤ q) (hqS : q + 1 ≤ S) (u : UInt8) :
    LeInv (M.write q [u]) (Bytes.writeAt img q [u]) S p :=
  ⟨h.1.write _ _, h.2.1.write h.1 _ _,
    by rw [Mem.size_write_of_le (by simp only [List.length_cons, List.length_nil]; rw [h.2.2.1]; omega),
      h.2.2.1],
    by rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega), h.2.2.2]⟩

theorem LeInv.leMem {M : Mem} {img : Bytes} {S p : Nat} {v : B256} (h : LeInv M img S p)
    (hS : p + 64 ≤ S) : ∀ i, i ≤ 8 →
    LeInv (leMem M (p + 32) v i) (leBytes img (p + 32) v i) S p
  | 0, _ => h
  | i + 1, hi => (LeInv.leMem h hS i (by omega)).write (by omega) (by omega) _

theorem leBytes_zeros (Z : Bytes) (q : Nat) (v : B256) :
    leBytes (Bytes.writeAt Z q (List.replicate 8 0)) q v 8 =
      Bytes.writeAt Z q (Blanc.BeaconDeposit.le64 v.toNat) := by
  simp only [leBytes]
  repeat rw [Bytes.writeAt_writeAt_set _ _ _ _ _ (by simp)]
  congr 1

/-! ## `to_little_endian_64` -/

/-- The memory image `to_little_endian_64` leaves over `img`, with the free pointer `pB`:
the length word `8` at `pB`, the free pointer advanced to `pB + 64`, and `le64 v` at `pB + 32`
(the rest of that word keeps whatever `img` had there). -/
def leImg (img : Bytes) (pB v : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt (Bytes.writeAt img pB.toNat (8 : B256).toBytes) 64
    (pB + 64).toBytes) (pB.toNat + 32) (Blanc.BeaconDeposit.le64 v.toNat)

/-- Its gas over a memory of size `n` with the free pointer at `p`: 821 and the expansion to
`p + 64`. -/
def leGas (n p : Nat) : Nat :=
  821 + (calculateMemoryGasCost (max n (p + 64)) - calculateMemoryGasCost n)

theorem le_mid {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome} {v ret pB : B256}
    {rest : List B256} {M : Mem} {Y : Bytes} {S : Nat} {c ib ib' d0 d1 : UInt8} {T : SFunc}
    {i : Nat} (hi : i + 1 < 8) (hc : (Bytes.toB256 [c]).toNat = 7 - (i + 1))
    (hib : (Bytes.toB256 [ib]).toNat = i) (hib' : (Bytes.toB256 [ib']).toNat = i + 1)
    (hroom : rest.length < 1000) (hS : S % 32 = 0) (hpS : pB.toNat + 64 ≤ S)
    (hp : pB.toNat + 64 < 2 ^ 256)
    (hinv : LeInv (leMem M (pB.toNat + 32) v i) (leBytes Y (pB.toNat + 32) v i) S pB.toNat)
    (hinv' : LeInv (leMem M (pB.toNat + 32) v (i + 1)) (leBytes Y (pB.toNat + 32) v (i + 1)) S
      pB.toNat)
    (k : SFunc.RunExact prog sevm
      (St b (Bytes.toB256 [ib'] :: pB :: leB v (i + 1) :: (v <<< 192) :: pB :: v :: ret :: rest)
        (leMem M (pB.toNat + 32) v (i + 1)) G) T o) :
    SFunc.RunExact prog sevm
      (St b (Bytes.toB256 [ib] :: pB :: leB v i :: (v <<< 192) :: pB :: v :: ret :: rest)
        (leMem M (pB.toNat + 32) v i) (G + 88)) (leHalf2 (leHalf1 c ib' d0 d1 T)) o :=
  le_half2 (by omega) hib hroom hinv.2.2.1 hS hpS hp
    (le_half1 hi hc hib' hroom hinv'.2.1 hinv'.2.2.2 hinv'.2.2.1 hS (by omega) k)

/-- **`to_little_endian_64`, gas-exact, for any caller.**  Entry 25 called with `v :: ret :: rest`
over a word-aligned memory of size `n ≥ 96` whose free pointer `pB` (at `0x40`) is word-aligned
and at least `0x60`, returns `pB :: rest` after exactly `leGas n pB` gas, over a memory of size
`max n (pB + 64)` reading as `leImg`: the length `8` at `pB`, the free pointer `pB + 64`, and
`le64 v` at `pB + 32`.  Only the machine state moves (`St b`: world and metadata are `b`'s). -/
theorem to_little_endian_64_run {sevm : Sevm} {b : Devm} {G : Nat} {v ret pB : B256}
    {rest : List B256} {M : Mem} {img : Bytes}
    (hroom : rest.length < 1000) (hwf : Mem.Wf M) (hr : Mem.Reads M img)
    (hn32 : M.size % 32 = 0) (hn96 : 96 ≤ M.size)
    (hfp : Bytes.toB256 (img.sliceD 64 32 0) = pB) (hp32 : pB.toNat % 32 = 0)
    (hp96 : 96 ≤ pB.toNat) (hp : pB.toNat + 64 < 2 ^ 256)
    (hcd : sevm.data.length < 2 ^ 256) :
    ∃ M', Mem.Wf M' ∧ Mem.Reads M' (leImg img pB v) ∧ M'.size = max M.size (pB.toNat + 64) ∧
      SFunc.RunExact prog sevm (St b (v :: ret :: rest) M (G + leGas M.size pB.toNat)) t_14ba_c25
        (.returned (St b (pB :: rest) M' G)) := by
  set n := M.size with hn_def
  set p := pB.toNat with hp_def
  have h8 : Bytes.toB256 [0x08] = 8 := by decide
  have h64 : (Bytes.toB256 [0x40]).toNat = 64 := by decide
  have hfpv : Bytes.toB256 [0x40] + pB = pB + 64 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, B256.toNat_add, h64, show (64 : B256).toNat = 64 from rfl, Nat.add_comm]
  have ha : (pB + Bytes.toB256 [0x20]).toNat = p + 32 := by
    rw [B256.toNat_add, show (Bytes.toB256 [0x20]).toNat = 32 by decide,
      Nat.lo_eq_of_lt (by omega)]
  have hsi : (Nat.toB256 sevm.data.length).toNat = sevm.data.length :=
    B256.toNat_toB256_of_lt hcd
  -- the three writes of the prefix
  set M1 := M.write p (Bytes.toB256 [0x08]).toBytes with hM1
  set M2 := M1.write 64 (Bytes.toB256 [0x40] + pB).toBytes with hM2
  set M3 := M2.write (p + 32) (List.replicate 8 0) with hM3
  have hs1 : M1.size = max n (p + 32) := Mem.size_write_word_aligned hn32 hp32
  have hs2 : M2.size = max n (p + 32) := by
    rw [Mem.size_write_word_aligned (by rw [hs1]; omega) (by decide), hs1]; omega
  have hs3 : M3.size = max n (p + 64) := by
    show (M2.write (p + 32) (0 :: List.replicate 7 0)).size = _
    rw [Mem.size_write_cons, hs2]
    simp only [List.length_cons, List.length_replicate]
    split_ifs with h
    · omega
    · unfold ceil32
      split <;> omega
  set Z := Bytes.writeAt (Bytes.writeAt img p (Bytes.toB256 [0x08]).toBytes) 64
    (Bytes.toB256 [0x40] + pB).toBytes with hZ
  have hwf3 : Mem.Wf M3 := ((hwf.write _ _).write _ _).write _ _
  have hr3 : Mem.Reads M3 (Bytes.writeAt Z (p + 32) (List.replicate 8 0)) :=
    ((hr.write hwf _ _).write (hwf.write _ _) _ _).write ((hwf.write _ _).write _ _) _ _
  have h80 : (Bytes.writeAt Z (p + 32) (List.replicate 8 0)).sliceD p 32 0 =
      (8 : B256).toBytes := by
    rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega),
      Bytes.sliceD_writeAt_after _ _ _ _ _ (by rw [B256.length_toBytes]; omega), h8]
    have := Bytes.sliceD_writeAt img (8 : B256).toBytes p
    rwa [B256.length_toBytes] at this
  have hS32 : max n (p + 64) % 32 = 0 := by omega
  have inv : ∀ i, i ≤ 8 → LeInv (leMem M3 (p + 32) v i)
      (leBytes (Bytes.writeAt Z (p + 32) (List.replicate 8 0)) (p + 32) v i) (max n (p + 64)) p :=
    LeInv.leMem ⟨hwf3, hr3, hs3, h80⟩ (by omega)
  refine ⟨leMem M3 (p + 32) v 8, (inv 8 le_rfl).1, ?_, (inv 8 le_rfl).2.2.1, ?_⟩
  · have := (inv 8 le_rfl).2.1
    rwa [leBytes_zeros, hZ, h8, hfpv] at this
  -- the walk
  have m1 := calculateMemoryGasCost_mono (show n ≤ max n (p + 32) by omega)
  have m2 := calculateMemoryGasCost_mono (show max n (p + 32) ≤ max n (p + 64) by omega)
  rw [show G + leGas n p =
    ((((G + 749) + (6 + (calculateMemoryGasCost (max n (p + 64))
      - calculateMemoryGasCost (max n (p + 32))))) + 44)
      + (3 + (calculateMemoryGasCost (max n (p + 32)) - calculateMemoryGasCost n))) + 19 by
    unfold leGas; omega]
  rw [t_14ba_eq]
  unfold lePrefix
  refine rx_dest ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup1 (by simp; omega) ?_
  refine rx_mload (c := 3) (v := pB) ?_ ?_ ?_ (by simp; omega) ?_
  · rw [h64, St.extCost_eq rfl, memExtSize_of_le hn32 hn96, Nat.sub_self]; rfl
  · rw [h64, hr.read, hfp]
  · rw [h64]; exact Mem.read_snd_eq_self (memExtSize_of_le hn32 hn96)
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup1 (by simp; omega) ?_
  refine rx_dup3 (by simp; omega) ?_
  refine rx_mstore (M' := M1) ?_ rfl ?_
  · rw [St.extCost_eq rfl, memExtSize_word_aligned hn32 hp32]; rfl
  refine rx_dup2 (by simp; omega) ?_
  refine rx_dup4 (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap3 ?_
  refine rx_mstore (c := 3) (M' := M2) ?_ (by rw [h64]) ?_
  · rw [h64, St.extCost_eq hs1, memExtSize_of_le (by omega) (by omega), Nat.sub_self]; rfl
  refine rx_push rfl (by simp; omega) ?_
  refine rx_swap2 ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup3 (by simp; omega) ?_
  refine rx_add (by simp; omega) ?_
  refine rx_dup2 (by simp; omega) ?_
  refine rx_dup1 (by simp; omega) ?_
  refine rx_calldatasize (by simp; omega) ?_
  refine rx_dup4 (by simp; omega) ?_
  refine rx_calldatacopy (M' := M3) ?_ ?_ ?_
  · rw [ha, show (Bytes.toB256 [0x08]).toNat = 8 by decide, St.extCost_eq hs2,
      memExtSize_aligned_small (by omega) (by omega) (by decide) (by decide)]
    rw [show max (max n (p + 32)) (p + 32 + 32) = max n (p + 64) by omega]
    rfl
  · rw [ha, hsi, show (Bytes.toB256 [0x08]).toNat = 8 by decide, sliceD_length_self]
  refine rx_add (by simp; omega) ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  refine rx_push rfl (by simp; omega) ?_
  refine rx_dup3 (by simp; omega) ?_
  refine rx_swap1 ?_
  refine rx_shl (v := v <<< 192) (by rw [show (Bytes.toB256 [0xc0]).toNat = 192 by decide])
    (by simp; omega) ?_
  -- the eight byte stores
  refine le_half1 (i := 0) (by decide) (by decide) (by decide) hroom (inv 0 (by omega)).2.1
    (inv 0 (by omega)).2.2.2 (inv 0 (by omega)).2.2.1 hS32 (by omega) ?_
  refine le_mid (i := 0) (by decide) (by decide) (by decide) (by decide) hroom hS32 (by omega) hp
    (inv 0 (by omega)) (inv 1 (by omega)) ?_
  refine le_mid (i := 1) (by decide) (by decide) (by decide) (by decide) hroom hS32 (by omega) hp
    (inv 1 (by omega)) (inv 2 (by omega)) ?_
  refine le_mid (i := 2) (by decide) (by decide) (by decide) (by decide) hroom hS32 (by omega) hp
    (inv 2 (by omega)) (inv 3 (by omega)) ?_
  refine le_mid (i := 3) (by decide) (by decide) (by decide) (by decide) hroom hS32 (by omega) hp
    (inv 3 (by omega)) (inv 4 (by omega)) ?_
  refine le_mid (i := 4) (by decide) (by decide) (by decide) (by decide) hroom hS32 (by omega) hp
    (inv 4 (by omega)) (inv 5 (by omega)) ?_
  refine le_mid (i := 5) (by decide) (by decide) (by decide) (by decide) hroom hS32 (by omega) hp
    (inv 5 (by omega)) (inv 6 (by omega)) ?_
  refine le_mid (i := 6) (by decide) (by decide) (by decide) (by decide) hroom hS32 (by omega) hp
    (inv 6 (by omega)) (inv 7 (by omega)) ?_
  refine le_half2 (i := 7) (by decide) (by decide) hroom (inv 7 (by omega)).2.2.1 hS32
    (by omega) hp ?_
  unfold leTail
  refine rx_pop ?_
  refine rx_swap2 ?_
  refine rx_swap1 ?_
  refine rx_pop ?_
  exact rx_ret

end Blanc.Lift.BeaconDeposit
