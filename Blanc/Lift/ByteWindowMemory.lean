import Blanc.Lift.ExactWalkMemory
import Blanc.Lift.WalkSteps
/-! Covered byte windows preserve the independent free-memory pointer. -/

namespace Blanc.Lift
open Jaune

/-- An arbitrary in-bounds byte write outside the pointer word keeps allocation and pointer. -/
theorem PtrMem.write_bytes_of_le {p : B256} {n : Nat} {M : Mem}
    (h : PtrMem p n M) (i : Nat) (bs : Bytes) (fit : i + bs.length ≤ n)
    (miss : i + bs.length ≤ 64 ∨ 96 ≤ i) :
    PtrMem p n (M.write i bs) := by
  refine ⟨(Mem.size_write_of_le (by rw [h.size]; exact fit)).trans h.size,
    h.n32, h.wf.write _ _, ?_⟩
  intro o av hav
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hav
  cases hav
  have hag := Mem.write_agree M i bs
  refine ⟨le_trans (by rw [h.size]; exact h.ge) hag.1, ?_⟩
  change memWord (M.write i bs) 64 = p
  rw [memWord_congr (μ := M) (fun j hj => hag.2 (64 + j)
    (by rw [h.size]; have := h.ge; omega) (by omega))]
  exact h.word

/-- Reading an arbitrary window grows allocation while preserving the pointer. -/
theorem PtrMem.extend {p : B256} {n : Nat} {M : Mem}
    (h : PtrMem p n M) (i sz : Nat) :
    PtrMem p (memExtSize n i sz) (M.read i sz).2 := by
  refine ⟨?_, memExtSize_mod_32 h.n32, h.wf.extend i sz, ?_⟩
  · change memExtSize M.size i sz = memExtSize n i sz
    rw [h.size]
  · exact MemMatches.of_data_eq (μ := M) (μ' := (M.read i sz).2) rfl
      (memExtSize_ge M.size i sz) h.map

/-- Four high bytes from the source and twenty-eight low bytes from the destination. -/
theorem mergeFour_bytes (x y : B256) :
    let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
    ((x &&& ~~~mask) ||| (y &&& mask)).toBytes = x.toBytes.take 4 ++ y.toBytes.drop 4 := by
  rcases x with ⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩
  rcases y with ⟨⟨y3, y2⟩, ⟨y1, y0⟩⟩
  change (B256.toBytes (⟨⟨(x3 &&& 0xffffffff00000000) ||| (y3 &&& 0xffffffff),
    (x2 &&& 0) ||| (y2 &&& (-1 : UInt64))⟩,
    ⟨(x1 &&& 0) ||| (y1 &&& (-1 : UInt64)),
      (x0 &&& 0) ||| (y0 &&& (-1 : UInt64))⟩⟩ : B256)) = _
  simp only [UInt64.and_zero, UInt64.and_neg_one, UInt64.zero_or]
  have high : (((x3 &&& 0xffffffff00000000) ||| (y3 &&& 0xffffffff)) >>> 32).toUInt32 =
      (x3 >>> 32).toUInt32 := by
    rw [UInt64.shiftRight_or, UInt64.shiftRight_and, UInt64.shiftRight_and,
      UInt64.toUInt32_or, UInt64.toUInt32_and, UInt64.toUInt32_and]
    change ((x3 >>> 32).toUInt32 &&& (-1 : UInt32)) ||| ((y3 >>> 32).toUInt32 &&& 0) = _
    simp only [UInt32.and_neg_one, UInt32.and_zero, UInt32.or_zero]
  have low : ((x3 &&& 0xffffffff00000000) ||| (y3 &&& 0xffffffff)).toUInt32 = y3.toUInt32 := by
    rw [UInt64.toUInt32_or, UInt64.toUInt32_and, UInt64.toUInt32_and]
    change (x3.toUInt32 &&& 0) ||| (y3.toUInt32 &&& (-1 : UInt32)) = _
    simp only [UInt32.and_zero, UInt32.and_neg_one, UInt32.zero_or]
  simp only [B256.toBytes, B128.toBytes, UInt64.toBytes, high, low,
    UInt32.toBytes, UInt16.toBytes, List.cons_append, List.nil_append, List.take, List.drop]

/-- Ordered two-word and four-byte copy, retaining the final destination word's
low bytes. The source's final 32-byte load may overlap earlier destination stores. -/
def copy68Memory (M : Mem) (source target : Nat) : Mem :=
  let N1 := M.write target (Bytes.toB256 (M.read source 32).1).toBytes
  let N2 := N1.write (target + 32) (Bytes.toB256 (N1.read (source + 32) 32).1).toBytes
  let mask := B256.bexp 256 (32 - 4) - 1
  (N2.read (target + 64) 32).2.write (target + 64)
    (((Bytes.toB256 (N2.read (source + 64) 32).1) &&& ~~~mask) |||
      ((Bytes.toB256 (N2.read (target + 64) 32).1) &&& mask)).toBytes

/-- Forward staging preserves all 68 source bytes, including an adjacent
source/destination pair whose padded final source load sees the earlier stores. -/
theorem copy68Memory_read {M : Mem} {source target : Nat}
    (forward : source + 68 ≤ target) :
    ((copy68Memory M source target).read target 68).1 = (M.read source 68).1 := by
  unfold copy68Memory
  dsimp only
  let N0 := M
  let left := Bytes.toB256 (N0.read source 32).1
  let N1 := N0.write target left.toBytes
  let right := Bytes.toB256 (N1.read (source + 32) 32).1
  let N2 := N1.write (target + 32) right.toBytes
  let src := Bytes.toB256 (N2.read (source + 64) 32).1
  let dst := Bytes.toB256 (N2.read (target + 64) 32).1
  let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
  have word0 : left.toBytes = (N0.read source 32).1 :=
    Bytes.toBytes_toB256_of_length (by simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range])
  have word1 : right.toBytes = (N1.read (source + 32) 32).1 :=
    Bytes.toBytes_toB256_of_length (by simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range])
  have word2 : src.toBytes = (N2.read (source + 64) 32).1 :=
    Bytes.toBytes_toB256_of_length (by simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range])
  have merge : (((src &&& ~~~mask) ||| (dst &&& mask)).toBytes) =
      src.toBytes.take 4 ++ dst.toBytes.drop 4 := mergeFour_bytes src dst
  have maskEq : B256.bexp 256 (32 - 4) - 1 = mask := by
    rw [show (32 : B256) - 4 = 28 from rfl]
    have expEq : Nat.powMod 256 28 (2 ^ 256) =
        0x100000000000000000000000000000000000000000000000000000000 := by
      norm_num only [Nat.powMod, Nat.powMod.go, ite_true, ite_false]
    unfold B256.bexp
    change (Nat.powMod 256 28 (2 ^ 256)).toB256 - 1 = mask
    rw [expEq]
    rfl
  rw [maskEq]
  change (((N2.read (target + 64) 32).2.write (target + 64) (((src &&& ~~~mask) ||| (dst &&& mask)).toBytes)).read target 68).1 =
    (N0.read source 68).1
  simp only [Mem.read, Array.sliceD_eq_map]
  apply List.ext_get
  · simp only [List.length_map, List.length_range]
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [Mem.getD_write_below_end _ (target + 64)
      (by intro eq; have len := B256.length_toBytes ((src &&& ~~~mask) ||| (dst &&& mask)); rw [eq] at len; contradiction)
      (by rw [B256.length_toBytes]; omega)]
    by_cases first64 : i < 64
    · rw [ite_eq_right (by omega)]
      change N2.data.getD (target + i) 0 = N0.data.getD (source + i) 0
      rw [Mem.getD_write_below_end N1 (target + 32)
        (by intro eq; have len := B256.length_toBytes right; rw [eq] at len; contradiction)
        (by rw [B256.length_toBytes]; omega)]
      by_cases first32 : i < 32
      · rw [ite_eq_right (by omega), Mem.getD_write_below_end N0 target
          (by intro eq; have len := B256.length_toBytes left; rw [eq] at len; contradiction)
          (by rw [B256.length_toBytes]; omega), ite_eq_left (by omega),
          show target + i - target = i by omega, word0]
        simp only [Mem.read, Array.sliceD_eq_map, List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range, first32, Option.map_some, Option.getD_some]
      · rw [ite_eq_left (by omega), show target + i - (target + 32) = i - 32 by omega, word1]
        have sub : i - 32 < 32 := by omega
        simp only [Mem.read, Array.sliceD_eq_map, List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range, sub, Option.map_some, Option.getD_some]
        rw [Mem.getD_write_below_end N0 target
          (by intro eq; have len := B256.length_toBytes left; rw [eq] at len; contradiction)
          (by rw [B256.length_toBytes]; omega), ite_eq_right (by omega)]
        congr 1; omega
    · rw [ite_eq_left (by omega), show target + i - (target + 64) = i - 64 by omega, merge]
      have sub : i - 64 < 4 := by omega
      have srcLen : src.toBytes.length = 32 := B256.length_toBytes src
      rw [List.getD_append_left (d := (0 : UInt8)) (by simp only [List.length_take, srcLen]; omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [List.length_take, srcLen]; omega)]
      simp only [Option.getD_some, List.getElem_take]
      have index : i - 64 < src.toBytes.length := by rw [srcLen]; omega
      have getEq : src.toBytes.getD (i - 64) 0 = src.toBytes[i - 64] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index]
        rfl
      rw [← getEq, word2]
      simp only [Mem.read, Array.sliceD_eq_map, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range, show i - 64 < 32 by omega,
        Option.map_some, Option.getD_some]
      rw [Mem.getD_write_below_end N1 (target + 32)
        (by intro eq; have len := B256.length_toBytes right; rw [eq] at len; contradiction)
        (by rw [B256.length_toBytes]; omega), ite_eq_right (by omega),
        Mem.getD_write_below_end N0 target
          (by intro eq; have len := B256.length_toBytes left; rw [eq] at len; contradiction)
          (by rw [B256.length_toBytes]; omega), ite_eq_right (by omega)]
      congr 1; omega

/-- A four-byte prefix store preserves the following 64 bytes at any offset. -/
theorem mergeFourMemory_read68 {M : Mem} {offset : Nat} (headWord : B256)
    (wf : Mem.Wf M) :
    let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
    let loaded := Bytes.toB256 (M.read offset 32).1
    ((M.write offset ((headWord &&& ~~~mask) ||| (loaded &&& mask)).toBytes).read offset 68).1 =
      headWord.toBytes.take 4 ++ (M.read (offset + 4) 64).1 := by
  dsimp only
  let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
  let loaded := Bytes.toB256 (M.read offset 32).1
  let merged := (headWord &&& ~~~mask) ||| (loaded &&& mask)
  let lead := headWord.toBytes.take 4
  let tail := (M.read (offset + 4) 64).1
  have leadLen : lead.length = 4 := by
    simp only [lead, List.length_take, B256.length_toBytes]
    rfl
  have tailLen : tail.length = 64 := by
    simp only [tail, Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range]
  have mergeBytes : merged.toBytes = lead ++ ((M.read offset 32).1).drop 4 := by
    rw [mergeFour_bytes, Bytes.toBytes_toB256_of_length
      (by simp only [Mem.read, Array.sliceD_eq_map, List.length_map, List.length_range])]
  have reads := Mem.reads_data M
  have postReads := reads.write wf offset merged.toBytes
  have image : M.data.toList.sliceD (offset + 4) 64 0 = tail := by
    rw [← reads.read]
  change (((M.write offset merged.toBytes).read offset 68).1) =
    lead ++ tail
  simp only [Mem.read, Array.sliceD_eq_map]
  apply List.ext_get
  · simp only [List.length_map, List.length_range, List.length_append, leadLen, tailLen]
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    have rhs : (lead ++ tail).getD i 0 =
        (lead ++ tail)[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    refine Eq.trans ?_ rhs
    rw [postReads (offset + i), Bytes.getD_writeAt]
    by_cases isPrefix : i < 4
    · rw [ite_eq_left (by rw [B256.length_toBytes]; omega),
        show offset + i - offset = i by omega, mergeBytes,
        List.getD_append_left (d := (0 : UInt8)) (by rw [leadLen]; exact isPrefix),
        List.getD_append_left (d := (0 : UInt8)) (by rw [leadLen]; exact isPrefix)]
    · rw [List.getD_append_right (d := (0 : UInt8)) (by rw [leadLen]; omega),
        leadLen]
      have old : M.data.toList.getD (offset + i) 0 =
          tail.getD (i - 4) 0 := by
        have projected := congrArg (fun bs : Bytes => bs.getD (i - 4) 0) image
        rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega)] at projected
        rw [show (offset + 4) + (i - 4) = offset + i by omega] at projected
        exact projected
      by_cases first32 : i < 32
      · rw [ite_eq_left (by rw [B256.length_toBytes]; omega),
          show offset + i - offset = i by omega, mergeBytes,
          List.getD_append_right (d := (0 : UInt8)) (by rw [leadLen]; omega),
          leadLen, List.getD_drop]
        rw [reads.read, Bytes.getD_sliceD_of_lt _ _ _ _ (by omega)]
        rw [show offset + (4 + (i - 4)) = offset + i by omega]
        exact old
      · rw [ite_eq_right (by rw [B256.length_toBytes]; omega)]
        exact old

end Blanc.Lift
