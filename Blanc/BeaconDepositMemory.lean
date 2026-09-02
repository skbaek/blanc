import Blanc.BeaconDeposit
import Blanc.BeaconDepositEncoding
import Blanc.BytesWrite
import Blanc.ForwardMstore8
import Jaune.Types

/-!
# Beacon deposit little-endian memory carriers

Contract-local symbolic images for the runtime's eight-byte little-endian
stores.  The recursive carrier follows the actual `MSTORE8` sequence one byte
at a time; consumers see only the eight-byte specialization and its memory
invariants.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

private def lowBytes : Nat → B256 → Bytes
  | 0, _ => []
  | n + 1, w => w.2.2.toUInt8 :: lowBytes n (w >>> 8)

private def storeLowBytesMemory : Nat → Mem → Nat → B256 → Mem
  | 0, memory, _, _ => memory
  | n + 1, memory, base, word =>
      storeLowBytesMemory n
        (memory.write base [word.2.2.toUInt8]) (base + 1) (word >>> 8)

private def storeLowBytesImage : Nat → Bytes → Nat → B256 → Bytes
  | 0, image, _, _ => image
  | n + 1, image, base, word =>
      storeLowBytesImage n
        (Bytes.writeAt image base [word.2.2.toUInt8])
        (base + 1) (word >>> 8)

@[simp] private theorem lowBytes_length (n : Nat) (word : B256) :
    (lowBytes n word).length = n := by
  induction n generalizing word with
  | zero => rfl
  | succ n ih => simp [lowBytes, ih]

private lemma bytesWriteAt_length (bs : Bytes) (n : Nat) (xs : Bytes) :
    (Bytes.writeAt bs n xs).length = max bs.length (n + xs.length) := by
  simp only [Bytes.writeAt, List.length_append, List.takeD_length,
    List.length_drop]
  omega

private lemma list_ext_getD_of_length_eq
    {α : Type} {left right : List α} (default : α)
    (hlen : left.length = right.length)
    (hget : ∀ i, left.getD i default = right.getD i default) :
    left = right := by
  apply List.ext_get hlen
  intro i hleft hright
  have hi := hget i
  simpa [List.getD, List.get_eq_getElem, hleft, hright] using hi

private lemma bytesWriteAt_single_then
    (image : Bytes) (base : Nat) (byte : UInt8) (tail : Bytes) :
    Bytes.writeAt (Bytes.writeAt image base [byte]) (base + 1) tail =
      Bytes.writeAt image base (byte :: tail) := by
  apply list_ext_getD_of_length_eq 0
  · simp only [bytesWriteAt_length, List.length_cons, List.length_nil]
    omega
  · intro i
    rw [Bytes.getD_writeAt, Bytes.getD_writeAt, Bytes.getD_writeAt]
    simp only [List.length_cons, List.length_nil]
    by_cases hi : i < base
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · by_cases hieq : i = base
      · subst i
        simp
      · have hgt : base + 1 ≤ i := by omega
        by_cases htail : i < base + 1 + tail.length
        · rw [if_pos ⟨hgt, htail⟩, if_pos (by omega)]
          have hsub : i - base = (i - (base + 1)) + 1 := by omega
          rw [hsub]
          rfl
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

private theorem storeLowBytesImage_eq
    {n : Nat} {image : Bytes} {base : Nat} {word : B256} (hn : 0 < n) :
    storeLowBytesImage n image base word =
      Bytes.writeAt image base (lowBytes n word) := by
  induction n generalizing image base word with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          rw [storeLowBytesImage, lowBytes]
          rw [ih (by omega)]
          exact bytesWriteAt_single_then image base word.2.2.toUInt8
            (lowBytes (n + 1) (word >>> 8))

/-- Memory after writing the low 64 bits of `word` little-endian at `base`. -/
def storeLe64Memory (memory : Mem) (base : Nat) (word : B256) : Mem :=
  storeLowBytesMemory 8 memory base word

/-- Symbolic image corresponding to `storeLe64Memory`. -/
def storeLe64Image (image : Bytes) (base : Nat) (word : B256) : Bytes :=
  storeLowBytesImage 8 image base word

private theorem storeLe64Image_eq_writeAt
    (image : Bytes) (base : Nat) (word : B256) :
    storeLe64Image image base word =
      Bytes.writeAt image base (lowBytes 8 word) := by
  exact storeLowBytesImage_eq (by omega)

private lemma Nat.shiftLeft_mod_two_pow_eq_zero
    (x k n : Nat) (h : n ≤ k) : (x <<< k) % 2 ^ n = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  simp only [Nat.shiftLeft_eq]
  exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 h) x

private lemma lowByte_eq (word : B256) :
    word.2.2.toUInt8 = word.toNat.toUInt8 := by
  rcases word with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  rw [← UInt8.toNat_inj]
  simp only [UInt64.toNat_toUInt8, Nat.toUInt8_eq,
    B256.toNat, B128.toNat]
  change d.toNat % 2 ^ 8 =
    (((a.toNat <<< 64 ||| b.toNat) <<< 128) |||
      (c.toNat <<< 64 ||| d.toNat)) % 2 ^ 8
  simp only [Nat.or_mod_two_pow]
  rw [Nat.shiftLeft_mod_two_pow_eq_zero _ _ _ (by omega)]
  rw [Nat.shiftLeft_mod_two_pow_eq_zero _ _ _ (by omega)]
  simp

private lemma concat_shr_eight_nat
    (x y width : Nat) (hwidth : 8 ≤ width) :
    (x >>> 8 <<< width) |||
        ((x <<< (width - 8)) % 2 ^ width ||| y >>> 8) =
      ((x <<< width) ||| y) >>> 8 := by
  rw [Nat.shiftRight_or_distrib]
  have hshift : (x <<< width) >>> 8 = x <<< (width - 8) := by
    conv_lhs => rw [show width = (width - 8) + 8 by omega]
    rw [Nat.shiftLeft_add, Nat.shiftLeft_shiftRight]
  rw [hshift]
  have hsplit := Jaune.Nat.hi_or_lo x 8
  simp only [Jaune.Nat.hi, Jaune.Nat.lo] at hsplit
  have hsplit' := congrArg (fun z : Nat => z <<< (width - 8)) hsplit
  simp only [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add] at hsplit'
  rw [show 8 + (width - 8) = width by omega] at hsplit'
  have hlo := Jaune.Nat.lo_shl (k := x) (m := 8) (n := width - 8)
  simp only [Jaune.Nat.lo] at hlo
  rw [show 8 + (width - 8) = width by omega] at hlo
  rw [← hlo]
  rw [← Nat.or_assoc, hsplit']

private lemma concat_shr_eight (x y : UInt64) :
    ((x >>> UInt64.ofNat 8).toNat <<< 64) |||
      ((x <<< UInt64.ofNat 56 ||| y >>> UInt64.ofNat 8).toNat) =
      ((x.toNat <<< 64) ||| y.toNat) >>> 8 := by
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft,
    UInt64.toNat_or]
  norm_num
  exact concat_shr_eight_nat x.toNat y.toNat 64 (by omega)

private lemma B128.toNat_or (x y : B128) :
    (B128.or x y).toNat = x.toNat ||| y.toNat := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp only [B128.or, B128.toNat, UInt64.toNat_or,
    Nat.shiftLeft_or_distrib]
  let A := a.toNat <<< 64
  let B := b.toNat
  let C := c.toNat <<< 64
  let D := d.toNat
  change (A ||| C) ||| (B ||| D) = (A ||| B) ||| (C ||| D)
  calc
    (A ||| C) ||| (B ||| D) = A ||| ((C ||| B) ||| D) := by
      rw [Nat.or_assoc A C (B ||| D), Nat.or_assoc C B D]
    _ = A ||| ((B ||| C) ||| D) := by
      rw [Nat.or_comm C B]
    _ = (A ||| B) ||| (C ||| D) := by
      rw [Nat.or_assoc B C D, Nat.or_assoc A B (C ||| D)]

private lemma B128.toNat_shift_eight (word : B128) :
    (B128.shiftRight word 8).toNat = word.toNat >>> 8 := by
  rcases word with ⟨x, y⟩
  simp only [B128.shiftRight]
  norm_num
  simp only [B128.toNat]
  exact concat_shr_eight x y

private lemma B128.toNat_shiftLeft_120 (word : B128) :
    (B128.shiftLeft word 120).toNat =
      (word.toNat <<< 120) % 2 ^ 128 := by
  rcases word with ⟨a, b⟩
  simp only [B128.shiftLeft]
  norm_num
  simp only [B128.toNat]
  have hlow :
      ((a.toNat <<< 64) ||| b.toNat) % 2 ^ 8 =
        b.toNat % 2 ^ 8 := by
    rw [Nat.or_mod_two_pow]
    rw [Nat.shiftLeft_mod_two_pow_eq_zero _ _ _ (by omega)]
    simp
  have hb56 := Jaune.Nat.lo_shl (k := b.toNat) (m := 8) (n := 56)
  simp only [Jaune.Nat.lo] at hb56
  norm_num at hb56
  have hw120 := Jaune.Nat.lo_shl
    (k := (a.toNat <<< 64) ||| b.toNat) (m := 8) (n := 120)
  simp only [Jaune.Nat.lo] at hw120
  norm_num at hw120 hlow
  simp only [UInt64.toNat_shiftLeft]
  norm_num
  rw [← hw120, hlow, ← hb56, ← Nat.shiftLeft_add]

private lemma B256.toNat_shift_eight (word : B256) :
    (word >>> 8).toNat = word.toNat >>> 8 := by
  rcases word with ⟨x, y⟩
  change (B256.shiftRight (x, y) 8).toNat =
    B256.toNat (x, y) >>> 8
  simp only [B256.shiftRight]
  norm_num
  change
    ((B128.shiftRight x 8).toNat <<< 128 |||
      (B128.or (B128.shiftLeft x 120)
        (B128.shiftRight y 8)).toNat) =
      ((x.toNat <<< 128) ||| y.toNat) >>> 8
  rw [B128.toNat_shift_eight, B128.toNat_or,
    B128.toNat_shiftLeft_120, B128.toNat_shift_eight]
  exact concat_shr_eight_nat x.toNat y.toNat 128 (by omega)

private def lowBytesNat : Nat → Nat → Bytes
  | 0, _ => []
  | n + 1, word => word.toUInt8 :: lowBytesNat n (word >>> 8)

private lemma lowBytes_eq_lowBytesNat : ∀ n word,
    lowBytes n word = lowBytesNat n word.toNat
  | 0, _ => rfl
  | n + 1, word => by
      simp only [lowBytes, lowBytesNat]
      rw [lowByte_eq, lowBytes_eq_lowBytesNat,
        B256.toNat_shift_eight]

private theorem lowBytes_eight_eq_le64 (word : B256) :
    lowBytes 8 word = le64 word.toNat := by
  rw [lowBytes_eq_lowBytesNat]
  simp [lowBytesNat, le64, ← Nat.shiftRight_add]

theorem storeLe64Image_eq_le64
    (image : Bytes) (base : Nat) (word : B256) :
    storeLe64Image image base word =
      Bytes.writeAt image base (le64 word.toNat) := by
  rw [storeLe64Image_eq_writeAt, lowBytes_eight_eq_le64]

private theorem storeLowBytes_inv
    (n : Nat) {memory : Mem} {image : Bytes} {base : Nat} {word : B256}
    (hwf : Mem.Wf memory) (hreads : Mem.Reads memory image) :
    Mem.Wf (storeLowBytesMemory n memory base word) ∧
      Mem.Reads (storeLowBytesMemory n memory base word)
        (storeLowBytesImage n image base word) := by
  induction n generalizing memory image base word with
  | zero => exact ⟨hwf, hreads⟩
  | succ n ih =>
      exact ih (Mem.Wf.write hwf _ _)
        (Mem.Reads.write hwf hreads _ _)

theorem storeLe64Memory_inv
    {memory : Mem} {image : Bytes} {base : Nat} {word : B256}
    (hwf : Mem.Wf memory) (hreads : Mem.Reads memory image) :
    Mem.Wf (storeLe64Memory memory base word) ∧
      Mem.Reads (storeLe64Memory memory base word)
        (storeLe64Image image base word) := by
  exact storeLowBytes_inv 8 hwf hreads

private theorem storeLowBytesMemory_size_of_le
    (n : Nat) {memory : Mem} {base : Nat} {word : B256}
    (hfit : base + n ≤ memory.size) :
    (storeLowBytesMemory n memory base word).size = memory.size := by
  induction n generalizing memory base word with
  | zero => rfl
  | succ n ih =>
      have hone :
          (memory.write base [word.2.2.toUInt8]).size = memory.size := by
        rw [Mem.size_write_of_le]
        simp only [List.length_cons, List.length_nil]
        omega
      rw [storeLowBytesMemory, ih (by rw [hone]; omega), hone]

theorem storeLe64Memory_size_of_le
    {memory : Mem} {base : Nat} {word : B256}
    (hfit : base + 8 ≤ memory.size) :
    (storeLe64Memory memory base word).size = memory.size := by
  exact storeLowBytesMemory_size_of_le 8 hfit

/-! ## The fixed dynamic-bytes return header -/

def getDepositCountHeaderMemory : Mem :=
  ((Mem.empty.write 0 (32 : B256).toBytes)
      |>.write 32 (8 : B256).toBytes)
    |>.write 64 (0 : B256).toBytes

def getDepositCountHeaderImage : Bytes :=
  ((Bytes.writeAt [] 0 (32 : B256).toBytes)
      |> fun image => Bytes.writeAt image 32 (8 : B256).toBytes)
    |> fun image => Bytes.writeAt image 64 (0 : B256).toBytes

theorem getDepositCountHeaderImage_eq :
    getDepositCountHeaderImage =
      (32 : B256).toBytes ++ (8 : B256).toBytes ++
        (0 : B256).toBytes := by
  decide +kernel

theorem getDepositCountHeaderMemory_spec :
    Mem.Wf getDepositCountHeaderMemory ∧
      Mem.Reads getDepositCountHeaderMemory getDepositCountHeaderImage ∧
      getDepositCountHeaderMemory.size = 96 ∧
      getDepositCountHeaderMemory.size % 32 = 0 := by
  let M0 := Mem.empty
  let I0 : Bytes := []
  let M1 := M0.write 0 (32 : B256).toBytes
  let I1 := Bytes.writeAt I0 0 (32 : B256).toBytes
  let M2 := M1.write 32 (8 : B256).toBytes
  let I2 := Bytes.writeAt I1 32 (8 : B256).toBytes
  let M3 := M2.write 64 (0 : B256).toBytes
  let I3 := Bytes.writeAt I2 64 (0 : B256).toBytes
  have hwf0 : Mem.Wf M0 := Mem.wf_empty
  have hreads0 : Mem.Reads M0 I0 := Mem.reads_empty
  have hwf1 : Mem.Wf M1 := hwf0.write _ _
  have hreads1 : Mem.Reads M1 I1 := Mem.Reads.write hwf0 hreads0 _ _
  have hwf2 : Mem.Wf M2 := hwf1.write _ _
  have hreads2 : Mem.Reads M2 I2 := Mem.Reads.write hwf1 hreads1 _ _
  have hwf3 : Mem.Wf M3 := hwf2.write _ _
  have hreads3 : Mem.Reads M3 I3 := Mem.Reads.write hwf2 hreads2 _ _
  have hsize1 : M1.size = 32 := by
    dsimp only [M1, M0]
    rw [Mem.size_write_word_at]
    decide +kernel
  have hsize2 : M2.size = 64 := by
    dsimp only [M2]
    rw [Mem.size_write_word_at, hsize1]
    decide +kernel
  have hsize3 : M3.size = 96 := by
    dsimp only [M3]
    rw [Mem.size_write_word_at, hsize2]
    decide +kernel
  change Mem.Wf M3 ∧ Mem.Reads M3 I3 ∧
    M3.size = 96 ∧ M3.size % 32 = 0
  exact ⟨hwf3, hreads3, hsize3, by rw [hsize3]⟩

def getDepositCountResultMemory (word : B256) : Mem :=
  storeLe64Memory getDepositCountHeaderMemory 64 word

def getDepositCountResultImage (word : B256) : Bytes :=
  storeLe64Image getDepositCountHeaderImage 64 word

theorem getDepositCountResultImage_eq (word : B256) :
    getDepositCountResultImage word =
      abiDynamicBytesReturn (le64 word.toNat) := by
  rw [getDepositCountResultImage, storeLe64Image_eq_le64,
    getDepositCountHeaderImage_eq,
    abiDynamicBytesReturn_le64_eq]
  have hzero :
      (0 : B256).toBytes =
        List.replicate 8 0 ++ List.replicate 24 0 := by
    decide +kernel
  rw [hzero]
  have h := Bytes.writeAt_append_middle_at
    (pre := (32 : B256).toBytes ++ (8 : B256).toBytes)
    (old := List.replicate 8 0)
    (suffix := List.replicate 24 0)
    (replacement := le64 word.toNat)
    (offset := 64)
    (by simp [B256.length_toBytes])
    (by simp [le64])
  simpa only [List.append_assoc] using h

/-- The exact symbolic memory image handed to the count endpoint's return. -/
structure GetDepositCountMemoryCarrier
    (memory : Mem) (word : B256) : Prop where
  wf : Mem.Wf memory
  reads :
    Mem.Reads memory (abiDynamicBytesReturn (le64 word.toNat))
  size_eq : memory.size = 96
  size_mod : memory.size % 32 = 0

theorem getDepositCountResultMemory_spec (word : B256) :
    GetDepositCountMemoryCarrier (getDepositCountResultMemory word) word := by
  rcases getDepositCountHeaderMemory_spec with
    ⟨hwf, hreads, hsize, hmod⟩
  have hinv := storeLe64Memory_inv
    (word := word) (base := 64) hwf hreads
  have hresultReads :
      Mem.Reads (getDepositCountResultMemory word)
        (getDepositCountResultImage word) := by
    exact hinv.2
  have hresultSize : (getDepositCountResultMemory word).size = 96 := by
    unfold getDepositCountResultMemory
    rw [storeLe64Memory_size_of_le (by rw [hsize]; omega), hsize]
  exact ⟨hinv.1, by
    rw [getDepositCountResultImage_eq] at hresultReads
    exact hresultReads,
    hresultSize, by rw [hresultSize]⟩

/-! ## Small compiled carriers for the count return -/

private theorem return96_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {image : Bytes} (G : Nat)
    (hreads : Mem.Reads memory image)
    (hsize : memory.size = 96)
    (hmod : memory.size % 32 = 0)
    (hlen : image.length = 96) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G + 5⟩)
      (returnMemoryRange 0 96)
      ((base.setMach ⟨[], memory, G⟩).withOutput image) := by
  let returnPre := base.setMach ⟨[(0 : B256), (96 : B256)], memory, G⟩
  have hext : returnPre.extCost [⟨(0 : Nat), (96 : Nat)⟩] = 0 := by
    apply Devm.extCost_zero_of_le
    · exact hmod
    · rw [hsize]
  have hread :
      (returnPre.setMach ⟨[], returnPre.memory, G⟩).memRead 0 96 =
        ⟨image, base.setMach ⟨[], memory, G⟩⟩ := by
    apply Prod.ext
    · change (memory.read 0 96).1 = image
      rw [Mem.Reads.read hreads]
      unfold List.sliceD
      rw [List.drop_zero, List.takeD_eq_take _ (by omega),
        List.take_of_length_le (by omega)]
    · change
        (base.setMach ⟨[], (memory.read 0 96).2, G⟩) =
          base.setMach ⟨[], memory, G⟩
      rw [Mem.read_snd_eq_self
        (memExtSize_of_le hmod (by rw [hsize]))]
  unfold returnMemoryRange pushList
  func_run (2) []
  change Func.RunCompiled fs sevm returnPre Func.return_
    ((base.setMach ⟨[], memory, G⟩).withOutput image)
  exact Func.runCompiled_return_of (devm := returnPre) (G := G) (e := 0)
    rfl hext
    (by simp only [returnPre, Devm.gasLeft_setMach, Nat.add_zero])
    hread

/-! ## Small compiled carriers for the `MSTORE8` chain -/

private theorem storeByteShiftStack_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {word i : B256} {G : Nat} {rest : Func}
    {stack : List B256}
    (hsize32 : memory.size % 32 = 0)
    (hfit : i.toNat + 1 ≤ memory.size)
    (hpush : pushCost i.toBytes.sig = gVerylow)
    (hroom : stack.length + 2 < 1024)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨(word >>> 8) :: stack,
          memory.write i.toNat [word.2.2.toUInt8], G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨word :: stack, memory, G + 15⟩)
      (dup 0 ::: pushB256 i ::: mstore8 :::
        pushB256 8 ::: shr ::: rest)
      post := by
  apply Func.RunCompiled.next
  · exact Ninst.runCompiled_dup (n := 0) (w := word) (G := G + 12) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_pushB256 (G := G + 9) hpush
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    · simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.RunCompiled.next
      · exact Ninst.runCompiled_mstore8_of
          (i := i) (v := word) (s := word :: stack) (G := G + 6) (e := 0)
          rfl
          (Devm.extCost_zero_of_le hsize32 hfit)
          (by simp only [Devm.gasLeft_setMach, gVerylow])
          rfl
      · simp only [Devm.setMach_setMach, Devm.memory_setMach]
        apply Func.RunCompiled.next
        · exact Ninst.runCompiled_pushB256 (w := 8) (c := gVerylow)
            (G := G + 3) (by decide +kernel)
            (by simp only [Devm.gasLeft_setMach, gVerylow])
            (by simp only [Devm.stack_setMach, List.length_cons]; omega)
        · simp only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach]
          apply Func.RunCompiled.next
          · exact Ninst.runCompiled_binary
              (r := .shr) (f := fun x y => y >>> x.toNat)
              (cost := gVerylow) (G := G) (x := 8) (y := word)
              (v := word >>> 8) (s := stack)
              (by rintro ⟨⟩) rfl rfl
              (by simp only [show (8 : B256).toNat = 8 by decide +kernel])
              (by simp only [Devm.gasLeft_setMach, gVerylow])
              (by omega)
          · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using
              hrest

private theorem storeByteLastStack_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {word i : B256} {G : Nat} {rest : Func}
    {stack : List B256}
    (hsize32 : memory.size % 32 = 0)
    (hfit : i.toNat + 1 ≤ memory.size)
    (hpush : pushCost i.toBytes.sig = gVerylow)
    (hroom : stack.length + 1 < 1024)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, memory.write i.toNat [word.2.2.toUInt8], G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨word :: stack, memory, G + 6⟩)
      (pushB256 i ::: mstore8 ::: rest)
      post := by
  apply Func.RunCompiled.next
  · exact Ninst.runCompiled_pushB256 (G := G + 3) hpush
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.RunCompiled.next
    · exact Ninst.runCompiled_mstore8_of
        (i := i) (v := word) (s := stack) (G := G) (e := 0)
        rfl
        (Devm.extCost_zero_of_le hsize32 hfit)
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        rfl
    · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hrest

/-- Execute `storeLe64At` at any non-wrapping concrete address.  The
continuation may retain an arbitrary tail stack; the chain costs exactly 111
gas and preserves the existing logical memory size. -/
theorem storeLe64At_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {word address : B256} {offset G : Nat}
    {rest : Func} {stack : List B256}
    (hsize32 : memory.size % 32 = 0)
    (hfit : offset + 8 ≤ memory.size)
    (hroom : stack.length + 2 < 1024)
    (hnat0 : address.toNat = offset)
    (hnat1 : (address + 1).toNat = offset + 1)
    (hnat2 : (address + 2).toNat = offset + 2)
    (hnat3 : (address + 3).toNat = offset + 3)
    (hnat4 : (address + 4).toNat = offset + 4)
    (hnat5 : (address + 5).toNat = offset + 5)
    (hnat6 : (address + 6).toNat = offset + 6)
    (hnat7 : (address + 7).toNat = offset + 7)
    (hpush0 : pushCost address.toBytes.sig = gVerylow)
    (hpush1 : pushCost (address + 1).toBytes.sig = gVerylow)
    (hpush2 : pushCost (address + 2).toBytes.sig = gVerylow)
    (hpush3 : pushCost (address + 3).toBytes.sig = gVerylow)
    (hpush4 : pushCost (address + 4).toBytes.sig = gVerylow)
    (hpush5 : pushCost (address + 5).toBytes.sig = gVerylow)
    (hpush6 : pushCost (address + 6).toBytes.sig = gVerylow)
    (hpush7 : pushCost (address + 7).toBytes.sig = gVerylow)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨stack, storeLe64Memory memory offset word, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨word :: stack, memory, G + 111⟩)
      (storeLe64At address +++ rest) post := by
  let M0 := memory
  let M1 := M0.write address.toNat [word.2.2.toUInt8]
  let M2 := M1.write (address + 1).toNat [(word >>> 8).2.2.toUInt8]
  let M3 := M2.write (address + 2).toNat
    [(word >>> 8 >>> 8).2.2.toUInt8]
  let M4 := M3.write (address + 3).toNat
    [(word >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M5 := M4.write (address + 4).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M6 := M5.write (address + 5).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M7 := M6.write (address + 6).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M8 := M7.write (address + 7).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  have hsize1 : M1.size = memory.size := by
    dsimp only [M1, M0]
    rw [Mem.size_write_of_le (by
      rw [hnat0]
      simp only [List.length_cons, List.length_nil]
      omega)]
  have hsize2 : M2.size = memory.size := by
    dsimp only [M2]
    rw [Mem.size_write_of_le (by
      rw [hnat1, hsize1]
      simp only [List.length_cons, List.length_nil]
      omega), hsize1]
  have hsize3 : M3.size = memory.size := by
    dsimp only [M3]
    rw [Mem.size_write_of_le (by
      rw [hnat2, hsize2]
      simp only [List.length_cons, List.length_nil]
      omega), hsize2]
  have hsize4 : M4.size = memory.size := by
    dsimp only [M4]
    rw [Mem.size_write_of_le (by
      rw [hnat3, hsize3]
      simp only [List.length_cons, List.length_nil]
      omega), hsize3]
  have hsize5 : M5.size = memory.size := by
    dsimp only [M5]
    rw [Mem.size_write_of_le (by
      rw [hnat4, hsize4]
      simp only [List.length_cons, List.length_nil]
      omega), hsize4]
  have hsize6 : M6.size = memory.size := by
    dsimp only [M6]
    rw [Mem.size_write_of_le (by
      rw [hnat5, hsize5]
      simp only [List.length_cons, List.length_nil]
      omega), hsize5]
  have hsize7 : M7.size = memory.size := by
    dsimp only [M7]
    rw [Mem.size_write_of_le (by
      rw [hnat6, hsize6]
      simp only [List.length_cons, List.length_nil]
      omega), hsize6]
  have hM8 : M8 = storeLe64Memory memory offset word := by
    dsimp only [M8, M7, M6, M5, M4, M3, M2, M1, M0]
    rw [hnat0, hnat1, hnat2, hnat3, hnat4, hnat5, hnat6, hnat7]
    rfl
  have htail : Func.RunCompiled fs sevm
      (base.setMach ⟨stack, M8, G⟩) rest post := by
    rw [hM8]
    exact hrest
  unfold storeLe64At
  apply storeByteShiftStack_runCompiled
      (memory := M0) (word := word) (i := address) (G := G + 96)
      (stack := stack)
  · simpa only [M0] using hsize32
  · rw [hnat0]; dsimp only [M0]; omega
  · exact hpush0
  · exact hroom
  apply storeByteShiftStack_runCompiled
      (memory := M1) (word := word >>> 8) (i := address + 1)
      (G := G + 81) (stack := stack)
  · rw [hsize1]; exact hsize32
  · rw [hnat1, hsize1]; omega
  · exact hpush1
  · exact hroom
  apply storeByteShiftStack_runCompiled
      (memory := M2) (word := word >>> 8 >>> 8) (i := address + 2)
      (G := G + 66) (stack := stack)
  · rw [hsize2]; exact hsize32
  · rw [hnat2, hsize2]; omega
  · exact hpush2
  · exact hroom
  apply storeByteShiftStack_runCompiled
      (memory := M3) (word := word >>> 8 >>> 8 >>> 8) (i := address + 3)
      (G := G + 51) (stack := stack)
  · rw [hsize3]; exact hsize32
  · rw [hnat3, hsize3]; omega
  · exact hpush3
  · exact hroom
  apply storeByteShiftStack_runCompiled
      (memory := M4) (word := word >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 4) (G := G + 36) (stack := stack)
  · rw [hsize4]; exact hsize32
  · rw [hnat4, hsize4]; omega
  · exact hpush4
  · exact hroom
  apply storeByteShiftStack_runCompiled
      (memory := M5) (word := word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 5) (G := G + 21) (stack := stack)
  · rw [hsize5]; exact hsize32
  · rw [hnat5, hsize5]; omega
  · exact hpush5
  · exact hroom
  apply storeByteShiftStack_runCompiled
      (memory := M6)
      (word := word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 6) (G := G + 6) (stack := stack)
  · rw [hsize6]; exact hsize32
  · rw [hnat6, hsize6]; omega
  · exact hpush6
  · exact hroom
  apply storeByteLastStack_runCompiled
      (memory := M7)
      (word := word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 7) (G := G) (stack := stack)
  · rw [hsize7]; exact hsize32
  · rw [hnat7, hsize7]; omega
  · exact hpush7
  · omega
  · exact htail

/-- The exact 111-gas compiled `storeLe64At 64` suffix used by the count
endpoint.  The continuation sees the canonical 96-byte dynamic-return image. -/
theorem storeLe64At64_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {word : B256} {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], getDepositCountResultMemory word, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[word], getDepositCountHeaderMemory, G + 111⟩)
      (storeLe64At 64 +++ rest) post := by
  exact storeLe64At_runCompiled
    (memory := getDepositCountHeaderMemory)
    (address := 64) (offset := 64) (stack := [])
    getDepositCountHeaderMemory_spec.2.2.2
    (by rw [getDepositCountHeaderMemory_spec.2.2.1]; omega)
    (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    hrest

/-- The root endpoint's exact 111-gas little-endian store at byte 32. -/
theorem storeLe64At32_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {memory : Mem} {word : B256} {G : Nat} {rest : Func}
    (hsize32 : memory.size % 32 = 0)
    (hfit : 32 + 8 ≤ memory.size)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], storeLe64Memory memory 32 word, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[word], memory, G + 111⟩)
      (storeLe64At 32 +++ rest) post := by
  exact storeLe64At_runCompiled
    (memory := memory) (address := 32) (offset := 32) (stack := [])
    hsize32 hfit
    (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    hrest

/-- Build the three-word ABI dynamic-bytes header in exactly 34 gas. -/
theorem getDepositCountHeader_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {G : Nat} {rest : Func}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], getDepositCountHeaderMemory, G⟩)
      rest post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + 34⟩)
      (pushB256 32 ::: mstoreAt 0 +++
       pushB256 8 ::: mstoreAt 1 +++
       pushB256 0 ::: mstoreAt 2 +++ rest) post := by
  apply Func.RunCompiled.next
  · exact Ninst.runCompiled_pushB256 (w := 32) (c := gVerylow)
      (G := G + 31) (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    func_run (2) [3]
    · exact Devm.extCost_empty_word
    · apply Func.RunCompiled.next
      · exact Ninst.runCompiled_pushB256 (w := 8) (c := gVerylow)
          (G := G + 20) (by decide +kernel)
          (by simp only [Devm.gasLeft_setMach, gVerylow]; omega)
          (by simp only [Devm.stack_setMach, List.length_nil]; omega)
      · simp only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach]
        func_run (2) [3]
        · exact Devm.extCost_of_size (n := 32) rfl
            (by decide +kernel)
        · apply Func.RunCompiled.next
          · exact Ninst.runCompiled_pushB256 (w := 0) (c := gBase)
              (G := G + 9) pushCost_zero
              (by simp only [Devm.gasLeft_setMach, gBase]; omega)
              (by simp only [Devm.stack_setMach, List.length_nil]; omega)
          · simp only [Devm.setMach_setMach, Devm.stack_setMach,
              Devm.memory_setMach]
            func_run (2) [3]
            · exact Devm.extCost_of_size (n := 64) rfl
                (by decide +kernel)
            · have hzero : ((0 : B256) * 32).toNat = 0 := by
                decide +kernel
              have hone : ((1 : B256) * 32).toNat = 32 := by
                decide +kernel
              have htwo : ((2 : B256) * 32).toNat = 64 := by
                decide +kernel
              have hgas : G + 9 - 9 = G := by omega
              simpa only [getDepositCountHeaderMemory,
                prepend, Devm.setMach_setMach, Devm.stack_setMach,
                Devm.memory_setMach, Devm.gasLeft_setMach,
                hzero, hone, htwo, hgas] using hrest

/-- Return the canonical count image without memory expansion, in five gas. -/
theorem getDepositCountReturn_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    (word : B256) (G : Nat) :
    Func.RunCompiled fs sevm
      (base.setMach
        ⟨[], getDepositCountResultMemory word, G + 5⟩)
      (returnMemoryRange 0 96)
      ((base.setMach
        ⟨[], getDepositCountResultMemory word, G⟩).withOutput
          (abiDynamicBytesReturn (le64 word.toNat))) := by
  have carrier := getDepositCountResultMemory_spec word
  exact return96_runCompiled G
    carrier.reads carrier.size_eq carrier.size_mod
    (abiDynamicBytesReturn_le64_length word.toNat)

/-! ## Outcome-general little-endian store carrier -/

private theorem storeByteShiftStack_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {word i : B256} {G : Nat} {rest : Func}
    {stack : List B256} {ex : Execution}
    (hsize32 : memory.size % 32 = 0)
    (hfit : i.toNat + 1 ≤ memory.size)
    (hpush : pushCost i.toBytes.sig = gVerylow)
    (hroom : stack.length + 2 < 1024)
    (hrest : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨(word >>> 8) :: stack,
          memory.write i.toNat [word.2.2.toUInt8], G⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨word :: stack, memory, G + 15⟩)
      (dup 0 ::: pushB256 i ::: mstore8 :::
        pushB256 8 ::: shr ::: rest)
      ex := by
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_dup (n := 0) (w := word) (G := G + 12) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.RunCompiledTo.next
    · exact Ninst.runCompiled_pushB256 (G := G + 9) hpush
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        (by simp only [Devm.stack_setMach, List.length_cons]; omega)
    · simp only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach]
      apply Func.RunCompiledTo.next
      · exact Ninst.runCompiled_mstore8_of
          (i := i) (v := word) (s := word :: stack) (G := G + 6) (e := 0)
          rfl
          (Devm.extCost_zero_of_le hsize32 hfit)
          (by simp only [Devm.gasLeft_setMach, gVerylow])
          rfl
      · simp only [Devm.setMach_setMach, Devm.memory_setMach]
        apply Func.RunCompiledTo.next
        · exact Ninst.runCompiled_pushB256 (w := 8) (c := gVerylow)
            (G := G + 3) (by decide +kernel)
            (by simp only [Devm.gasLeft_setMach, gVerylow])
            (by simp only [Devm.stack_setMach, List.length_cons]; omega)
        · simp only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach]
          apply Func.RunCompiledTo.next
          · exact Ninst.runCompiled_binary
              (r := .shr) (f := fun x y => y >>> x.toNat)
              (cost := gVerylow) (G := G) (x := 8) (y := word)
              (v := word >>> 8) (s := stack)
              (by rintro ⟨⟩) rfl rfl
              (by simp only [show (8 : B256).toNat = 8 by decide +kernel])
              (by simp only [Devm.gasLeft_setMach, gVerylow])
              (by omega)
          · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using
              hrest

private theorem storeByteLastStack_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {word i : B256} {G : Nat} {rest : Func}
    {stack : List B256} {ex : Execution}
    (hsize32 : memory.size % 32 = 0)
    (hfit : i.toNat + 1 ≤ memory.size)
    (hpush : pushCost i.toBytes.sig = gVerylow)
    (hroom : stack.length + 1 < 1024)
    (hrest : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory.write i.toNat [word.2.2.toUInt8], G⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨word :: stack, memory, G + 6⟩)
      (pushB256 i ::: mstore8 ::: rest)
      ex := by
  apply Func.RunCompiledTo.next
  · exact Ninst.runCompiled_pushB256 (G := G + 3) hpush
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)
  · simp only [Devm.setMach_setMach, Devm.stack_setMach,
      Devm.memory_setMach]
    apply Func.RunCompiledTo.next
    · exact Ninst.runCompiled_mstore8_of
        (i := i) (v := word) (s := stack) (G := G) (e := 0)
        rfl
        (Devm.extCost_zero_of_le hsize32 hfit)
        (by simp only [Devm.gasLeft_setMach, gVerylow])
        rfl
    · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hrest

/-- Execute `storeLe64At` before an arbitrary final `Execution`.  This is the
outcome-general sibling of `storeLe64At_runCompiled`; it is needed by prefixes
whose later guards can still revert. -/
theorem storeLe64At_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {word address : B256} {offset G : Nat}
    {rest : Func} {stack : List B256} {ex : Execution}
    (hsize32 : memory.size % 32 = 0)
    (hfit : offset + 8 ≤ memory.size)
    (hroom : stack.length + 2 < 1024)
    (hnat0 : address.toNat = offset)
    (hnat1 : (address + 1).toNat = offset + 1)
    (hnat2 : (address + 2).toNat = offset + 2)
    (hnat3 : (address + 3).toNat = offset + 3)
    (hnat4 : (address + 4).toNat = offset + 4)
    (hnat5 : (address + 5).toNat = offset + 5)
    (hnat6 : (address + 6).toNat = offset + 6)
    (hnat7 : (address + 7).toNat = offset + 7)
    (hpush0 : pushCost address.toBytes.sig = gVerylow)
    (hpush1 : pushCost (address + 1).toBytes.sig = gVerylow)
    (hpush2 : pushCost (address + 2).toBytes.sig = gVerylow)
    (hpush3 : pushCost (address + 3).toBytes.sig = gVerylow)
    (hpush4 : pushCost (address + 4).toBytes.sig = gVerylow)
    (hpush5 : pushCost (address + 5).toBytes.sig = gVerylow)
    (hpush6 : pushCost (address + 6).toBytes.sig = gVerylow)
    (hpush7 : pushCost (address + 7).toBytes.sig = gVerylow)
    (hrest : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, storeLe64Memory memory offset word, G⟩)
      rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨word :: stack, memory, G + 111⟩)
      (storeLe64At address +++ rest) ex := by
  let M0 := memory
  let M1 := M0.write address.toNat [word.2.2.toUInt8]
  let M2 := M1.write (address + 1).toNat [(word >>> 8).2.2.toUInt8]
  let M3 := M2.write (address + 2).toNat
    [(word >>> 8 >>> 8).2.2.toUInt8]
  let M4 := M3.write (address + 3).toNat
    [(word >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M5 := M4.write (address + 4).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M6 := M5.write (address + 5).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M7 := M6.write (address + 6).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  let M8 := M7.write (address + 7).toNat
    [(word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8).2.2.toUInt8]
  have hsize1 : M1.size = memory.size := by
    dsimp only [M1, M0]
    rw [Mem.size_write_of_le (by
      rw [hnat0]
      simp only [List.length_cons, List.length_nil]
      omega)]
  have hsize2 : M2.size = memory.size := by
    dsimp only [M2]
    rw [Mem.size_write_of_le (by
      rw [hnat1, hsize1]
      simp only [List.length_cons, List.length_nil]
      omega), hsize1]
  have hsize3 : M3.size = memory.size := by
    dsimp only [M3]
    rw [Mem.size_write_of_le (by
      rw [hnat2, hsize2]
      simp only [List.length_cons, List.length_nil]
      omega), hsize2]
  have hsize4 : M4.size = memory.size := by
    dsimp only [M4]
    rw [Mem.size_write_of_le (by
      rw [hnat3, hsize3]
      simp only [List.length_cons, List.length_nil]
      omega), hsize3]
  have hsize5 : M5.size = memory.size := by
    dsimp only [M5]
    rw [Mem.size_write_of_le (by
      rw [hnat4, hsize4]
      simp only [List.length_cons, List.length_nil]
      omega), hsize4]
  have hsize6 : M6.size = memory.size := by
    dsimp only [M6]
    rw [Mem.size_write_of_le (by
      rw [hnat5, hsize5]
      simp only [List.length_cons, List.length_nil]
      omega), hsize5]
  have hsize7 : M7.size = memory.size := by
    dsimp only [M7]
    rw [Mem.size_write_of_le (by
      rw [hnat6, hsize6]
      simp only [List.length_cons, List.length_nil]
      omega), hsize6]
  have hM8 : M8 = storeLe64Memory memory offset word := by
    dsimp only [M8, M7, M6, M5, M4, M3, M2, M1, M0]
    rw [hnat0, hnat1, hnat2, hnat3, hnat4, hnat5, hnat6, hnat7]
    rfl
  have htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, M8, G⟩) rest ex := by
    rw [hM8]
    exact hrest
  unfold storeLe64At
  apply storeByteShiftStack_runCompiledTo
      (memory := M0) (word := word) (i := address) (G := G + 96)
      (stack := stack)
  · simpa only [M0] using hsize32
  · rw [hnat0]; dsimp only [M0]; omega
  · exact hpush0
  · exact hroom
  apply storeByteShiftStack_runCompiledTo
      (memory := M1) (word := word >>> 8) (i := address + 1)
      (G := G + 81) (stack := stack)
  · rw [hsize1]; exact hsize32
  · rw [hnat1, hsize1]; omega
  · exact hpush1
  · exact hroom
  apply storeByteShiftStack_runCompiledTo
      (memory := M2) (word := word >>> 8 >>> 8) (i := address + 2)
      (G := G + 66) (stack := stack)
  · rw [hsize2]; exact hsize32
  · rw [hnat2, hsize2]; omega
  · exact hpush2
  · exact hroom
  apply storeByteShiftStack_runCompiledTo
      (memory := M3) (word := word >>> 8 >>> 8 >>> 8) (i := address + 3)
      (G := G + 51) (stack := stack)
  · rw [hsize3]; exact hsize32
  · rw [hnat3, hsize3]; omega
  · exact hpush3
  · exact hroom
  apply storeByteShiftStack_runCompiledTo
      (memory := M4) (word := word >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 4) (G := G + 36) (stack := stack)
  · rw [hsize4]; exact hsize32
  · rw [hnat4, hsize4]; omega
  · exact hpush4
  · exact hroom
  apply storeByteShiftStack_runCompiledTo
      (memory := M5) (word := word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 5) (G := G + 21) (stack := stack)
  · rw [hsize5]; exact hsize32
  · rw [hnat5, hsize5]; omega
  · exact hpush5
  · exact hroom
  apply storeByteShiftStack_runCompiledTo
      (memory := M6)
      (word := word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 6) (G := G + 6) (stack := stack)
  · rw [hsize6]; exact hsize32
  · rw [hnat6, hsize6]; omega
  · exact hpush6
  · exact hroom
  apply storeByteLastStack_runCompiledTo
      (memory := M7)
      (word := word >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8 >>> 8)
      (i := address + 7) (G := G) (stack := stack)
  · rw [hsize7]; exact hsize32
  · rw [hnat7, hsize7]; omega
  · exact hpush7
  · omega
  · exact htail

end Blanc.BeaconDeposit
