import Blanc.Lift.UniswapV2Factory.Code
import Blanc.Lift.UniswapV2Pair.Creation.Facts
import Blanc.Lift.ExactWalkOps

/-!
# The factory's `createPair` memory, by byte images

The memories the factory frame builds while it runs `createPair(WETH, USDC)` (the recorded Pair
creation call: `tokenA = WETH`, `tokenB = USDC`), named in order (`fm1` .. `fm26`), each with its
byte image (`fimg*`), well-formedness, size, and the reads the walk takes: the free pointer and the
creation-code length word (`MLOAD`), the four mapping keys and the salt (`KECCAK256`), the copied
creation code (the `CREATE2` window) and the `initialize` calldata. Every read is decided by
stripping the image's writes that miss the read window (`fslice`); no hash is evaluated.

The memories after the `allPairs` update take the new length word `v` as a parameter.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc.Lift

/-- Strip the writes of a byte image that miss a read window, and open the write containing it. -/
macro "fslice" : tactic => `(tactic|
  simp (disch := first | omega |
      (simp only [B256.length_toBytes, UniswapV2Pair.Creation.code_toList_length]; omega)) only
    [Bytes.sliceD_writeAt_before, Bytes.sliceD_writeAt_after, Bytes.sliceD_writeAt_inside])

/-- The recorded calldata: `createPair(WETH, USDC)`. -/
def createPairData : Bytes :=
  [0xc9, 0xc6, 0x53, 0x96] ++ UniswapV2Pair.Creation.token1.toB256.toBytes ++
    UniswapV2Pair.Creation.token0.toB256.toBytes

/-- `keccak(USDC ‖ 2)`: the `getPair[USDC]` mapping base. -/
def fk1 : B256 := Bytes.keccak ((0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes ++
  (0x2 : B256).toBytes)
/-- `keccak(WETH ‖ keccak(USDC ‖ 2))`: the slot of `getPair[USDC][WETH]`. -/
def fk2 : B256 := Bytes.keccak ((0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes ++
  fk1.toBytes)
/-- The salt `keccak(USDC ‖ WETH)`. -/
def fk3 : B256 := UniswapV2Pair.Creation.salt
/-- `keccak(WETH ‖ 2)`: the `getPair[WETH]` mapping base. -/
def fk4 : B256 := Bytes.keccak ((0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes ++
  (0x2 : B256).toBytes)
/-- `keccak(USDC ‖ keccak(WETH ‖ 2))`: the slot of `getPair[WETH][USDC]`. -/
def fk5 : B256 := Bytes.keccak ((0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes ++
  fk4.toBytes)

/-! ### The walk's memories and their byte images -/

abbrev fm0 : Mem := Mem.empty
def fimg0 : Bytes := []
theorem fm0_wf : Mem.Wf fm0 := Mem.wf_empty
theorem fm0_reads : Mem.Reads fm0 fimg0 := Mem.reads_data _
theorem fm0_size : fm0.size = 0 := rfl

def fm1 : Mem := fm0.write 64 (0x80 : B256).toBytes
def fimg1 : Bytes := Bytes.writeAt fimg0 64 (0x80 : B256).toBytes
theorem fm1_wf : Mem.Wf fm1 := (fm0_wf).write _ _
theorem fm1_reads : Mem.Reads fm1 fimg1 :=
  Mem.Reads.write (fm0_wf) (fm0_reads) _ _
theorem fm1_size : fm1.size = 96 := by
  rw [fm1, Mem.size_write_of_size (fm0_size) (by decide) (B256.length_toBytes _)]; decide

def fm2 : Mem := fm1.write 0 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
def fimg2 : Bytes := Bytes.writeAt fimg1 0 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
theorem fm2_wf : Mem.Wf fm2 := (fm1_wf).write _ _
theorem fm2_reads : Mem.Reads fm2 fimg2 :=
  Mem.Reads.write (fm1_wf) (fm1_reads) _ _
theorem fm2_size : fm2.size = 96 := by
  rw [fm2, Mem.size_write_of_size (fm1_size) (by decide) (B256.length_toBytes _)]; decide

def fm3 : Mem := fm2.write 32 (0x2 : B256).toBytes
def fimg3 : Bytes := Bytes.writeAt fimg2 32 (0x2 : B256).toBytes
theorem fm3_wf : Mem.Wf fm3 := (fm2_wf).write _ _
theorem fm3_reads : Mem.Reads fm3 fimg3 :=
  Mem.Reads.write (fm2_wf) (fm2_reads) _ _
theorem fm3_size : fm3.size = 96 := by
  rw [fm3, Mem.size_write_of_size (fm2_size) (by decide) (B256.length_toBytes _)]; decide

def fm4 : Mem := fm3.write 0 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes
def fimg4 : Bytes := Bytes.writeAt fimg3 0 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes
theorem fm4_wf : Mem.Wf fm4 := (fm3_wf).write _ _
theorem fm4_reads : Mem.Reads fm4 fimg4 :=
  Mem.Reads.write (fm3_wf) (fm3_reads) _ _
theorem fm4_size : fm4.size = 96 := by
  rw [fm4, Mem.size_write_of_size (fm3_size) (by decide) (B256.length_toBytes _)]; decide

def fm5 : Mem := fm4.write 32 fk1.toBytes
def fimg5 : Bytes := Bytes.writeAt fimg4 32 fk1.toBytes
theorem fm5_wf : Mem.Wf fm5 := (fm4_wf).write _ _
theorem fm5_reads : Mem.Reads fm5 fimg5 :=
  Mem.Reads.write (fm4_wf) (fm4_reads) _ _
theorem fm5_size : fm5.size = 96 := by
  rw [fm5, Mem.size_write_of_size (fm4_size) (by decide) (B256.length_toBytes _)]; decide

def fm6 : Mem := fm5.write 160 UniswapV2Pair.Creation.code.toList
def fimg6 : Bytes := Bytes.writeAt fimg5 160 UniswapV2Pair.Creation.code.toList
theorem fm6_wf : Mem.Wf fm6 := (fm5_wf).write _ _
theorem fm6_reads : Mem.Reads fm6 fimg6 :=
  Mem.Reads.write (fm5_wf) (fm5_reads) _ _
theorem fm6_size : fm6.size = 11808 := by
  rw [fm6, Mem.size_write_of_size (fm5_size) (by decide) UniswapV2Pair.Creation.code_toList_length]; decide

def fm7 : Mem := fm6.write 128 (0x2d74 : B256).toBytes
def fimg7 : Bytes := Bytes.writeAt fimg6 128 (0x2d74 : B256).toBytes
theorem fm7_wf : Mem.Wf fm7 := (fm6_wf).write _ _
theorem fm7_reads : Mem.Reads fm7 fimg7 :=
  Mem.Reads.write (fm6_wf) (fm6_reads) _ _
theorem fm7_size : fm7.size = 11808 := by
  rw [fm7, Mem.size_write_of_size (fm6_size) (by decide) (B256.length_toBytes _)]; decide

def fm8 : Mem := fm7.write 64 (0x2e20 : B256).toBytes
def fimg8 : Bytes := Bytes.writeAt fimg7 64 (0x2e20 : B256).toBytes
theorem fm8_wf : Mem.Wf fm8 := (fm7_wf).write _ _
theorem fm8_reads : Mem.Reads fm8 fimg8 :=
  Mem.Reads.write (fm7_wf) (fm7_reads) _ _
theorem fm8_size : fm8.size = 11808 := by
  rw [fm8, Mem.size_write_of_size (fm7_size) (by decide) (B256.length_toBytes _)]; decide

def fm9 : Mem := fm8.write 11840 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48000000000000000000000000 : B256).toBytes
def fimg9 : Bytes := Bytes.writeAt fimg8 11840 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48000000000000000000000000 : B256).toBytes
theorem fm9_wf : Mem.Wf fm9 := (fm8_wf).write _ _
theorem fm9_reads : Mem.Reads fm9 fimg9 :=
  Mem.Reads.write (fm8_wf) (fm8_reads) _ _
theorem fm9_size : fm9.size = 11872 := by
  rw [fm9, Mem.size_write_of_size (fm8_size) (by decide) (B256.length_toBytes _)]; decide

def fm10 : Mem := fm9.write 11860 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2000000000000000000000000 : B256).toBytes
def fimg10 : Bytes := Bytes.writeAt fimg9 11860 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2000000000000000000000000 : B256).toBytes
theorem fm10_wf : Mem.Wf fm10 := (fm9_wf).write _ _
theorem fm10_reads : Mem.Reads fm10 fimg10 :=
  Mem.Reads.write (fm9_wf) (fm9_reads) _ _
theorem fm10_size : fm10.size = 11904 := by
  rw [fm10, Mem.size_write_of_size (fm9_size) (by decide) (B256.length_toBytes _)]; decide

def fm11 : Mem := fm10.write 11808 (0x28 : B256).toBytes
def fimg11 : Bytes := Bytes.writeAt fimg10 11808 (0x28 : B256).toBytes
theorem fm11_wf : Mem.Wf fm11 := (fm10_wf).write _ _
theorem fm11_reads : Mem.Reads fm11 fimg11 :=
  Mem.Reads.write (fm10_wf) (fm10_reads) _ _
theorem fm11_size : fm11.size = 11904 := by
  rw [fm11, Mem.size_write_of_size (fm10_size) (by decide) (B256.length_toBytes _)]; decide

def fm12 : Mem := fm11.write 64 (0x2e68 : B256).toBytes
def fimg12 : Bytes := Bytes.writeAt fimg11 64 (0x2e68 : B256).toBytes
theorem fm12_wf : Mem.Wf fm12 := (fm11_wf).write _ _
theorem fm12_reads : Mem.Reads fm12 fimg12 :=
  Mem.Reads.write (fm11_wf) (fm11_reads) _ _
theorem fm12_size : fm12.size = 11904 := by
  rw [fm12, Mem.size_write_of_size (fm11_size) (by decide) (B256.length_toBytes _)]; decide

def fm13 : Mem := fm12.write 11880 (0x485cc95500000000000000000000000000000000000000000000000000000000 : B256).toBytes
def fimg13 : Bytes := Bytes.writeAt fimg12 11880 (0x485cc95500000000000000000000000000000000000000000000000000000000 : B256).toBytes
theorem fm13_wf : Mem.Wf fm13 := (fm12_wf).write _ _
theorem fm13_reads : Mem.Reads fm13 fimg13 :=
  Mem.Reads.write (fm12_wf) (fm12_reads) _ _
theorem fm13_size : fm13.size = 11936 := by
  rw [fm13, Mem.size_write_of_size (fm12_size) (by decide) (B256.length_toBytes _)]; decide

def fm14 : Mem := fm13.write 11884 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
def fimg14 : Bytes := Bytes.writeAt fimg13 11884 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
theorem fm14_wf : Mem.Wf fm14 := (fm13_wf).write _ _
theorem fm14_reads : Mem.Reads fm14 fimg14 :=
  Mem.Reads.write (fm13_wf) (fm13_reads) _ _
theorem fm14_size : fm14.size = 11936 := by
  rw [fm14, Mem.size_write_of_size (fm13_size) (by decide) (B256.length_toBytes _)]; decide

def fm15 : Mem := fm14.write 11916 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes
def fimg15 : Bytes := Bytes.writeAt fimg14 11916 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes
theorem fm15_wf : Mem.Wf fm15 := (fm14_wf).write _ _
theorem fm15_reads : Mem.Reads fm15 fimg15 :=
  Mem.Reads.write (fm14_wf) (fm14_reads) _ _
theorem fm15_size : fm15.size = 11968 := by
  rw [fm15, Mem.size_write_of_size (fm14_size) (by decide) (B256.length_toBytes _)]; decide

def fm16 : Mem := fm15.write 0 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
def fimg16 : Bytes := Bytes.writeAt fimg15 0 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
theorem fm16_wf : Mem.Wf fm16 := (fm15_wf).write _ _
theorem fm16_reads : Mem.Reads fm16 fimg16 :=
  Mem.Reads.write (fm15_wf) (fm15_reads) _ _
theorem fm16_size : fm16.size = 11968 := by
  rw [fm16, Mem.size_write_of_size (fm15_size) (by decide) (B256.length_toBytes _)]; decide

def fm17 : Mem := fm16.write 32 (0x2 : B256).toBytes
def fimg17 : Bytes := Bytes.writeAt fimg16 32 (0x2 : B256).toBytes
theorem fm17_wf : Mem.Wf fm17 := (fm16_wf).write _ _
theorem fm17_reads : Mem.Reads fm17 fimg17 :=
  Mem.Reads.write (fm16_wf) (fm16_reads) _ _
theorem fm17_size : fm17.size = 11968 := by
  rw [fm17, Mem.size_write_of_size (fm16_size) (by decide) (B256.length_toBytes _)]; decide

def fm18 : Mem := fm17.write 0 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes
def fimg18 : Bytes := Bytes.writeAt fimg17 0 (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256).toBytes
theorem fm18_wf : Mem.Wf fm18 := (fm17_wf).write _ _
theorem fm18_reads : Mem.Reads fm18 fimg18 :=
  Mem.Reads.write (fm17_wf) (fm17_reads) _ _
theorem fm18_size : fm18.size = 11968 := by
  rw [fm18, Mem.size_write_of_size (fm17_size) (by decide) (B256.length_toBytes _)]; decide

def fm19 : Mem := fm18.write 32 fk1.toBytes
def fimg19 : Bytes := Bytes.writeAt fimg18 32 fk1.toBytes
theorem fm19_wf : Mem.Wf fm19 := (fm18_wf).write _ _
theorem fm19_reads : Mem.Reads fm19 fimg19 :=
  Mem.Reads.write (fm18_wf) (fm18_reads) _ _
theorem fm19_size : fm19.size = 11968 := by
  rw [fm19, Mem.size_write_of_size (fm18_size) (by decide) (B256.length_toBytes _)]; decide

def fm20 : Mem := fm19.write 32 (0x2 : B256).toBytes
def fimg20 : Bytes := Bytes.writeAt fimg19 32 (0x2 : B256).toBytes
theorem fm20_wf : Mem.Wf fm20 := (fm19_wf).write _ _
theorem fm20_reads : Mem.Reads fm20 fimg20 :=
  Mem.Reads.write (fm19_wf) (fm19_reads) _ _
theorem fm20_size : fm20.size = 11968 := by
  rw [fm20, Mem.size_write_of_size (fm19_size) (by decide) (B256.length_toBytes _)]; decide

def fm21 : Mem := fm20.write 0 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
def fimg21 : Bytes := Bytes.writeAt fimg20 0 (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256).toBytes
theorem fm21_wf : Mem.Wf fm21 := (fm20_wf).write _ _
theorem fm21_reads : Mem.Reads fm21 fimg21 :=
  Mem.Reads.write (fm20_wf) (fm20_reads) _ _
theorem fm21_size : fm21.size = 11968 := by
  rw [fm21, Mem.size_write_of_size (fm20_size) (by decide) (B256.length_toBytes _)]; decide

def fm22 : Mem := fm21.write 32 fk4.toBytes
def fimg22 : Bytes := Bytes.writeAt fimg21 32 fk4.toBytes
theorem fm22_wf : Mem.Wf fm22 := (fm21_wf).write _ _
theorem fm22_reads : Mem.Reads fm22 fimg22 :=
  Mem.Reads.write (fm21_wf) (fm21_reads) _ _
theorem fm22_size : fm22.size = 11968 := by
  rw [fm22, Mem.size_write_of_size (fm21_size) (by decide) (B256.length_toBytes _)]; decide

def fm23 : Mem := fm22.write 0 (0x3 : B256).toBytes
def fimg23 : Bytes := Bytes.writeAt fimg22 0 (0x3 : B256).toBytes
theorem fm23_wf : Mem.Wf fm23 := (fm22_wf).write _ _
theorem fm23_reads : Mem.Reads fm23 fimg23 :=
  Mem.Reads.write (fm22_wf) (fm22_reads) _ _
theorem fm23_size : fm23.size = 11968 := by
  rw [fm23, Mem.size_write_of_size (fm22_size) (by decide) (B256.length_toBytes _)]; decide

def fm24 : Mem := fm23.write 11880 (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256).toBytes
def fimg24 : Bytes := Bytes.writeAt fimg23 11880 (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256).toBytes
theorem fm24_wf : Mem.Wf fm24 := (fm23_wf).write _ _
theorem fm24_reads : Mem.Reads fm24 fimg24 :=
  Mem.Reads.write (fm23_wf) (fm23_reads) _ _
theorem fm24_size : fm24.size = 11968 := by
  rw [fm24, Mem.size_write_of_size (fm23_size) (by decide) (B256.length_toBytes _)]; decide

def fm25 (v : B256) : Mem := fm24.write 11912 v.toBytes
def fimg25 (v : B256) : Bytes := Bytes.writeAt fimg24 11912 v.toBytes
theorem fm25_wf (v : B256) : Mem.Wf (fm25 v) := (fm24_wf).write _ _
theorem fm25_reads (v : B256) : Mem.Reads (fm25 v) (fimg25 v) :=
  Mem.Reads.write (fm24_wf) (fm24_reads) _ _
theorem fm25_size (v : B256) : (fm25 v).size = 11968 := by
  rw [fm25, Mem.size_write_of_size (fm24_size) (by decide) (B256.length_toBytes _)]; decide

def fm26 (v : B256) : Mem := (fm25 v).write 11880 (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256).toBytes
def fimg26 (v : B256) : Bytes := Bytes.writeAt (fimg25 v) 11880 (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256).toBytes
theorem fm26_reads (v : B256) : Mem.Reads (fm26 v) (fimg26 v) :=
  Mem.Reads.write (fm25_wf v) (fm25_reads v) _ _
theorem fm26_size (v : B256) : (fm26 v).size = 11968 := by
  rw [fm26, Mem.size_write_of_size (fm25_size v) (by decide) (B256.length_toBytes _)]; decide

/-! ### Reads -/

theorem fm5_mload_40 : Bytes.toB256 (fm5.read 64 32).1 = (0x80 : B256) := by
  rw [Mem.Reads.read (fm5_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5]
  fslice
  decide

theorem fm8_mload_40 : Bytes.toB256 (fm8.read 64 32).1 = (0x2e20 : B256) := by
  rw [Mem.Reads.read (fm8_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8]
  fslice
  decide

theorem fm10_mload_40 : Bytes.toB256 (fm10.read 64 32).1 = (0x2e20 : B256) := by
  rw [Mem.Reads.read (fm10_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10]
  fslice
  decide

theorem fm12_mload_2e20 : Bytes.toB256 (fm12.read 11808 32).1 = (0x28 : B256) := by
  rw [Mem.Reads.read (fm12_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12]
  fslice
  decide

theorem fm12_mload_80 : Bytes.toB256 (fm12.read 128 32).1 = (0x2d74 : B256) := by
  rw [Mem.Reads.read (fm12_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12]
  fslice
  decide

theorem fm12_mload_40 : Bytes.toB256 (fm12.read 64 32).1 = (0x2e68 : B256) := by
  rw [Mem.Reads.read (fm12_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12]
  fslice
  decide

theorem fm15_mload_40 : Bytes.toB256 (fm15.read 64 32).1 = (0x2e68 : B256) := by
  rw [Mem.Reads.read (fm15_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15]
  fslice
  decide

theorem fm23_mload_40 : Bytes.toB256 (fm23.read 64 32).1 = (0x2e68 : B256) := by
  rw [Mem.Reads.read (fm23_reads)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15, fimg16, fimg17, fimg18, fimg19, fimg20, fimg21, fimg22, fimg23]
  fslice
  decide

theorem fm25_mload_40 (v : B256) : Bytes.toB256 ((fm25 v).read 64 32).1 = (0x2e68 : B256) := by
  rw [Mem.Reads.read (fm25_reads v)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15, fimg16, fimg17, fimg18, fimg19, fimg20, fimg21, fimg22, fimg23, fimg24, fimg25]
  fslice
  decide

theorem fm26_mload_40 (v : B256) : Bytes.toB256 ((fm26 v).read 64 32).1 = (0x2e68 : B256) := by
  rw [Mem.Reads.read (fm26_reads v)]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15, fimg16, fimg17, fimg18, fimg19, fimg20, fimg21, fimg22, fimg23, fimg24, fimg25, fimg26]
  fslice
  decide

theorem fm3_keccak_0 : Bytes.keccak (fm3.read 0 64).1 = fk1 := by
  rw [Mem.Reads.read (fm3_reads), fk1]
  refine congrArg Bytes.keccak ?_
  simp only [fimg1, fimg2, fimg3]
  rw [show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split]
  fslice
  simp only [show (0 : Nat) - 0 = 0 from rfl]
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _),
    Bytes.sliceD_zero_length (B256.length_toBytes _)]

theorem fm5_keccak_0 : Bytes.keccak (fm5.read 0 64).1 = fk2 := by
  rw [Mem.Reads.read (fm5_reads), fk2]
  refine congrArg Bytes.keccak ?_
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5]
  rw [show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split]
  fslice
  simp only [show (0 : Nat) - 0 = 0 from rfl]
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _),
    Bytes.sliceD_zero_length (B256.length_toBytes _)]

theorem fm12_keccak_2e40 : Bytes.keccak (fm12.read 11840 40).1 = fk3 := by
  rw [Mem.Reads.read fm12_reads, fk3, UniswapV2Pair.Creation.salt]
  refine congrArg Bytes.keccak ?_
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12]
  rw [show (40 : Nat) = 20 + 20 from rfl, List.sliceD_split]
  fslice
  decide

theorem fm17_keccak_0 : Bytes.keccak (fm17.read 0 64).1 = fk1 := by
  rw [Mem.Reads.read (fm17_reads), fk1]
  refine congrArg Bytes.keccak ?_
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15, fimg16, fimg17]
  rw [show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split]
  fslice
  simp only [show (0 : Nat) - 0 = 0 from rfl]
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _),
    Bytes.sliceD_zero_length (B256.length_toBytes _)]

theorem fm19_keccak_0 : Bytes.keccak (fm19.read 0 64).1 = fk2 := by
  rw [Mem.Reads.read (fm19_reads), fk2]
  refine congrArg Bytes.keccak ?_
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15, fimg16, fimg17, fimg18, fimg19]
  rw [show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split]
  fslice
  simp only [show (0 : Nat) - 0 = 0 from rfl]
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _),
    Bytes.sliceD_zero_length (B256.length_toBytes _)]

theorem fm20_keccak_0 : Bytes.keccak (fm20.read 0 64).1 = fk4 := by
  rw [Mem.Reads.read (fm20_reads), fk4]
  refine congrArg Bytes.keccak ?_
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15, fimg16, fimg17, fimg18, fimg19, fimg20]
  rw [show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split]
  fslice
  simp only [show (0 : Nat) - 0 = 0 from rfl]
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _),
    Bytes.sliceD_zero_length (B256.length_toBytes _)]

theorem fm22_keccak_0 : Bytes.keccak (fm22.read 0 64).1 = fk5 := by
  rw [Mem.Reads.read (fm22_reads), fk5]
  refine congrArg Bytes.keccak ?_
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15, fimg16, fimg17, fimg18, fimg19, fimg20, fimg21, fimg22]
  rw [show (64 : Nat) = 32 + 32 from rfl, List.sliceD_split]
  fslice
  simp only [show (0 : Nat) - 0 = 0 from rfl]
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _),
    Bytes.sliceD_zero_length (B256.length_toBytes _)]


/-! ### The `CODECOPY`, the `CREATE2` window and the `initialize` calldata -/

private theorem mem_read_fst (μ : Mem) (i n : Nat) : (μ.read i n).1 = μ.data.sliceD i n 0 := rfl

theorem fm6_codecopy : fm5.write (0xa0 : B256).toNat
    (code.sliceD (0x87b : B256).toNat (0x2d74 : B256).toNat (Linst.toUInt8 .stop)) = fm6 := by
  rw [show (0xa0 : B256).toNat = 160 from rfl, show (0x87b : B256).toNat = 2171 from rfl,
    show (0x2d74 : B256).toNat = 11636 from rfl, show Linst.toUInt8 .stop = 0 from rfl,
    pairCreation_window]
  rfl

/-- The `CREATE2` window `[0xa0, 0xa0 + 11636)` of the memory at the `CREATE2` node is the Pair
creation code. -/
theorem fm12_create2InitCode :
    create2InitCode fm12 0xa0 0x2d74 = UniswapV2Pair.Creation.code.toList := by
  unfold create2InitCode
  rw [Mem.extends_covered (by rw [fm12_size]; decide), show (0xa0 : B256).toNat = 160 from rfl,
    show (0x2d74 : B256).toNat = 11636 from rfl,
    ← mem_read_fst]
  rw [Mem.Reads.read fm12_reads]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12]
  fslice
  exact Bytes.sliceD_zero_length UniswapV2Pair.Creation.code_toList_length

/-- `initialize(USDC, WETH)`: the selector and the two sorted token words. -/
def initializeCalldata : Bytes :=
  [0x48, 0x5c, 0xc9, 0x55] ++ UniswapV2Pair.Creation.token0.toB256.toBytes ++
    UniswapV2Pair.Creation.token1.toB256.toBytes

/-- The `CALL`'s input window `[0x2e68, 0x2e68 + 0x44)` is `initialize(USDC, WETH)`. -/
theorem fm15_calldata : fm15.data.sliceD 11880 68 0 = initializeCalldata := by
  rw [← mem_read_fst]
  rw [Mem.Reads.read fm15_reads]
  simp only [fimg1, fimg2, fimg3, fimg4, fimg5, fimg6, fimg7, fimg8, fimg9, fimg10, fimg11, fimg12, fimg13, fimg14, fimg15]
  rw [show (68 : Nat) = 4 + (32 + 32) from rfl, List.sliceD_split, List.sliceD_split]
  fslice
  decide

end Blanc.Lift.UniswapV2Factory
