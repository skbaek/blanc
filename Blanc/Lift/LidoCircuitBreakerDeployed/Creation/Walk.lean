import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Cert
import Blanc.Lift.LidoCircuitBreakerDeployed.Cert
import Blanc.Lift.CreationOps
import Blanc.Lift.Vyper
import Blanc.Lift.PackedSha
import Blanc.Lift.WalkSteps
import Blanc.Lift.Deploy

/-!
# The Lido CircuitBreaker constructor, walked

A gas-exact synthetic run (`SFunc.RunExact`) of the lifted solc 0.8.34 constructor of the Lido
CircuitBreaker's creation input (`Creation/Cert.lean`), with the recorded mainnet constructor
arguments appended to the code (admin `0x3e40D73E...9C8c`, minimum/maximum pause duration
432000/5184000, minimum/maximum heartbeat interval 2592000/94608000, initial pause duration
1814400, initial heartbeat interval 31536000).  The constructor

* copies its seven argument words from the code (`CODECOPY` at `CODESIZE - 5414`, entry 0) and
  ABI-decodes them (`abi_decode_tuple`, entry 1, one internal call), validating the admin
  address, the minimum heartbeat interval and the bounds;
* stores the five immutables in memory, emits `CircuitBreakerInitialized` (`LOG2`);
* sets the pause duration (entry 2, storage slot 0) and the heartbeat interval (entry 3,
  slot 1), each emitting its update event (`LOG1`) with the old value read by `SLOAD`;
* copies the 4,584-byte runtime template into memory, patches the twelve immutable spans with
  the five immutable values (`MSTORE`s) and returns it (entry 4).

Every memory image is a named `Mem.write` chain over `Mem.empty` (`mem0 … mem{N}`) with a
parallel list image (`img0 … img{N}`, `Mem.Reads`), so nothing ever evaluates a concrete memory:
sizes are by `Mem.size_write_of_size`, reads by `Mem.Reads.read` over the list image.  Gas is
exact; the start gas is only bounded below, and the `SLOAD`/`SSTORE` charges are kept as
`sloadCost`/`sstoreCost` terms (bounded, never evaluated).  The old values the events log are
the fresh storage's zeros.

This file is emitted by a scratch script (not a registered generator) from the certificate; the
kernel checks every step.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed.Creation

open Jaune

/-- The lifted constructor program. -/
abbrev prog : List SFunc := Cert.prog cert

/-- The frame facts the walk needs of the creation frame. -/
structure CtorFrame (sevm : Sevm) : Prop where
  fork : CoveredFork sevm.benvStat.fork
  static : sevm.isStatic = false

theorem sliceD_len (a len : Nat) : (code.sliceD a len (Linst.toUInt8 .stop)).length = len :=
  ByteArray.length_sliceD _ _ _ _

/-- A code window, read through `toList` (the kernel-cheap form). -/
theorem code_slice (a len : Nat) :
    code.sliceD a len (Linst.toUInt8 .stop) = code.data.toList.sliceD a len 0 := by
  rw [ByteArray.sliceD_eq, ByteArray.toList_eq_toList_data]; rfl

theorem code_size : code.size.toB256 = 5638 := by decide +kernel


/-! ## Constants and the memory images -/

def pw0 : B256 := Bytes.toB256 [0xd0, 0xd5, 0xe7, 0xf6, 0x35, 0xb5, 0xf3, 0xb6, 0xc0, 0xab, 0xab, 0x1c, 0x16, 0x4d, 0x7e, 0x19, 0x30, 0x4f, 0xc8, 0x99, 0xd9, 0x98, 0x8e, 0xf3, 0xe6, 0xd9, 0xa9, 0xad, 0x86, 0xb7, 0xb, 0xde]
def pw1 : B256 := Bytes.toB256 [0xf6, 0xe1, 0xf1, 0xaf, 0xec, 0x51, 0x1d, 0x8b, 0x8e, 0x9a, 0x65, 0xbb, 0x53, 0xc9, 0x47, 0xac, 0x99, 0xea, 0x42, 0x11, 0xfb, 0x22, 0xe0, 0xd6, 0xa0, 0xe3, 0x31, 0xd5, 0x5d, 0x73, 0x45, 0xf8]
def pw2 : B256 := Bytes.toB256 [0xca, 0xa, 0x37, 0xda, 0x24, 0x60, 0x42, 0x76, 0xf6, 0x61, 0xe3, 0x6e, 0x2b, 0xe, 0x71, 0x66, 0x1b, 0xb5, 0x6f, 0x8d, 0x13, 0x99, 0x4a, 0x5d, 0xf, 0x20, 0x70, 0x70, 0x12, 0x5b, 0x95, 0xc]

abbrev mem0 : Mem := Mem.empty
def img0 : Bytes := []
theorem mem0_wf : Mem.Wf mem0 := Mem.wf_empty
theorem mem0_reads : Mem.Reads mem0 img0 := Mem.reads_data _
theorem mem0_size : mem0.size = 0 := rfl

def mem1 : Mem := mem0.write 64 (0x120 : B256).toBytes
def img1 : Bytes := Bytes.writeAt img0 64 (0x120 : B256).toBytes
theorem mem1_wf : Mem.Wf mem1 := mem0_wf.write _ _
theorem mem1_reads : Mem.Reads mem1 img1 := Mem.Reads.write mem0_wf mem0_reads _ _
theorem mem1_size : mem1.size = 96 := by
  rw [mem1, Mem.size_write_of_size mem0_size (by decide) (B256.length_toBytes _)]; decide

def mem2 : Mem := mem1.write 288 (code.sliceD 5414 224 (Linst.toUInt8 .stop))
def img2 : Bytes := Bytes.writeAt img1 288 (code.data.toList.sliceD 5414 224 0)
theorem mem2_wf : Mem.Wf mem2 := mem1_wf.write _ _
theorem mem2_reads : Mem.Reads mem2 img2 := by
  unfold mem2 img2
  rw [← code_slice]
  exact Mem.Reads.write mem1_wf mem1_reads _ _
theorem mem2_size : mem2.size = 512 := by
  rw [mem2, Mem.size_write_of_size mem1_size (by decide) (sliceD_len _ _)]; decide

def mem3 : Mem := mem2.write 64 (0x200 : B256).toBytes
def img3 : Bytes := Bytes.writeAt img2 64 (0x200 : B256).toBytes
theorem mem3_wf : Mem.Wf mem3 := mem2_wf.write _ _
theorem mem3_reads : Mem.Reads mem3 img3 := Mem.Reads.write mem2_wf mem2_reads _ _
theorem mem3_size : mem3.size = 512 := by
  rw [mem3, Mem.size_write_of_size mem2_size (by decide) (B256.length_toBytes _)]; decide

def mem4 : Mem := mem3.write 128 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
def img4 : Bytes := Bytes.writeAt img3 128 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
theorem mem4_wf : Mem.Wf mem4 := mem3_wf.write _ _
theorem mem4_reads : Mem.Reads mem4 img4 := Mem.Reads.write mem3_wf mem3_reads _ _
theorem mem4_size : mem4.size = 512 := by
  rw [mem4, Mem.size_write_of_size mem3_size (by decide) (B256.length_toBytes _)]; decide

def mem5 : Mem := mem4.write 160 (0x69780 : B256).toBytes
def img5 : Bytes := Bytes.writeAt img4 160 (0x69780 : B256).toBytes
theorem mem5_wf : Mem.Wf mem5 := mem4_wf.write _ _
theorem mem5_reads : Mem.Reads mem5 img5 := Mem.Reads.write mem4_wf mem4_reads _ _
theorem mem5_size : mem5.size = 512 := by
  rw [mem5, Mem.size_write_of_size mem4_size (by decide) (B256.length_toBytes _)]; decide

def mem6 : Mem := mem5.write 192 (0x4f1a00 : B256).toBytes
def img6 : Bytes := Bytes.writeAt img5 192 (0x4f1a00 : B256).toBytes
theorem mem6_wf : Mem.Wf mem6 := mem5_wf.write _ _
theorem mem6_reads : Mem.Reads mem6 img6 := Mem.Reads.write mem5_wf mem5_reads _ _
theorem mem6_size : mem6.size = 512 := by
  rw [mem6, Mem.size_write_of_size mem5_size (by decide) (B256.length_toBytes _)]; decide

def mem7 : Mem := mem6.write 224 (0x278d00 : B256).toBytes
def img7 : Bytes := Bytes.writeAt img6 224 (0x278d00 : B256).toBytes
theorem mem7_wf : Mem.Wf mem7 := mem6_wf.write _ _
theorem mem7_reads : Mem.Reads mem7 img7 := Mem.Reads.write mem6_wf mem6_reads _ _
theorem mem7_size : mem7.size = 512 := by
  rw [mem7, Mem.size_write_of_size mem6_size (by decide) (B256.length_toBytes _)]; decide

def mem8 : Mem := mem7.write 256 (0x5a39a80 : B256).toBytes
def img8 : Bytes := Bytes.writeAt img7 256 (0x5a39a80 : B256).toBytes
theorem mem8_wf : Mem.Wf mem8 := mem7_wf.write _ _
theorem mem8_reads : Mem.Reads mem8 img8 := Mem.Reads.write mem7_wf mem7_reads _ _
theorem mem8_size : mem8.size = 512 := by
  rw [mem8, Mem.size_write_of_size mem7_size (by decide) (B256.length_toBytes _)]; decide

def mem9 : Mem := mem8.write 512 (0x69780 : B256).toBytes
def img9 : Bytes := Bytes.writeAt img8 512 (0x69780 : B256).toBytes
theorem mem9_wf : Mem.Wf mem9 := mem8_wf.write _ _
theorem mem9_reads : Mem.Reads mem9 img9 := Mem.Reads.write mem8_wf mem8_reads _ _
theorem mem9_size : mem9.size = 544 := by
  rw [mem9, Mem.size_write_of_size mem8_size (by decide) (B256.length_toBytes _)]; decide

def mem10 : Mem := mem9.write 544 (0x4f1a00 : B256).toBytes
def img10 : Bytes := Bytes.writeAt img9 544 (0x4f1a00 : B256).toBytes
theorem mem10_wf : Mem.Wf mem10 := mem9_wf.write _ _
theorem mem10_reads : Mem.Reads mem10 img10 := Mem.Reads.write mem9_wf mem9_reads _ _
theorem mem10_size : mem10.size = 576 := by
  rw [mem10, Mem.size_write_of_size mem9_size (by decide) (B256.length_toBytes _)]; decide

def mem11 : Mem := mem10.write 576 (0x278d00 : B256).toBytes
def img11 : Bytes := Bytes.writeAt img10 576 (0x278d00 : B256).toBytes
theorem mem11_wf : Mem.Wf mem11 := mem10_wf.write _ _
theorem mem11_reads : Mem.Reads mem11 img11 := Mem.Reads.write mem10_wf mem10_reads _ _
theorem mem11_size : mem11.size = 608 := by
  rw [mem11, Mem.size_write_of_size mem10_size (by decide) (B256.length_toBytes _)]; decide

def mem12 : Mem := mem11.write 608 (0x5a39a80 : B256).toBytes
def img12 : Bytes := Bytes.writeAt img11 608 (0x5a39a80 : B256).toBytes
theorem mem12_wf : Mem.Wf mem12 := mem11_wf.write _ _
theorem mem12_reads : Mem.Reads mem12 img12 := Mem.Reads.write mem11_wf mem11_reads _ _
theorem mem12_size : mem12.size = 640 := by
  rw [mem12, Mem.size_write_of_size mem11_size (by decide) (B256.length_toBytes _)]; decide

def mem13 : Mem := mem12.write 512 (0x0 : B256).toBytes
def img13 : Bytes := Bytes.writeAt img12 512 (0x0 : B256).toBytes
theorem mem13_wf : Mem.Wf mem13 := mem12_wf.write _ _
theorem mem13_reads : Mem.Reads mem13 img13 := Mem.Reads.write mem12_wf mem12_reads _ _
theorem mem13_size : mem13.size = 640 := by
  rw [mem13, Mem.size_write_of_size mem12_size (by decide) (B256.length_toBytes _)]; decide

def mem14 : Mem := mem13.write 544 (0x1baf80 : B256).toBytes
def img14 : Bytes := Bytes.writeAt img13 544 (0x1baf80 : B256).toBytes
theorem mem14_wf : Mem.Wf mem14 := mem13_wf.write _ _
theorem mem14_reads : Mem.Reads mem14 img14 := Mem.Reads.write mem13_wf mem13_reads _ _
theorem mem14_size : mem14.size = 640 := by
  rw [mem14, Mem.size_write_of_size mem13_size (by decide) (B256.length_toBytes _)]; decide

def mem15 : Mem := mem14.write 512 (0x0 : B256).toBytes
def img15 : Bytes := Bytes.writeAt img14 512 (0x0 : B256).toBytes
theorem mem15_wf : Mem.Wf mem15 := mem14_wf.write _ _
theorem mem15_reads : Mem.Reads mem15 img15 := Mem.Reads.write mem14_wf mem14_reads _ _
theorem mem15_size : mem15.size = 640 := by
  rw [mem15, Mem.size_write_of_size mem14_size (by decide) (B256.length_toBytes _)]; decide

def mem16 : Mem := mem15.write 544 (0x1e13380 : B256).toBytes
def img16 : Bytes := Bytes.writeAt img15 544 (0x1e13380 : B256).toBytes
theorem mem16_wf : Mem.Wf mem16 := mem15_wf.write _ _
theorem mem16_reads : Mem.Reads mem16 img16 := Mem.Reads.write mem15_wf mem15_reads _ _
theorem mem16_size : mem16.size = 640 := by
  rw [mem16, Mem.size_write_of_size mem15_size (by decide) (B256.length_toBytes _)]; decide

def mem17 : Mem := mem16.write 0 (code.sliceD 830 4584 (Linst.toUInt8 .stop))
def img17 : Bytes := Bytes.writeAt img16 0 (code.data.toList.sliceD 830 4584 0)
theorem mem17_wf : Mem.Wf mem17 := mem16_wf.write _ _
theorem mem17_reads : Mem.Reads mem17 img17 := by
  unfold mem17 img17
  rw [← code_slice]
  exact Mem.Reads.write mem16_wf mem16_reads _ _
theorem mem17_size : mem17.size = 4608 := by
  rw [mem17, Mem.size_write_of_size mem16_size (by decide) (sliceD_len _ _)]; decide

def mem18 : Mem := mem17.write 583 (0x5a39a80 : B256).toBytes
def img18 : Bytes := Bytes.writeAt img17 583 (0x5a39a80 : B256).toBytes
theorem mem18_wf : Mem.Wf mem18 := mem17_wf.write _ _
theorem mem18_reads : Mem.Reads mem18 img18 := Mem.Reads.write mem17_wf mem17_reads _ _
theorem mem18_size : mem18.size = 4608 := by
  rw [mem18, Mem.size_write_of_size mem17_size (by decide) (B256.length_toBytes _)]; decide

def mem19 : Mem := mem18.write 3591 (0x5a39a80 : B256).toBytes
def img19 : Bytes := Bytes.writeAt img18 3591 (0x5a39a80 : B256).toBytes
theorem mem19_wf : Mem.Wf mem19 := mem18_wf.write _ _
theorem mem19_reads : Mem.Reads mem19 img19 := Mem.Reads.write mem18_wf mem18_reads _ _
theorem mem19_size : mem19.size = 4608 := by
  rw [mem19, Mem.size_write_of_size mem18_size (by decide) (B256.length_toBytes _)]; decide

def mem20 : Mem := mem19.write 641 (0x278d00 : B256).toBytes
def img20 : Bytes := Bytes.writeAt img19 641 (0x278d00 : B256).toBytes
theorem mem20_wf : Mem.Wf mem20 := mem19_wf.write _ _
theorem mem20_reads : Mem.Reads mem20 img20 := Mem.Reads.write mem19_wf mem19_reads _ _
theorem mem20_size : mem20.size = 4608 := by
  rw [mem20, Mem.size_write_of_size mem19_size (by decide) (B256.length_toBytes _)]; decide

def mem21 : Mem := mem20.write 3501 (0x278d00 : B256).toBytes
def img21 : Bytes := Bytes.writeAt img20 3501 (0x278d00 : B256).toBytes
theorem mem21_wf : Mem.Wf mem21 := mem20_wf.write _ _
theorem mem21_reads : Mem.Reads mem21 img21 := Mem.Reads.write mem20_wf mem20_reads _ _
theorem mem21_size : mem21.size = 4608 := by
  rw [mem21, Mem.size_write_of_size mem20_size (by decide) (B256.length_toBytes _)]; decide

def mem22 : Mem := mem21.write 313 (0x4f1a00 : B256).toBytes
def img22 : Bytes := Bytes.writeAt img21 313 (0x4f1a00 : B256).toBytes
theorem mem22_wf : Mem.Wf mem22 := mem21_wf.write _ _
theorem mem22_reads : Mem.Reads mem22 img22 := Mem.Reads.write mem21_wf mem21_reads _ _
theorem mem22_size : mem22.size = 4608 := by
  rw [mem22, Mem.size_write_of_size mem21_size (by decide) (B256.length_toBytes _)]; decide

def mem23 : Mem := mem22.write 3836 (0x4f1a00 : B256).toBytes
def img23 : Bytes := Bytes.writeAt img22 3836 (0x4f1a00 : B256).toBytes
theorem mem23_wf : Mem.Wf mem23 := mem22_wf.write _ _
theorem mem23_reads : Mem.Reads mem23 img23 := Mem.Reads.write mem22_wf mem22_reads _ _
theorem mem23_size : mem23.size = 4608 := by
  rw [mem23, Mem.size_write_of_size mem22_size (by decide) (B256.length_toBytes _)]; decide

def mem24 : Mem := mem23.write 544 (0x69780 : B256).toBytes
def img24 : Bytes := Bytes.writeAt img23 544 (0x69780 : B256).toBytes
theorem mem24_wf : Mem.Wf mem24 := mem23_wf.write _ _
theorem mem24_reads : Mem.Reads mem24 img24 := Mem.Reads.write mem23_wf mem23_reads _ _
theorem mem24_size : mem24.size = 4608 := by
  rw [mem24, Mem.size_write_of_size mem23_size (by decide) (B256.length_toBytes _)]; decide

def mem25 : Mem := mem24.write 3746 (0x69780 : B256).toBytes
def img25 : Bytes := Bytes.writeAt img24 3746 (0x69780 : B256).toBytes
theorem mem25_wf : Mem.Wf mem25 := mem24_wf.write _ _
theorem mem25_reads : Mem.Reads mem25 img25 := Mem.Reads.write mem24_wf mem24_reads _ _
theorem mem25_size : mem25.size = 4608 := by
  rw [mem25, Mem.size_write_of_size mem24_size (by decide) (B256.length_toBytes _)]; decide

def mem26 : Mem := mem25.write 352 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
def img26 : Bytes := Bytes.writeAt img25 352 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
theorem mem26_wf : Mem.Wf mem26 := mem25_wf.write _ _
theorem mem26_reads : Mem.Reads mem26 img26 := Mem.Reads.write mem25_wf mem25_reads _ _
theorem mem26_size : mem26.size = 4608 := by
  rw [mem26, Mem.size_write_of_size mem25_size (by decide) (B256.length_toBytes _)]; decide

def mem27 : Mem := mem26.write 820 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
def img27 : Bytes := Bytes.writeAt img26 820 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
theorem mem27_wf : Mem.Wf mem27 := mem26_wf.write _ _
theorem mem27_reads : Mem.Reads mem27 img27 := Mem.Reads.write mem26_wf mem26_reads _ _
theorem mem27_size : mem27.size = 4608 := by
  rw [mem27, Mem.size_write_of_size mem26_size (by decide) (B256.length_toBytes _)]; decide

def mem28 : Mem := mem27.write 1353 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
def img28 : Bytes := Bytes.writeAt img27 1353 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
theorem mem28_wf : Mem.Wf mem28 := mem27_wf.write _ _
theorem mem28_reads : Mem.Reads mem28 img28 := Mem.Reads.write mem27_wf mem27_reads _ _
theorem mem28_size : mem28.size = 4608 := by
  rw [mem28, Mem.size_write_of_size mem27_size (by decide) (B256.length_toBytes _)]; decide

def mem29 : Mem := mem28.write 2260 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
def img29 : Bytes := Bytes.writeAt img28 2260 (0x3e40d73eb977dc6a537af587d48316fee66e9c8c : B256).toBytes
theorem mem29_wf : Mem.Wf mem29 := mem28_wf.write _ _
theorem mem29_reads : Mem.Reads mem29 img29 := Mem.Reads.write mem28_wf mem28_reads _ _
theorem mem29_size : mem29.size = 4608 := by
  rw [mem29, Mem.size_write_of_size mem28_size (by decide) (B256.length_toBytes _)]; decide

def logData1 : Bytes := (mem12.read 512 128).1
def logData2 : Bytes := (mem14.read 512 64).1
def logData3 : Bytes := (mem16.read 512 64).1

/-! ## The internal calls -/

theorem sloadCost_le (sevm : Sevm) (b : Devm) (k : B256) : sloadCost sevm b k ≤ 2100 := by
  unfold sloadCost; split_ifs <;> decide

theorem sstoreCost_le' (sevm : Sevm) (b : Devm) (k v : B256) : sstoreCost sevm b k v ≤ 22100 :=
  le_trans (sstoreCost_le sevm b k v) (by decide)

theorem fn1_run {sevm : Sevm} {b : Devm} {G : Nat} :
    SFunc.RunExact prog sevm (St b [0x120, 0x200, 0x2f] mem3 (G + 235)) t_026d_c1
      (.returned (St b [0x1e13380, 0x1baf80, 0x5a39a80, 0x278d00, 0x4f1a00, 0x69780, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c] mem3 G)) := by
  unfold t_026d_c1
  refine rx_dest ?_
  refine rx_push0 (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_push (w := 0xe0) (by decide) (by simp) ?_
  refine rx_dup (n := 8) rfl (by simp) ?_
  refine rx_dup (n := 10) rfl (by simp) ?_
  refine rx_sub' (v := 0xe0) (by decide +kernel) (by simp) ?_
  refine rx_slt (v := 0x0) (by decide +kernel) (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x283) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0283_c1
  refine rx_dest ?_
  refine rx_dup (n := 7) rfl (by simp) ?_
  refine rx_mload (c := 3) (v := 0x3e40d73eb977dc6a537af587d48316fee66e9c8c) (by rw [St.extCost_eq mem3_size]; decide) (by rw [Mem.Reads.read mem3_reads]; decide +kernel) (read_covered mem3_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_shl (v := 0x10000000000000000000000000000000000000000) (by decide +kernel) (by simp) ?_
  refine rx_sub' (v := 0xffffffffffffffffffffffffffffffffffffffff) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_and (v := 0x3e40d73eb977dc6a537af587d48316fee66e9c8c) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_eq (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x299) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0299_c1
  refine rx_dest ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_dup (n := 9) rfl (by simp) ?_
  refine rx_add' (v := 0x140) (by decide +kernel) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x69780) (by rw [St.extCost_eq mem3_size]; decide) (by rw [Mem.Reads.read mem3_reads]; decide +kernel) (read_covered mem3_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_dup (n := 10) rfl (by simp) ?_
  refine rx_add' (v := 0x160) (by decide +kernel) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x4f1a00) (by rw [St.extCost_eq mem3_size]; decide) (by rw [Mem.Reads.read mem3_reads]; decide +kernel) (read_covered mem3_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x60) (by decide) (by simp) ?_
  refine rx_dup (n := 11) rfl (by simp) ?_
  refine rx_add' (v := 0x180) (by decide +kernel) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x278d00) (by rw [St.extCost_eq mem3_size]; decide) (by rw [Mem.Reads.read mem3_reads]; decide +kernel) (read_covered mem3_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x80) (by decide) (by simp) ?_
  refine rx_dup (n := 12) rfl (by simp) ?_
  refine rx_add' (v := 0x1a0) (by decide +kernel) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x5a39a80) (by rw [St.extCost_eq mem3_size]; decide) (by rw [Mem.Reads.read mem3_reads]; decide +kernel) (read_covered mem3_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_dup (n := 13) rfl (by simp) ?_
  refine rx_add' (v := 0x1c0) (by decide +kernel) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x1baf80) (by rw [St.extCost_eq mem3_size]; decide) (by rw [Mem.Reads.read mem3_reads]; decide +kernel) (read_covered mem3_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 13) rfl ?_
  refine rx_add' (v := 0x1e0) (by decide +kernel) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x1e13380) (by rw [St.extCost_eq mem3_size]; decide) (by rw [Mem.Reads.read mem3_reads]; decide +kernel) (read_covered mem3_size (by decide) (by decide)) (by simp) ?_
  refine rx_swap (n := 4) rfl ?_
  refine rx_swap (n := 14) rfl ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_swap (n := 13) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_swap (n := 11) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 10) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 8) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 6) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_swap (n := 4) rfl ?_
  refine rx_pop ?_
  refine rx_swap (n := 2) rfl ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

def fn2Cost (sevm : Sevm) (b : Devm) : Nat := 8 + sstoreCost sevm ((afterSload sevm b 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80 + 1327 + sloadCost sevm b 0x0 + 61

theorem fn2_run {sevm : Sevm} (fr : CtorFrame sevm) {b : Devm} {G : Nat} (hG : 2300 < G) (hz0 : b.getStorVal sevm.currentTarget 0x0 = 0) :
    SFunc.RunExact prog sevm (St b [0x1baf80, 0x14b, 0x1e13380, 0x1baf80, 0x5a39a80, 0x278d00, 0x4f1a00, 0x69780, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c] mem12 (G + fn2Cost sevm b)) t_0160_c2
      (.returned (St (afterSstore sevm ((afterSload sevm b 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80) [0x1e13380, 0x1baf80, 0x5a39a80, 0x278d00, 0x4f1a00, 0x69780, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c] mem14 G)) := by
  rw [show G + fn2Cost sevm b = G + 8 + sstoreCost sevm ((afterSload sevm b 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80 + 1327 + sloadCost sevm b 0x0 + 61 by unfold fn2Cost; omega]
  unfold t_0160_c2
  refine rx_dest ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x69780) (by rw [St.extCost_eq mem12_size]; decide) (by rw [Mem.Reads.read mem12_reads]; decide +kernel) (read_covered mem12_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_lt (v := 0x0) (by decide +kernel) (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x183) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0183_c2
  refine rx_dest ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x4f1a00) (by rw [St.extCost_eq mem12_size]; decide) (by rw [Mem.Reads.read mem12_reads]; decide +kernel) (read_covered mem12_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_gt (v := 0x0) (by decide +kernel) (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x1a6) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_01a6_c2
  refine rx_dest ?_
  refine rx_push0 (by simp) ?_
  refine rx_sload_sel fr.fork (by simp) ?_
  rw [hz0]
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_mload (c := 3) (v := 0x200) (by rw [St.extCost_eq mem12_size]; decide) (by rw [Mem.Reads.read mem12_reads]; decide +kernel) (read_covered mem12_size (by decide) (by decide)) (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem13) (by rw [St.extCost_eq mem12_size]; decide) rfl ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_add' (v := 0x220) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 3) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := mem14) (by rw [St.extCost_eq mem13_size]; decide) rfl ?_
  refine rx_push (w := pw1) rfl (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_add' (v := 0x240) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x200) (by rw [St.extCost_eq mem14_size]; decide) (by rw [Mem.Reads.read mem14_reads]; decide +kernel) (read_covered mem14_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_sub' (v := 0x40) (by decide +kernel) (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_log1 (c := 1262) (data := logData2) fr.static (by rw [St.extCost_eq mem14_size]; decide) rfl (read_covered_len mem14_size (by decide) (by decide)) ?_
  refine rx_push0 (by simp) ?_
  refine rx_sstore fr.fork (by unfold gCallStipend; omega) fr.static ?_
  exact rx_ret

theorem fn2Cost_le (sevm : Sevm) (b : Devm) : fn2Cost sevm b ≤ 25596 := by
  unfold fn2Cost
  have h18 := sloadCost_le sevm b 0x0
  have h42 := sstoreCost_le' sevm ((afterSload sevm b 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80
  omega

def fn3Cost (sevm : Sevm) (b : Devm) : Nat := 8 + sstoreCost sevm ((afterSload sevm b 0x1).addLog ⟨sevm.currentTarget, [pw2], logData3⟩) 0x1 0x1e13380 + 1328 + sloadCost sevm b 0x1 + 62

theorem fn3_run {sevm : Sevm} (fr : CtorFrame sevm) {b : Devm} {G : Nat} (hG : 2300 < G) (hz1 : b.getStorVal sevm.currentTarget 0x1 = 0) :
    SFunc.RunExact prog sevm (St b [0x1e13380, 0x154, 0x1e13380, 0x1baf80, 0x5a39a80, 0x278d00, 0x4f1a00, 0x69780, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c] mem14 (G + fn3Cost sevm b)) t_01e5_c3
      (.returned (St (afterSstore sevm ((afterSload sevm b 0x1).addLog ⟨sevm.currentTarget, [pw2], logData3⟩) 0x1 0x1e13380) [0x1e13380, 0x1baf80, 0x5a39a80, 0x278d00, 0x4f1a00, 0x69780, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c] mem16 G)) := by
  rw [show G + fn3Cost sevm b = G + 8 + sstoreCost sevm ((afterSload sevm b 0x1).addLog ⟨sevm.currentTarget, [pw2], logData3⟩) 0x1 0x1e13380 + 1328 + sloadCost sevm b 0x1 + 62 by unfold fn3Cost; omega]
  unfold t_01e5_c3
  refine rx_dest ?_
  refine rx_push (w := 0xe0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x278d00) (by rw [St.extCost_eq mem14_size]; decide) (by rw [Mem.Reads.read mem14_reads]; decide +kernel) (read_covered mem14_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_lt (v := 0x0) (by decide +kernel) (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x208) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0208_c3
  refine rx_dest ?_
  refine rx_push (w := 0x100) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x5a39a80) (by rw [St.extCost_eq mem14_size]; decide) (by rw [Mem.Reads.read mem14_reads]; decide +kernel) (read_covered mem14_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_gt (v := 0x0) (by decide +kernel) (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x22c) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_022c_c3
  refine rx_dest ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_sload_sel fr.fork (by simp) ?_
  rw [hz1]
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_mload (c := 3) (v := 0x200) (by rw [St.extCost_eq mem14_size]; decide) (by rw [Mem.Reads.read mem14_reads]; decide +kernel) (read_covered mem14_size (by decide) (by decide)) (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem15) (by rw [St.extCost_eq mem14_size]; decide) rfl ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_add' (v := 0x220) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 3) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := mem16) (by rw [St.extCost_eq mem15_size]; decide) rfl ?_
  refine rx_push (w := pw2) rfl (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_add' (v := 0x240) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x200) (by rw [St.extCost_eq mem16_size]; decide) (by rw [Mem.Reads.read mem16_reads]; decide +kernel) (read_covered mem16_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_sub' (v := 0x40) (by decide +kernel) (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_log1 (c := 1262) (data := logData3) fr.static (by rw [St.extCost_eq mem16_size]; decide) rfl (read_covered_len mem16_size (by decide) (by decide)) ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_sstore fr.fork (by unfold gCallStipend; omega) fr.static ?_
  exact rx_ret

theorem fn3Cost_le (sevm : Sevm) (b : Devm) : fn3Cost sevm b ≤ 25598 := by
  unfold fn3Cost
  have h18 := sloadCost_le sevm b 0x1
  have h42 := sstoreCost_le' sevm ((afterSload sevm b 0x1).addLog ⟨sevm.currentTarget, [pw2], logData3⟩) 0x1 0x1e13380
  omega

/-! ## The whole constructor -/

/-- The constructor's exact cost from the world `b`. -/
def ctorCost (sevm : Sevm) (b : Devm) : Nat := 1077 + fn3Cost sevm (afterSstore sevm ((afterSload sevm (b.addLog ⟨sevm.currentTarget, [pw0, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c], logData1⟩) 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80) + 18 + fn2Cost sevm (b.addLog ⟨sevm.currentTarget, [pw0, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c], logData1⟩) + 2888

/-- The world the constructor leaves. -/
def ctorWorld (sevm : Sevm) (b : Devm) : Devm := (afterSstore sevm ((afterSload sevm (afterSstore sevm ((afterSload sevm (b.addLog ⟨sevm.currentTarget, [pw0, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c], logData1⟩) 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80) 0x1).addLog ⟨sevm.currentTarget, [pw2], logData3⟩) 0x1 0x1e13380)

/-- **The Lido CircuitBreaker constructor, gas-exact**: from a fresh creation frame (zero call
value) with an empty stack and memory and `G + ctorCost` gas, the lifted constructor halts with
`G` gas left, returning the memory window `[0, 4584)`. -/
theorem ctor_run {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) {b : Devm} (hempty : Devm.getStor b sevm.currentTarget = Stor.empty)
    {G : Nat} (hG : 2300 < G) :
    SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCost sevm b))
      (returnPost (St (ctorWorld sevm b) [0x0, 0x11e8] mem29 G) 0x0 0x11e8 []) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  rw [show G + ctorCost sevm b = G + 1077 + fn3Cost sevm (afterSstore sevm ((afterSload sevm (b.addLog ⟨sevm.currentTarget, [pw0, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c], logData1⟩) 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80) + 18 + fn2Cost sevm (b.addLog ⟨sevm.currentTarget, [pw0, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c], logData1⟩) + 2888 by unfold ctorCost; omega]

  unfold t_0000_c0
  refine rx_push (w := 0x120) (by decide) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mstore (c := 12) (M' := mem1) (by rw [St.extCost_eq mem0_size]; decide) rfl ?_
  refine rx_callvalue (by simp) ?_
  rw [hvalue]
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x10) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0010_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x120) (by rw [St.extCost_eq mem1_size]; decide) (by rw [Mem.Reads.read mem1_reads]; decide +kernel) (read_covered mem1_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x1526) (by decide) (by simp) ?_
  refine rx_codesize (by simp) ?_
  rw [hcode, code_size]
  refine rx_sub' (v := 0xe0) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_push (w := 0x1526) (by decide) (by simp) ?_
  refine rx_dup (n := 3) rfl (by simp) ?_
  refine rx_codecopy (c := 63) (M' := mem2) (by rw [St.extCost_eq mem1_size]; decide) (by rw [hcode]; rfl) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_add' (v := 0x200) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := mem3) (by rw [St.extCost_eq mem2_size]; decide) rfl ?_
  refine rx_push (w := 0x2f) (by decide) (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_push (w := 0x26d) (by decide) (by simp) ?_
  refine rx_callRet (j := 1) rfl (fn1_run) ?_
  unfold t_002f_c0
  refine rx_dest ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_shl (v := 0x10000000000000000000000000000000000000000) (by decide +kernel) (by simp) ?_
  refine rx_sub' (v := 0xffffffffffffffffffffffffffffffffffffffff) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 7) rfl (by simp) ?_
  refine rx_and (v := 0x3e40d73eb977dc6a537af587d48316fee66e9c8c) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x56) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0056_c0
  refine rx_dest ?_
  refine rx_dup (n := 5) rfl (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_sub' (v := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff96880) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x76) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0076_c0
  refine rx_dest ?_
  refine rx_dup (n := 4) rfl (by simp) ?_
  refine rx_dup (n := 6) rfl (by simp) ?_
  refine rx_gt (v := 0x0) (by decide +kernel) (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x97) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0097_c0
  refine rx_dest ?_
  refine rx_dup (n := 3) rfl (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_sub' (v := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd87300) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0xb7) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00b7_c0
  refine rx_dest ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_dup (n := 4) rfl (by simp) ?_
  refine rx_gt (v := 0x0) (by decide +kernel) (by simp) ?_
  refine rx_iszero (v := 0x1) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0xd8) (by decide) (by simp) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00d8_c0
  refine rx_dest ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_push (w := 0x1) (by decide) (by simp) ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_shl (v := 0x10000000000000000000000000000000000000000) (by decide +kernel) (by simp) ?_
  refine rx_sub' (v := 0xffffffffffffffffffffffffffffffffffffffff) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 7) rfl (by simp) ?_
  refine rx_and (v := 0x3e40d73eb977dc6a537af587d48316fee66e9c8c) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x80) (by decide) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem4) (by rw [St.extCost_eq mem3_size]; decide) rfl ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_dup (n := 8) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := mem5) (by rw [St.extCost_eq mem4_size]; decide) rfl ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_dup (n := 7) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := mem6) (by rw [St.extCost_eq mem5_size]; decide) rfl ?_
  refine rx_push (w := 0xe0) (by decide) (by simp) ?_
  refine rx_dup (n := 6) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := mem7) (by rw [St.extCost_eq mem6_size]; decide) rfl ?_
  refine rx_push (w := 0x100) (by decide) (by simp) ?_
  refine rx_dup (n := 5) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 3) (M' := mem8) (by rw [St.extCost_eq mem7_size]; decide) rfl ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_mload (c := 3) (v := 0x200) (by rw [St.extCost_eq mem8_size]; decide) (by rw [Mem.Reads.read mem8_reads]; decide +kernel) (read_covered mem8_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 9) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_mstore (c := 6) (M' := mem9) (by rw [St.extCost_eq mem8_size]; decide) rfl ?_
  refine rx_push (w := 0x20) (by decide) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_add' (v := 0x220) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 9) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := mem10) (by rw [St.extCost_eq mem9_size]; decide) rfl ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_add' (v := 0x240) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 7) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := mem11) (by rw [St.extCost_eq mem10_size]; decide) rfl ?_
  refine rx_push (w := 0x60) (by decide) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_add' (v := 0x260) (by decide +kernel) (by simp) ?_
  refine rx_dup (n := 6) rfl (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_mstore (c := 6) (M' := mem12) (by rw [St.extCost_eq mem11_size]; decide) rfl ?_
  refine rx_push (w := pw0) rfl (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_add' (v := 0x280) (by decide +kernel) (by simp) ?_
  refine rx_push (w := 0x40) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x200) (by rw [St.extCost_eq mem12_size]; decide) (by rw [Mem.Reads.read mem12_reads]; decide +kernel) (read_covered mem12_size (by decide) (by decide)) (by simp) ?_
  refine rx_dup (n := 0) rfl (by simp) ?_
  refine rx_swap (n := 1) rfl ?_
  refine rx_sub' (v := 0x80) (by decide +kernel) (by simp) ?_
  refine rx_swap (n := 0) rfl ?_
  refine rx_log2 (c := 2149) (data := logData1) fr.static (by rw [St.extCost_eq mem12_size]; decide) rfl (read_covered_len mem12_size (by decide) (by decide)) ?_
  refine rx_push (w := 0x14b) (by decide) (by simp) ?_
  refine rx_dup (n := 2) rfl (by simp) ?_
  refine rx_push (w := 0x160) (by decide) (by simp) ?_
  refine rx_callRet (j := 2) rfl (fn2_run fr (by omega) (by show (Devm.getStor _ sevm.currentTarget).get _ = 0; simp only [Devm.addLog_getStor, hempty]; decide +kernel)) ?_
  unfold t_014b_c0
  refine rx_dest ?_
  refine rx_push (w := 0x154) (by decide) (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x1e5) (by decide) (by simp) ?_
  refine rx_callRet (j := 3) rfl (fn3_run fr (by omega) (by show (Devm.getStor _ sevm.currentTarget).get _ = 0; simp only [Devm.addLog_getStor, afterSload_getStor, afterSstore_getStor_self, Stor.get_set_ite, hempty]; decide +kernel)) ?_
  unfold t_0154_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_push (w := 0x2d0) (by decide) (by simp) ?_
  refine rx_jump (j := 4) rfl ?_
  unfold t_02d0_c4
  refine rx_dest ?_
  refine rx_push (w := 0x80) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x3e40d73eb977dc6a537af587d48316fee66e9c8c) (by rw [St.extCost_eq mem16_size]; decide) (by rw [Mem.Reads.read mem16_reads]; decide +kernel) (read_covered mem16_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0xa0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x69780) (by rw [St.extCost_eq mem16_size]; decide) (by rw [Mem.Reads.read mem16_reads]; decide +kernel) (read_covered mem16_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0xc0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x4f1a00) (by rw [St.extCost_eq mem16_size]; decide) (by rw [Mem.Reads.read mem16_reads]; decide +kernel) (read_covered mem16_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0xe0) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x278d00) (by rw [St.extCost_eq mem16_size]; decide) (by rw [Mem.Reads.read mem16_reads]; decide +kernel) (read_covered mem16_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x100) (by decide) (by simp) ?_
  refine rx_mload (c := 3) (v := 0x5a39a80) (by rw [St.extCost_eq mem16_size]; decide) (by rw [Mem.Reads.read mem16_reads]; decide +kernel) (read_covered mem16_size (by decide) (by decide)) (by simp) ?_
  refine rx_push (w := 0x11e8) (by decide) (by simp) ?_
  refine rx_push (w := 0x33e) (by decide) (by simp) ?_
  refine rx_push0 (by simp) ?_
  refine rx_codecopy (c := 847) (M' := mem17) (by rw [St.extCost_eq mem16_size]; decide) (by rw [hcode]; rfl) ?_
  refine rx_push0 (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x247) (by decide) (by simp) ?_
  refine rx_add' (v := 0x247) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem18) (by rw [St.extCost_eq mem17_size]; decide) rfl ?_
  refine rx_push (w := 0xe07) (by decide) (by simp) ?_
  refine rx_add' (v := 0xe07) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem19) (by rw [St.extCost_eq mem18_size]; decide) rfl ?_
  refine rx_push0 (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x281) (by decide) (by simp) ?_
  refine rx_add' (v := 0x281) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem20) (by rw [St.extCost_eq mem19_size]; decide) rfl ?_
  refine rx_push (w := 0xdad) (by decide) (by simp) ?_
  refine rx_add' (v := 0xdad) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem21) (by rw [St.extCost_eq mem20_size]; decide) rfl ?_
  refine rx_push0 (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x139) (by decide) (by simp) ?_
  refine rx_add' (v := 0x139) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem22) (by rw [St.extCost_eq mem21_size]; decide) rfl ?_
  refine rx_push (w := 0xefc) (by decide) (by simp) ?_
  refine rx_add' (v := 0xefc) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem23) (by rw [St.extCost_eq mem22_size]; decide) rfl ?_
  refine rx_push0 (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x220) (by decide) (by simp) ?_
  refine rx_add' (v := 0x220) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem24) (by rw [St.extCost_eq mem23_size]; decide) rfl ?_
  refine rx_push (w := 0xea2) (by decide) (by simp) ?_
  refine rx_add' (v := 0xea2) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem25) (by rw [St.extCost_eq mem24_size]; decide) rfl ?_
  refine rx_push0 (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x160) (by decide) (by simp) ?_
  refine rx_add' (v := 0x160) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem26) (by rw [St.extCost_eq mem25_size]; decide) rfl ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x334) (by decide) (by simp) ?_
  refine rx_add' (v := 0x334) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem27) (by rw [St.extCost_eq mem26_size]; decide) rfl ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_dup (n := 1) rfl (by simp) ?_
  refine rx_push (w := 0x549) (by decide) (by simp) ?_
  refine rx_add' (v := 0x549) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem28) (by rw [St.extCost_eq mem27_size]; decide) rfl ?_
  refine rx_push (w := 0x8d4) (by decide) (by simp) ?_
  refine rx_add' (v := 0x8d4) (by decide +kernel) (by simp) ?_
  refine rx_mstore (c := 3) (M' := mem29) (by rw [St.extCost_eq mem28_size]; decide) rfl ?_
  refine rx_push (w := 0x11e8) (by decide) (by simp) ?_
  refine rx_push0 (by simp) ?_
  exact rx_return_any rfl (by rw [St.extCost_eq mem29_size]; decide)

theorem ctorCost_le (sevm : Sevm) (b : Devm) : ctorCost sevm b ≤ 55177 := by
  unfold ctorCost
  have h132 := fn2Cost_le sevm (b.addLog ⟨sevm.currentTarget, [pw0, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c], logData1⟩)
  have h138 := fn3Cost_le sevm (afterSstore sevm ((afterSload sevm (b.addLog ⟨sevm.currentTarget, [pw0, 0x3e40d73eb977dc6a537af587d48316fee66e9c8c], logData1⟩) 0x0).addLog ⟨sevm.currentTarget, [pw1], logData2⟩) 0x0 0x1baf80)
  omega

/-! ## The returned runtime and the constructor's facts -/

/-- The window the constructor returns is the certified deployed runtime: the template copied
from the creation input with the five immutable values patched into the twelve reference spans. -/
theorem runtime_window :
    img29.sliceD 0 4584 0 = Blanc.Lift.LidoCircuitBreakerDeployed.code.toList := by
  rw [ByteArray.toList_eq_toList_data]
  apply eq_of_beq
  decide +kernel

theorem returned_read : (mem29.read 0 4584).1 = Blanc.Lift.LidoCircuitBreakerDeployed.code.toList := by
  rw [Mem.Reads.read mem29_reads]
  exact runtime_window

/-- **The Lido constructor, with its halting state's facts**: output the certified runtime, the
world's error, storage slots 0 and 1 set to the initial pause duration and heartbeat interval,
`G` gas left. -/
theorem ctor_run_facts {sevm : Sevm} (fr : CtorFrame sevm) (hcode : sevm.code = code)
    (hvalue : sevm.value = 0) {b : Devm} (hempty : Devm.getStor b sevm.currentTarget = Stor.empty)
    {G : Nat} (hG : 2300 < G) :
    ∃ post, SProg.RunExact prog sevm (St b [] Mem.empty (G + ctorCost sevm b)) post ∧
      post.output = Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧ post.error = b.error ∧
      Devm.getStor post sevm.currentTarget =
        ((Stor.empty).set 0x0 0x1baf80).set 0x1 0x1e13380 ∧
      post.gasLeft = G := by
  obtain ⟨p1, p2, p3, p4⟩ := returnPost_facts (St (ctorWorld sevm b) [0x0, 0x11e8] mem29 G)
    0x0 0x11e8 []
  have h0 : (0x0 : B256).toNat = 0 := by decide
  have h1 : (0x11e8 : B256).toNat = 4584 := by decide
  refine ⟨_, ctor_run fr hcode hvalue hempty hG, ?_, ?_, ?_, p4⟩
  · rw [p1, St.memory, h0, h1]
    exact returned_read
  · rw [p2, St_error]
    simp only [ctorWorld, afterSstore_error, afterSload_error, Devm.addLog_error]
  · rw [p3, St_getStor]
    simp only [ctorWorld, afterSstore_getStor_self, afterSload_getStor, Devm.addLog_getStor, hempty]

end Blanc.Lift.LidoCircuitBreakerDeployed.Creation
