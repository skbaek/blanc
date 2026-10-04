import Blanc.Lift.UniswapV2Pair.SafeTransferWalk

/-! Pointer-generic literal helper57 (safeTransfer) walk for skim's second transfer.

The helper reads the free pointer from memory; these stages keep it symbolic so a
caller whose free pointer moved (skim's transfer1 follows transfer0's allocation)
can instantiate them. Consolidation note: SafeTransferWalk holds private,
pointer-generic stages with the same semantics; see the lane report. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The literal eighty-instruction helper57 initializer before its copy loop. -/
def skimTransferInitLine : List Ninst := [
  .push [0x40] (by decide),
  .reg (.dup 0),
  .reg .mload,
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .add,
  .reg (.dup 2),
  .reg .mstore,
  .push [0x19] (by decide),
  .reg (.dup 1),
  .reg .mstore,
  .push [0x74, 0x72, 0x61, 0x6e, 0x73, 0x66, 0x65, 0x72, 0x28, 0x61, 0x64, 0x64, 0x72, 0x65, 0x73, 0x73, 0x2c, 0x75, 0x69, 0x6e, 0x74, 0x32, 0x35, 0x36, 0x29, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .push [0x20] (by decide),
  .reg (.swap 1),
  .reg (.dup 2),
  .reg .add,
  .reg .mstore,
  .reg (.dup 1),
  .reg .mload,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg (.dup 5),
  .reg (.dup 1),
  .reg .and,
  .push [0x24] (by decide),
  .reg (.dup 3),
  .reg .add,
  .reg .mstore,
  .push [0x44] (by decide),
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .add,
  .reg (.dup 6),
  .reg (.swap 0),
  .reg .mstore,
  .reg (.dup 4),
  .reg .mload,
  .reg (.dup 0),
  .reg (.dup 4),
  .reg .sub,
  .reg (.swap 0),
  .reg (.swap 1),
  .reg .add,
  .reg (.dup 1),
  .reg .mstore,
  .push [0x64] (by decide),
  .reg (.swap 0),
  .reg (.swap 2),
  .reg .add,
  .reg (.dup 4),
  .reg .mstore,
  .reg (.swap 1),
  .reg (.dup 1),
  .reg .add,
  .reg (.dup 0),
  .reg .mload,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide),
  .reg .and,
  .push [0xa9, 0x05, 0x9c, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide),
  .reg .or,
  .reg (.dup 1),
  .reg .mstore,
  .reg (.swap 2),
  .reg .mload,
  .reg (.dup 1),
  .reg .mload,
  .push [0x00] (by decide),
  .reg (.swap 4),
  .push [0x60] (by decide),
  .reg (.swap 4),
  .reg (.dup 9),
  .reg .and,
  .reg (.swap 3),
  .reg (.swap 2),
  .reg (.swap 1),
  .reg (.dup 2),
  .reg (.swap 1),
  .reg (.swap 0),
  .reg (.dup 0),
  .reg (.dup 3),
  .reg (.dup 3)]

/-- Symbolic initializer state: every free-pointer read stays a read of the actual memory. -/
theorem skimTransferInitLine_inv {sevm : Sevm} {b final : Devm} {R : List B256} {M : Mem}
    {G : Nat} {amount toWord tokenWord rho : B256}
    (run : Line.Run sevm (St b (amount :: toWord :: tokenWord :: rho :: R) M G)
      skimTransferInitLine final) :
    let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
    let M1 := (M.read (64 : B256).toNat 32).2
    let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
    let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
    let M4 := M3.write ((32 + p1) : B256).toNat
      (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
    let M5 := (M4.read (64 : B256).toNat 32).2
    let M6 := M5.write ((p2 + 36) : B256).toNat
      ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
    let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
    let M8 := (M7.read (64 : B256).toNat 32).2
    let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
    let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
    let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
    let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
    let M12 := M11.write ((p3 + 32) : B256).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
        (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
    let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
    let M13 := (M12.read (64 : B256).toNat 32).2
    let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
    let M14 := (M13.read (p3 : B256).toNat 32).2
    ∃ gas, final = St b ((p3 + 32) :: p5 :: p6 :: p6 :: (p3 + 32) :: p5 :: p5 :: p3 ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount ::
      toWord :: tokenWord :: rho :: R) M14 gas := by
  dsimp only [skimTransferInitLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_or hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨gas, rfl⟩ := ri_dup rfl hs
  cases run
  exact ⟨gas, rfl⟩

/-- The literal four-byte merge and CALL operand preparation of helper57. -/
def skimTransferCallLine : List Ninst := [
  .push [0x01] (by decide),
  .reg (.dup 3),
  .push [0x20] (by decide),
  .reg .sub,
  .push [0x01, 0x00] (by decide),
  .reg .exp,
  .reg .sub,
  .reg (.dup 0),
  .reg .not,
  .reg (.dup 2),
  .reg .mload,
  .reg .and,
  .reg (.dup 1),
  .reg (.dup 4),
  .reg .mload,
  .reg .and,
  .reg (.dup 0),
  .reg (.dup 2),
  .reg .or,
  .reg (.dup 5),
  .reg .mstore,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg .pop,
  .reg (.swap 0),
  .reg .pop,
  .reg .add,
  .reg (.swap 1),
  .reg .pop,
  .reg .pop,
  .push [0x00] (by decide),
  .push [0x40] (by decide),
  .reg .mload,
  .reg (.dup 0),
  .reg (.dup 3),
  .reg .sub,
  .reg (.dup 1),
  .push [0x00] (by decide),
  .reg (.dup 6),
  .reg .gas]

/-- Symbolic CALL operands: the input pointer is the actual reloaded free pointer. -/
theorem skimTransferCallLine_inv {sevm : Sevm} {b final : Devm} {R : List B256} {M : Mem}
    {G : Nat} {src dst a x y z w token : B256}
    (run : Line.Run sevm (St b (src :: dst :: 4 :: a :: x :: y :: z :: w :: token :: R) M G)
      skimTransferCallLine final) :
    let mask := B256.bexp 256 (32 - 4) - 1
    let M1 := (M.read src.toNat 32).2
    let M2 := (M1.read dst.toNat 32).2
    let M3 := M2.write dst.toNat
      (((Bytes.toB256 (M.read src.toNat 32).1) &&& ~~~mask) |||
        ((Bytes.toB256 (M1.read dst.toNat 32).1) &&& mask)).toBytes
    let q := Bytes.toB256 (M3.read 64 32).1
    let M4 := (M3.read 64 32).2
    ∃ forwarded callGas, final = St b (forwarded :: token :: 0 :: q :: ((a + y) - q) :: q ::
      0 :: (a + y) :: token :: R) M4 callGas := by
  dsimp only [skimTransferCallLine] at run
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_exp hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_not hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_or hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_mload hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_sub hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := Line.of_run_cons run; obtain ⟨forwarded, callGas, rfl⟩ := ri_gas hs
  cases run
  exact ⟨forwarded, callGas, rfl⟩

/-- The literal copy-loop body of helper57 (one 32-byte word). -/
def skimCopyBodyLine : List Ninst := [
  .reg (.dup 0), .reg .mload, .reg (.dup 2), .reg .mstore,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xe0] (by decide),
  .reg (.swap 0), .reg (.swap 2), .reg .add, .reg (.swap 1), .push [0x20] (by decide),
  .reg (.swap 1), .reg (.dup 2), .reg .add, .reg (.swap 1), .reg .add,
  .push [0x20, 0xa4] (by decide)]

/-- One copy-loop guard and body: a remaining length of at least32 copies one word. -/
theorem skimCopyPass_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {src dst len : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 71 ∉ C) (enough : ¬ len < (32 : B256))
    (run : SFunc.RunCutP P cert.prog sevm C (St b (src :: dst :: len :: R) M G) t_20a4_c57 r) :
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b ((32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
        ((M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes)
        residual) t_20a4_c57 r := by
  have h := run
  unfold t_20a4_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := len) rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [32] = (32 : B256) from rfl, B256.ltCheck,
    ite_eq_right enough] at h
  rcases ric_branchP h with ⟨_, _, body⟩ | ⟨nonzero, _, _⟩
  · change SFunc.RunCutP P cert.prog sevm C _
      (skimCopyBodyLine.foldr SFunc.next (.jump 71)) r at body
    obtain ⟨_, line, tail⟩ := SFunc.RunCutP.split_nexts (fun step => project step)
      skimCopyBodyLine body
    dsimp only [skimCopyBodyLine] at line
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mload hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_mstore hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_swap rfl hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_add hs
    obtain ⟨_, hs, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_push hs
    cases line
    cases tail with
    | jumpCut _ cut _ => exact (notCut cut).elim
    | jump _ _ lookup pop k =>
      change some t_20a4_c57 = _ at lookup
      cases lookup
      obtain ⟨_, eq⟩ := St.of_pop1 pop
      rw [eq] at k
      exact ⟨_, k⟩
  · exact (nonzero rfl).elim

/-- The68-byte payload copy: two whole words, then the guard exits with a4-byte tail. -/
theorem skimCopy68_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {src dst : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 71 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (src :: dst :: 68 :: R) M G) t_20a4_c57 r) :
    let M1 := (M.read src.toNat 32).2.write dst.toNat
      (Bytes.toB256 (M.read src.toNat 32).1).toBytes
    let M2 := (M1.read (32 + src).toNat 32).2.write (32 + dst).toNat
      (Bytes.toB256 (M1.read (32 + src).toNat 32).1).toBytes
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b ((32 + (32 + src)) :: (32 + (32 + dst)) :: 4 :: R) M2 residual) t_20e1_c57 r := by
  dsimp only
  obtain ⟨_, first⟩ := skimCopyPass_inv project notCut (by decide : ¬ (68 : B256) < 32) run
  rw [show (68 : B256) + ~~~31 = 36 from rfl] at first
  obtain ⟨_, second⟩ := skimCopyPass_inv project notCut (by decide : ¬ (36 : B256) < 32) first
  rw [show (36 : B256) + ~~~31 = 4 from rfl] at second
  have h := second
  unfold t_20a4_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := (4 : B256)) rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rw [show B256.ltCheck (4 : B256) (Bytes.toB256 [32]) = 1 from by decide] at h
  rcases ric_branchP h with ⟨zero, _, _⟩ | ⟨_, _, body⟩
  · exact ((by decide : (1 : B256) ≠ 0) zero).elim
  · exact ⟨_, body⟩

/-- The literal tree after helper57's CALL: keep the flag, then branch on the reply width. -/
def skimTransferReplyTree : SFunc :=
  .next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .returndatasize)
    (.next (.reg (.dup 0)) (.next (.push [0x00] (by decide)) (.next (.reg (.dup 1))
      (.next (.reg .eq) (.next (.push [0x21, 0x43] (by decide))
        (.branch t_2122_c57 t_2143_c57)))))))))

/-- After the CALL, an empty reply keeps memory and the sentinel96; a nonempty reply
allocates its full returndata at the actual free pointer (modular pointer bump). -/
theorem skimTransferReply_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {d : Devm} {R : List B256} {V : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {flag endWord tokenM y z amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 16 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St d (flag :: endWord :: tokenM :: y :: z :: amount :: toWord :: tokenWord :: rho :: R) V G)
      skimTransferReplyTree r) :
    let len := d.returnData.length.toB256
    let ptr := Bytes.toB256 (V.read 64 32).1
    let V2 := (V.read 64 32).2.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
    let V3 := V2.write ptr.toNat len.toBytes
    let allocated := V3.write (ptr + 32).toNat (d.returnData.sliceD 0 len.toNat 0)
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St d (len :: (if len = 0 then 96 else ptr) :: flag :: y :: z :: amount :: toWord ::
        tokenWord :: rho :: R) (if len = 0 then V else allocated) residual) t_2148_c16 r := by
  dsimp only
  have h := run
  unfold skimTransferReplyTree at h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_eq (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl] at h
  by_cases empty : d.returnData.length.toB256 = 0
  · rw [empty, show B256.eqCheck 0 0 = (1 : B256) from rfl] at h
    rcases ric_branchP h with ⟨zero, _, _⟩ | ⟨_, _, body⟩
    · exact ((by decide : (1 : B256) ≠ 0) zero).elim
    · unfold t_2143_c57 at body
      obtain ⟨_, body⟩ := ric_destP body
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
      simp only [empty, ite_true]
      exact ⟨_, body⟩
  · have flag0 : B256.eqCheck d.returnData.length.toB256 0 = 0 := ite_eq_right empty
    rw [flag0] at h
    rcases ric_branchP h with ⟨_, _, body⟩ | ⟨nonzero, _, _⟩
    · simp only [empty, ite_false]
      unfold t_2122_c57 at body
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mload (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_not (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_and (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body
      obtain ⟨_, _, rfl⟩ := ri_returndatacopy (project hd)
      obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      cases body with
      | jumpCut _ cut _ => exact (notCut cut).elim
      | jump _ _ lookup pop tail =>
        change some t_2148_c16 = _ at lookup
        cases lookup
        obtain ⟨_, eq⟩ := St.of_pop1 pop
        rw [eq] at tail
        exact ⟨_, tail⟩
    · exact (nonzero rfl).elim

/-- The literal guard-and-cleanup tail of helper57 at entry 17: a nonzero flag
returns past the five helper locals; a zero flag reverts. -/
theorem skimTransferCheck_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {flag a x y z w rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm []
      (St b (flag :: a :: x :: y :: z :: w :: rho :: R) M G) t_2176_c17 (.done (.returned out))) :
    flag ≠ 0 ∧ ∃ residual, out = St b R M residual := by
  have h := run
  unfold t_2176_c17 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨positive, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_217b_c17.noOk = true)).elim
  · refine ⟨positive, ?_⟩
    unfold t_21e1_c17 at body
    obtain ⟨_, body⟩ := ric_destP body
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
    cases body with
    | ret _ pop =>
      obtain ⟨_, eq⟩ := St.of_pop1 pop
      exact ⟨_, eq⟩

/-- The helper's reply decoder: a returned run derives the CALL's success flag and the
optional-bool acceptance on the actual memory words, then returns past the helper locals. -/
theorem skimTransferDecode_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {x ptr success y z value toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm []
      (St b (x :: ptr :: success :: y :: z :: value :: toWord :: tokenWord :: rho :: R) M G)
      t_2148_c16 (.done (.returned out))) :
    success ≠ 0 ∧ (∃ M' residual, out = St b R M' residual) ∧
      (Bytes.toB256 (M.read ptr.toNat 32).1 = 0 ∨
        (32 ≤ (Bytes.toB256 (M.read ptr.toNat 32).1).toNat ∧
          Bytes.toB256 (M.read (32 + ptr).toNat 32).1 ≠ 0)) := by
  have h := run
  unfold t_2148_c16 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := success) rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := success) rfl (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨_, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  by_cases failed : success = 0
  · rw [failed, show B256.eqCheck 0 0 = (1 : B256) from by decide] at h
    cases h with
    | toZero _ pop _ =>
      obtain ⟨_, bad, _⟩ := St.of_pop2 pop
      exact ((by decide : (1 : B256) ≠ 0) bad).elim
    | toSucc _ _ _ _ lookup pop tail =>
      change some t_2176_c17 = _ at lookup
      cases lookup
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      exact ((skimTransferCheck_inv project tail).1 rfl).elim
  · have flag : B256.eqCheck success 0 = 0 := ite_eq_right failed
    rw [flag] at h
    refine ⟨failed, ?_⟩
    cases h with
    | toSucc _ _ nonzero _ _ pop _ =>
      obtain ⟨_, rfl, _⟩ := St.of_pop2 pop
      exact (nonzero rfl).elim
    | toZero _ pop tail =>
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      unfold t_2155_c16 at tail
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_pop (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_mload (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
      obtain ⟨_, hd, tail⟩ := ric_nextP tail; obtain ⟨_, rfl⟩ := ri_push (project hd)
      by_cases empty : Bytes.toB256 (M.read ptr.toNat 32).1 = 0
      · rw [empty, show B256.eqCheck 0 0 = (1 : B256) from by decide] at tail
        cases tail with
        | toZero _ pop _ =>
          obtain ⟨_, bad, _⟩ := St.of_pop2 pop
          exact ((by decide : (1 : B256) ≠ 0) bad).elim
        | toSucc _ _ _ _ lookup pop body =>
          change some t_2176_c17 = _ at lookup
          cases lookup
          obtain ⟨_, _, eq⟩ := St.of_pop2 pop
          rw [eq] at body
          obtain ⟨_, residual, result⟩ := skimTransferCheck_inv project body
          exact ⟨⟨_, residual, result⟩, Or.inl empty⟩
      · have flag1 : B256.eqCheck (Bytes.toB256 (M.read ptr.toNat 32).1) 0 = 0 :=
          ite_eq_right empty
        rw [flag1] at tail
        cases tail with
        | toSucc _ _ nonzero _ _ pop _ =>
          obtain ⟨_, rfl, _⟩ := St.of_pop2 pop
          exact (nonzero rfl).elim
        | toZero _ pop body =>
          obtain ⟨_, _, eq⟩ := St.of_pop2 pop
          rw [eq] at body
          unfold t_215e_c16 at body
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_add (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_mload (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body
          obtain ⟨_, rfl⟩ := ri_dup (w := Bytes.toB256 (M.read ptr.toNat 32).1) rfl (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_lt (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
          obtain ⟨_, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
          rcases ric_branchP body with ⟨_, _, failed⟩ | ⟨positive, _, head⟩
          · exact (failed.false_of_noOk (by decide : t_216f_c16.noOk = true)).elim
          · have width := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero positive)
            unfold t_2173_c16 at head
            obtain ⟨_, head⟩ := ric_destP head
            obtain ⟨_, hd, head⟩ := ric_nextP head; obtain ⟨_, rfl⟩ := ri_pop (project hd)
            obtain ⟨_, hd, head⟩ := ric_nextP head; obtain ⟨_, rfl⟩ := ri_mload (project hd)
            obtain ⟨nonzero, residual, result⟩ := skimTransferCheck_inv project head
            exact ⟨⟨_, residual, result⟩, Or.inr ⟨width, nonzero⟩⟩

/-- No-wrap pointer arithmetic below the fit bound. -/
theorem skimOffset {x y : B256} (fit : x.toNat + y.toNat < 2 ^ 256) :
    (x + y).toNat = x.toNat + y.toNat :=
  B256.toNat_add_eq_of_nof x y fit

/-- The helper57 initializer's byte image over an arbitrary prior image, at a free
pointer `p` (Nat offset `p.toNat`): selector table, recipient, amount, length word,
two free-pointer bumps and the merged selector word. -/
def skimPayloadImage (I : Bytes) (p amount toWord : B256) : Bytes :=
  let q := p.toNat
  let J1 := Bytes.writeAt I 64 (64 + p).toBytes
  let J2 := Bytes.writeAt J1 q (25 : B256).toBytes
  let J3 := Bytes.writeAt J2 (q + 32)
    (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let J4 := Bytes.writeAt J3 (q + 100)
    ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
  let J5 := Bytes.writeAt J4 (q + 132) amount.toBytes
  let J6 := Bytes.writeAt J5 (q + 64) (68 : B256).toBytes
  let J7 := Bytes.writeAt J6 64 (64 + p + 100).toBytes
  Bytes.writeAt J7 (q + 96)
    ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
      ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
        Bytes.toB256 (J7.sliceD (q + 96) 32 0))).toBytes

/-- Evaluation of the symbolic initializer at a fitting free pointer. -/
theorem skimTransferInit_eval {M : Mem} {p amount toWord : B256}
    (wf : Mem.Wf M) (word : Bytes.toB256 (M.read 64 32).1 = p)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256) :
    let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
    let M1 := (M.read (64 : B256).toNat 32).2
    let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
    let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
    let M4 := M3.write ((32 + p1) : B256).toNat
      (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
    let M5 := (M4.read (64 : B256).toNat 32).2
    let M6 := M5.write ((p2 + 36) : B256).toNat
      ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
    let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
    let M8 := (M7.read (64 : B256).toNat 32).2
    let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
    let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
    let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
    let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
    let M12 := M11.write ((p3 + 32) : B256).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
        (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
    let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
    let M13 := (M12.read (64 : B256).toNat 32).2
    let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
    let M14 := (M13.read (p3 : B256).toNat 32).2
    p1 = p ∧ p2 = 64 + p ∧ p3 = 64 + p ∧ p5 = 64 + p + 100 ∧ p6 = 68 ∧
      Mem.Wf M14 ∧ Mem.Reads M14 (skimPayloadImage M.data.toList p amount toWord) := by
  intro p1 M1 M2 M3 M4 p2 M5 M6 M7 p3 M8 M9 M10 p4 M11 M12 p5 M13 p6 M14
  have q64 : (64 + p).toNat = p.toNat + 64 := by
    rw [B256.add_comm, skimOffset (by change p.toNat + 64 < 2 ^ 256; omega)]; rfl
  have hp1 : p1 = p := word
  have r1 : Mem.Reads M1 M.data.toList := Mem.reads_data M
  have w1 : Mem.Wf M1 := wf.extend _ _
  have r2 := r1.write w1 64 (64 + p1).toBytes
  change Mem.Reads M2 _ at r2
  have w2 : Mem.Wf M2 := w1.write _ _
  have r3 := r2.write w2 p1.toNat (25 : B256).toBytes
  change Mem.Reads M3 _ at r3
  have w3 : Mem.Wf M3 := w2.write _ _
  have q32 : (32 + p1).toNat = p.toNat + 32 := by
    rw [hp1, B256.add_comm, skimOffset (by change p.toNat + 32 < 2 ^ 256; omega)]; rfl
  have r4 := r3.write w3 (32 + p1).toNat
    (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  change Mem.Reads M4 _ at r4
  have w4 : Mem.Wf M4 := w3.write _ _
  rw [q32, hp1] at r4
  have hp2 : p2 = 64 + p := by
    change Bytes.toB256 (M4.read 64 32).1 = 64 + p
    rw [r4.read, Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_self]
  have w5 : Mem.Wf M5 := w4.extend _ _
  have r5 : Mem.Reads M5 _ := r4.extend 64 32
  have q100 : (p2 + 36).toNat = p.toNat + 100 := by
    rw [hp2, skimOffset (by rw [q64]; change p.toNat + 64 + 36 < 2 ^ 256; omega), q64]; rfl
  have q132 : (p2 + 68).toNat = p.toNat + 132 := by
    rw [hp2, skimOffset (by rw [q64]; change p.toNat + 64 + 68 < 2 ^ 256; omega), q64]; rfl
  have r6 := r5.write w5 (p2 + 36).toNat
    ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
  change Mem.Reads M6 _ at r6
  rw [q100] at r6
  have w6 : Mem.Wf M6 := w5.write _ _
  have r7 := r6.write w6 (p2 + 68).toNat amount.toBytes
  change Mem.Reads M7 _ at r7
  rw [q132] at r7
  have w7 : Mem.Wf M7 := w6.write _ _
  have hp3 : p3 = 64 + p := by
    change Bytes.toB256 (M7.read 64 32).1 = 64 + p
    rw [r7.read, Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_self]
  have w8 : Mem.Wf M8 := w7.extend _ _
  have r8 : Mem.Reads M8 _ := r7.extend 64 32
  have len68 : (68 + (p2 - p3) : B256) = 68 := by
    rw [hp2, hp3, B256.sub_self]; rfl
  have r9 := r8.write w8 p3.toNat (68 + (p2 - p3)).toBytes
  change Mem.Reads M9 _ at r9
  rw [len68, hp3, q64] at r9
  have w9 : Mem.Wf M9 := w8.write _ _
  have r10 := r9.write w9 64 (p2 + 100).toBytes
  change Mem.Reads M10 _ at r10
  rw [hp2] at r10
  have w10 : Mem.Wf M10 := w9.write _ _
  have q96 : (p3 + 32).toNat = p.toNat + 96 := by
    rw [hp3, skimOffset (by rw [q64]; change p.toNat + 64 + 32 < 2 ^ 256; omega), q64]; rfl
  have hp4 : p4 = Bytes.toB256 ((Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt M.data.toList 64
        (64 + p).toBytes) p.toNat (25 : B256).toBytes) (p.toNat + 32)
        (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes)
        (p.toNat + 100) ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes)
        (p.toNat + 132) amount.toBytes) (p.toNat + 64) (68 : B256).toBytes) 64
        (64 + p + 100).toBytes).sliceD (p.toNat + 96) 32 0) := by
    change Bytes.toB256 (M10.read (p3 + 32).toNat 32).1 = _
    rw [q96, r10.read]
  have w11 : Mem.Wf M11 := w10.extend _ _
  have r11 : Mem.Reads M11 _ := r10.extend _ 32
  have r12 := r11.write w11 (p3 + 32).toNat
    ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
      (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
  change Mem.Reads M12 _ at r12
  rw [q96, hp4] at r12
  have w12 : Mem.Wf M12 := w11.write _ _
  have hp5 : p5 = 64 + p + 100 := by
    change Bytes.toB256 (M12.read 64 32).1 = 64 + p + 100
    rw [r12.read, Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_self]
  have w13 : Mem.Wf M13 := w12.extend _ _
  have r13 : Mem.Reads M13 _ := r12.extend 64 32
  have hp6 : p6 = 68 := by
    change Bytes.toB256 (M13.read p3.toNat 32).1 = 68
    rw [hp3, q64, r13.read, Bytes.readWord_writeAt_of_disjoint _ _ _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ _ _ _ (Or.inr (by omega)),
      Bytes.readWord_writeAt_self]
  exact ⟨hp1, hp2, hp3, hp5, hp6, w13.extend _ _, r13.extend _ 32⟩

/-- Canonical transfer calldata in the initializer image: the merged selector word
followed by the recipient and amount words, for any prior image below the payload. -/
theorem skimPayload_tail {J3 : Bytes} {q : Nat} {w64 rec amount : B256} (low : 96 ≤ q) :
    let J7 := Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt J3 (q + 100)
      rec.toBytes) (q + 132) amount.toBytes) (q + 64) (68 : B256).toBytes) 64 w64.toBytes
    (Bytes.writeAt J7 (q + 96)
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
          Bytes.toB256 (J7.sliceD (q + 96) 32 0))).toBytes).sliceD (q + 96) 68 0 =
      abiSelectorBytes 0xa9059cbb ++ rec.toBytes ++ amount.toBytes := by
  intro J7
  have pair : J7.sliceD (q + 100) 64 0 = rec.toBytes ++ amount.toBytes := by
    change (Bytes.writeAt (Bytes.writeAt _ (q + 64) (68 : B256).toBytes) 64 w64.toBytes).sliceD
      (q + 100) 64 0 = _
    rw [Bytes.sliceD_writeAt_after _ _ _ 64 64 (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_after _ _ _ 64 (q + 64) (by rw [B256.length_toBytes]; omega)]
    rw [show q + 132 = q + 100 + 32 by omega]
    exact Bytes.read_two_word_writes_at J3 (q + 100) rec amount
  let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
  let selectorWord := (0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256)
  let loaded := Bytes.toB256 (J7.sliceD (q + 96) 32 0)
  have loadedBytes : loaded.toBytes = J7.sliceD (q + 96) 32 0 :=
    Bytes.toBytes_toB256_of_length (by rw [List.sliceD_eq_map, List.length_map, List.length_range])
  have mergeEq : selectorWord ||| (mask &&& loaded) =
      (selectorWord &&& ~~~mask) ||| (loaded &&& mask) := by
    rw [show selectorWord &&& ~~~mask = selectorWord from rfl]
    exact congrArg (fun x => selectorWord ||| x) (B256.and_comm mask loaded)
  have mergeBytes : (selectorWord ||| (mask &&& loaded)).toBytes =
      abiSelectorBytes 0xa9059cbb ++ (J7.sliceD (q + 96) 32 0).drop 4 := by
    rw [mergeEq, mergeFour_bytes, loadedBytes,
      show selectorWord.toBytes.take 4 = abiSelectorBytes 0xa9059cbb from by decide]
  change (Bytes.writeAt J7 (q + 96) (selectorWord ||| (mask &&& loaded)).toBytes).sliceD
    (q + 96) 68 0 = _
  rw [List.append_assoc, List.sliceD_eq_map]
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_append, abiSelectorBytes_length,
      B256.length_toBytes]
  · intro i hi hj
    simp only [List.length_map, List.length_range] at hi
    simp only [List.getElem_map, List.getElem_range]
    have rhs : (abiSelectorBytes 0xa9059cbb ++ (rec.toBytes ++ amount.toBytes)).getD i 0 =
        (abiSelectorBytes 0xa9059cbb ++ (rec.toBytes ++ amount.toBytes))[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      rfl
    refine Eq.trans ?_ rhs
    rw [Bytes.getD_writeAt]
    by_cases isPrefix : i < 4
    · rw [ite_eq_left ⟨by omega, by rw [B256.length_toBytes]; omega⟩,
        show q + 96 + i - (q + 96) = i by omega, mergeBytes,
        List.getD_append_left (d := (0 : UInt8)) (by rw [abiSelectorBytes_length]; exact isPrefix),
        List.getD_append_left (d := (0 : UInt8)) (by rw [abiSelectorBytes_length]; exact isPrefix)]
    · rw [List.getD_append_right (d := (0 : UInt8)) (by rw [abiSelectorBytes_length]; omega),
        abiSelectorBytes_length]
      have old : J7.getD (q + 96 + i) 0 = (rec.toBytes ++ amount.toBytes).getD (i - 4) 0 := by
        have projected : (J7.sliceD (q + 100) 64 0).getD (i - 4) 0 =
            (rec.toBytes ++ amount.toBytes).getD (i - 4) 0 := by rw [pair]
        rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega),
          show q + 100 + (i - 4) = q + 96 + i by omega] at projected
        exact projected
      by_cases first32 : i < 32
      · rw [ite_eq_left ⟨by omega, by rw [B256.length_toBytes]; omega⟩,
          show q + 96 + i - (q + 96) = i by omega, mergeBytes,
          List.getD_append_right (d := (0 : UInt8)) (by rw [abiSelectorBytes_length]; omega),
          abiSelectorBytes_length, List.getD_drop,
          Bytes.getD_sliceD_of_lt _ _ _ _ (by omega),
          show 4 + (i - 4) = i by omega]
        exact old
      · rw [ite_eq_right (by rw [B256.length_toBytes]; omega)]
        exact old

/-- The literal four-byte merge mask of helper57 is the low-28-byte mask. -/
theorem skimMergeMask :
    B256.bexp 256 (32 - 4) - 1 = (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) := by
  rw [show (32 : B256) - 4 = 28 from rfl]
  have expEq : Nat.powMod 256 28 (2 ^ 256) = 2 ^ 224 := by
    simp only [Nat.powMod, Nat.powMod.go, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, Nat.reduceLeDiff, ite_true, ite_false,
      Nat.reduceEqDiff]
  unfold B256.bexp
  change (Nat.powMod 256 28 (2 ^ 256)).toB256 - 1 = _
  rw [expEq]
  rfl

/-- The actual unaligned68-byte copy (two words, then the four-byte merge) moves the
payload window exactly, at any free-pointer offset `q`. -/
theorem skimCopy_image {J8 : Bytes} {q : Nat} :
    let K1 := Bytes.writeAt J8 (q + 164) (Bytes.toB256 (J8.sliceD (q + 96) 32 0)).toBytes
    let K2 := Bytes.writeAt K1 (q + 196) (Bytes.toB256 (K1.sliceD (q + 128) 32 0)).toBytes
    let mask := B256.bexp 256 (32 - 4) - 1
    let K3 := Bytes.writeAt K2 (q + 228)
      (((Bytes.toB256 (K2.sliceD (q + 160) 32 0)) &&& ~~~mask) |||
        ((Bytes.toB256 (K2.sliceD (q + 228) 32 0)) &&& mask)).toBytes
    K3.sliceD (q + 164) 68 0 = J8.sliceD (q + 96) 68 0 := by
  intro K1 K2 mask K3
  have word32 : ∀ (X : Bytes) (s : Nat), (Bytes.toB256 (X.sliceD s 32 0)).toBytes = X.sliceD s 32 0 :=
    fun X s => Bytes.toBytes_toB256_of_length
      (by rw [List.sliceD_eq_map, List.length_map, List.length_range])
  have merge : (((Bytes.toB256 (K2.sliceD (q + 160) 32 0)) &&& ~~~mask) |||
      ((Bytes.toB256 (K2.sliceD (q + 228) 32 0)) &&& mask)).toBytes =
      (K2.sliceD (q + 160) 32 0).take 4 ++ (K2.sliceD (q + 228) 32 0).drop 4 := by
    change (((Bytes.toB256 (K2.sliceD (q + 160) 32 0)) &&& ~~~(B256.bexp 256 (32 - 4) - 1)) |||
      ((Bytes.toB256 (K2.sliceD (q + 228) 32 0)) &&& (B256.bexp 256 (32 - 4) - 1))).toBytes = _
    rw [skimMergeMask, mergeFour_bytes, word32, word32]
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have short := List.mem_range.mp hi
  change (Bytes.writeAt K2 (q + 228) _).getD (q + 164 + i) 0 = J8.getD (q + 96 + i) 0
  rw [Bytes.getD_writeAt, B256.length_toBytes]
  by_cases tail4 : 64 ≤ i
  · rw [ite_eq_left ⟨by omega, by omega⟩, merge,
      List.getD_append_left (d := (0 : UInt8)) (by
        rw [List.length_take, List.sliceD_eq_map, List.length_map, List.length_range]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD, Bytes.getD_sliceD_of_lt _ _ _ _ (by omega),
      show q + 160 + (q + 164 + i - (q + 228)) = q + 96 + i by omega]
    change (Bytes.writeAt K1 (q + 196) _).getD (q + 96 + i) 0 = _
    rw [Bytes.getD_writeAt, B256.length_toBytes, ite_eq_right (by omega)]
    change (Bytes.writeAt J8 (q + 164) _).getD (q + 96 + i) 0 = _
    rw [Bytes.getD_writeAt, B256.length_toBytes, ite_eq_right (by omega)]
  · rw [ite_eq_right (by omega)]
    change (Bytes.writeAt K1 (q + 196) _).getD (q + 164 + i) 0 = _
    rw [Bytes.getD_writeAt, B256.length_toBytes]
    by_cases second : 32 ≤ i
    · rw [ite_eq_left ⟨by omega, by omega⟩, word32, Bytes.getD_sliceD_of_lt _ _ _ _ (by omega),
        show q + 128 + (q + 164 + i - (q + 196)) = q + 96 + i by omega]
      change (Bytes.writeAt J8 (q + 164) _).getD (q + 96 + i) 0 = _
      rw [Bytes.getD_writeAt, B256.length_toBytes, ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega)]
      change (Bytes.writeAt J8 (q + 164) _).getD (q + 164 + i) 0 = _
      rw [Bytes.getD_writeAt, B256.length_toBytes, ite_eq_left ⟨by omega, by omega⟩, word32,
        Bytes.getD_sliceD_of_lt _ _ _ _ (by omega),
        show q + 96 + (q + 164 + i - (q + 164)) = q + 96 + i by omega]

theorem skimAddSub {x : B256} (fit : x.toNat + 68 < 2 ^ 256) : 68 + x - x = 68 := by
  apply B256.toNat_inj
  rw [B256.toNat_sub, skimOffset (by change 68 + x.toNat < 2 ^ 256; omega)]
  change (2 ^ 256 + (68 + x.toNat) - x.toNat) % 2 ^ 256 = 68
  rw [show 2 ^ 256 + (68 + x.toNat) - x.toNat = 68 + 2 ^ 256 by omega, Nat.add_mod_right]
  rfl

/-- The helper57 initializer at a fitting free pointer `p`: evaluated stack, and the
memory's byte image is the payload image over the prior memory. -/
theorem skimTransferInitEval_inv {sevm : Sevm} {b final : Devm} {R : List B256} {M : Mem}
    {G : Nat} {p amount toWord tokenWord rho : B256}
    (wf : Mem.Wf M) (word : Bytes.toB256 (M.read 64 32).1 = p)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : Line.Run sevm (St b (amount :: toWord :: tokenWord :: rho :: R) M G)
      skimTransferInitLine final) :
    ∃ V gas, final = St b ((64 + p + 32) :: (64 + p + 100) :: 68 :: 68 :: (64 + p + 32) ::
      (64 + p + 100) :: (64 + p + 100) :: (64 + p) ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount ::
      toWord :: tokenWord :: rho :: R) V gas ∧ Mem.Wf V ∧
      Mem.Reads V (skimPayloadImage M.data.toList p amount toWord) := by
  have sym := skimTransferInitLine_inv run
  have ev := skimTransferInit_eval (amount := amount) (toWord := toWord) wf word low high
  dsimp only at sym ev
  obtain ⟨gas, hfinal⟩ := sym
  obtain ⟨_, _, e3, e5, e6, w14, r14⟩ := ev
  refine ⟨_, gas, ?_, w14, r14⟩
  rw [hfinal, e5, e6, e3]

/-- Evaluation of the copy and CALL preparation over a known payload image: the CALL
input pointer is the bumped free pointer and the68 CALL bytes are the payload window. -/
theorem skimTransferCall_eval {V : Mem} {J : Bytes} {p : B256}
    (wf : Mem.Wf V) (r : Mem.Reads V J)
    (word64 : Bytes.toB256 (J.sliceD 64 32 0) = 64 + p + 100)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256) :
    let src : B256 := 64 + p + 32
    let dst : B256 := 64 + p + 100
    let C1 := (V.read src.toNat 32).2.write dst.toNat
      (Bytes.toB256 (V.read src.toNat 32).1).toBytes
    let C2 := (C1.read (32 + src).toNat 32).2.write (32 + dst).toNat
      (Bytes.toB256 (C1.read (32 + src).toNat 32).1).toBytes
    let mask := B256.bexp 256 (32 - 4) - 1
    let N1 := (C2.read (32 + (32 + src)).toNat 32).2
    let N2 := (N1.read (32 + (32 + dst)).toNat 32).2
    let N3 := N2.write (32 + (32 + dst)).toNat
      (((Bytes.toB256 (C2.read (32 + (32 + src)).toNat 32).1) &&& ~~~mask) |||
        ((Bytes.toB256 (N1.read (32 + (32 + dst)).toNat 32).1) &&& mask)).toBytes
    let q := Bytes.toB256 (N3.read 64 32).1
    let N4 := (N3.read 64 32).2
    q = 64 + p + 100 ∧ (N4.read (p.toNat + 164) 68).1 = J.sliceD (p.toNat + 96) 68 0 ∧
      Mem.Wf N4 := by
  intro src dst C1 C2 mask N1 N2 N3 q N4
  have h64 : (64 + p).toNat = p.toNat + 64 := by
    rw [B256.add_comm, skimOffset (by change p.toNat + 64 < 2 ^ 256; omega)]; rfl
  have hs0 : src.toNat = p.toNat + 96 := by
    have fit : (64 + p).toNat + (32 : B256).toNat < 2 ^ 256 := by
      rw [h64]; change p.toNat + 64 + 32 < 2 ^ 256; omega
    change (64 + p + 32).toNat = _
    rw [skimOffset fit, h64]; change p.toNat + 64 + 32 = p.toNat + 96; omega
  have hd0 : dst.toNat = p.toNat + 164 := by
    have fit : (64 + p).toNat + (100 : B256).toNat < 2 ^ 256 := by
      rw [h64]; change p.toNat + 64 + 100 < 2 ^ 256; omega
    change (64 + p + 100).toNat = _
    rw [skimOffset fit, h64]; change p.toNat + 64 + 100 = p.toNat + 164; omega
  have hs1 : (32 + src).toNat = p.toNat + 128 := by
    have fit : (32 : B256).toNat + src.toNat < 2 ^ 256 := by
      rw [hs0]; change 32 + (p.toNat + 96) < 2 ^ 256; omega
    rw [skimOffset fit, hs0]; change 32 + (p.toNat + 96) = p.toNat + 128; omega
  have hd1 : (32 + dst).toNat = p.toNat + 196 := by
    have fit : (32 : B256).toNat + dst.toNat < 2 ^ 256 := by
      rw [hd0]; change 32 + (p.toNat + 164) < 2 ^ 256; omega
    rw [skimOffset fit, hd0]; change 32 + (p.toNat + 164) = p.toNat + 196; omega
  have hs2 : (32 + (32 + src)).toNat = p.toNat + 160 := by
    have fit : (32 : B256).toNat + (32 + src).toNat < 2 ^ 256 := by
      rw [hs1]; change 32 + (p.toNat + 128) < 2 ^ 256; omega
    rw [skimOffset fit, hs1]; change 32 + (p.toNat + 128) = p.toNat + 160; omega
  have hd2 : (32 + (32 + dst)).toNat = p.toNat + 228 := by
    have fit : (32 : B256).toNat + (32 + dst).toNat < 2 ^ 256 := by
      rw [hd1]; change 32 + (p.toNat + 196) < 2 ^ 256; omega
    rw [skimOffset fit, hd1]; change 32 + (p.toNat + 196) = p.toNat + 228; omega
  have w1 : Mem.Wf C1 := (wf.extend _ _).write _ _
  have r1 := (r.extend src.toNat 32).write (wf.extend _ _) dst.toNat
    (Bytes.toB256 (V.read src.toNat 32).1).toBytes
  change Mem.Reads C1 _ at r1
  rw [hd0, r.read, hs0] at r1
  have w2 : Mem.Wf C2 := (w1.extend _ _).write _ _
  have r2 := (r1.extend (32 + src).toNat 32).write (w1.extend _ _) (32 + dst).toNat
    (Bytes.toB256 (C1.read (32 + src).toNat 32).1).toBytes
  change Mem.Reads C2 _ at r2
  rw [hd1, r1.read, hs1] at r2
  have wN : Mem.Wf N3 := ((w2.extend _ _).extend _ _).write _ _
  have rN := ((r2.extend (32 + (32 + src)).toNat 32).extend (32 + (32 + dst)).toNat 32).write
    ((w2.extend _ _).extend _ _) (32 + (32 + dst)).toNat
    (((Bytes.toB256 (C2.read (32 + (32 + src)).toNat 32).1) &&& ~~~mask) |||
      ((Bytes.toB256 (N1.read (32 + (32 + dst)).toNat 32).1) &&& mask)).toBytes
  change Mem.Reads N3 _ at rN
  have readN1 : (N1.read (32 + (32 + dst)).toNat 32).1 = _ :=
    (r2.extend (32 + (32 + src)).toNat 32).read (32 + (32 + dst)).toNat 32
  rw [readN1, hd2, r2.read, hs2] at rN
  have copied := skimCopy_image (J8 := J) (q := p.toNat)
  dsimp only at copied
  refine ⟨?_, ?_, wN.extend _ _⟩
  · change Bytes.toB256 (N3.read 64 32).1 = _
    rw [rN.read, Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
      Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega))]
    exact word64
  · have r4 : Mem.Reads N4 _ := rN.extend 64 32
    rw [r4.read]
    exact copied

/-- The real helper57 CALL keeps the seven-operand frame below its pushed flag; a
nonzero flag is an entered call whose parent memory and output settle literally. -/
theorem skimTransferCallStep_inv {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {G : Nat} {forwarded token ptr inputSize endWord : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (callStep : Ninst.Run sevm
      (St b (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: endWord :: token :: R)
        M G) (.exec .call) d) :
    ∃ flag, d.stack = flag :: endWord :: token :: R ∧ d.returnData.length < 2 ^ 256 ∧
      (flag ≠ 0 → d.memory = (M.extends [(ptr.toNat, inputSize.toNat), (ptr.toNat, 0)]).write
        ptr.toNat (d.returnData.take 0) ∧ d.output = b.output) := by
  let rest := endWord :: token :: R
  have matched : AbstractStackSafety.Matches
      ((none :: none :: none :: none :: none :: none :: none :: rest.map some) :
        AbstractStackSafety.Pattern)
      (St b (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) M G).stack :=
    ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
      Or.inl rfl, matches_some_map rest⟩
  have transferred : AbstractStackSafety.Matches (none :: rest.map some) d.stack :=
    ninstTransfer_run fork matched rfl callStep
  obtain ⟨flag, stack⟩ : ∃ flag, d.stack = flag :: rest := by
    cases eq : d.stack with
    | nil => rw [eq] at transferred; exact transferred.elim
    | cons flag tail =>
      rw [eq] at transferred
      exact ⟨flag, by rw [matches_some_map_eq transferred.2]⟩
  refine ⟨flag, stack, ReturnDataBound.call_returnData_length_lt callStep fork, ?_⟩
  intro nonzero
  have operands : (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) <<+
      (St b (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) M G).stack := by
    simpa only [List.append_nil, St.stack] using
      (pref_append (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) [])
  rcases of_run_call_val_with_depth_frame operands callStep fork with failed | entered
  · rw [stack] at failed
    exact (nonzero (pref_head_unique failed.1 (pref_append [flag] rest)).symm).elim
  · obtain ⟨parent, _, _, _, _, _, _, _, _, _, _, _, parentMemory, _, parentOutput, _, _, _,
      _, resume, _, returned, memory, _⟩ := entered
    refine ⟨?_, (Resume.call_output resume).trans parentOutput⟩
    rw [memory, parentMemory, returned]
    rfl

/-- The payload image keeps the bumped free pointer in its pointer word. -/
theorem skimPayloadImage_word {I : Bytes} {p amount toWord : B256} (low : 96 ≤ p.toNat) :
    Bytes.toB256 ((skimPayloadImage I p amount toWord).sliceD 64 32 0) = 64 + p + 100 := by
  unfold skimPayloadImage
  dsimp only
  rw [Bytes.readWord_writeAt_of_disjoint _ 64 _ _ (Or.inl (by omega)),
    Bytes.readWord_writeAt_self]

/-- Canonical transfer calldata at the payload window of the initializer image. -/
theorem skimPayloadImage_data {I : Bytes} {p amount toWord : B256} (low : 96 ≤ p.toNat) :
    (skimPayloadImage I p amount toWord).sliceD (p.toNat + 96) 68 0 =
      abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++
          amount.toBytes := by
  unfold skimPayloadImage
  exact skimPayload_tail low

/-- A window inside a zero-padded prefix slice reads the original prefix. -/
theorem skimSliceD_prefix (xs : Bytes) {n : Nat} (enough : 32 ≤ n) :
    (xs.sliceD 0 n 0).sliceD 0 32 0 = xs.sliceD 0 32 0 := by
  conv_lhs => rw [List.sliceD_eq_map]
  conv_rhs => rw [List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have short := List.mem_range.mp hi
  rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega), Nat.zero_add]

/-- The helper57 CALL and reply tail at a memory whose free pointer word is `ptr`:
the flag is nonzero, the call entered, and the reply passes the optional-bool rule. -/
theorem skimTransferTail_flag_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {N : Mem} {G : Nat}
    {forwarded tokenM ptr endWord amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf (N.read 64 32).2)
    (word : Bytes.toB256 (N.read 64 32).1 = ptr)
    (low : 96 ≤ ptr.toNat) (high : ptr.toNat + 64 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm []
      (St b (forwarded :: tokenM :: 0 :: ptr :: 68 :: ptr :: 0 :: endWord :: tokenM :: 96 :: 0 ::
        amount :: toWord :: tokenWord :: rho :: R) (N.read 64 32).2 G)
      (.next (.exec .call) skimTransferReplyTree) (.done (.returned out))) :
    ∃ d, P sevm (St b (forwarded :: tokenM :: 0 :: ptr :: 68 :: ptr :: 0 :: endWord :: tokenM ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) (N.read 64 32).2 G) (.exec .call) d ∧
      (∃ flag rest, d.stack = flag :: rest ∧ flag ≠ 0) ∧
      d.output = b.output ∧ d.returnData.length < 2 ^ 256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      ∃ M' residual, out = St d R M' residual := by
  obtain ⟨d, callP, h⟩ := ric_nextP run
  obtain ⟨flag, stack, width, entered⟩ := skimTransferCallStep_inv fork (project callP)
  rw [St.self stack rfl] at h
  obtain ⟨_, h⟩ := skimTransferReply_inv project (by decide : 16 ∉ ([] : List Nat)) h
  obtain ⟨nonzero, outEq, accept⟩ := skimTransferDecode_inv project h
  obtain ⟨memory, output⟩ := entered nonzero
  refine ⟨d, callP, ⟨flag, _, stack, nonzero⟩, output, width, ?_, outEq⟩
  have lenNat : d.returnData.length.toB256.toNat = d.returnData.length :=
    B256.toNat_toB256_of_lt width
  by_cases empty : d.returnData.length.toB256 = 0
  · left
    rw [empty] at lenNat
    exact List.eq_nil_of_length_eq_zero (by rw [← lenNat]; rfl)
  · right
    rw [ite_eq_right empty, ite_eq_right empty] at accept
    have wD : Mem.Wf d.memory := by
      rw [memory]
      exact (wf.extends _).write _ _
    have rD : Mem.Reads d.memory (Bytes.writeAt N.data.toList ptr.toNat []) := by
      rw [memory, List.take_zero]
      exact (((Mem.reads_data N).extend 64 32).extends _).write
        (wf.extends _) ptr.toNat []
    have hptr : Bytes.toB256 (d.memory.read 64 32).1 = ptr := by
      rw [rD.read, Bytes.sliceD_writeAt_before _ _ 64 32 ptr.toNat (by omega),
        ← (Mem.reads_data N).read]
      exact word
    rw [hptr] at accept
    have p32 : (ptr + 32).toNat = ptr.toNat + 32 := skimOffset (by change ptr.toNat + 32 < 2 ^ 256; omega)
    have p32' : (32 + ptr).toNat = ptr.toNat + 32 := by rw [B256.add_comm]; exact p32
    have rD1 : Mem.Reads (d.memory.read 64 32).2 _ := rD.extend 64 32
    have wD1 : Mem.Wf (d.memory.read 64 32).2 := wD.extend 64 32
    have rA := ((rD1.write wD1 64
      (ptr + (d.returnData.length.toB256 + 63 &&& ~~~31)).toBytes).write
        (wD1.write _ _) ptr.toNat d.returnData.length.toB256.toBytes).write
        ((wD1.write _ _).write _ _) (ptr + 32).toNat
        (d.returnData.sliceD 0 d.returnData.length.toB256.toNat 0)
    rw [rA.read, rA.read, p32, p32', Bytes.sliceD_writeAt_before _ _ _ 32 _ (by omega),
      Bytes.readWord_writeAt_self] at accept
    rcases accept with zero | ⟨enough, head⟩
    · exact (empty zero).elim
    · rw [lenNat] at enough
      rw [Bytes.sliceD_writeAt_inside _ _ _ _ 32 (by omega)
          (by rw [List.sliceD_eq_map, List.length_map, List.length_range, lenNat]; omega),
        Nat.sub_self, lenNat, skimSliceD_prefix _ enough] at head
      exact ⟨enough, head⟩

/-- The same tail without the success flag. -/
theorem skimTransferTail_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {N : Mem} {G : Nat}
    {forwarded tokenM ptr endWord amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (wf : Mem.Wf (N.read 64 32).2)
    (word : Bytes.toB256 (N.read 64 32).1 = ptr)
    (low : 96 ≤ ptr.toNat) (high : ptr.toNat + 64 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm []
      (St b (forwarded :: tokenM :: 0 :: ptr :: 68 :: ptr :: 0 :: endWord :: tokenM :: 96 :: 0 ::
        amount :: toWord :: tokenWord :: rho :: R) (N.read 64 32).2 G)
      (.next (.exec .call) skimTransferReplyTree) (.done (.returned out))) :
    ∃ d, P sevm (St b (forwarded :: tokenM :: 0 :: ptr :: 68 :: ptr :: 0 :: endWord :: tokenM ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) (N.read 64 32).2 G) (.exec .call) d ∧
      d.output = b.output ∧ d.returnData.length < 2 ^ 256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      ∃ M' residual, out = St d R M' residual := by
  obtain ⟨d, callP, _, output, width, accept, outEq⟩ :=
    skimTransferTail_flag_inv project fork wf word low high run
  exact ⟨d, callP, output, width, accept, outEq⟩

/-- A returned pointer-generic helper57 run at a fitting free pointer `p`: the SAME
P-step CALL with canonical transfer calldata at `p+164`, the optional-bool acceptance
of its full reply, and the returned frame. Child effects stay opaque in `d`. -/
theorem skimTransfer_flag_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {p amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork)
    (wf : Mem.Wf M) (word : Bytes.toB256 (M.read 64 32).1 = p)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : SFunc.RunP P cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 (.returned out)) :
    ∃ (forwarded : B256) (callGas : Nat) (V : Mem) (d : Devm),
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (64 + p + 100) :: 68 :: (64 + p + 100) :: 0 :: (68 + (64 + p + 100)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount ::
        toWord :: tokenWord :: rho :: R) V callGas) (.exec .call) d ∧
      (V.read (p.toNat + 164) 68).1 = abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++
          amount.toBytes ∧
      (∃ flag rest, d.stack = flag :: rest ∧ flag ≠ 0) ∧
      d.output = b.output ∧ d.returnData.length < 2 ^ 256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      ∃ M' residual, out = St d R M' residual := by
  have h := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_1fdb_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  change SFunc.RunCutP P cert.prog sevm [] _
    (skimTransferInitLine.foldr SFunc.next t_20a4_c57) _ at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => project step)
    skimTransferInitLine h
  obtain ⟨V0, _, state, w0, r0⟩ := skimTransferInitEval_inv wf word low high line
  rw [state] at h
  obtain ⟨_, h⟩ := skimCopy68_inv project (by decide : 71 ∉ ([] : List Nat)) h
  unfold t_20e1_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  change SFunc.RunCutP P cert.prog sevm [] _
    (skimTransferCallLine.foldr SFunc.next (.next (.exec .call) skimTransferReplyTree)) _ at h
  obtain ⟨_, line, h⟩ := SFunc.RunCutP.split_nexts (fun step => project step)
    skimTransferCallLine h
  obtain ⟨forwarded, callGas, state⟩ := skimTransferCallLine_inv line
  have ev := skimTransferCall_eval (V := V0) w0 r0 (skimPayloadImage_word low) low high
  dsimp only at state ev
  obtain ⟨hq, calldata, wN⟩ := ev
  have h64 : (64 + p).toNat = p.toNat + 64 := by
    rw [B256.add_comm, skimOffset (by change p.toNat + 64 < 2 ^ 256; omega)]; rfl
  have h164 : (64 + p + 100).toNat = p.toNat + 164 := by
    have fit : (64 + p).toNat + (100 : B256).toNat < 2 ^ 256 := by
      rw [h64]; change p.toNat + 64 + 100 < 2 ^ 256; omega
    rw [skimOffset fit, h64]; change p.toNat + 64 + 100 = p.toNat + 164; omega
  have fit68 : (64 + p + 100).toNat + 68 < 2 ^ 256 := by rw [h164]; omega
  rw [hq, skimAddSub fit68] at state
  rw [state] at h
  obtain ⟨d, call, flagged, output, width, accept, outEq⟩ :=
    skimTransferTail_flag_inv project fork wN hq
    (by rw [h164]; omega) (by rw [h164]; omega) h
  exact ⟨forwarded, callGas, _, d, call, calldata.trans (skimPayloadImage_data low), flagged,
    output, width, accept, outEq⟩

/-- The same helper inverse without the success flag. -/
theorem skimTransfer_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {p amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork)
    (wf : Mem.Wf M) (word : Bytes.toB256 (M.read 64 32).1 = p)
    (low : 96 ≤ p.toNat) (high : p.toNat + 1024 < 2 ^ 256)
    (run : SFunc.RunP P cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 (.returned out)) :
    ∃ (forwarded : B256) (callGas : Nat) (V : Mem) (d : Devm),
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (64 + p + 100) :: 68 :: (64 + p + 100) :: 0 :: (68 + (64 + p + 100)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount ::
        toWord :: tokenWord :: rho :: R) V callGas) (.exec .call) d ∧
      (V.read (p.toNat + 164) 68).1 = abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++
          amount.toBytes ∧
      d.output = b.output ∧ d.returnData.length < 2 ^ 256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      ∃ M' residual, out = St d R M' residual := by
  obtain ⟨forwarded, callGas, V, d, call, calldata, _, output, width, accept, outEq⟩ :=
    skimTransfer_flag_inv project fork wf word low high run
  exact ⟨forwarded, callGas, V, d, call, calldata, output, width, accept, outEq⟩

end Blanc.Lift.UniswapV2Pair
