import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.UniswapV2Pair.Check

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def pairTransferInitializeLine : List Ninst := [
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

/-- The literal transfer initializer retains each selected read and ordered
write. This is the primitive inverse hoisted from SafeTransferWalk. -/
theorem pair_transfer_initialize_line_inv {sevm : Sevm} {b d : Devm}
    {R : List B256} {M : Mem} {G : Nat} {amount toWord tokenWord rho : B256}
    (run : Line.Run sevm (St b (amount :: toWord :: tokenWord :: rho :: R) M G)
      pairTransferInitializeLine d) :
    let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
    let M1 := (M.read (64 : B256).toNat 32).2
    let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
    let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
    let M4 := M3.write ((32 + p1) : B256).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
    let M5 := (M4.read (64 : B256).toNat 32).2
    let M6 := M5.write ((p2 + 36) : B256).toNat ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
    let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
    let M8 := (M7.read (64 : B256).toNat 32).2
    let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
    let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
    let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
    let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
    let M12 := M11.write ((p3 + 32) : B256).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 ||| (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
    let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
    let M13 := (M12.read (64 : B256).toNat 32).2
    let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
    let M14 := (M13.read (p3 : B256).toNat 32).2
    ∃ residual, d = St b ((p3 + 32) :: p5 :: p6 :: p6 :: (p3 + 32) :: p5 :: p5 :: p3 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) M14 residual := by
  dsimp only
  let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
  let M1 := (M.read (64 : B256).toNat 32).2
  let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
  let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
  let M4 := M3.write ((32 + p1) : B256).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
  let M5 := (M4.read (64 : B256).toNat 32).2
  let M6 := M5.write ((p2 + 36) : B256).toNat ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
  let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
  let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
  let M8 := (M7.read (64 : B256).toNat 32).2
  let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
  let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
  let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
  let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
  let M12 := M11.write ((p3 + 32) : B256).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 ||| (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
  let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
  let M13 := (M12.read (64 : B256).toNat 32).2
  let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
  let M14 := (M13.read (p3 : B256).toNat 32).2
  have h := run
  dsimp only [pairTransferInitializeLine] at h
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_or hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  cases h
  exact ⟨_, rfl⟩

end Blanc.Lift.UniswapV2Pair
