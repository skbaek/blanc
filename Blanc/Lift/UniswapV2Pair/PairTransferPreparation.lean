import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkProvenance
import Blanc.Lift.UniswapV2Pair.Check

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def pairTransferCopyLine : List Ninst := [
  .reg (.dup 0),
  .reg .mload,
  .reg (.dup 2),
  .reg .mstore,
  .push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xe0] (by decide),
  .reg (.swap 0),
  .reg (.swap 2),
  .reg .add,
  .reg (.swap 1),
  .push [0x20] (by decide),
  .reg (.swap 1),
  .reg (.dup 2),
  .reg .add,
  .reg (.swap 1),
  .reg .add,
  .push [0x20, 0xa4] (by decide)]

def pairTransferPartialLine : List Ninst := [
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
  .reg (.dup 6)]

/-- One original copy pass exposes the selected read expansion and full stored word. -/
theorem pair_transfer_copy_line_inv {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {G : Nat} {src dst len : B256}
    (run : Line.Run sevm (St b (src :: dst :: len :: R) M G) pairTransferCopyLine d) :
    ∃ residual, d = St b
      (0x20a4 :: (32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
      ((M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes)
      residual := by
  have h := run
  unfold pairTransferCopyLine at h
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup (w := src) rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup (w := dst) rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup (w := 32) rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  cases h
  exact ⟨_, rfl⟩

/-- The original partial-word merge exposes every CALL operand before the actual GAS step. -/
theorem pair_transfer_partial_line_inv {sevm : Sevm} {b d : Devm} {R : List B256}
    {M : Mem} {G : Nat} {src dst a x y z w token : B256}
    (run : Line.Run sevm
      (St b (src :: dst :: 4 :: a :: x :: y :: z :: w :: token :: R) M G)
      pairTransferPartialLine d) :
    let mask := B256.bexp 256 (32 - 4) - 1
    let M1 := (M.read src.toNat 32).2
    let M2 := (M1.read dst.toNat 32).2
    let M3 := M2.write dst.toNat
      (((Bytes.toB256 (M.read src.toNat 32).1) &&& ~~~mask) |||
        ((Bytes.toB256 (M1.read dst.toNat 32).1) &&& mask)).toBytes
    let q := Bytes.toB256 (M3.read 64 32).1
    let M4 := (M3.read 64 32).2
    ∃ residual, d = St b
      (token :: 0 :: q :: ((a + y) - q) :: q :: 0 :: (a + y) :: token :: R) M4 residual := by
  dsimp only
  have h := run
  unfold pairTransferPartialLine at h
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_exp hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_not hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_or hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_mload hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := Line.of_run_cons h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  cases h
  exact ⟨_, rfl⟩

end Blanc.Lift.UniswapV2Pair
