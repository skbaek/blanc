import Blanc.Lift.UniswapV2Pair.SafeTransferWalk

/-! Skim's helper57 (safeTransfer) inverse at a moved free pointer.

The initializer is consumed from SafeTransferWalk's public pointer-generic API
(`safeTransfer_initialize_dynamic_inv`) and the CALL window from
`safeTransfer_dynamicCall_data`. Only public declarations of SafeTransferWalk are used.
The ordered copy, CALL preparation and post-CALL decoder are walked here: the public
CALL/returned theorems are stated over a private continuation or omit the CALL's
success flag, which skim's commit/precompile discharge needs on the same step. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The literal CALL preparation after helper57's copy loop. -/
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

theorem skimAddSub {x : B256} (fit : x.toNat + 68 < 2 ^ 256) : 68 + x - x = 68 := by
  apply B256.toNat_inj
  rw [B256.toNat_sub, B256.toNat_add_eq_of_nof 68 x (by change 68 + x.toNat < 2 ^ 256; omega)]
  change (2 ^ 256 + (68 + x.toNat) - x.toNat) % 2 ^ 256 = 68
  rw [show 2 ^ 256 + (68 + x.toNat) - x.toNat = 68 + 2 ^ 256 by omega, Nat.add_mod_right]
  rfl

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
    have p32 : (ptr + 32).toNat = ptr.toNat + 32 := B256.toNat_add_eq_of_nof _ _ (by change ptr.toNat + 32 < 2 ^ 256; omega)
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


/-- The memory the literal copy loop and CALL preparation leave before the CALL's
free-pointer reload: two copied words, then the merged four-byte tail word. -/
def skimCopyCallMemory (N : Mem) (src dst : B256) : Mem :=
  let M1 := (N.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (N.read src.toNat 32).1).toBytes
  let M2 := (M1.read (32 + src).toNat 32).2.write (32 + dst).toNat
    (Bytes.toB256 (M1.read (32 + src).toNat 32).1).toBytes
  let mask := B256.bexp 256 (32 - 4) - 1
  let M3 := (M2.read (32 + (32 + src)).toNat 32).2
  (M3.read (32 + (32 + dst)).toNat 32).2.write (32 + (32 + dst)).toNat
    (((Bytes.toB256 (M2.read (32 + (32 + src)).toNat 32).1) &&& ~~~mask) |||
      ((Bytes.toB256 (M3.read (32 + (32 + dst)).toNat 32).1) &&& mask)).toBytes

/-- The walked copy keeps the free pointer carried by the actual memory. -/
theorem skimCopyCallMemory_ptr {N : Mem} {q src dst : B256} {n : Nat} (mem : PtrMem q n N)
    (low : 96 ≤ dst.toNat) (d32 : (32 + dst).toNat = dst.toNat + 32)
    (d64 : (32 + (32 + dst)).toNat = dst.toNat + 64) :
    ∃ m, PtrMem q m (skimCopyCallMemory N src dst) := by
  unfold skimCopyCallMemory
  dsimp only
  exact ⟨_, ((((((mem.extend _ 32).write _ _ (Or.inr low)).extend _ 32).write _ _
    (Or.inr (by rw [d32]; omega))).extend _ 32).extend _ 32).write _ _
      (Or.inr (by rw [d64]; omega))⟩

/-- The walked copy has the same bytes as the API's ordered copy image. -/
theorem skimCopyCallMemory_read {N : Mem} {src dst : B256} (wf : Mem.Wf N)
    (s32 : (32 + src).toNat = src.toNat + 32) (s64 : (32 + (32 + src)).toNat = src.toNat + 64)
    (d32 : (32 + dst).toNat = dst.toNat + 32) (d64 : (32 + (32 + dst)).toNat = dst.toNat + 64)
    (i n : Nat) :
    ((skimCopyCallMemory N src dst).read i n).1 =
      ((Blanc.Lift.copy68Memory N src.toNat dst.toNat).read i n).1 := by
  unfold skimCopyCallMemory Blanc.Lift.copy68Memory
  dsimp only
  rw [s32, s64, d32, d64]
  simp only [show ∀ (μ : Mem) (j k : Nat), (μ.read j k).2 = μ.extend j k from fun _ _ _ => rfl]
  have r0 := Mem.reads_data N
  have rW1 := (r0.extend src.toNat 32).write (wf.extend src.toNat 32) dst.toNat
    (Bytes.toB256 (N.read src.toNat 32).1).toBytes
  have rD1 := r0.write wf dst.toNat (Bytes.toB256 (N.read src.toNat 32).1).toBytes
  have wW1 := (wf.extend src.toNat 32).write dst.toNat (Bytes.toB256 (N.read src.toNat 32).1).toBytes
  have wD1 := wf.write dst.toNat (Bytes.toB256 (N.read src.toNat 32).1).toBytes
  rw [rW1.read (src.toNat + 32) 32, rD1.read (src.toNat + 32) 32]
  have rW2 := (rW1.extend (src.toNat + 32) 32).write (wW1.extend (src.toNat + 32) 32)
    (dst.toNat + 32) (Bytes.toB256 ((Bytes.writeAt N.data.toList dst.toNat
      (Bytes.toB256 (N.read src.toNat 32).1).toBytes).sliceD (src.toNat + 32) 32 0)).toBytes
  have rD2 := rD1.write wD1
    (dst.toNat + 32) (Bytes.toB256 ((Bytes.writeAt N.data.toList dst.toNat
      (Bytes.toB256 (N.read src.toNat 32).1).toBytes).sliceD (src.toNat + 32) 32 0)).toBytes
  have wW2 := (wW1.extend (src.toNat + 32) 32).write (dst.toNat + 32) (Bytes.toB256
    ((Bytes.writeAt N.data.toList dst.toNat
      (Bytes.toB256 (N.read src.toNat 32).1).toBytes).sliceD (src.toNat + 32) 32 0)).toBytes
  have wD2 := wD1.write (dst.toNat + 32) (Bytes.toB256
    ((Bytes.writeAt N.data.toList dst.toNat
      (Bytes.toB256 (N.read src.toNat 32).1).toBytes).sliceD (src.toNat + 32) 32 0)).toBytes
  have rW3 := rW2.extend (src.toNat + 64) 32
  have wW3 := wW2.extend (src.toNat + 64) 32
  rw [rW2.read (src.toNat + 64) 32, rD2.read (src.toNat + 64) 32,
    rW3.read (dst.toNat + 64) 32, rD2.read (dst.toNat + 64) 32,
    ((rW3.extend (dst.toNat + 64) 32).write (wW3.extend (dst.toNat + 64) 32) _ _).read,
    ((rD2.extend (dst.toNat + 64) 32).write (wD2.extend (dst.toNat + 64) 32) _ _).read]

/-- A returned pointer-generic helper57 run at a free pointer `p` carried by the actual
memory (`PtrMem`): the SAME P-step CALL with canonical transfer calldata at `p+164`, its
nonzero success flag, the optional-bool acceptance of its full reply, and the returned
frame. Child effects stay opaque in `d`. -/
theorem skimTransfer_flag_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat} {n : Nat}
    {p amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork)
    (mem : PtrMem p n M) (low : 128 ≤ p.toNat) (high : p.toNat + 260 < 2 ^ 256)
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
  have nat64 : (64 + p).toNat = p.toNat + 64 := by
    rw [B256.add_comm (xs := 64)]
    exact B256.toNat_add_eq_of_nof p 64 (by change p.toNat + 64 < 2 ^ 256; omega)
  have nat96 : (p + 96).toNat = p.toNat + 96 :=
    B256.toNat_add_eq_of_nof p 96 (by change p.toNat + 96 < 2 ^ 256; omega)
  have nat164 : (p + 164).toNat = p.toNat + 164 :=
    B256.toNat_add_eq_of_nof p 164 (by change p.toNat + 164 < 2 ^ 256; omega)
  have shape : 64 + p + 100 = p + 164 := by
    apply B256.toNat_inj
    rw [B256.toNat_add_eq_of_nof (64 + p) 100
      (by change (64 + p).toNat + 100 < 2 ^ 256; rw [nat64]; omega), nat64, nat164]
    change p.toNat + 64 + 100 = p.toNat + 164
    omega
  rw [shape]
  have h := (SFunc.runP_iff_runCutP_nil (P := P)).mp run
  obtain ⟨_, init, carrier, room⟩ :=
    safeTransfer_initialize_dynamic_inv project mem low (by omega) h
  obtain ⟨_, copied⟩ := skimCopy68_inv project (by decide : 71 ∉ ([] : List Nat)) init
  unfold t_20e1_c57 at copied
  obtain ⟨_, copied⟩ := ric_destP copied
  change SFunc.RunCutP P cert.prog sevm [] _
    (skimTransferCallLine.foldr SFunc.next (.next (.exec .call) skimTransferReplyTree)) _ at copied
  obtain ⟨fin, line, tail⟩ := SFunc.RunCutP.split_nexts (fun step => project step)
    skimTransferCallLine copied
  obtain ⟨forwarded, callGas, state⟩ := skimTransferCallLine_inv line
  obtain ⟨C, hC⟩ : ∃ C, C = skimCopyCallMemory (safeTransfer_dynamicPayloadMemory M p amount toWord)
      (p + 96) (p + 164) := ⟨_, rfl⟩
  have s32 : (32 + (p + 96)).toNat = (p + 96).toNat + 32 := by
    rw [B256.add_comm (xs := 32)]
    exact B256.toNat_add_eq_of_nof (p + 96) 32
      (by change (p + 96).toNat + 32 < 2 ^ 256; rw [nat96]; omega)
  have s64 : (32 + (32 + (p + 96))).toNat = (p + 96).toNat + 64 := by
    rw [B256.add_comm (xs := 32) (ys := 32 + (p + 96)),
      B256.toNat_add_eq_of_nof (32 + (p + 96)) 32
        (by change (32 + (p + 96)).toNat + 32 < 2 ^ 256; rw [s32, nat96]; omega), s32]
    change (p + 96).toNat + 32 + 32 = (p + 96).toNat + 64
    omega
  have d32 : (32 + (p + 164)).toNat = (p + 164).toNat + 32 := by
    rw [B256.add_comm (xs := 32)]
    exact B256.toNat_add_eq_of_nof (p + 164) 32
      (by change (p + 164).toNat + 32 < 2 ^ 256; rw [nat164]; omega)
  have d64 : (32 + (32 + (p + 164))).toNat = (p + 164).toNat + 64 := by
    rw [B256.add_comm (xs := 32) (ys := 32 + (p + 164)),
      B256.toNat_add_eq_of_nof (32 + (p + 164)) 32
        (by change (32 + (p + 164)).toNat + 32 < 2 ^ 256; rw [d32, nat164]; omega), d32]
    change (p + 164).toNat + 32 + 32 = (p + 164).toNat + 64
    omega
  obtain ⟨_, cM⟩ := skimCopyCallMemory_ptr (src := p + 96) carrier (by rw [nat164]; omega) d32 d64
  rw [← hC] at cM
  have hq : Bytes.toB256 (C.read 64 32).1 = p + 164 := cM.word
  have wq : Mem.Wf (C.read 64 32).2 := cM.wf.extend 64 32
  have calldata : ((C.read 64 32).2.read (p.toNat + 164) 68).1 = abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++
        amount.toBytes := by
    rw [cM.read_self (by have := cM.ge; omega), hC, ← nat164,
      skimCopyCallMemory_read carrier.wf s32 s64 d32 d64]
    exact safeTransfer_dynamicCall_data mem.wf low (by omega)
  simp only [hC, skimCopyCallMemory] at hq wq calldata
  rw [hq, skimAddSub (by rw [nat164]; omega)] at state
  rw [state] at tail
  obtain ⟨d, call, flagged, output, width, accept, outEq⟩ :=
    skimTransferTail_flag_inv project fork wq hq (by rw [nat164]; omega)
      (by rw [nat164]; omega) tail
  exact ⟨forwarded, callGas, _, d, call, calldata, flagged, output, width, accept, outEq⟩

end Blanc.Lift.UniswapV2Pair
