import Blanc.Lift.UniswapV2Pair.GetterStorageMappingWalk
import Blanc.Lift.UniswapV2Pair.GetterStorageReservesWalk
import Blanc.Lift.UniswapV2Pair.WriterEntries
import Blanc.Lift.UniswapV2Pair.TransferFromEntries
import Blanc.Lift.UniswapV2Pair.InitializeEntries
import Blanc.Lift.UniswapV2Pair.SyncWalk

/-! Actual successful static calls to the certified Pair runtime. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The existing getter families, decoded at their actual calldata operands. -/
inductive StaticView
  | scalar (s : ScalarGetter)
  | string (s : StringGetter)
  | totalSupply
  | singleMapping (s : SingleMappingGetter)
  | allowance
  | getReserves

def StaticView.selector : StaticView → B256
  | .scalar s => s.selector
  | .string s => s.selector
  | .totalSupply => 0x18160ddd
  | .singleMapping .balanceOf => 0x70a08231
  | .singleMapping .nonces => 0x7ecebe00
  | .allowance => 0xdd62ed3e
  | .getReserves => 0x0902f1ac

def StaticView.entry (sevm : Sevm) : StaticView → Entry
  | .scalar s => s.entry
  | .string s => s.entry
  | .totalSupply => .totalSupply
  | .singleMapping .balanceOf => .balanceOf (Sevm.dataWord sevm 4).toAdr
  | .singleMapping .nonces => .nonces (Sevm.dataWord sevm 4).toAdr
  | .allowance => .allowance (Sevm.dataWord sevm 4).toAdr (Sevm.dataWord sevm 36).toAdr
  | .getReserves => .getReserves

/-- The actual nonce write precedes permit's external recovery call. -/
private theorem permitNoncePrefix_nonstatic {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1b7b_c29 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1b7b_c29 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, store, _⟩ := ric_next h
  exact Blanc.of_run_sstore_not_static store


private theorem permitExpired_impossible {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1b15_c29 o) : False := by
  have h := run.cut
  unfold t_1b15_c29 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact ric_revert h

private theorem permitGuard_nonstatic {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1b0c_c29 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1b0c_c29 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact (permitExpired_impossible (SFunc.RunCut.uncut body)).elim
  | succ _ _ _ _ body => exact permitNoncePrefix_nonstatic (SFunc.RunCut.uncut body)


private theorem staticReject_t_01d0_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_01d0_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_01d0_c99 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_0214_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_0214_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_0214_c99 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_0226_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_0226_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_0226_c99 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_0248_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_0248_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_0248_c99 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_068e_c54 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_068e_c54 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_068e_c54 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_06f4_c54 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_06f4_c54 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_06f4_c54 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, store, _⟩ := ric_next h
  exact Blanc.of_run_sstore_not_static store

private theorem staticReject_t_0683_c54 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_0683_c54 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_0683_c54 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_068e_c54 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_06f4_c54 (SFunc.RunCut.uncut body)

private theorem staticReject_t_024c_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_024c_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_024c_c99 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases (SFunc.RunCut.uncut h) with
  | callHalt _ lookup _ body =>
      rw [show cert.prog[54]? = some t_0683_c54 from rfl] at lookup
      cases lookup
      exact staticReject_t_0683_c54 body
  | callRet _ lookup _ body _ =>
      rw [show cert.prog[54]? = some t_0683_c54 from rfl] at lookup
      cases lookup
      exact staticReject_t_0683_c54 body

private theorem staticReject_t_022a_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_022a_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_022a_c99 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_0248_c99 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_024c_c99 (SFunc.RunCut.uncut body)

private theorem staticReject_t_0218_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_0218_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_0218_c99 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_0226_c99 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_022a_c99 (SFunc.RunCut.uncut body)

private theorem staticReject_t_01d4_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_01d4_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_01d4_c99 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_0214_c99 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_0218_c99 (SFunc.RunCut.uncut body)

private theorem staticReject_t_01be_c99 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_01be_c99 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_01be_c99 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_01d0_c99 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_01d4_c99 (SFunc.RunCut.uncut body)


private theorem staticReject_t_047b_c86 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_047b_c86 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_047b_c86 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_101e_c41 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_101e_c41 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_101e_c41 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_1084_c41 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1084_c41 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1084_c41 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, store, _⟩ := ric_next h
  exact Blanc.of_run_sstore_not_static store

private theorem staticReject_t_1011_c41 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1011_c41 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1011_c41 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_101e_c41 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_1084_c41 (SFunc.RunCut.uncut body)

private theorem staticReject_t_047f_c86 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_047f_c86 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_047f_c86 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases (SFunc.RunCut.uncut h) with
  | callHalt _ lookup _ body =>
      rw [show cert.prog[41]? = some t_1011_c41 from rfl] at lookup
      cases lookup
      exact staticReject_t_1011_c41 body
  | callRet _ lookup _ body _ =>
      rw [show cert.prog[41]? = some t_1011_c41 from rfl] at lookup
      cases lookup
      exact staticReject_t_1011_c41 body

private theorem staticReject_t_0469_c86 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_0469_c86 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_0469_c86 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_047b_c86 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_047f_c86 (SFunc.RunCut.uncut body)

private theorem staticReject_t_051c_c83 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_051c_c83 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_051c_c83 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_1403_c37 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1403_c37 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1403_c37 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_1469_c37 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1469_c37 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1469_c37 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, store, _⟩ := ric_next h
  exact Blanc.of_run_sstore_not_static store

private theorem staticReject_t_13f5_c37 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_13f5_c37 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_13f5_c37 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_1403_c37 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_1469_c37 (SFunc.RunCut.uncut body)

private theorem staticReject_t_0520_c83 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_0520_c83 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_0520_c83 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases (SFunc.RunCut.uncut h) with
  | callHalt _ lookup _ body =>
      rw [show cert.prog[37]? = some t_13f5_c37 from rfl] at lookup
      cases lookup
      exact staticReject_t_13f5_c37 body
  | callRet _ lookup _ body _ =>
      rw [show cert.prog[37]? = some t_13f5_c37 from rfl] at lookup
      cases lookup
      exact staticReject_t_13f5_c37 body

private theorem staticReject_t_050a_c83 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_050a_c83 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_050a_c83 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_051c_c83 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_0520_c83 (SFunc.RunCut.uncut body)

private theorem staticReject_t_05b1_c80 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_05b1_c80 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_05b1_c80 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_18e9_c34 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_18e9_c34 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_18e9_c34 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_194f_c34 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_194f_c34 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_194f_c34 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, store, _⟩ := ric_next h
  exact Blanc.of_run_sstore_not_static store

private theorem staticReject_t_18de_c34 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_18de_c34 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_18de_c34 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_18e9_c34 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_194f_c34 (SFunc.RunCut.uncut body)

private theorem staticReject_t_05b5_c80 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_05b5_c80 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_05b5_c80 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases (SFunc.RunCut.uncut h) with
  | jump _ lookup _ body =>
      rw [show cert.prog[34]? = some t_18de_c34 from rfl] at lookup
      cases lookup
      exact staticReject_t_18de_c34 body

private theorem staticReject_t_059f_c80 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_059f_c80 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_059f_c80 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_05b1_c80 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_05b5_c80 (SFunc.RunCut.uncut body)

private theorem staticReject_t_1e00_c31 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1e00_c31 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1e00_c31 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_1e66_c31 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1e66_c31 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1e66_c31 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, store, _⟩ := ric_next h
  exact Blanc.of_run_sstore_not_static store

private theorem staticReject_t_1df5_c31 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_1df5_c31 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_1df5_c31 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_1e00_c31 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_1e66_c31 (SFunc.RunCut.uncut body)

private theorem staticReject_t_067b_c78 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_067b_c78 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_067b_c78 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases (SFunc.RunCut.uncut h) with
  | callHalt _ lookup _ body =>
      rw [show cert.prog[31]? = some t_1df5_c31 from rfl] at lookup
      cases lookup
      exact staticReject_t_1df5_c31 body
  | callRet _ lookup _ body _ =>
      rw [show cert.prog[31]? = some t_1df5_c31 from rfl] at lookup
      cases lookup
      exact staticReject_t_1df5_c31 body

private theorem staticReject_t_05f4_c76 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_05f4_c76 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_05f4_c76 at h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  exact (ric_revert h).elim

private theorem staticReject_t_05f8_c76 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_05f8_c76 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_05f8_c76 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases (SFunc.RunCut.uncut h) with
  | callHalt _ lookup _ body =>
      rw [show cert.prog[29]? = some t_1b0c_c29 from rfl] at lookup
      cases lookup
      exact permitGuard_nonstatic body
  | callRet _ lookup _ body _ =>
      rw [show cert.prog[29]? = some t_1b0c_c29 from rfl] at lookup
      cases lookup
      exact permitGuard_nonstatic body

private theorem staticReject_t_05e2_c76 {sevm : Sevm} {d : Devm} {o : Outcome}
    (run : SFunc.Run cert.prog sevm d t_05e2_c76 o) : sevm.isStatic = false := by
  have h := run.cut
  unfold t_05e2_c76 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  obtain ⟨_, _, h⟩ := ric_next h
  cases h with
  | zero _ _ body => exact staticReject_t_05f4_c76 (SFunc.RunCut.uncut body)
  | succ _ _ _ _ body => exact staticReject_t_05f8_c76 (SFunc.RunCut.uncut body)


theorem staticView_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (static : sevm.isStatic = true)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ view : StaticView, Blanc.Sevm.selector sevm = view.selector := by
  have h := run.cut
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gt h
  split at h
  next less =>
    unfold t_002b_c0 at h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    split at h
    next less =>
      unfold t_0036_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_0041_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05da_c75) (by decide) rfl h
        split at h
        next miss =>
          unfold t_004c_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05e2_c76) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0057_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0640_c77) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0062_c0 at h
              obtain ⟨_, h⟩ := ric_cmp_eq (g := t_067b_c78) (by decide) rfl h
              split at h
              next miss =>
                unfold t_006d_c0 at h
                obtain ⟨_, _, h⟩ := ric_next h
                cases (SFunc.RunCut.uncut h) with
                | jump _ lookup _ body =>
                    rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                    cases lookup
                    have impossible := SFunc.Run.cut body
                    change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                    obtain ⟨_, impossible⟩ := ric_dest impossible
                    exact (getter_zeroRevert_impossible impossible).elim
              next hit =>
                have nonstatic := staticReject_t_067b_c78 h.uncut
                exact Bool.noConfusion (static.symm.trans nonstatic)
            next hit =>
              have equal : Bytes.toB256 [0xdd, 0x62, 0xed, 0x3e] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0xdd, 0x62, 0xed, 0x3e])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.allowance, equal.symm⟩
          next hit =>
            have nonstatic := staticReject_t_05e2_c76 h.uncut
            exact Bool.noConfusion (static.symm.trans nonstatic)
        next hit =>
          have equal : Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7] = Blanc.Sevm.selector sevm := by
            by_contra different
            have zero : B256.eqCheck (Bytes.toB256 [0xd2, 0x12, 0x20, 0xa7])
                (Blanc.Sevm.selector sevm) = 0 := by
              simp only [B256.eqCheck, different, ite_false]
            exact hit zero
          exact ⟨.scalar (.address .token1), equal.symm⟩
      next greater =>
        unfold t_0071_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0597_c79) (by decide) rfl h
        split at h
        next miss =>
          unfold t_007d_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_059f_c80) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0088_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_05d2_c81) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0093_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              have equal : Bytes.toB256 [0xc4, 0x5a, 0x01, 0x55] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0xc4, 0x5a, 0x01, 0x55])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.scalar (.address .factory), equal.symm⟩
          next hit =>
            have nonstatic := staticReject_t_059f_c80 h.uncut
            exact Bool.noConfusion (static.symm.trans nonstatic)
        next hit =>
          have equal : Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56] = Blanc.Sevm.selector sevm := by
            by_contra different
            have zero : B256.eqCheck (Bytes.toB256 [0xba, 0x9a, 0x7a, 0x56])
                (Blanc.Sevm.selector sevm) = 0 := by
              simp only [B256.eqCheck, different, ite_false]
            exact hit zero
          exact ⟨.scalar (.constant .minimumLiquidity), equal.symm⟩
    next greater =>
      unfold t_0097_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_00a3_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_04d7_c82) (by decide) rfl h
        split at h
        next miss =>
          unfold t_00ae_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_050a_c83) (by decide) rfl h
          split at h
          next miss =>
            unfold t_00b9_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0556_c84) (by decide) rfl h
            split at h
            next miss =>
              unfold t_00c4_c0 at h
              obtain ⟨_, h⟩ := ric_cmp_eq (g := t_055e_c85) (by decide) rfl h
              split at h
              next miss =>
                unfold t_00cf_c0 at h
                obtain ⟨_, _, h⟩ := ric_next h
                cases (SFunc.RunCut.uncut h) with
                | jump _ lookup _ body =>
                    rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                    cases lookup
                    have impossible := SFunc.Run.cut body
                    change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                    obtain ⟨_, impossible⟩ := ric_dest impossible
                    exact (getter_zeroRevert_impossible impossible).elim
              next hit =>
                obtain ⟨_, _, nonstatic, _⟩ := transfer_entry_inv fork mem h.uncut
                exact Bool.noConfusion (static.symm.trans nonstatic)
            next hit =>
              have equal : Bytes.toB256 [0x95, 0xd8, 0x9b, 0x41] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0x95, 0xd8, 0x9b, 0x41])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.string .symbol, equal.symm⟩
          next hit =>
            have nonstatic := staticReject_t_050a_c83 h.uncut
            exact Bool.noConfusion (static.symm.trans nonstatic)
        next hit =>
          have equal : Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00] = Blanc.Sevm.selector sevm := by
            by_contra different
            have zero : B256.eqCheck (Bytes.toB256 [0x7e, 0xce, 0xbe, 0x00])
                (Blanc.Sevm.selector sevm) = 0 := by
              simp only [B256.eqCheck, different, ite_false]
            exact hit zero
          exact ⟨.singleMapping .nonces, equal.symm⟩
      next greater =>
        unfold t_00d3_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0469_c86) (by decide) rfl h
        split at h
        next miss =>
          unfold t_00df_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_049c_c87) (by decide) rfl h
          split at h
          next miss =>
            unfold t_00ea_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_04cf_c88) (by decide) rfl h
            split at h
            next miss =>
              unfold t_00f5_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              have equal : Bytes.toB256 [0x74, 0x64, 0xfc, 0x3d] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0x74, 0x64, 0xfc, 0x3d])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.scalar (.stored .kLast), equal.symm⟩
          next hit =>
            have equal : Bytes.toB256 [0x70, 0xa0, 0x82, 0x31] = Blanc.Sevm.selector sevm := by
              by_contra different
              have zero : B256.eqCheck (Bytes.toB256 [0x70, 0xa0, 0x82, 0x31])
                  (Blanc.Sevm.selector sevm) = 0 := by
                simp only [B256.eqCheck, different, ite_false]
              exact hit zero
            exact ⟨.singleMapping .balanceOf, equal.symm⟩
        next hit =>
          have nonstatic := staticReject_t_0469_c86 h.uncut
          exact Bool.noConfusion (static.symm.trans nonstatic)
  next greater =>
    unfold t_00f9_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨_, h⟩ := ric_cmp_gt h
    split at h
    next less =>
      unfold t_0105_c0 at h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_0110_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0416_c89) (by decide) rfl h
        split at h
        next miss =>
          unfold t_011b_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_041e_c90) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0126_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0459_c91) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0131_c0 at h
              obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0461_c92) (by decide) rfl h
              split at h
              next miss =>
                unfold t_013c_c0 at h
                obtain ⟨_, _, h⟩ := ric_next h
                cases (SFunc.RunCut.uncut h) with
                | jump _ lookup _ body =>
                    rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                    cases lookup
                    have impossible := SFunc.Run.cut body
                    change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                    obtain ⟨_, impossible⟩ := ric_dest impossible
                    exact (getter_zeroRevert_impossible impossible).elim
              next hit =>
                have equal : Bytes.toB256 [0x5a, 0x3d, 0x54, 0x93] = Blanc.Sevm.selector sevm := by
                  by_contra different
                  have zero : B256.eqCheck (Bytes.toB256 [0x5a, 0x3d, 0x54, 0x93])
                      (Blanc.Sevm.selector sevm) = 0 := by
                    simp only [B256.eqCheck, different, ite_false]
                  exact hit zero
                exact ⟨.scalar (.stored .price1CumulativeLast), equal.symm⟩
            next hit =>
              have equal : Bytes.toB256 [0x59, 0x09, 0xc0, 0xd5] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0x59, 0x09, 0xc0, 0xd5])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.scalar (.stored .price0CumulativeLast), equal.symm⟩
          next hit =>
            obtain ⟨_, _, nonstatic, _⟩ := initialize_entry_inv fork h.uncut
            exact Bool.noConfusion (static.symm.trans nonstatic)
        next hit =>
          have equal : Bytes.toB256 [0x36, 0x44, 0xe5, 0x15] = Blanc.Sevm.selector sevm := by
            by_contra different
            have zero : B256.eqCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15])
                (Blanc.Sevm.selector sevm) = 0 := by
              simp only [B256.eqCheck, different, ite_false]
            exact hit zero
          exact ⟨.scalar (.stored .domainSeparator), equal.symm⟩
      next greater =>
        unfold t_0140_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03ad_c93) (by decide) rfl h
        split at h
        next miss =>
          unfold t_014c_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03f0_c94) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0157_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03f8_c95) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0162_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              have equal : Bytes.toB256 [0x31, 0x3c, 0xe5, 0x67] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0x31, 0x3c, 0xe5, 0x67])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.scalar (.constant .decimals), equal.symm⟩
          next hit =>
            have equal : Bytes.toB256 [0x30, 0xad, 0xf8, 0x1f] = Blanc.Sevm.selector sevm := by
              by_contra different
              have zero : B256.eqCheck (Bytes.toB256 [0x30, 0xad, 0xf8, 0x1f])
                  (Blanc.Sevm.selector sevm) = 0 := by
                simp only [B256.eqCheck, different, ite_false]
              exact hit zero
            exact ⟨.scalar (.constant .permitTypehash), equal.symm⟩
        next hit =>
          obtain ⟨_, _, _, nonstatic, _⟩ := transferFrom_entry_inv fork mem h.uncut
          exact Bool.noConfusion (static.symm.trans nonstatic)
    next greater =>
      unfold t_0166_c0 at h
      obtain ⟨_, h⟩ := ric_dest h
      obtain ⟨_, h⟩ := ric_cmp_gt h
      split at h
      next less =>
        unfold t_0172_c0 at h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0315_c96) (by decide) rfl h
        split at h
        next miss =>
          unfold t_017d_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0362_c97) (by decide) rfl h
          split at h
          next miss =>
            unfold t_0188_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0393_c98) (by decide) rfl h
            split at h
            next miss =>
              unfold t_0193_c0 at h
              obtain ⟨_, _, h⟩ := ric_next h
              cases (SFunc.RunCut.uncut h) with
              | jump _ lookup _ body =>
                  rw [show cert.prog[32]? = some t_01b9_c32 from rfl] at lookup
                  cases lookup
                  have impossible := SFunc.Run.cut body
                  change SFunc.RunCut cert.prog sevm [] _ (.dest t_000c_c0) (.done o) at impossible
                  obtain ⟨_, impossible⟩ := ric_dest impossible
                  exact (getter_zeroRevert_impossible impossible).elim
            next hit =>
              have equal : Bytes.toB256 [0x18, 0x16, 0x0d, 0xdd] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0x18, 0x16, 0x0d, 0xdd])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.totalSupply, equal.symm⟩
          next hit =>
            have equal : Bytes.toB256 [0x0d, 0xfe, 0x16, 0x81] = Blanc.Sevm.selector sevm := by
              by_contra different
              have zero : B256.eqCheck (Bytes.toB256 [0x0d, 0xfe, 0x16, 0x81])
                  (Blanc.Sevm.selector sevm) = 0 := by
                simp only [B256.eqCheck, different, ite_false]
              exact hit zero
            exact ⟨.scalar (.address .token0), equal.symm⟩
        next hit =>
          obtain ⟨_, nonstatic, _⟩ := approve_entry_inv fork mem h.uncut
          exact Bool.noConfusion (static.symm.trans nonstatic)
      next greater =>
        unfold t_0197_c0 at h
        obtain ⟨_, h⟩ := ric_dest h
        obtain ⟨_, h⟩ := ric_cmp_eq (g := t_01be_c99) (by decide) rfl h
        split at h
        next miss =>
          unfold t_01a3_c0 at h
          obtain ⟨_, h⟩ := ric_cmp_eq (g := t_0259_c100) (by decide) rfl h
          split at h
          next miss =>
            unfold t_01ae_c0 at h
            obtain ⟨_, h⟩ := ric_cmp_eq (g := t_02d6_c101) (by decide) rfl h
            split at h
            next miss =>
              unfold t_01b9_c0 at h
              obtain ⟨_, h⟩ := ric_dest h
              obtain ⟨_, _, h⟩ := ric_next h
              obtain ⟨_, _, h⟩ := ric_next h
              exact (ric_revert h).elim
            next hit =>
              have equal : Bytes.toB256 [0x09, 0x02, 0xf1, 0xac] = Blanc.Sevm.selector sevm := by
                by_contra different
                have zero : B256.eqCheck (Bytes.toB256 [0x09, 0x02, 0xf1, 0xac])
                    (Blanc.Sevm.selector sevm) = 0 := by
                  simp only [B256.eqCheck, different, ite_false]
                exact hit zero
              exact ⟨.getReserves, equal.symm⟩
          next hit =>
            have equal : Bytes.toB256 [0x06, 0xfd, 0xde, 0x03] = Blanc.Sevm.selector sevm := by
              by_contra different
              have zero : B256.eqCheck (Bytes.toB256 [0x06, 0xfd, 0xde, 0x03])
                  (Blanc.Sevm.selector sevm) = 0 := by
                simp only [B256.eqCheck, different, ite_false]
              exact hit zero
            exact ⟨.string .name, equal.symm⟩
        next hit =>
          have nonstatic := staticReject_t_01be_c99 h.uncut
          exact Bool.noConfusion (static.symm.trans nonstatic)


/-- Successful static certified pc-zero execution reaches an actual view selector. -/
theorem staticView_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = true)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      ∃ view : StaticView, Blanc.Sevm.selector sevm = view.selector := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  exact ⟨value, size, staticView_selector_inv fork getterInitMemory_ptr static run⟩

/-- Actual raw operational success supplies the selector partition, without a selector premise. -/
theorem staticView_bytecode_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      ∃ view : StaticView, Blanc.Sevm.selector sevm = view.selector := by
  exact staticView_pc0_inv fork static (lift_sound cert_check codeEq fork run)

end Blanc.Lift.UniswapV2Pair
