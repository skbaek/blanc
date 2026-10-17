import Blanc.Lift.Curve3Pool.Cert
import Blanc.Lift.InvWalkCallNext
import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.CallSiteChildren

/-!
# The internal-call and frame-loop kits on the 3pool runtime

Kernel facts and instances of `Blanc/Lift/InvWalkCallNext.lean` (K1) and
`Blanc/Lift/VyperFrameLoop.lean` (K3) at the 3pool runtime certificate, taken from
`get_D_mem` (entry 29, pc `0x7b7`), whose walk consumes them:

* the frame save of `[0x140, 0x420)` at `0x7d3` (23 iterations: the first inline in entry 29's
  tree, copies at entries `54 … 415`, exit tree `t_07f5_c415`);
* the call of `get_D` (entry 417) at `PC` pc `0x8c6`, returning to `t_08cc_c718`, with
  `get_D`'s never-halts scan;
* the frame restore of `[0x140, 0x420)` at `0x8d8` (copies at entries `727 … 918`, exit tree
  `t_08fb_c918`).

Each chain is one kernel fact (`FrameSaveChain`/`FrameRestoreChain`, `decide +kernel` over the
`DecidableEq SFunc` of `Blanc/Lift/CallSiteChildren.lean`), each start tree one kernel equation,
and the scan one `decide +kernel`.  (Elaborator `rfl` exceeds the default recursion depth on
lookups this deep into the certificate.)
-/

namespace Blanc.Lift.Curve3Pool

open Jaune

/-- The lifted runtime program. -/
abbrev prog : List SFunc := Cert.prog cert

/-! ## `get_D_mem`'s frame save, `0x7d3` -/

/-- Counter `0x420`, bound `0x420`, exit tag `0x7f5`, head tag `0x7d3`. -/
def saveTpl_07d3 : FrameLoopTpl := ⟨0x04, 0x20, 0x04, 0x20, 0x07, 0xf5, 0x07, 0xd3⟩

/-- The unrolled copies after the first iteration. -/
def saveKs_07d3 : List Nat :=
  [54, 81, 103, 124, 146, 168, 190, 208, 222, 236, 250, 265, 280, 295, 310, 325, 340, 355, 370,
    385, 400, 415]

theorem saveTpl_07d3_c : saveTpl_07d3.c = 0x420 := by decide

theorem saveKs_07d3_length : saveKs_07d3.length = 22 := rfl

theorem t_07d3_c29_eq : t_07d3_c29 = saveTpl_07d3.saveTree t_07f5_c415 saveKs_07d3 := by
  decide +kernel

theorem saveChain_07d3 : FrameSaveChain prog saveTpl_07d3 t_07f5_c415 saveKs_07d3 := by
  unfold FrameSaveChain
  decide +kernel

/-- The save, inverted at the 3pool instance: 23 frame words of `[0x140, 0x420)` pushed, the
counter at `0x420`. -/
theorem ric_save_07d3 {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {r : Seg} (hC : ∀ k ∈ saveKs_07d3, k ∉ C) (hsz : M.size % 32 = 0)
    (hcs : 0x440 ≤ M.size) (hctr : memWord M 0x420 = Nat.toB256 0x140)
    (run : SFunc.RunCut prog sevm C (St b S M G) t_07d3_c29 r) :
    ∃ G', SFunc.RunCut prog sevm C (St b ((frameWords M 0x140 23).reverse ++ S)
      (saveMem M 0x420 0x140 23) G') t_07f5_c415 r := by
  rw [t_07d3_c29_eq] at run
  have h := ric_frameSave_chain saveChain_07d3 hC hsz (by rw [saveTpl_07d3_c]; omega)
    (by rw [saveTpl_07d3_c]; exact hctr) (by rw [saveTpl_07d3_c, saveKs_07d3_length]) run
  simpa only [saveTpl_07d3_c, saveKs_07d3_length] using h

/-! ## The call of `get_D`, `0x8c6` -/

theorem prog_417 : prog[417]? = some t_04c9_c417 := by decide +kernel

theorem getD_neverHalts : calleeNeverHalts prog 417 4096 = true := by decide +kernel

/-- The call of `get_D` from `get_D_mem`, inverted: `get_D` runs from return address `0x8cc`
to `.returned D`, and `get_D_mem` goes on at the return tag from `D`. -/
theorem ric_call_getD_08c6 {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) (pcCallTree 0x8c6 0x04 0xc9 417 t_08cc_c718) r) :
    ∃ G' D, SFunc.Run prog sevm (St b (Nat.toB256 0x8cc :: S) M G') t_04c9_c417 (.returned D) ∧
      SFunc.RunCut prog sevm C D t_08cc_c718 r :=
  ric_pcCall getD_neverHalts prog_417 (by decide) run

/-! ## `get_D_mem`'s frame restore, `0x8d8` -/

/-- Counter `0x420`, bound `lo = 0x140`, exit tag `0x8fb`, head tag `0x8d8`. -/
def restoreTpl_08d8 : FrameLoopTpl := ⟨0x04, 0x20, 0x01, 0x40, 0x08, 0xfb, 0x08, 0xd8⟩

def restoreKs_08d8 : List Nat :=
  [727, 736, 745, 755, 765, 774, 783, 792, 801, 810, 819, 828, 837, 846, 855, 864, 873, 882, 891,
    900, 909, 918]

theorem restoreTpl_08d8_c : restoreTpl_08d8.c = 0x420 := by decide

theorem restoreKs_08d8_length : restoreKs_08d8.length = 22 := rfl

theorem t_08d8_c718_eq : t_08d8_c718 = restoreTpl_08d8.restoreTree t_08fb_c918 restoreKs_08d8 := by
  decide +kernel

theorem restoreChain_08d8 : FrameRestoreChain prog restoreTpl_08d8 t_08fb_c918 restoreKs_08d8 := by
  unfold FrameRestoreChain
  decide +kernel

/-- The restore, inverted at the 3pool instance: the 23 saved words of `W` written back, so the
frame `[0x140, 0x420)` reads as `W`'s. -/
theorem ric_restore_08d8 {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M W : Mem}
    {G : Nat} {r : Seg} (hC : ∀ k ∈ restoreKs_08d8, k ∉ C) (hsz : M.size % 32 = 0)
    (hcs : 0x440 ≤ M.size) (hctr : memWord M 0x420 = Nat.toB256 0x400)
    (run : SFunc.RunCut prog sevm C (St b ((frameWords W 0x140 23).reverse ++ S) M G)
      t_08d8_c718 r) :
    ∃ G' M', SFunc.RunCut prog sevm C (St b S M' G') t_08fb_c918 r ∧
      Words M' (frameSlots W 0x140 23) ∧ M'.size = M.size := by
  rw [t_08d8_c718_eq] at run
  have h := ric_frameRestore_chain (lo := 0x140) restoreChain_08d8 hC
    (by rw [List.length_reverse, length_frameWords, restoreKs_08d8_length]) hsz
    (by rw [restoreTpl_08d8_c]; omega) (by decide)
    (by rw [restoreTpl_08d8_c, restoreKs_08d8_length])
    (by rw [restoreTpl_08d8_c, restoreKs_08d8_length]; exact hctr) run
  obtain ⟨G', h⟩ := h
  rw [restoreTpl_08d8_c, restoreKs_08d8_length] at h
  refine ⟨G', _, h, restoreMem_frameWords (n := 23) (by omega) (by decide), ?_⟩
  exact restoreMem_size _ (by omega) (by omega)

end Blanc.Lift.Curve3Pool
