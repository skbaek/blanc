import Blanc.Lift.ChainNoExec
import Blanc.Lift.PoolCoinSel
import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.Dai.Check

/-!
# A DAI frame on `transfer`, `transferFrom` or `balanceOf` enters no frame

A frame (of any outcome) whose calldata selector is one of the three the pool sends decodes no external instruction on its
own chain: the dispatcher sends the reach to the selector's wrapper, whose closure lies in a decided exec-free set, the
largest exec-free reference-closed set of the certificate.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift

section Dai

def daiFree : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59]

theorem daiFree_execFree : ExecFreeSet Dai.cert.prog daiFree = true := by decide +kernel

/-- **DAI on the pool's selectors enters no frame.** -/
theorem dai_noExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Dai.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run :=
  noExec_of_reach Dai.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Dai.t_0000_c0, []⟩ T at h
    repeat rstepN h t
    rbranchE h t daiFree_execFree
    repeat rstepN h t
    rbranchE h t daiFree_execFree
    iterate 4 rstepN h t
    rw [shr_selector_word] at h
    rcases sel with s | s | s <;> rw [s] at h <;> repeat rdispE h t daiFree_execFree

end Dai

theorem dai_frameKeeps (c : Exec.Frame) (hpc : c.pc = 0) (hcode : c.sevm.code = Dai.code)
    (hsg : c.sevm.benvStat.rules.stateGas = none)
    (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) : FrameKeepsForeign c :=
  frameKeeps_of_noExec c hpc hsg fun run e _ => dai_noExec run (e ▸ hcode) (e ▸ hsg) (e ▸ sel)

end Blanc.Lift.CurveCoins
