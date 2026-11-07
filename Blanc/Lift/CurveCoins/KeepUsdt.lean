import Blanc.Lift.ChainNoExec
import Blanc.Lift.PoolCoinSel
import Blanc.Lift.HistIdentityCall
import Blanc.Lift.InvWalkLegacy
import Blanc.Lift.UsdtFrames

/-!
# A USDT frame on `transfer`, `transferFrom` or `balanceOf` enters no frame

A frame (of any outcome) whose calldata selector is one of the three the pool sends decodes no external instruction on its
own chain, given the named premise `flag20 (slot 10) = 0`: these selectors leave the decided exec-free set only at the
deprecated forwards, so the theorem walks past that branch. Nothing else about storage is assumed, and no fit premise.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift

section Usdt

def usdtFree : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 24, 25, 26, 27, 28, 29, 30, 31, 32, 34, 35, 36, 37, 38, 40, 41, 42, 44, 45, 46, 47, 48, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 67, 68, 71, 72, 73, 74, 75, 76, 77, 78, 79, 81, 82, 83, 84, 86, 87, 88, 90, 91, 92, 93, 94]

theorem usdtFree_execFree : ExecFreeSet Usdt.cert.prog usdtFree = true := by decide +kernel

/-- The branch on `deprecated`: the forwarding arm contradicts the flag, the other lies in the set. -/
macro "rdeprecated " h:ident t:ident c:ident hdep:ident : tactic => `(tactic|
  (rcases rr_branch $h $t with ⟨$c, _, $h:ident⟩ | ⟨$c, _, $h:ident⟩
   · exfalso
     simp only [afterSloadH_getStor, afterSloadH_getStorVal, gsv, show Bytes.toB256 [10] = 10 from by decide] at $c:ident
     rw [show (Bytes.toB256 [255] &&& (Devm.getStor _ _).get 10 /
       B256.bexp (Bytes.toB256 [1, 0]) (Bytes.toB256 [20])) = 0 from $hdep] at $c:ident
     exact absurd $c (by decide)
   · exact Reach.false_of_execFree usdtFree_execFree $h $t (by decide)
       (fun _ hs => absurd hs List.not_mem_nil)))

section Reach

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {R : Exec.Deriv} {T : Conf}

/-- `transfer`'s body, not deprecated. -/
theorem usdt_e39_reach {v t' ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (v :: t' :: ret :: S) M G, Usdt.t_14f4_c39, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rdeprecated h t c hdep

/-- `transferFrom`'s body, not deprecated. -/
theorem usdt_e23_reach {v t' r ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (v :: t' :: r :: ret :: S) M G, Usdt.t_0ebd_c23, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rdeprecated h t c hdep

/-- `balanceOf`'s body, not deprecated. -/
theorem usdt_e33_reach {a ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (a :: ret :: S) M G, Usdt.t_1239_c33, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rdeprecated h t c hdep

end Reach

/-- Enter wrapper callee `k` (tree `g`), whose continuation lies in the set, from a reach `h`. -/
macro "rinto " h:ident t:ident k:num g:term : tactic => `(tactic|
  (have h' := rr_callInto (k := $k) (g := $g) usdtFree_execFree rfl (by decide)
     (fun _ hs => absurd hs List.not_mem_nil) $h $t
   clear $h
   obtain ⟨_, _, $h:ident, e⟩ := h'
   subst e
   replace $t:ident := AtExec.below.1 $t))

/-- **TetherToken on the pool's selectors, not deprecated, enters no frame.** -/
theorem usdt_noExec {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Usdt.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor pre sevm.currentTarget).get 10) = 0)
    (sel : PoolCoinSel (Blanc.Sevm.selector sevm)) : ChainNoExec run :=
  noExec_of_reach Usdt.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Usdt.t_0000_c0, []⟩ T at h
    iterate 7 rstepN h t
    rbranchE h t usdtFree_execFree
    iterate 7 rstepN h t
    rw [legacy_selector_word] at h
    rcases sel with s | s | s <;> rw [s] at h <;> repeat rdispE h t usdtFree_execFree
    · repeat rstepN h t
      rbranchE h t usdtFree_execFree
      repeat rstepN h t
      rinto h t 39 Usdt.t_14f4_c39
      exact usdt_e39_reach bal (by simpa only [St_getStor] using hdep) h t
    · repeat rstepN h t
      rbranchE h t usdtFree_execFree
      repeat rstepN h t
      rinto h t 23 Usdt.t_0ebd_c23
      exact usdt_e23_reach bal (by simpa only [St_getStor] using hdep) h t
    · repeat rstepN h t
      rbranchE h t usdtFree_execFree
      repeat rstepN h t
      rinto h t 33 Usdt.t_1239_c33
      exact usdt_e33_reach bal (by simpa only [St_getStor] using hdep) h t

end Usdt

/-- **`deprecated` is the operator power USDT's keep names**: TetherToken's slot `10` flag clear at the
frame's entry. While it is set, these selectors forward to an owner-chosen address, about which
nothing holds. -/
theorem usdt_frameKeeps (c : Exec.Frame) (hpc : c.pc = 0) (hcode : c.sevm.code = Usdt.code)
    (hsg : c.sevm.benvStat.rules.stateGas = none) (bal : c.sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor c.pre c.sevm.currentTarget).get 10) = 0)
    (sel : PoolCoinSel (Blanc.Sevm.selector c.sevm)) : FrameKeepsForeign c :=
  frameKeeps_of_noExec c hpc hsg fun run e p =>
    usdt_noExec run (e ▸ hcode) (e ▸ hsg) (e ▸ bal) (by subst e; subst p; exact hdep) (e ▸ sel)

end Blanc.Lift.CurveCoins
