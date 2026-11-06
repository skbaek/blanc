import Blanc.Lift.CurveCoins.KeepUsdt

/-!
# A TetherToken frame, not deprecated, enters no frame

`usdt_noExec` covers the pool's three selectors. USDT's six `CALL`s are the deprecated forwards of `transfer`,
`transferFrom`, `balanceOf`, `approve`, `allowance` and `totalSupply`, and `destroyBlackFunds` reaches the
`balanceOf` forward through its internal call. So:

* `usdt_noExec_any`: under `flag20 (slot 10) = 0` at its entry, a frame on *any* selector decodes no external
  instruction on its chain;
* `usdt_descendants_nil`: it has no raw descendant frame at all.

The dispatcher is crossed once, by `Reach.gotoTree`, whatever the selector: each of its gotos lies in the
exec-free set but those seven wrappers.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc Blanc.Lift

section Reach

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {R : Exec.Deriv} {T : Conf}

/-- `approve`'s body, not deprecated. -/
theorem usdt_e19_reach {v t' ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (v :: t' :: ret :: S) M G, Usdt.t_0b73_c19, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rdeprecated h t c hdep

/-- `totalSupply`'s body, not deprecated. -/
theorem usdt_e22_reach {ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (ret :: S) M G, Usdt.t_0ded_c22, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rdeprecated h t c hdep

/-- `allowance`'s body, not deprecated. -/
theorem usdt_e43_reach {a o ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (a :: o :: ret :: S) M G, Usdt.t_1b0d_c43, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rdeprecated h t c hdep

/-- `destroyBlackFunds`' body, not deprecated: its internal `balanceOf` does not forward. -/
theorem usdt_e49_reach {a ret : B256} (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor b sevm.currentTarget).get 10) = 0)
    (h : Reach (StepIn R) Usdt.cert.prog sevm ⟨St b (a :: ret :: S) M G, Usdt.t_1e8a_c49, []⟩ T)
    (t : AtExec T) : False := by
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rbranchE h t usdtFree_execFree
  repeat rstepS h t bal
  rinto h t 33 Usdt.t_1239_c33
  exact usdt_e33_reach bal (by simpa only [afterSloadH_getStor] using hdep) h t

end Reach

/-- Every goto of TetherToken's dispatcher: the exec-free set, and the seven forwarding wrappers. -/
def usdtGotos : List Nat := usdtFree ++ [66, 69, 70, 80, 85, 89, 95]

theorem usdt_dispatch : Usdt.t_0000_c0.gotoTree usdtGotos regSilent = true := by decide +kernel

/-- **TetherToken, on any selector, not deprecated at its entry, enters no frame.** -/
theorem usdt_noExec_any {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Usdt.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor pre sevm.currentTarget).get 10) = 0) : ChainNoExec run :=
  noExec_of_reach Usdt.cert_check rfl rfl run hcode hsg fun T h t => by
    change Reach _ _ _ ⟨_, Usdt.t_0000_c0, []⟩ T at h
    obtain ⟨k, hk, g, d, look, same, h'⟩ := Reach.gotoTree (W := usdtGotos) (ok := regSilent)
      (Ψ := fun d => d.state = pre.state) (fun _ => rfl)
      (fun ok step e => (Ninst.Run.state_of_regSilent ok (StepIn.toRun step)).trans e)
      (fun pop e => pop.state.symm.trans e) (fun burn e => burn.state.symm.trans e)
      h t usdt_dispatch rfl
    clear h
    have h := h'
    clear h'
    have hd : Usdt.flag20 ((Devm.getStor d sevm.currentTarget).get 10) = 0 := by
      have e : Devm.getStor d = Devm.getStor pre := by
        funext a
        simp only [Devm.getStor, Devm.getAcct, same]
      rw [e]
      exact hdep
    rw [St.self' d] at h
    rcases List.mem_append.mp hk with free | forward
    · exact Reach.false_of_execFree usdtFree_execFree h t (ExecFreeSet.lookup usdtFree_execFree free look)
        (fun _ hs => absurd hs List.not_mem_nil)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at forward
      rcases forward with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> cases look
      · repeat rstepN h t
        rbranchE h t usdtFree_execFree
        repeat rstepN h t
        rinto h t 19 Usdt.t_0b73_c19
        exact usdt_e19_reach bal hd h t
      · repeat rstepN h t
        rbranchE h t usdtFree_execFree
        repeat rstepN h t
        rinto h t 22 Usdt.t_0ded_c22
        exact usdt_e22_reach bal hd h t
      · repeat rstepN h t
        rbranchE h t usdtFree_execFree
        repeat rstepN h t
        rinto h t 23 Usdt.t_0ebd_c23
        exact usdt_e23_reach bal hd h t
      · repeat rstepN h t
        rbranchE h t usdtFree_execFree
        repeat rstepN h t
        rinto h t 33 Usdt.t_1239_c33
        exact usdt_e33_reach bal hd h t
      · repeat rstepN h t
        rbranchE h t usdtFree_execFree
        repeat rstepN h t
        rinto h t 39 Usdt.t_14f4_c39
        exact usdt_e39_reach bal hd h t
      · repeat rstepN h t
        rbranchE h t usdtFree_execFree
        repeat rstepN h t
        rinto h t 43 Usdt.t_1b0d_c43
        exact usdt_e43_reach bal hd h t
      · repeat rstepN h t
        rbranchE h t usdtFree_execFree
        repeat rstepN h t
        rinto h t 49 Usdt.t_1e8a_c49
        exact usdt_e49_reach bal hd h t

/-- **A TetherToken frame, not deprecated at its entry, has no raw descendant**, whatever its outcome. -/
theorem usdt_descendants_nil {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = Usdt.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (hdep : Usdt.flag20 ((Devm.getStor pre sevm.currentTarget).get 10) = 0) :
    Exec.rawFrameDescendants run = [] :=
  Exec.rawFrameDescendants_eq_nil_of_noExec run (usdt_noExec_any run hcode hsg bal hdep)

end Blanc.Lift.CurveCoins
