import Blanc.Lift.Curve3Pool.Walk.ExchangeModel

/-!
# `exchange`, inverted: every checked step of a successful model `exchange`

`exchange_inv` reads a successful `exchange s e i j dx minDy = some o` back into each checked
operation it passed (the converse of `ex_model_eq`), as the liveness walk needs them to steer the
frame's checks.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **A successful model `exchange`, inverted.** -/
theorem exchange_inv {s : State} {e : Env} {i j : Fin 3} {dx minDy : Nat} {o : Out}
    (h : exchange s e i j dx minDy = some o) :
    s.isKilled = false ∧ ∃ xp D X Y x amp y dy1 dy dfp fee dop outp out afp adm0 aop adm bi bj1 bj,
      xpChk s.balances = some xp ∧ pullIn e i dx = some D ∧ chkMul D (rates.get i) = some X ∧
      chkDiv X precision = some Y ∧ chkAdd (xp.get i) Y = some x ∧ aChk s e.time = some amp ∧
      getYChk amp i j x xp.get = some y ∧ chkSub (xp.get j) y = some dy1 ∧
      chkSub dy1 1 = some dy ∧ chkMul dy s.fee = some dfp ∧ chkDiv dfp feeDen = some fee ∧
      chkSub dy fee = some dop ∧ chkMul dop precision = some outp ∧
      chkDiv outp (rates.get j) = some out ∧ minDy ≤ out ∧ chkMul fee s.adminFee = some afp ∧
      chkDiv afp feeDen = some adm0 ∧ chkMul adm0 precision = some aop ∧
      chkDiv aop (rates.get j) = some adm ∧ chkAdd (s.balances.get i) D = some bi ∧
      chkSub (s.balances.get j) out = some bj1 ∧ chkSub bj1 adm = some bj ∧
      (e.coin j).pushOk = true ∧
      o = ⟨{s with balances := (s.balances.set i bi).set j bj}, none,
        [.tokenExchange e.caller i.val dx j.val out], [.pull i e.caller dx, .push j e.caller out]⟩ := by
  unfold exchange req at h
  obtain ⟨u0, hk, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨xp, hxp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨D, hD, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Y, hY, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨amp, hamp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dy1, hdy1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dy, hdy, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dfp, hdfp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fee, hfee, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨dop, hdop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨outp, houtp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨out, hout, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u1, hmin, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨afp, hafp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨adm0, hadm0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨aop, haop, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨adm, hadm, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨bi, hbi, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨bj1, hbj1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨bj, hbj, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨u2, hpush, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := (Option.some.inj h).symm
  refine ⟨?_, xp, D, X, Y, x, amp, y, dy1, dy, dfp, fee, dop, outp, out, afp, adm0, aop, adm, bi,
    bj1, bj, hxp, hD, hX, hY, hx, hamp, hy, hdy1, hdy, hdfp, hfee, hdop, houtp, hout, ?_, hafp, hadm0,
    haop, hadm, hbi, hbj1, hbj, ?_, rfl⟩
  · split_ifs at hk with hc
    · exact hc
  · split_ifs at hmin with hc
    · exact hc
  · split_ifs at hpush with hc
    · exact hc

end Blanc.Lift.Curve3Pool
