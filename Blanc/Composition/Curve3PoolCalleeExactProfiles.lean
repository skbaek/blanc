import Blanc.Lift.StaticGasTransport
import Blanc.Lift.CallProfileTransport
import Blanc.Lift.Curve3Pool.ExactLivePremises
import Blanc.Composition.Curve3PoolCalleeLive

/-!
# Selected-cost exact profiles for the pool's deployed 3Crv calls

Retain a supplied, proved exact child cost and choose its full canonical
successor from normalized inputs before supplying call gas. Existing bounded profile statements
are retained; the closed-cost exports supply the exact body runs.
-/

namespace Blanc.Composition.Curve3PoolCalleeExactProfiles

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3PoolCalleeLive

private theorem supply_body_certificate :
    Curve3Crv.t_0240_c0.gasFree = true ∧ Curve3Crv.t_0240_c0.refs = [] := by
  sorry

private theorem mint_body_certificate :
    Curve3Crv.t_056e_c0.gasFree = true ∧ Curve3Crv.t_056e_c0.refs = [] := by
  sorry

private theorem burn_body_certificate :
    Curve3Crv.t_0644_c0.gasFree = true ∧ Curve3Crv.t_0644_c0.refs = [] := by
  sorry

/-- A supplied exact body cost has one full canonical post before either gas parameter. -/
theorem fixed_cost_body
    {s : Sevm} {b : Devm} {f : SFunc} {r : Curve3Crv.Raw}
    (c : Nat)
    (hsg : s.benvStat.rules.stateGas = none)
    (hf : f.gasFree = true) (hrefs : f.refs = [])
    (hbody : ∀ R, gCallStipend < R → ∃ post,
      SFunc.RunExact Curve3Crv.prog s (Curve3Crv.entrySt s b (R + c)) f (.halted post) ∧
      post.gasLeft = R ∧ Curve3Crv.Lands s b post r) :
    ∃ canonical : Devm, canonical.gasLeft = 0 ∧
      ∀ staticGas R, gCallStipend < R → ∃ post,
        SFunc.RunExact Curve3Crv.prog {s with gas := staticGas}
          (Curve3Crv.entrySt s b (R + c)) f (.halted post) ∧
        post.gasLeft = R ∧ Curve3Crv.Lands s b post r ∧
        Devm.EqModGas post canonical := by
  sorry

end Blanc.Composition.Curve3PoolCalleeExactProfiles
