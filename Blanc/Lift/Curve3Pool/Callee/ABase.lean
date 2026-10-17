import Blanc.Lift.Curve3Pool.Callee.A
import Blanc.Lift.IdentityCallGas

/-!
# What `_A`'s base keeps

`aBase` only loads storage words, so it keeps every account's storage and code, the logs and the
output, and an identity-ready base stays identity-ready. Walk-neutral: the `exchange` and
`add_liquidity` walks both consume these facts, and this file does not reach `Check.lean`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift

theorem aBase_getStor (sevm : Sevm) (b : Devm) (a : Adr) : (aBase sevm b).getStor a = b.getStor a := by
  unfold aBase; split <;> simp only [afterSload_getStor]

theorem aBase_logs (sevm : Sevm) (b : Devm) : (aBase sevm b).logs = b.logs := by
  unfold aBase; split <;> simp only [afterSload_logs]

theorem aBase_output (sevm : Sevm) (b : Devm) : (aBase sevm b).output = b.output := by
  unfold aBase; split <;> simp only [afterSload_output]

theorem aBase_getCode (sevm : Sevm) (b : Devm) (a : Adr) : (aBase sevm b).getCode a = b.getCode a := by
  unfold aBase; split <;> simp only [afterSload_getCode]

theorem IdReady_aBase {sevm : Sevm} {b : Devm} (h : IdReady sevm b) : IdReady sevm (aBase sevm b) := by
  unfold aBase; split
  · exact (((h.afterSload _).afterSload _).afterSload _).afterSload _
  · exact (h.afterSload _).afterSload _

end Blanc.Lift.Curve3Pool
