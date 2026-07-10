import Blanc.Temp

open Temp

lemma foo {xs : B8L} {hxs : xs.length ≤ 32} :
    Ninst.EffectGen Devm.BalNoninc (.push xs hxs) := by
  unfold Ninst.EffectGen Ninst.Run'
  intro pc sevm pre xl out hxl hRun
  cases xl
  · simp only at hRun
    cases hcg : chargeGas (if xs = [] then gBase else gVerylow) pre with
    | error e =>
      simp [hcg] at hRun
      subst hRun
      unfold Execution.Rel Outcome.Rel
      simp only [chargeGas] at hcg
      split at hcg
      · cases hcg; exact balNoninc_refl_trans.2.1 pre
      · contradiction
    | ok devm' => sorry
  · simp only at hRun
