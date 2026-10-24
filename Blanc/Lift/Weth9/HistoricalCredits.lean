import Blanc.ExecutionRewardCredits
import Blanc.ExecutionStagedBodyTrace
import Blanc.Lift.Weth9.Footprint

/-!
# WETH9 historical fork selection and proof-of-work reward credits

Rewards leave the deployed contract's storage intact and increase its backing
balance under the exact total-mint budget. This is the frame-free reward stage
of a historical body, not a deployment-to-checkpoint history theorem.
-/

namespace Blanc.Lift.Weth9

open Jaune

/-- The mainnet schedule selects Byzantium at WETH9's recorded deployment
coordinates: block 4719568, timestamp 1513077455. These coordinates are retained
in Plans `evidence/deploy-init-v1/weth9-creation-drpc.json` for transaction
`0xb95343413e459a0f97461812111254163ae53467855c0d73e0f1e7c5b8442fa3`.
This theorem selects rules; it does not assert historical execution/inclusion. -/
theorem weth9_deployment_fork :
    mainnetChainConfig.forkAt 4719568 1513077455 = .ok .byzantium := by
  decide +kernel

/-- The real PoW credit stage preserves the same footprint and its backing.
The input is the preceding stage's footprint, never an assumed endpoint one. -/
theorem FootInv.payRewards {K : Key → Prop} {world : Jaune.State} {ca : Adr}
    (initial : FootInv K (world.getStor ca) (world.bal ca))
    (protection : Blanc.State.Protected world ca)
    (pow : PowRules) (number : Nat) (coinbase : Adr) (ommers : List Header)
    (bound : sum world.bal + ChainConfig.rewardTotal pow number ommers < 2 ^ 256) :
    FootInv K ((payRewards pow number coinbase ommers world).getStor ca)
      ((payRewards pow number coinbase ommers world).bal ca) := by
  have storage := payRewards_getStor_of_protected pow number coinbase ommers protection
  rw [storage]
  exact ⟨initial.support, initial.inj, initial.apart,
    initial.backed.trans (payRewards_balance_mono pow number coinbase ommers bound ca)⟩

/-- WETH9's request-stage footprint reaches the actual retained body endpoint,
including the selected fork's PoW mint. Earlier stages are not assumed solved. -/
theorem footprint_after_rewardStage {K : Key → Prop} {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {world : Jaune.State} {bout : BlockOutput}
    (trace : ExecutionTrace.StagedBodyTrace benv txs ommers wds world bout)
    (initial : FootInv K (trace.requestState.getStor ca) (trace.requestState.bal ca))
    (protection : Blanc.State.Protected trace.requestState ca)
    (budget : ∀ pow, benv.stat.rules.pow = some pow →
      sum trace.requestState.bal + ChainConfig.rewardTotal pow benv.stat.number ommers < 2 ^ 256) :
    FootInv K (world.getStor ca) (world.bal ca) := by
  have endpoint := trace.state_eq_rewardState.trans trace.rewardState_eq
  cases enabled : benv.stat.rules.pow with
  | none =>
      simp only [enabled] at endpoint
      exact (congrArg (fun w : Jaune.State => FootInv K (w.getStor ca) (w.bal ca))
        endpoint).mpr initial
  | some pow =>
      simp only [enabled] at endpoint
      have preserved := initial.payRewards protection pow benv.stat.number benv.stat.coinbase
        ommers (budget pow enabled)
      exact (congrArg (fun w : Jaune.State => FootInv K (w.getStor ca) (w.bal ca))
        endpoint).mpr preserved

/-- The configured pre-block bound supplies the reward budget at the actual
request stage. The footprint and protection are still the preceding stage's
inputs; earlier historical invariant preservation is not asserted here. -/
theorem footprint_after_configured_rewardStage
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {K : Key → Prop} {ca : Adr}
    (trace : ExecutionTrace.ConfiguredBlockTraceIn F cfg pre post)
    (hsg : trace.fork.ruleSet.stateGas = none)
    (initial : FootInv K (trace.bodyTrace.requestState.getStor ca)
      (trace.bodyTrace.requestState.bal ca))
    (protection : Blanc.State.Protected trace.bodyTrace.requestState ca) :
    FootInv K (post.state.getStor ca) (post.state.bal ca) := by
  rw [show post.state = trace.bodyState from congrArg BlockChain.state trace.postEq]
  exact footprint_after_rewardStage trace.bodyTrace initial protection
    (fun pow enabled => trace.request_reward_budget hsg pow enabled)

end Blanc.Lift.Weth9
