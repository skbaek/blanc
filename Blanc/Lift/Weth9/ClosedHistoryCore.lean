import Blanc.Lift.Weth9.ClosedBody
import Blanc.ExecutionTraceSettledFrames

/-! Retained traces of the exact one-deposit configured block. The record
keeps its concrete block and body projections explicit for later footprint
and committed-invocation proofs. -/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc Blanc.ExecutionTrace

noncomputable def retainedDepositBody {st post : Jaune.State} {bout : BlockOutput}
    (body : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    AppliedBodyTrace (input st) [Sum.inr depositTx] [] post bout :=
  Classical.choice (exists_appliedBodyTrace body CoveredFork.bpo2)

noncomputable def retainedDepositBlock {st post : Jaune.State} {bout : BlockOutput}
    (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    ConfiguredBlockTrace config (checkpoint st) (depositChain st post bout) where
  block := depositBlock st post bout
  bound := by
    change sum st.bal + 0 < 2 ^ 256
    rw [Nat.add_zero]
    exact bound
  fork := .bpo2
  forkAt := config_forkAt _
  rules := Fork.bpo2.ruleSet
  rulesEq := rfl
  rulesAt := by
    unfold ChainConfig.rulesAt
    rw [config_forkAt]
    rfl
  covered := CoveredFork.bpo2
  transition := depositBlock_transition gas body
  bodyState := post
  blockOutput := bout
  bodyRun := body
  bodyTrace := retainedDepositBody body
  postEq := rfl

noncomputable def retainedDepositHistory {st post : Jaune.State} {bout : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    ConfiguredHistoryTrace config (checkpoint st) (depositChain st post bout) :=
  depositHistory canonical (retainedDepositBlock bound gas body)

theorem retainedDepositBlock_transactions {st post : Jaune.State} {bout : BlockOutput}
    (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    (retainedDepositBlock bound gas body).block.txs = [Sum.inr depositTx] := rfl

theorem retainedDepositHistory_rawFrames {st post : Jaune.State} {bout : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    (retainedDepositHistory canonical bound gas body).rawFrames =
      (retainedDepositBody body).rawFrames := rfl

theorem retainedDepositHistory_settledFrames {st post : Jaune.State} {bout : BlockOutput}
    (canonical : st.Canonical) (bound : SumNof st.bal) (gas : bout.blockGasUsed ≤ 1000000)
    (body : applyBody (input st) [Sum.inr depositTx] [] = .ok (post, bout)) :
    (retainedDepositHistory canonical bound gas body).settledFrames =
      (retainedDepositBody body).settledFrames := rfl

end Blanc.Lift.Weth9.ClosedInstance
