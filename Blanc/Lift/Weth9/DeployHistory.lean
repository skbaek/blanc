import Blanc.Lift.Weth9.FootHistory
import Blanc.Lift.Weth9.Creation.DeployInit

/-!
# WETH9 from its Byzantium deployment through a historical-domain history

`weth9_history_from_byzantium_deployment` composes the recorded creation input run under
Byzantium rules (`Creation.weth9_deploy_init_byzantium`: code installed, empty footprint) with the
historical-domain footprint history (`weth9_history_footprint_universeHist`). The checkpoint is
tied to the deployment by the deployed account's code and storage; how the deployment transaction
reaches that checkpoint (inclusion in its block and the blocks after it) is not stated here, and
neither is the committed-history replay.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc
open Blanc.ExecutionTrace

/-- **WETH9 from its Byzantium deployment to a later checkpoint.**  The recorded creation input,
run as a CREATE message under Byzantium rules, succeeds with a post-state `post`; from any
checkpoint whose WETH9 account carries `post`'s code and storage and whose balances sum below the
word bound, a configured history over the historical fork domain reaches a future state with the
runtime installed, `SumNof`, and the footprint over the touched keys, given their trace-local
freshness. -/
theorem weth9_history_from_byzantium_deployment :
    ∃ post, processCreateMessage (Creation.deployMsg.withFork .byzantium) = .ok post ∧
      (post.getCode Creation.weth9Address).toList = code.toList ∧
      ∀ {cfg : ChainConfig} {checkpoint future : BlockChain}
        (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future),
        checkpoint.state.getCode Creation.weth9Address = post.getCode Creation.weth9Address →
        checkpoint.state.getStor Creation.weth9Address =
          Devm.getStor post Creation.weth9Address →
        SumNof checkpoint.state.bal →
        KeysFresh (fun _ => False) (historyTouchedKeysIn Creation.weth9Address trace) →
        some (future.state.getCode Creation.weth9Address).toList = weth9Sem.image ∧
          SumNof future.state.bal ∧
          FootInv (historyKeyUniverseIn Creation.weth9Address trace (fun _ => False))
            (future.state.getStor Creation.weth9Address)
            (future.state.bal Creation.weth9Address) := by
  obtain ⟨-, post, hpost, hcode, hfoot⟩ := Creation.weth9_deploy_init_byzantium
  refine ⟨post, hpost, hcode, ?_⟩
  intro cfg checkpoint future trace hc hs hsum fresh
  refine weth9_history_footprint_universeHist trace ?_ hsum ?_ fresh
  · show some _ = some code.toList
    rw [hc, hcode]
  · rw [hs]
    exact hfoot _

end Blanc.Lift.Weth9
