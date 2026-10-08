import Blanc.Lift.UniswapV2Pair.BurnPositionalFacts
import Blanc.Lift.CursorSourceRun

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Liquidity sampling preserves the same incoming locked finite state. -/
theorem BurnThreeCalls.fee_before_rep {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnThreeCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    WriterRep K
      ((feeBurnWorld r.initial.second.returned.sevm r.initial.second.returned.devm).getStor
        r.initial.second.returned.sevm.currentTarget) {current.state with unlocked := 0} := by
  have env : r.initial.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.initial.second.edge).trans r.initial.second_sevm
  rw [env, feeBurnWorld, afterSload_getStor]
  exact r.initial.fee_entry_rep rep

/-- The same physical factory reply supplies the represented kLast branch input. -/
theorem BurnThreeCalls.fee_branch_rep {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnThreeCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    WriterRep K
      ((feeKLastWorld r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm).getStor
        r.initial.second.returned.sevm.currentTarget) {current.state with unlocked := 0} := by
  exact (r.fee_before_rep rep).fee_factory_post r.fee.reply

/-- The retained branch's kLast read is fixed by that same incoming representation. -/
theorem BurnThreeCalls.fee_last_word {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnThreeCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    feeKLastWord r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm =
      current.state.kLast := by
  rcases (r.fee_branch_rep rep).fixed with ⟨_, _, _, _, _, _, _, _, _, _, last, _⟩
  rw [feeKLastWorld, afterSload_getStor] at last
  exact last

/-- The actual pricing node is the finite fee result of this same physical reply. -/
theorem BurnFourCalls.fee_source_result {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : FeeMintFresh K {current.state with unlocked := 0}
      r.three.initial.second.returned.sevm
      (feeKLastWorld r.three.initial.second.returned.sevm r.three.fee.occurrence.call.returned.devm)
      (Bytes.toB256 (r.three.fee.out.take 32))
      (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)) :
    ∃ gas,
      r.pricing.devm = feeBranchPost r.three.initial.second.returned.sevm
        (feeKLastWorld r.three.initial.second.returned.sevm r.three.fee.occurrence.call.returned.devm)
        r.three.feeReturnLocals
        (feeReplyMemory
          (feeBurnMemory (burnInitialReplyMemory sevm r.three.initial.out0 r.three.initial.out1)
            r.three.initial.second.returned.sevm.currentTarget) r.three.fee.out)
        current.state.kLast (Bytes.toB256 (r.three.fee.out.take 32))
        (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b) gas ∧
      FeeMintSourceResult K {current.state with unlocked := 0} r.three.initial.second.returned.sevm
        (feeKLastWorld r.three.initial.second.returned.sevm r.three.fee.occurrence.call.returned.devm)
        r.three.feeReturnLocals
        (feeReplyMemory
          (feeBurnMemory (burnInitialReplyMemory sevm r.three.initial.out0 r.three.initial.out1)
            r.three.initial.second.returned.sevm.currentTarget) r.three.fee.out)
        (Bytes.toB256 (r.three.fee.out.take 32))
        (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b) gas := by
  obtain ⟨cache0, cache1, _, _, _⟩ := r.three.initial.cache_targets rep
  have bound0 : (burnInitialReserve0 sevm b).toNat < 2 ^ 112 := by
    rw [cache0, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
    exact current.state.reserve0.isLt
  have bound1 : (burnInitialReserve1 sevm b).toNat < 2 ^ 112 := by
    rw [cache1, B256.toNat_toB256_of_lt
      (lt_trans current.state.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))]
    exact current.state.reserve1.isLt
  have last := r.three.fee_last_word rep
  have guards := r.pricing_data.guards
  rw [last] at guards
  obtain ⟨gas, state⟩ := r.pricing_data.state
  rw [last] at state
  exact ⟨gas, state,
    feeBranch_source_result (r.three.fee_branch_rep rep) bound0 bound1 guards fresh⟩

end Blanc.Lift.UniswapV2Pair
