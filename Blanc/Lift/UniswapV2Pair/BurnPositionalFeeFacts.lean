import Blanc.Lift.UniswapV2Pair.BurnPositionalLPFacts
import Blanc.Lift.UniswapV2Pair.PairFeeSourceKeys

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnThreeCalls.sourceFee {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (current : Checkpoint) : FeeResult :=
  feeBranchSourceFee {current.state with unlocked := 0} r.initial.second.returned.sevm
    (feeKLastWorld r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (Bytes.toB256 (r.fee.out.take 32)) (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)

def BurnThreeCalls.sourceFeeKeys {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (K : WriterKey → Prop) (current : Checkpoint) : WriterKey → Prop :=
  feeBranchSourceKeys K {current.state with unlocked := 0} r.initial.second.returned.sevm
    (feeKLastWorld r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (Bytes.toB256 (r.fee.out.take 32)) (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)

def BurnThreeCalls.feeFresh {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnThreeCalls root sevm b) (K : WriterKey → Prop) (current : Checkpoint) : Prop :=
  FeeMintFresh K {current.state with unlocked := 0} r.initial.second.returned.sevm
    (feeKLastWorld r.initial.second.returned.sevm r.fee.occurrence.call.returned.devm)
    (Bytes.toB256 (r.fee.out.take 32)) (burnInitialReserve0 sevm b) (burnInitialReserve1 sevm b)

/-- The same fee result represents the retained actual pricing node. -/
theorem BurnFourCalls.pricingRep {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : r.three.feeFresh K current) :
    WriterRep (r.three.sourceFeeKeys K current)
      (r.pricing.devm.getStor r.three.fee.occurrence.call.returned.sevm.currentTarget)
      (r.three.sourceFee current).state := by
  obtain ⟨gas, state, result⟩ := r.fee_source_result rep fresh
  have env : r.three.fee.occurrence.call.returned.sevm = r.three.initial.second.returned.sevm :=
    (Cursor.parentStep_sevm r.three.fee.occurrence.call.edge).trans r.three.fee.occurrence.sevm_eq
  rw [env, state]
  exact result.2.1

/-- The original tracked Pair balance derives LP-row freshness after the same
fee branch, with no extra finite-universe obligation. -/
theorem BurnFourCalls.pricingFresh {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnFourCalls root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (fresh : r.three.feeFresh K current) (tracked : K (.balance sevm.currentTarget)) :
    WriterFreshKeys (r.three.sourceFeeKeys K current)
      (lpMintTouched r.three.fee.occurrence.call.returned.sevm.currentTarget) := by
  have represented := r.pricingRep rep fresh
  have env : r.three.fee.occurrence.call.returned.sevm = sevm :=
    ((Cursor.parentStep_sevm r.three.fee.occurrence.call.edge).trans
      r.three.fee.occurrence.sevm_eq).trans
        ((Cursor.parentStep_sevm r.three.initial.second.edge).trans r.three.initial.second_sevm)
  have selected : r.three.sourceFeeKeys K current
      (.balance r.three.fee.occurrence.call.returned.sevm.currentTarget) := by
    rw [env]
    exact feeBranchSourceKeys_contains tracked
  apply Blanc.SlotFootprint.FreshKeys.of_universe represented.inj represented.apart (fun _ h => h)
  intro key member
  have same := List.mem_singleton.mp (show key ∈ [WriterKey.balance
    r.three.fee.occurrence.call.returned.sevm.currentTarget] from member)
  subst key
  exact selected

end Blanc.Lift.UniswapV2Pair
