import Blanc.Lift.UniswapV2Pair.BurnPositionalSeven

/-! Incoming storage bindings for the same seven original Burn positions. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The retained first static reply preserves this entry's locked storage. -/
theorem BurnInitialPair.first_storage {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnInitialPair root sevm b) (a : Adr) :
    r.first.returned.devm.getStor a = (burnLockedWorld sevm b).getStor a := by
  rw [r.first_reply.stor]
  simp only [burnInitialWorld0, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
  change (burnTokensWorld sevm (burnInitialReserveWorld sevm b)).getStor a = _
  rw [burnTokensWorld, afterSload_getStor, afterSload_getStor,
    burnInitialReserveWorld, afterSload_getStor]
  rfl

/-- The second retained static reply advances the same full returned world. -/
theorem BurnInitialPair.second_storage {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnInitialPair root sevm b) (a : Adr) :
    r.second.returned.devm.getStor a = (burnLockedWorld sevm b).getStor a := by
  rw [r.second_reply.stor]
  simpa only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    using r.first_storage a

/-- Finite incoming storage is transported through these two actual slots. -/
theorem BurnInitialPair.fee_entry_rep {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnInitialPair root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state) :
    WriterRep K (r.second.returned.devm.getStor sevm.currentTarget)
      { current.state with unlocked := 0 } := by
  rw [r.second_storage]
  exact rep.burn_locked_world

end Blanc.Lift.UniswapV2Pair
