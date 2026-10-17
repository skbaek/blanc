import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.ExecutionAccountingPositionalHistory

/-!
# The Pair's model state at every unlocked position

`pair_history_stateAt`: in a configured history from a checkpoint whose Pair storage represents the
model state `st₀`, at the entry of every settled frame not enclosed by an earlier non-static Pair
frame (the positions where the Pair is unlocked), the Pair storage represents the model state that
the observed Pair steps of exactly the settled frames before it replay to.  The proof is the
positional Pair ladder (`wholeFramePositionalLadder` over `pairCarrierWith`, the arguments of
`pairLadderWith`) read through `PositionalLadder.configuredHistory_at`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- **The positional accounting ladder of the Pair** over a separated universe `U`: the arguments
of `pairLadderWith`, positional outside the Pair's own non-static frames. -/
noncomputable def pairPositionalLadderWith
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop} (pair : Adr) {U : WriterKey → Prop}
    (supply : PairStepSupplyWith Consumes Auth U (fun _ => True)) :
    PositionalLadder (pairSpec U) pair (pairEntry U) :=
  wholeFramePositionalLadder (c := pairSpec U) (pairCarrierWith Consumes Auth pair U)
    (pairObservationWith Consumes Auth pair U)
    PairReplayWith.append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => funext h) (fun _ h => pairFrameObs_static h)
    (fun _ h => pairFrameObs_foreign h) (pair_spawnKinds pair)
    (pair_wholeFrameReplayWith pair supply) (pairSpec_preservesAdmittedWith pair supply)

/-- **The Pair's model state at every settled frame outside its own frames** (positional Pair
ladder, `wholeFramePositionalLadder` over `pairCarrierWith`). -/
theorem pair_history_stateAt {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      trace.settledFrames = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ (A.sevm.currentTarget = pair ∧ A.sevm.isStatic = false)) →
      ∃ (steps : List PairStep) (st : State) (K : WriterKey → Prop),
        steps.flatMap (fun s => pairSubtreeFrames pair s.frame) =
          before.flatMap (pairFrameObs pair) ∧
        PairObservedReplayWith PairAdmittedConsumes st₀ steps st ∧
        WriterRep K (f.pre.state.getStor pair) st := by
  intro before f after split noOpaque
  let U := WriterExtend K₀ (pairHistoryTouchedKeys pair trace)
  have extended : WriterRep U (checkpoint.state.getStor pair) st₀ := initial.extend fresh
  have admitted : trace.FrameAdmitted pair (pairEntry U) :=
    pair_trace_admitted trace (fun k row => Or.inr row)
  have start : (pairSpec U).StateInv pair checkpoint.state :=
    ⟨installed, trivial, ⟨st₀, K₀, fun _ h => Or.inl h, initial⟩⟩
  obtain ⟨frames, replay, observed⟩ :=
    (pairPositionalLadderWith pair
      (pairAdmittedSupply extended.inj extended.apart pairSem pairSem_image)).configuredHistory_at
      trace admitted start before f after split noOpaque
  change PairReplayWith PairAdmittedConsumes PairEntryAuth pair U
    (checkpoint.state.getStor pair).get frames (f.pre.state.getStor pair).get at replay
  change frames.flatMap (pairSubtreeFrames pair) = before.flatMap (pairFrameObs pair) at observed
  obtain ⟨steps, framesEq, _, st, K, source, _, _, s, view, rep⟩ :=
    replay st₀ K₀ (fun _ h => Or.inl h) ⟨_, rfl, initial⟩
  refine ⟨steps, st, K, ?_, source, WriterRep.congr (fun k => (congrFun view k).symm) rep⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

end Blanc.Lift.UniswapV2Pair
