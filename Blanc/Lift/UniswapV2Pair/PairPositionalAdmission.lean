import Blanc.Lift.UniswapV2Pair.PairPositionalEntry
import Blanc.Lift.UniswapV2Pair.AdmittedMutableFold
import Blanc.Lift.UniswapV2Pair.SourceAdmission
import Blanc.Lift.UniswapV2Pair.LockedSupply

namespace Blanc.Lift.UniswapV2Pair

open Jaune

abbrev PairSourceAdmission {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (selected : PositionalConsumes root start index segment transcript out) :=
  SourceAdmission LockedAuth selected

abbrev PairMutableAdmission {frame : Frame} {request : Request} {turn : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)} {transcript : Transcript} {out : TurnsResult}
    (selected : PositionalMutableTurns frame request turn events transcript out) :=
  MutableAdmission LockedAuth selected

/-- The stronger endpoint retains admission on the same rooted consumption proof. -/
def PairAdmittedConsumes (root : Exec.Deriv) (segment : SegmentResult)
    (transcript : Transcript) (out : RunResult) : Prop :=
  ∃ selected : PositionalConsumes root root 0 segment transcript out,
    PairSourceAdmission selected

def PairAdmittedOutcome (U : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (K : WriterKey → Prop) (root : Exec.Deriv) (post : Devm) : Prop :=
  PairStepOutcomeWith PairAdmittedConsumes PairEntryAuth U current invocation K root post

def PairAdmittedSupply (U : WriterKey → Prop) (selected : Sevm → Prop) : Prop :=
  PairStepSupplyWith PairAdmittedConsumes PairEntryAuth U selected

abbrev PairAdmittedChildConsumes := AdmittedChildConsumes LockedAuth

abbrev PairAdmittedMutableTurns := AdmittedMutableTurns LockedAuth

theorem PairAdmittedConsumes.positional {root : Exec.Deriv} {segment : SegmentResult}
    {transcript : Transcript} {out : RunResult}
    (admitted : PairAdmittedConsumes root segment transcript out) :
    PairRootedConsumes root segment transcript out := admitted.choose

theorem PairAdmittedOutcome.positional {U : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {K : WriterKey → Prop} {root : Exec.Deriv} {post : Devm}
    (outcome : PairAdmittedOutcome U current invocation K root post) :
    PairPositionalOutcome U current invocation K root post :=
  PairStepOutcomeWith.mono (fun _ _ _ consumed => consumed.positional)
    (fun _ _ authentic => authentic) outcome

theorem PairAdmittedSupply.positional {U : WriterKey → Prop} {selected : Sevm → Prop}
    (supply : PairAdmittedSupply U selected) : PairPositionalSupply U selected := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput
    representable selector good sub rep
  exact PairAdmittedOutcome.positional
    (supply current invocation run (K := K) codeEq installed fork freshOutput
      representable selector good sub rep)

theorem admittedMutableTurnRules :
    MutableTurnRules PairAdmittedChildConsumes PairAdmittedMutableTurns :=
  sourceAdmittedMutableTurnRules LockedAuth

theorem admittedMutableTurns_done (frame : Frame) (request : Request) (turn : Nat) :
    PairAdmittedMutableTurns frame request turn [] .done
      {complete := true, frame := frame, childReturns := []} :=
  sourceAdmittedMutableTurns_done LockedAuth frame request turn

end Blanc.Lift.UniswapV2Pair
