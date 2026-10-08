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

abbrev PairAdmittedChildConsumes := AdmittedChildConsumes LockedAuth

abbrev PairAdmittedMutableTurns := AdmittedMutableTurns LockedAuth

theorem PairAdmittedConsumes.positional {root : Exec.Deriv} {segment : SegmentResult}
    {transcript : Transcript} {out : RunResult}
    (admitted : PairAdmittedConsumes root segment transcript out) :
    PairRootedConsumes root segment transcript out := admitted.choose

theorem admittedMutableTurnRules :
    MutableTurnRules PairAdmittedChildConsumes PairAdmittedMutableTurns :=
  sourceAdmittedMutableTurnRules LockedAuth

theorem admittedMutableTurns_done (frame : Frame) (request : Request) (turn : Nat) :
    PairAdmittedMutableTurns frame request turn [] .done
      {complete := true, frame := frame, childReturns := []} :=
  sourceAdmittedMutableTurns_done LockedAuth frame request turn

end Blanc.Lift.UniswapV2Pair
