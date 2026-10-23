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

/-- `PairAdmittedConsumes` with every re-entered Pair frame authenticated by `LockedAuthH`
(the permit by `PermitRecoveryAuthH`), as the historical rule facts supply. -/
def PairAdmittedConsumesH (root : Exec.Deriv) (segment : SegmentResult)
    (transcript : Transcript) (out : RunResult) : Prop :=
  ∃ selected : PositionalConsumes root root 0 segment transcript out,
    SourceAdmission LockedAuthH selected

/-- Under the root's covered fork every admitted frame runs at a covered fork, where `LockedAuthH`
is `LockedAuth`. -/
theorem PairAdmittedConsumesH.covered {root : Exec.Deriv} {segment : SegmentResult}
    {transcript : Transcript} {out : RunResult} (fork : CoveredFork root.sevm.benvStat.fork)
    (admitted : PairAdmittedConsumesH root segment transcript out) :
    PairAdmittedConsumes root segment transcript out :=
  ⟨admitted.1, SourceAdmission.mono_benvStat (P := fun stat => CoveredFork stat.fork)
    (fun _ _ _ covered auth => auth.toCovered covered) fork admitted.2⟩

/-- `PairAdmittedSupply` from the historical rule facts (`PairStepSupplyWithH`), with
`PairAdmittedConsumesH` consumption. -/
def PairAdmittedSupplyH (U : WriterKey → Prop) (selected : Sevm → Prop) : Prop :=
  PairStepSupplyWithH PairAdmittedConsumesH PairEntryAuth U selected

theorem PairAdmittedSupplyH.covered {U : WriterKey → Prop} {selected : Sevm → Prop}
    (supply : PairAdmittedSupplyH U selected) : PairAdmittedSupply U selected := by
  intro current invocation sevm b post G run K codeEq installed fork freshOutput representable
    chosen good sub rep
  exact PairStepOutcomeWith.mono (fun _ _ _ consumed => consumed.covered fork)
    (fun _ _ authentic => authentic)
    (PairStepSupplyWithH.covered supply current invocation run codeEq installed fork freshOutput
      representable chosen good sub rep)

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

end Blanc.Lift.UniswapV2Pair
