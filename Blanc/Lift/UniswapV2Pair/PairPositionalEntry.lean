import Blanc.Lift.UniswapV2Pair.PairSupply
import Blanc.Lift.UniswapV2Pair.SourceOccurrence

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The actual outer selector and all decoded source-entry fields.
Nested admission and call provenance must be retained by the same positional producer. -/
inductive PairEntryAt (root : Exec.Deriv) : Entry → Prop
  | transfer (selector : Blanc.Sevm.selector root.sevm = 0xa9059cbb) :
      PairEntryAt root (transferDecodedEntry root.sevm)
  | approve (selector : Blanc.Sevm.selector root.sevm = 0x095ea7b3) :
      PairEntryAt root (approveDecodedEntry root.sevm)
  | transferFrom (selector : Blanc.Sevm.selector root.sevm = 0x23b872dd) :
      PairEntryAt root (transferFromDecodedEntry root.sevm)
  | initializeEntry (selector : Blanc.Sevm.selector root.sevm = 0x485cc955) :
      PairEntryAt root (initializeDecodedEntry root.sevm)
  | permit (selector : Blanc.Sevm.selector root.sevm = 0xd505accf) :
      PairEntryAt root (permitDecodedEntry root.sevm)
  | mint (selector : Blanc.Sevm.selector root.sevm = 0x6a627842) :
      PairEntryAt root (.mint (Sevm.dataWord root.sevm 4).toAdr)
  | sync (selector : Blanc.Sevm.selector root.sevm = 0xfff6cae9) :
      PairEntryAt root .sync
  | skim (selector : Blanc.Sevm.selector root.sevm = 0xbc25cf77) :
      PairEntryAt root (.skim (skimRecipient root.sevm))
  | swap (selector : Blanc.Sevm.selector root.sevm = 0x022c0d9f) :
      PairEntryAt root (swapDecodedEntry root.sevm)
  | burn (selector : Blanc.Sevm.selector root.sevm = 0x89afcb44) :
      PairEntryAt root (.burn
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord root.sevm 4).toAdr)
  | view (view : StaticView) (selector : Blanc.Sevm.selector root.sevm = view.selector) :
      PairEntryAt root (view.entry root.sevm)

def PairEntryAuth (root : Exec.Deriv) (entry : Entry) (_ : Transcript) : Prop :=
  PairEntryAt root entry

/-- An annotation begins at the very same original root and child index zero. -/
def PairRootedConsumes (root : Exec.Deriv) (segment : SegmentResult)
    (transcript : Transcript) (result : RunResult) : Prop :=
  PositionalConsumes root root 0 segment transcript result

def PairPositionalOutcome (U : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (K : WriterKey → Prop) (root : Exec.Deriv) (post : Devm) : Prop :=
  PairStepOutcomeWith PairRootedConsumes PairEntryAuth U current invocation K root post

def PairPositionalSupply (U : WriterKey → Prop) (selected : Sevm → Prop) : Prop :=
  PairStepSupplyWith PairRootedConsumes PairEntryAuth U selected

/-- Erasure keeps this same entry, transcript, result and actual returned bytes.
It does not assert legacy family authentication with a different entry bit. -/
theorem PairPositionalOutcome.forget {U : WriterKey → Prop} {current : Checkpoint}
    {invocation : List Nat} {K : WriterKey → Prop} {root : Exec.Deriv} {post : Devm}
    (outcome : PairPositionalOutcome U current invocation K root post) :
    PairStepOutcome PairEntryAuth U current invocation K root post :=
  PairStepOutcomeWith.mono (fun _ _ _ consumed => consumed.forget)
    (fun _ _ auth => auth) outcome

end Blanc.Lift.UniswapV2Pair
