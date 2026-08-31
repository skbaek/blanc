import Blanc.ExecutionBodyAdmission
import Blanc.ExecutionHistoryEffects

/-!
# Trace-local admission through configured histories

One configured block inherits admission from its retained body.  A configured
history requires that condition pointwise, preserving the exact fork schedule
and execution traces already carried by `ConfiguredHistoryTrace`.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Admission for every interpreter execution retained by one configured
block's body. -/
def ConfiguredBlockTrace.FrameAdmitted
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  trace.bodyTrace.FrameAdmitted ca entry

/-- Pointwise admission for every configured block in a retained history. -/
def ConfiguredHistoryTrace.FrameAdmitted
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (ca : Adr) (entry : Sevm → Devm → Prop) : Prop :=
  match trace with
  | .refl _ _ _ => True
  | .step prior block =>
      prior.FrameAdmitted ca entry ∧ block.FrameAdmitted ca entry

open ContractSpec

variable {c : ContractSpec}

/-- One configured block transports an arbitrary contract invariant under the
admission carried by its exact retained body. -/
theorem ConfiguredBlockTrace.stateInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca pre.state) :
    c.StateInv ca post.state := by
  rw [trace.postState]
  exact trace.bodyTrace.stateInv_admitted preserves admitted
    trace.openingBound (trace.openingBenvInv inv)

/-- A retained configured history transports an arbitrary contract invariant
when each concrete block trace is admitted. -/
theorem ConfiguredHistoryTrace.stateInv_admitted
    {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (preserves : c.PreservesAdmitted ca entry)
    (admitted : trace.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) :
    c.StateInv ca future.state := by
  induction trace with
  | refl => exact inv
  | step prior block ih =>
      exact block.stateInv_admitted preserves admitted.2
        (ih admitted.1)

end ExecutionTrace

end Blanc
