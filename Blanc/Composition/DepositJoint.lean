import Blanc.Composition.DepositRequests
import Blanc.Composition.DepositLedgerFate

/-! Positional execution/consensus deposit joins and the original request seam controls. -/
namespace Blanc.Composition.DepositJoint

open Jaune JauneConsensus Blanc Blanc.ExecutionTrace
open Blanc.Corpus.Freeze.Deposit

/-- A successful joint step cannot accept requests different from its own executed body. -/
theorem deliveryControl : D9DeliveryControl := by
  intro P cfg ccfg bls s b req f st bout converted resolved executed different post accepted
  obtain ⟨_, actualReq, actualConverted, engine⟩ := Blanc.jointStep_engine accepted
  obtain rfl : actualReq = req := Except.ok.inj (actualConverted.symm.trans converted)
  obtain ⟨_, _, _, _, actualFork, actualResolved, _, _, _, actualState, actualOutput,
    actualExecuted, requests⟩ := engineVerdict_ok_iff.mp engine
  obtain rfl : actualFork = f := Except.ok.inj (actualResolved.symm.trans resolved)
  have same : (actualState, actualOutput) = (st, bout) :=
    Except.ok.inj (actualExecuted.symm.trans executed)
  cases same
  exact different requests

end Blanc.Composition.DepositJoint
