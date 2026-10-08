import Blanc.Lift.UniswapV2Pair.SkimPositionalSuffix
import Blanc.Lift.CursorOccurrenceRoots
import Blanc.Lift.TargetLogEvents

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem SkimFirstObservation.requestStor {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFirstObservation root b toWord R) :
    r.call.occurrence.node.devm.getStor root.sevm.currentTarget =
      (b.getStor root.sevm.currentTarget).set 12 0 := by
  rw [r.input, St, Devm.getStor, Devm.getAcct, Devm.setMach_state,
    temporalAccountAccessBase_state]
  exact skim_cached_getStor root.sevm b

theorem SkimFirstObservation.returnStor {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFirstObservation root b toWord R) :
    r.call.returned.devm.getStor root.sevm.currentTarget =
      (b.getStor root.sevm.currentTarget).set 12 0 := by
  rw [r.reply.stor, Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
  exact skim_cached_getStor root.sevm b

theorem SkimFirstObservation.requestCode {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFirstObservation root b toWord R) (a : Adr) :
    r.call.occurrence.node.devm.getCode a = b.getCode a := by
  rw [r.input, St, Devm.getCode_setMach, Devm.getCode_state, temporalAccountAccessBase_state]
  exact skim_cached_getCode root.sevm b a

theorem SkimFirstObservation.returnCode {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFirstObservation root b toWord R)
    (present : (b.getCode root.sevm.currentTarget).toList ≠ []) :
    r.call.returned.devm.getCode root.sevm.currentTarget = b.getCode root.sevm.currentTarget := by
  rw [Blanc.Lift.StepIn.codePreserve r.call.toStepIn root.sevm.currentTarget
    (by rw [r.requestCode]; exact present), r.requestCode]

theorem SkimTransferObservation.requestStor {root start : Exec.Deriv}
    {site : SkimBalanceSite} {b : Devm} {M : Mem} {p amount toWord tokenWord rho : B256}
    {R : List B256} {K : List SFunc}
    (r : SkimTransferObservation root start site b M p amount toWord tokenWord rho R K) (a : Adr) :
    r.call.occurrence.node.devm.getStor a = b.getStor a := by
  rw [r.input, St, Devm.getStor, Devm.getAcct, Devm.setMach_state]
  rfl

theorem SkimTransferObservation.requestCode {root start : Exec.Deriv}
    {site : SkimBalanceSite} {b : Devm} {M : Mem} {p amount toWord tokenWord rho : B256}
    {R : List B256} {K : List SFunc}
    (r : SkimTransferObservation root start site b M p amount toWord tokenWord rho R K) (a : Adr) :
    r.call.occurrence.node.devm.getCode a = b.getCode a := by
  rw [r.input, St, Devm.getCode_setMach]

theorem SkimTransferObservation.returnCode {root start : Exec.Deriv}
    {site : SkimBalanceSite} {b : Devm} {M : Mem} {p amount toWord tokenWord rho : B256}
    {R : List B256} {K : List SFunc}
    (r : SkimTransferObservation root start site b M p amount toWord tokenWord rho R K)
    (a : Adr) (present : (b.getCode a).toList ≠ []) :
    r.call.returned.devm.getCode a = b.getCode a := by
  rw [Blanc.Lift.StepIn.codePreserve r.call.toStepIn a (by rw [r.requestCode]; exact present), r.requestCode]

theorem SkimFourCalls.requestStor2 {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFourCalls root b toWord R) (a : Adr) :
    r.third.call.occurrence.node.devm.getStor a = r.two.transfer.call.returned.devm.getStor a := by
  rw [r.third.input, SkimTwoCalls.secondInput, St, Devm.getStor, Devm.getAcct,
    Devm.setMach_state, temporalAccountAccessBase_state]
  exact afterSload_getStor _ _ _ _

theorem SkimFourCalls.returnStor2 {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFourCalls root b toWord R) (a : Adr) :
    r.third.call.returned.devm.getStor a = r.two.transfer.call.returned.devm.getStor a := by
  rw [r.reply.reply.stor, SkimTwoCalls.secondWorld, Devm.getStor, Devm.getAcct,
    temporalAccountAccessBase_state]
  exact afterSload_getStor _ _ _ _

theorem SkimFourCalls.requestCode2 {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFourCalls root b toWord R) (a : Adr) :
    r.third.call.occurrence.node.devm.getCode a = r.two.transfer.call.returned.devm.getCode a := by
  rw [r.third.input, SkimTwoCalls.secondInput, St, Devm.getCode_setMach, Devm.getCode_state,
    temporalAccountAccessBase_state]
  exact afterSload_getCode _ _ _ _

theorem SkimFourCalls.returnCode2 {root : Exec.Deriv} {b : Devm}
    {toWord : B256} {R : List B256} (r : SkimFourCalls root b toWord R)
    (a : Adr) (present : (r.two.transfer.call.returned.devm.getCode a).toList ≠ []) :
    r.third.call.returned.devm.getCode a = r.two.transfer.call.returned.devm.getCode a := by
  rw [Blanc.Lift.StepIn.codePreserve r.third.call.toStepIn a (by rw [r.requestCode2]; exact present), r.requestCode2]

end Blanc.Lift.UniswapV2Pair
