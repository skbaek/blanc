import Blanc.Lift.CodeSizeWalk

namespace Blanc.Lift

open Jaune

/-- Account warming preserves storage at every address. -/
theorem temporalAccountAccessBase_getStor (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getStor x = base.getStor x := by
  simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]

/-- Account warming preserves code at every address. -/
theorem temporalAccountAccessBase_getCode (base : Devm) (a x : Adr) :
    (temporalAccountAccessBase base a).getCode x = base.getCode x := by
  simp only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state]

end Blanc.Lift
