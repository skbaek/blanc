import Blanc.Lift.ExactWalk

/-! Exact ADDRESS staging over a symbolic machine world. -/

namespace Blanc.Lift

open Jaune

/-- ADDRESS pushes the current target and charges exactly the base cost. -/
theorem rx_address {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {f : SFunc} {o : Outcome}
    (room : S.length < 1024)
    (tail : SFunc.RunExact fs sevm (St b (sevm.currentTarget.toB256 :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b S M (G + 2)) (.next (.reg .address) f) o := by
  exact .next (Ninst.runCompiled_pushItem (devm := St b S M (G + 2))
    (G := G) (cost := gBase) (by rintro ⟨⟩) rfl rfl room) tail

end Blanc.Lift
