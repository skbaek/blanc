import Blanc.Lift.FreePtrMem
import Blanc.Lift.Sound

namespace Blanc.Lift.FreePtr

open Jaune AbstractStackSafety

/-- A good free-pointer value. -/
def FpGood (w : B256) : Prop := fpLo ≤ w.toNat ∧ w.toNat ≤ fpCap

/-- What a step observes: an `MLOAD` of offset `0x40` reads a good free pointer. -/
def FpObs (d : Devm) (n : Ninst) : Prop :=
  n = .reg .mload → d.stack.head? = some 64 → FpGood (memWord d.memory 64)

/-- A step relation that also records the free-pointer observation. -/
def FpStep (P : Sevm → Devm → Ninst → Devm → Prop) : Sevm → Devm → Ninst → Devm → Prop :=
  fun s d n d' => P s d n d' ∧ FpObs d n

end Blanc.Lift.FreePtr
