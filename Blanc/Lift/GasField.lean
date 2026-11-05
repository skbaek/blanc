import Blanc.Lift.ExactWalkOps

/-!
# Frame gas-field independence

Storage charges, storage updates and calldata words do not depend on the
static frame's initial gas field. These identities are shared by actual
call-frame proofs from different contract families.
-/

namespace Blanc.Lift.GasField

open Jaune Blanc Blanc.Lift

variable (s : Sevm) (f : Nat)

theorem sloadCost_gasField (b : Devm) (k : B256) :
    sloadCost { s with gas := f } b k = sloadCost s b k := rfl

theorem sstoreCost_gasField (b : Devm) (k v : B256) :
    sstoreCost { s with gas := f } b k v = sstoreCost s b k v := rfl

theorem afterSload_gasField (b : Devm) (k : B256) :
    afterSload { s with gas := f } b k = afterSload s b k := rfl

theorem afterSstore_gasField (b : Devm) (k v : B256) :
    afterSstore { s with gas := f } b k v = afterSstore s b k v := rfl

theorem dataWord_gasField (i : B256) : Sevm.dataWord { s with gas := f } i = Sevm.dataWord s i :=
  rfl

end Blanc.Lift.GasField
