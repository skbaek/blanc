import Blanc.Lift.InvWalkOps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkDispatch
import Blanc.Lift.ReachDispatch
import Blanc.Lift.ExactWalkSolc
import Blanc.AddressSlotProofs
import Blanc.Lift.Deploy
import Blanc.Lift.InvWalkStep
import Jaune.WordFacts
import Blanc.Lift.WalkInvKit

/-!
# Cut-run walk kit for certificate-driven inversions

Contract-neutral steps for inverting a lifted run (`SFunc.RunCut … []`, i.e. `SFunc.RunP` through
`SFunc.runP_iff_runCutP_nil`) and a prefix reach (`Reach`) node by node over a checked certificate:

* terminals (`ric_stop`, `ric_return`) and internal calls into a callee that cannot halt
  (`ric_callRet`, from a `NoHaltSet`);
* a solc dispatcher's comparison rows with the branch decided by a closed comparison
  (`ric_gt_le`/`ric_gt_gt`/`ric_eq_miss`/`ric_eq_hit`, and the `rr_*` reach forms);
* storage projections of the walk bases (`afterSload`, `afterSstore`, `addLog`, `St`);
* the reuse by solc's mapping hash of the key word left by the previous hash (`keccak_scratch2`;
  from `Mem.read_after_right_write`; the fresh hash is `InvWalkStep.lean`'s `keccak_scratch`).
-/

namespace Blanc.Lift

open Jaune Blanc

section Kit

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

end Kit

section ReachKit

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf} {f g : SFunc}

end ReachKit

theorem getStorVal_eq (d : Devm) (a : Adr) (k : B256) : d.getStorVal a k = (d.getStor a).get k := rfl


end Blanc.Lift
