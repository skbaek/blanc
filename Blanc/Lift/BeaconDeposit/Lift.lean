import Blanc.Lift.Sound
import Blanc.Lift.BeaconDeposit.Check
import Blanc.Lift.BeaconDeposit.Prog
import Blanc.Lift.WalkKitSupport

/-!
# Every successful Jaune execution of the deployed beacon deposit runtime is a synthetic run

The deployed runtime of mainnet `0x00000000219ab540356cBB839Cbe05303d7705Fa` (`code`, 6358
bytes; SHA-256 of the bytes `5aaa8327c5765ec883224895ca02cade2871e12dad0197bdc791efc91c7ef18d`,
of Blanc's pinned hex text `scripts/reference/beacon-deposit/inputs/deployed-runtime.norm.hex`
`867e261f9811c5227ff0e2ec5d7803156f1af3428e49d6ffc041102da3050432`) with its kernel-checked
certificate (`cert_check`) instantiates the generic lifting theorem at its use sites:
`lift_sound cert_check hcode hfork exc` turns a successful execution into a run of the
synthetic program `prog`, which the contract proofs reason about.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-- The deployed checked certificate's original closed STATICCALL membership fact. -/
theorem cert_execs_staticcall :
    ∀ f ∈ cert.prog, f.execsSatisfy Xinst.isStaticcall = true := by
  intro f member
  simp only [Cert.prog, cert, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

/-- Successful actual bytecode execution, retaining its original StepIn provenance on every rule set. -/
theorem lift_sound_in_any_rules {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (executed : Exec 0 sevm pre (.ok post)) :
    SProg.RunP (StepIn ⟨0, sevm, pre, .ok post, executed⟩) prog sevm pre post := by
  apply lift_sound_inM_staticcall (allowed := Xinst.isStaticcall)
    (Cert.checkedM_of_check cert_check) _ hcode _ cert_execs_staticcall executed
  · exact ⟨_, _, _, rfl, rfl, rfl, rfl⟩
  · intro x admitted
    cases x <;> simp_all only [Xinst.isStaticcall, Bool.false_eq_true]

end Blanc.Lift.BeaconDeposit
