import Blanc.Lift.Weth9.Creation.Deploy
import Blanc.Lift.Weth9.Footprint

/-!
# The recorded WETH9 deployment starts the footprint history

`weth9_deploy` (`Creation/Deploy.lean`) leaves storage whose only nonzero words are the
constructor's `name`/`symbol`/`decimals` at the fixed slots `0`, `1`, `2`.  That is exactly the
premise of `FootInv.deployed` (`Footprint.lean`), so the deployment satisfies the footprint
invariant of the history theorems with the empty tracked set, whatever the contract's balance and
with no hash premise: there are no tracked keys whose slots could collide.

This is a separate module so that it does not re-elaborate `Creation/Deploy.lean`, whose
constructor-frame proof is the heavy one.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune

/-- **The same under every covered fork.**  By `weth9_deploy_covered`. -/
theorem weth9_deploy_init_covered (f : Fork) (hf : CoveredFork f) :
    weth9Address = computeContractAddress deployer 446 ∧
    ∃ post, processCreateMessage (deployMsg.withFork f) = .ok post ∧
      (post.getCode weth9Address).toList = Blanc.Lift.Weth9.code.toList ∧
      ∀ b : B256, FootInv (fun _ => False) (Devm.getStor post weth9Address) b := by
  obtain ⟨haddress, post, hpost, hcode, hstor⟩ := weth9_deploy_covered f hf
  exact ⟨haddress, post, hpost, hcode, fun b => by
    rw [hstor]
    exact FootInv.deployed deployedStor_metadata⟩

end Blanc.Lift.Weth9.Creation
