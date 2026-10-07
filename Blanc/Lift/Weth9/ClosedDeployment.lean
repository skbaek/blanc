import Blanc.Lift.Weth9.ClosedWorld
import Jaune.Sufficiency

/-!
The actual recorded WETH9 constructor is run in the finite funded synthetic
world. `deploymentPost.state` is the state used by the checkpoint, without
copying code, storage, or balances into a separately constructed state.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc

structure DeploymentFacts (post : Devm) : Prop where
  run : processCreateMessage creationMessage = .ok post
  code : (post.getCode contractAddress).toList = Weth9.code.toList
  storage : Devm.getStor post contractAddress = Creation.deployedStor
  accounts : ∀ a, post.state.get a = if a = contractAddress then
    { initialWorld.get a with nonce := (initialWorld.get a).nonce + 1, stor := Creation.deployedStor, code := Weth9.code }
    else initialWorld.get a

theorem deployment_exists : ∃ post, DeploymentFacts post := by
  obtain ⟨post, hrun, hcode, hstorage, haccounts⟩ :=
    Creation.weth9_create_framed creationMessage rfl rfl rfl
      (by decide +kernel) (by decide +kernel) CoveredFork.bpo2 rfl
      (by decide +kernel)
  exact ⟨post, ⟨hrun, hcode, hstorage, haccounts⟩⟩

noncomputable def deploymentPost : Devm := Classical.choose deployment_exists

theorem deployment_facts : DeploymentFacts deploymentPost :=
  Classical.choose_spec deployment_exists

theorem creationMessage_canonical : creationMessage.Canonical :=
  ⟨⟨initialWorld_canonical, initialWorld_canonical⟩, Tra.canonical_empty⟩

theorem deployment_canonical : deploymentPost.state.Canonical :=
  (processCreateMessage_ok_canonical creationMessage_canonical deployment_facts.run).1

theorem deployment_account_ne (a : Adr) (h : a ≠ contractAddress) :
    deploymentPost.state.get a = initialWorld.get a := by
  rw [deployment_facts.accounts, ite_eq_right h]

theorem deployment_contract : deploymentPost.state.get contractAddress =
    { Acct.nil with nonce := 1, stor := Creation.deployedStor, code := Weth9.code } := by
  rw [deployment_facts.accounts, ite_eq_left rfl, initialWorld_weth_empty]
  rfl

theorem deployment_installed : deploymentPost.state.getCode contractAddress = Weth9.code := by
  change (deploymentPost.state.get contractAddress).code = _
  rw [deployment_contract]

theorem deployment_initial : FootInv (fun _ => False)
    (deploymentPost.state.getStor contractAddress) (deploymentPost.state.bal contractAddress) := by
  change FootInv (fun _ => False) (Devm.getStor deploymentPost contractAddress) _
  rw [deployment_facts.storage]
  exact FootInv.deployed Creation.deployedStor_metadata

theorem deployment_balances : deploymentPost.state.bal = initialWorld.bal := by
  funext a
  change (deploymentPost.state.get a).bal = (initialWorld.get a).bal
  rw [deployment_facts.accounts]
  by_cases h : a = contractAddress
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]

theorem deployment_sumNof : SumNof deploymentPost.state.bal := by
  rw [deployment_balances]
  exact initialWorld_sumNof

theorem deployment_holder : deploymentPost.state.get senderE = holderAccount := by
  rw [deployment_account_ne senderE (by decide +kernel), initialWorld_holder]

theorem deployment_deployer : deploymentPost.state.get Creation.deployer = deployerAccount := by
  rw [deployment_account_ne Creation.deployer (by decide +kernel), initialWorld_deployer]

/-- The message seed increments the newly created account's nonce; this
message-level deployment does not admit a historical deployment transaction. -/
theorem deployment_target_nonce : (deploymentPost.state.get contractAddress).nonce = 1 := by
  rw [deployment_contract]

/-- The selected protocol addresses, all outside WETH9. -/
def systemAddresses : List Adr :=
  [beaconRootsAddress, historyStorageAddress, withdrawalRequestPredeployAddress,
    consolidationRequestPredeployAddress]

def SystemCodes (st : Jaune.State) : Prop :=
  ∀ a ∈ systemAddresses, st.getCode a = systemCode

theorem systemAddresses_foreign (a : Adr) (ha : a ∈ systemAddresses) :
    a ≠ contractAddress := by
  simp only [systemAddresses, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel

theorem initialWorld_systemCodes : SystemCodes initialWorld := by
  intro a ha
  simp only [systemAddresses, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel

theorem deployment_systemCodes : SystemCodes deploymentPost.state := by
  intro a ha
  change (deploymentPost.state.get a).code = _
  rw [deployment_account_ne a (systemAddresses_foreign a ha)]
  exact initialWorld_systemCodes a ha

end Blanc.Lift.Weth9.ClosedInstance
