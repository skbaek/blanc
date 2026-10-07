import Blanc.Lift.Weth9.ClosedSigningData
import Blanc.Lift.Weth9.Creation.Deploy
import Blanc.DeploymentMessage

/-!
Finite synthetic funding for the closed WETH9 applicability witness. The
protocol addresses contain the common STOP fixture, rather than mainnet's
system contracts. The configured block still executes every required system
message. No WETH code, storage, or balances are installed here.
-/

namespace Blanc.Lift.Weth9.ClosedInstance

open Jaune Blanc

/-- Compiled nonempty STOP fixture at the four required system addresses. -/
def systemCode : ByteArray := ⟨#[0x5b, 0]⟩

def systemWorld : Jaune.State :=
  (((Jaune.State.setCode (.empty : Jaune.State) beaconRootsAddress systemCode).setCode
    historyStorageAddress systemCode).setCode withdrawalRequestPredeployAddress
    systemCode).setCode consolidationRequestPredeployAddress systemCode

def holderAccount : Acct := { Acct.nil with bal := 1000000 }
def deployerAccount : Acct := { Acct.nil with bal := 1, nonce := 446 }

/-- The only funded accounts are the holder and the recorded deployer. -/
def initialWorld : Jaune.State :=
  (systemWorld.set senderE holderAccount).set Creation.deployer deployerAccount

theorem systemCode_compile : some systemCode.toList =
    Prog.compile deploymentSystemProgram := by decide +kernel

theorem systemWorld_bal (a : Adr) : (systemWorld.get a).bal = 0 := by
  unfold systemWorld
  rw [State.setCode_get_bal, State.setCode_get_bal, State.setCode_get_bal,
    State.setCode_get_bal]
  rfl

theorem systemWorld_stor (a : Adr) : (systemWorld.get a).stor = .empty := by
  unfold systemWorld
  rw [State.setCode_get_stor, State.setCode_get_stor, State.setCode_get_stor,
    State.setCode_get_stor]
  rfl

theorem initialWorld_canonical : initialWorld.Canonical :=
  (((((State.canonical_empty.setCode beaconRootsAddress systemCode).setCode
    historyStorageAddress systemCode).setCode withdrawalRequestPredeployAddress
    systemCode).setCode consolidationRequestPredeployAddress systemCode).set
    senderE (ac := holderAccount) Acct.canonical_nil_stor).set Creation.deployer
    (ac := deployerAccount) Acct.canonical_nil_stor

theorem initialWorld_holder : initialWorld.get senderE = holderAccount := by
  unfold initialWorld
  rw [State.get_set_ne _ (by decide +kernel), State.get_set_self]

theorem initialWorld_deployer : initialWorld.get Creation.deployer = deployerAccount :=
  State.get_set_self ..

theorem initialWorld_weth_empty : initialWorld.get contractAddress = Acct.nil := by
  decide +kernel

theorem initialWorld_stor (a : Adr) : (initialWorld.get a).stor = .empty := by
  unfold initialWorld
  by_cases hd : Creation.deployer = a
  · subst a
    rw [State.get_set_self]
    rfl
  · rw [State.get_set_ne _ hd]
    by_cases he : senderE = a
    · subst a
      rw [State.get_set_self]
      rfl
    · rw [State.get_set_ne _ he, systemWorld_stor]

theorem initialWorld_bal (a : Adr) : initialWorld.bal a =
    if a = Creation.deployer then 1 else if a = senderE then 1000000 else 0 := by
  change (initialWorld.get a).bal = _
  unfold initialWorld
  by_cases hd : a = Creation.deployer
  · subst a
    rw [State.get_set_self, ite_eq_left rfl]
    rfl
  · rw [State.get_set_ne _ (Ne.symm hd), ite_eq_right hd]
    by_cases he : a = senderE
    · subst a
      rw [State.get_set_self, ite_eq_left rfl]
      rfl
    · rw [State.get_set_ne _ (Ne.symm he), ite_eq_right he, systemWorld_bal]

def holderFunding (a : Adr) : B256 := if a = senderE then 1000000 else 0

theorem holderFunding_sum : sum holderFunding = 1000000 := by
  have total := sum_eq_add_of_row_add (f := fun _ => (0 : B256))
    (g := holderFunding) (x := senderE) (m := 1000000)
    (by change (if senderE = senderE then (1000000 : B256) else 0).toNat = _
        rw [ite_eq_left rfl]; decide +kernel)
    (fun a ha => by unfold holderFunding; rw [ite_eq_right ha])
  have zero : sum (fun _ => (0 : B256)) = 0 := sumBelow_zero _
  rw [zero, Nat.zero_add] at total
  exact total

theorem initialWorld_sum : sum initialWorld.bal = 1000001 := by
  have total := sum_eq_add_of_row_add (f := holderFunding)
    (g := initialWorld.bal) (x := Creation.deployer) (m := 1)
    (by rw [initialWorld_bal, ite_eq_left rfl]
        unfold holderFunding
        rw [ite_eq_right (by decide +kernel)]
        decide +kernel)
    (fun a ha => by rw [initialWorld_bal, ite_eq_right ha]; rfl)
  rw [holderFunding_sum] at total
  exact total

theorem initialWorld_sumNof : SumNof initialWorld.bal := by
  unfold SumNof
  rw [initialWorld_sum]
  decide +kernel

/-- The recorded creation input in the funded world, under BPO2. -/
def creationMessage : Msg :=
  { Creation.deployMsg with benv :=
      { (default : Benv) with state := initialWorld, stat :=
          { (default : BenvStat) with fork := .bpo2, chainId := 1, origState := initialWorld } } }

theorem creation_target : creationMessage.currentTarget =
    computeContractAddress creationMessage.caller
      (initialWorld.getNonce creationMessage.caller) := by
  change Creation.weth9Address = computeContractAddress Creation.deployer
    (initialWorld.get Creation.deployer).nonce
  rw [initialWorld_deployer]
  exact Creation.weth9Address_eq

end Blanc.Lift.Weth9.ClosedInstance
