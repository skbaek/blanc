import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.World
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Creation.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Clone.Check

/-! # V− setup, messages 1–2: implementation and synthetic clone creation

From any world in which the implementation and clone addresses are absent, the preserved
implementation creation input and then, from exactly its settled world, the synthetic clone
creation input both succeed on every covered fork with exact finite gas. The final world has the
registered runtime with `fee := 31337` at `implAddr`, the forwarder to it with empty storage at
`proxyAddr`, and every other account of the starting world unchanged; it is also stated as the
explicit term `setupState W`, which a following message evaluates as its block-original state. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach

open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach (creator creatorFunds initialWorld rootBenv rootTenv)

open Jaune Blanc.Lift

/-- The implementation account once created from absence. -/
def implAccount : Acct where
  nonce := 1
  bal := 0
  stor := Stor.empty.set 10 31337
  code := Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code

/-- The clone account once created from absence. -/
def proxyAccount : Acct where
  nonce := 1
  bal := 0
  stor := Stor.empty
  code := Blanc.forwarderCode Blanc.curvePlainImpl6326

/-- The settled world after message 1, as a term of the starting world. -/
def implState (W : State) : State :=
  ((CreateEntry.entryState W creator implAddr).setStorVal implAddr 10 31337).setCode implAddr
    Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.code

/-- The settled world after messages 1 and 2, as a term of the starting world. -/
def setupState (W : State) : State :=
  (CreateEntry.entryState (implState W) creator proxyAddr).setCode proxyAddr
    (Blanc.forwarderCode Blanc.curvePlainImpl6326)

theorem implAddr_ne_proxyAddr : implAddr ≠ proxyAddr := by decide

theorem implSstoreGas_fresh (fork : Fork) (W : State) (hI : W.get implAddr = .nil) :
    Creation.implSstoreGas (implCreateMsg fork W) = 22100 := by
  unfold Creation.implSstoreGas
  have hcold : ((implCreateMsg fork W).currentTarget, (10 : B256)) ∉
      (implCreateMsg fork W).accessedStorageKeys := Std.HashSet.not_mem_emptyWithCapacity
  rw [if_neg hcold]
  change gasColdSload + sstoreValueCost ((W.get implAddr).stor.get 10) 0 31337 = 22100
  rw [hI]
  rfl

/-- **Messages 1 and 2 compose.** The clone message's input world is exactly the
implementation message's settled world. -/
theorem setup_creations (fork : Fork) (hfork : CoveredFork fork) (W : State)
    (hI : W.get implAddr = .nil) (hP : W.get proxyAddr = .nil) :
    ∃ postI postP : Devm,
      processCreateMessage (implCreateMsg fork W) = .ok postI ∧ postI.error = none ∧
      postI.gasLeft = 466978 ∧
      postI.state.get implAddr = implAccount ∧
      (∀ a, a ≠ implAddr → postI.state.get a = W.get a) ∧
      postI.state = implState W ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧
      postP.error = none ∧ postP.gasLeft = 90972 ∧
      postP.state.get implAddr = implAccount ∧
      postP.state.get proxyAddr = proxyAccount ∧
      (∀ a, a ≠ implAddr → a ≠ proxyAddr → postP.state.get a = W.get a) ∧
      postP.state = setupState W := by
  obtain ⟨postI, hI1, eI, gI, aI, fI, sI⟩ :=
    Creation.create_impl (implCreateMsg fork W) hfork rfl rfl rfl rfl rfl
      (by change 3533022 ≤ 4000000; decide)
  obtain ⟨postP, hP1, eP, gP, aP, fP, sP⟩ :=
    Clone1167.create Blanc.curvePlainImpl6326 rfl Clone.cert_check
      (cloneCreateMsg fork postI.state) hfork rfl rfl rfl rfl (by change 9028 ≤ 100000; decide)
  change postI.state.get implAddr = Creation.implAcct W implAddr at aI
  change ∀ a, a ≠ implAddr → postI.state.get a = W.get a at fI
  change postP.state.get proxyAddr = Clone1167.cloneAcct _ postI.state proxyAddr at aP
  change ∀ a, a ≠ proxyAddr → postP.state.get a = postI.state.get a at fP
  change postI.gasLeft = 4000000 - (3922 + Creation.implSstoreGas (implCreateMsg fork W)) -
    3507000 at gI
  change postP.gasLeft = 100000 - 28 - 9000 at gP
  have hIacct : postI.state.get implAddr = implAccount := by
    rw [aI]
    unfold Creation.implAcct
    rw [hI]
    rfl
  have hsI : postI.state = implState W := sI
  refine ⟨postI, postP, hI1, eI, ?_, hIacct, fI, hsI, hP1, eP, gP, ?_, ?_, ?_, ?_⟩
  · rw [gI, implSstoreGas_fresh fork W hI]
  · rw [fP implAddr implAddr_ne_proxyAddr, hIacct]
  · rw [aP]
    unfold Clone1167.cloneAcct
    rw [fI proxyAddr (Ne.symm implAddr_ne_proxyAddr), hP]
    rfl
  · intro a haI haP
    rw [fP a haP, fI a haI]
  · rw [sP]
    change (CreateEntry.entryState postI.state creator proxyAddr).setCode proxyAddr _ = _
    rw [hsI]
    rfl

/-- The disclosed starting world satisfies the creation premises. -/
theorem initialWorld_absent :
    initialWorld.get implAddr = .nil ∧ initialWorld.get proxyAddr = .nil := by
  constructor <;> decide +kernel

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach
