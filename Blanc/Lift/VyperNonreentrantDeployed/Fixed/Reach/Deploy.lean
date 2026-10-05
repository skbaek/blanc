import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach.World
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Creation.Deploy
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Clone.Deploy

/-! # V+ setup, messages 1–2: implementation and synthetic clone creation

From any world in which the implementation and clone addresses are absent, the preserved
implementation creation input and then, from exactly its settled world, the synthetic clone
creation input both succeed on every covered fork with exact finite gas. The final world has the
registered runtime with `factory := 1` at `implAddr`, the forwarder to it with empty storage at
`proxyAddr`, and every other account of the starting world unchanged. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach

open Jaune Blanc.Lift

/-- The implementation account once created from absence. -/
def implAccount : Acct where
  nonce := 1
  bal := 0
  stor := Stor.empty.set 1 1
  code := Blanc.Lift.VyperNonreentrantDeployed.Fixed.code

/-- The clone account once created from absence. -/
def proxyAccount : Acct where
  nonce := 1
  bal := 0
  stor := Stor.empty
  code := Blanc.forwarderCode Blanc.curvePlainImpl847e

theorem implAddr_ne_proxyAddr : implAddr ≠ proxyAddr := by decide

theorem implSstoreGas_fresh (fork : Fork) (W : State) (hI : W.get implAddr = .nil) :
    Creation.implSstoreGas (implCreateMsg fork W) = 22100 := by
  unfold Creation.implSstoreGas
  have hcold : ((implCreateMsg fork W).currentTarget, (1 : B256)) ∉
      (implCreateMsg fork W).accessedStorageKeys := Std.HashSet.not_mem_emptyWithCapacity
  rw [if_neg hcold]
  change gasColdSload + sstoreValueCost ((W.get implAddr).stor.get 1) 0 1 = 22100
  rw [hI]
  rfl

/-- **Messages 1 and 2 compose.** The clone message's input world is exactly the
implementation message's settled world. -/
theorem setup_creations (fork : Fork) (hfork : CoveredFork fork) (W : State)
    (hI : W.get implAddr = .nil) (hP : W.get proxyAddr = .nil) :
    ∃ postI postP : Devm,
      processCreateMessage (implCreateMsg fork W) = .ok postI ∧ postI.error = none ∧
      postI.gasLeft = 309782 ∧
      postI.state.get implAddr = implAccount ∧
      (∀ a, a ≠ implAddr → postI.state.get a = W.get a) ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧
      postP.error = none ∧ postP.gasLeft = 90972 ∧
      postP.state.get implAddr = implAccount ∧
      postP.state.get proxyAddr = proxyAccount ∧
      ∀ a, a ≠ implAddr → a ≠ proxyAddr → postP.state.get a = W.get a := by
  obtain ⟨postI, hI1, eI, gI, aI, fI⟩ :=
    Creation.create_impl (implCreateMsg fork W) hfork rfl rfl rfl rfl
      (by change 3690218 ≤ 4000000; decide)
  obtain ⟨postP, hP1, eP, gP, aP, fP⟩ :=
    Clone.create_clone (cloneCreateMsg fork postI.state) hfork rfl rfl rfl
      (by change 9028 ≤ 100000; decide)
  change postI.state.get implAddr = Creation.implAcct W implAddr at aI
  change ∀ a, a ≠ implAddr → postI.state.get a = W.get a at fI
  change postP.state.get proxyAddr = Clone.cloneAcct postI.state proxyAddr at aP
  change ∀ a, a ≠ proxyAddr → postP.state.get a = postI.state.get a at fP
  change postI.gasLeft = 4000000 - (4118 + Creation.implSstoreGas (implCreateMsg fork W)) -
    3664000 at gI
  change postP.gasLeft = 100000 - 28 - 9000 at gP
  have hIacct : postI.state.get implAddr = implAccount := by
    rw [aI]
    unfold Creation.implAcct
    rw [hI]
    rfl
  refine ⟨postI, postP, hI1, eI, ?_, hIacct, fI, hP1, eP, gP, ?_, ?_, ?_⟩
  · rw [gI, implSstoreGas_fresh fork W hI]
  · rw [fP implAddr implAddr_ne_proxyAddr, hIacct]
  · rw [aP]
    unfold Clone.cloneAcct
    rw [fI proxyAddr (Ne.symm implAddr_ne_proxyAddr), hP]
    rfl
  · intro a haI haP
    rw [fP a haP, fI a haI]

/-- The disclosed starting world satisfies the creation premises. -/
theorem initialWorld_absent :
    initialWorld.get implAddr = .nil ∧ initialWorld.get proxyAddr = .nil := by
  constructor <;> decide +kernel

/-- **Nonvacuity at the disclosed world**, every covered fork: both creations succeed and the
funded creator is untouched. -/
theorem setup_creations_initial (fork : Fork) (hfork : CoveredFork fork) :
    ∃ postI postP : Devm,
      processCreateMessage (implCreateMsg fork initialWorld) = .ok postI ∧
      processCreateMessage (cloneCreateMsg fork postI.state) = .ok postP ∧
      postP.error = none ∧
      postP.state.get implAddr = implAccount ∧ postP.state.get proxyAddr = proxyAccount ∧
      postP.state.get creator = initialWorld.get creator := by
  obtain ⟨postI, postP, h1, -, -, -, -, h2, e2, -, hi, hp, hf⟩ :=
    setup_creations fork hfork initialWorld initialWorld_absent.1 initialWorld_absent.2
  exact ⟨postI, postP, h1, h2, e2, hi, hp, hf creator (by decide) (by decide)⟩

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach
