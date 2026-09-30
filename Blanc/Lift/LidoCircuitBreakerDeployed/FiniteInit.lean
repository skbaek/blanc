import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteRegistry
import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Deploy

/-!
# Finite initialization of the deployed Lido registry

From the actual `Creation.lido_create` deployment (the recorded creation input
executed as a CREATE message), plus a computable finite slot-apart check of the
constructor's two written slots (`0` for `pauseDuration`, `1` for
`heartbeatInterval`) against exactly the canonical probes' finite query keys,
the deployed storage carries the finite empty-registry observation
`RegistryOn` with actual raw storage.

This is modeled deployment, not historical authentication: the apart premise is
the decidable `SlotFootprint.checkApartOn` checker returning `true` on explicit
finite lists, never a universal hash premise, and the conclusion is the finite
`RegistryOn` observation, never a whole-world `RegistryWitness`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker Blanc.ForkUniform

/-- The constructor's storage satisfies the finite empty-registry observation:
`registryOn_empty_raw` at `Stor.empty`, preserved across the two foreign writes
by `RegistryOn.set_foreign`. No hash premise beyond the finite checker. -/
theorem registryOn_deployedStor {probes : List B256}
    (hp : ∀ p ∈ probes, canonicalAddress p)
    (hapart : Blanc.SlotFootprint.checkApartOn solKey
      (registryQueries probes 0) [0, 1] = true) :
    RegistryOn (solRegistryStorage Creation.deployedStor) [] probes := by
  have hsingle : ∀ w ∈ ([0, 1] : List B256),
      Blanc.SlotFootprint.checkApartOn solKey (registryQueries probes 0) [w] = true := by
    intro w hw
    rw [Blanc.SlotFootprint.checkApartOn_eq_true]
    intro x hx k hk
    simp only [List.mem_singleton] at hx
    subst x
    exact Blanc.SlotFootprint.checkApartOn_eq_true.mp hapart w hw k hk
  have h0 : RegistryOn (solRegistryStorage Stor.empty) [] probes :=
    registryOn_empty_raw hp
  have h1 : RegistryOn
      (solRegistryStorage (Stor.empty.set 0 1814400)) [] probes :=
    h0.set_foreign (hsingle 0 (by simp))
  have h2 : RegistryOn
      (solRegistryStorage ((Stor.empty.set 0 1814400).set 1 31536000)) [] probes :=
    h1.set_foreign (hsingle 1 (by simp))
  have hdep : Creation.deployedStor =
      (Stor.empty.set 0 1814400).set 1 31536000 := rfl
  rw [hdep]
  exact h2

/-- **Finite deployment initialization.** The recorded creation input, executed
as a zero-value CREATE message with enough gas under a covered fork, succeeds;
the new account's code is exactly the certified deployed runtime and its
storage carries the finite empty-registry observation for the canonical probes.
The post state (code and storage) comes from `Creation.lido_create`; only the
storage observation is rewritten through `registryOn_deployedStor`. -/
theorem lido_create_finite_init (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Creation.code)
    (hgas : 1000000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork)
    (hstatic : msg.isStatic = false)
    (hmax : 4584 ≤ msg.benv.stat.rules.code.maxCodeSize)
    {probes : List B256} (hp : ∀ p ∈ probes, canonicalAddress p)
    (hapart : Blanc.SlotFootprint.checkApartOn solKey
      (registryQueries probes 0) [0, 1] = true) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList =
        Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      RegistryOn (solRegistryStorage (Devm.getStor post msg.currentTarget)) [] probes := by
  obtain ⟨post, h1, h2, h3⟩ :=
    Creation.lido_create msg hvalue hcodeAddress hcode hgas hfork hstatic hmax
  refine ⟨post, h1, h2, ?_⟩
  rw [h3]
  exact registryOn_deployedStor hp hapart

end Blanc.Lift.LidoCircuitBreakerDeployed
