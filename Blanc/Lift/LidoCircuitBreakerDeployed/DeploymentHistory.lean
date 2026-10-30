import Blanc.Lift.LidoCircuitBreakerDeployed.History
import Blanc.Lift.LidoCircuitBreakerDeployed.FiniteInit
import Blanc.Lift.LidoCircuitBreakerDeployed.SlotsApart
import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Transaction
import Blanc.Lift.LidoCircuitBreakerDeployed.L2History
import Blanc.ExecutionEntryAccountingMidHistory
import Blanc.ExecutionNoDelHistory

/-!
# The Lido CircuitBreaker history tier, rooted in its actual creation transaction

`LidoDeploymentTo cfg future` retains the configured block containing the CircuitBreaker's
creation, the creation's actual transaction cut (`Creation.DeploymentCut`: one-block
observations of the creation transaction and its receipt), and the configured blocks after it
up to `future`, all on the covered fork domain. Its `remainder` is exact: the rest of
the deployment block (suffix transactions, withdrawals, requests, rewards) followed by the later
blocks.

The headlines `lido_registry_consistent` and `lido_remove_repairs` state the named Props
`ConsistentRegistry` and `RemovalRepaired` over the storage observers of
`RegistryObservers.lean`. Their premises are the retained history (the configured
history premise) and the one universal non-collision hypothesis `LidoSlotsApart`; the installed
code, the empty Registry after the constructor, every frame entry condition (`lidoEntry lidoA`)
and the checkpoint `ForeignApart` premises are derived. `lido_deployment_finite_init` states the
finite empty-registry observation right after the actual creation transaction, with no hash
premise (only the decidable finite apart checker over the chosen probes).
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker Blanc.ExecutionTrace
open scoped BigOperators

/-! ## The runtime's installed-certificate facts -/

/-- Every function of the runtime certificate spawns only by `CALL`/`STATICCALL`. -/
theorem cert_callOnly : cert.callOnly = true := by
  decide +kernel

/-- No function of the runtime certificate ends in `SELFDESTRUCT`. -/
theorem cert_noSelfdestruct : cert.noSelfdestruct = true := by
  decide +kernel

/-- The checked runtime meets every fact the installed-runtime producer consumes. -/
theorem installedCert : InstalledCert code :=
  ⟨⟨_, cert_check, cert_callOnly, cert_noSelfdestruct⟩,
    fun hdel => lidoSem.not_delegation rfl hdel,
    fun h => by
      have := code_toList_length
      rw [h] at this
      cases this⟩

/-! ## The deployment record -/

/-- The CircuitBreaker's actual deployment and the configured history after it, up to
`future`: the deployment block, the creation's transaction cut in it, and the following
configured blocks, all on the covered fork domain. -/
structure LidoDeploymentTo (cfg : ChainConfig) (future : BlockChain) where
  before : BlockChain
  after : BlockChain
  block : ConfiguredBlockTraceIn CoveredFork cfg before after
  deployment : Creation.DeploymentCut block
  following : ConfiguredHistoryTraceIn CoveredFork cfg after future

namespace LidoDeploymentTo

variable {cfg : ChainConfig} {future : BlockChain}

/-- The exact post-deployment remainder: the deployment block's suffix and later stages,
followed by the retained configured history. -/
def remainder (history : LidoDeploymentTo cfg future) :
    MidHistoryTraceIn CoveredFork cfg history.deployment.cut.afterBenv future :=
  (MidHistoryTraceIn.tail history.block history.deployment.cut).append history.following

/-- Under the non-collision hypothesis, the CircuitBreaker satisfies the Lido state invariant
right after its actual creation transaction. -/
theorem stateInv_deployed (history : LidoDeploymentTo cfg future) (H : LidoSlotsApart) :
    lidoSpec.StateInv Creation.breakerAddress history.deployment.cut.afterBenv.state := by
  obtain ⟨hcode, hstor⟩ := history.deployment.initial
  refine stateInv_of_registryZeroRaw (by rw [hcode]; rfl) ?_
  rw [hstor]
  exact Creation.registryZeroRaw_deployedStor
    (H.foreignApart_fixed (Or.inl rfl) (Nat.zero_le _))
    (H.foreignApart_fixed (Or.inr rfl) (Nat.zero_le _))

/-- Every raw frame at the CircuitBreaker along the remainder is admitted: fresh entry is
derived from the retained executions, and the per-frame hash entry from the hypothesis. -/
theorem admitted (history : LidoDeploymentTo cfg future) (H : LidoSlotsApart) :
    history.remainder.FrameAdmitted Creation.breakerAddress (lidoFrameEntry lidoA) :=
  (history.remainder.frameAdmitted_iff_rawFrames _ _).2 fun root member _ =>
    ⟨history.remainder.rawFrames_entered enteredCondition_fresh root member,
      H.lidoEntry root.sevm root.devm⟩

/-- The Lido state invariant at `future`. -/
theorem stateInv_future (history : LidoDeploymentTo cfg future) (H : LidoSlotsApart) :
    lidoSpec.StateInv Creation.breakerAddress future.state :=
  history.remainder.stateInv_admitted_semIn
    (ContractSpecSem.PreservesAdmitted.toIn
      (lidoSpec_preservesAdmitted_mem lidoWriterSpecsM Creation.breakerAddress))
    BodyStageCapabilities.covered (history.admitted H)
    (history.remainder.rewardCreditsFunded BodyStageCapabilities.covered)
    (history.stateInv_deployed H) installedCert rfl

end LidoDeploymentTo

/-- **The CircuitBreaker Registry is consistent after any history from its actual deployment.**
For the CircuitBreaker's actual creation transaction and any configured covered-fork history
after it up to `future`, under the one non-collision hypothesis `LidoSlotsApart`, the Registry
read from the CircuitBreaker's storage at `future` is consistent: the stored targets are
distinct, a target has a nonzero pauser and index exactly when it is stored, each stored
target's index is its position plus one, each pauser's guard count is the number of stored
targets it guards, and the zero address guards nothing. -/
theorem lido_registry_consistent {cfg : ChainConfig} {future : BlockChain}
    (history : LidoDeploymentTo cfg future) (H : LidoSlotsApart) :
    ConsistentRegistry (future.state.getStor Creation.breakerAddress) := by
  have h := (history.stateInv_future H).inv
  rw [lidoSpec_inv] at h
  obtain ⟨entries, hw⟩ := h
  exact consistentRegistry_of_witness hw

/-- **Removal repairs the CircuitBreaker Registry.** For the CircuitBreaker's actual creation
transaction and any configured covered-fork history after it up to `future`, under the one
non-collision hypothesis `LidoSlotsApart`, every settlement-committed non-static frame at the
CircuitBreaker whose calldata is `registerPauser(t, 0)` (including one re-entered from inside
`pause`'s `CALL`) clears `t`'s pauser and index, and leaves the stored target array equal to the
one at the frame's entry with `t` swap-and-popped out (unchanged when `t` was not stored).
Frames rolled back by an ancestor are not claimed; static frames are not observed. -/
theorem lido_remove_repairs {cfg : ChainConfig} {future : BlockChain}
    (history : LidoDeploymentTo cfg future) (H : LidoSlotsApart)
    (frame : Exec.Frame) (member : frame ∈ history.remainder.settledFrames)
    (target : frame.sevm.currentTarget = Creation.breakerAddress)
    (nonstatic : frame.sevm.isStatic = false)
    (hsig : Sevm.dataWord frame.sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hnp0 : Sevm.dataWord frame.sevm 36 = 0) :
    RemovalRepaired (Devm.getStor frame.pre Creation.breakerAddress)
      (Devm.getStor frame.post Creation.breakerAddress) (Sevm.dataWord frame.sevm 4) := by
  have inv := history.stateInv_deployed H
  obtain ⟨-, good⟩ := history.remainder.entryGood_settled (c := lidoSpec)
    (I := fun s => RegInv s) (history.admitted H) inv inv.inv
    (lidoSpec_preservesAdmitted_mem lidoWriterSpecsM Creation.breakerAddress)
    (lido_framePreserves Creation.breakerAddress) (lido_spawnKinds Creation.breakerAddress)
    (lido_spawnEntry Creation.breakerAddress) installedCert rfl
  obtain ⟨entries, hpre, hl2, hpost⟩ :=
    l2_of_entryGood frame (good frame member target nonstatic) target hsig hnp0
  exact removalRepaired_of_witness hpre hpost hl2.2.1 hl2.2.2.1

/-- **Finite deployment initialization on the actual creation transaction.** Right after the
CircuitBreaker's actual creation transaction, its address holds the certified runtime and its
storage carries the finite empty-registry observation for any canonical probe list whose finite
apart check against the constructor's two written slots succeeds. No hash premise. -/
theorem lido_deployment_finite_init {cfg : ChainConfig} {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn CoveredFork cfg pre post}
    (deployment : Creation.DeploymentCut block)
    {probes : List B256} (hp : ∀ p ∈ probes, canonicalAddress p)
    (hapart : Blanc.SlotFootprint.checkApartOn solKey
      (registryQueries probes 0) [0, 1] = true) :
    (deployment.cut.afterBenv.state.getCode Creation.breakerAddress).toList = code.toList ∧
      RegistryOn (solRegistryStorage
        (deployment.cut.afterBenv.state.getStor Creation.breakerAddress)) [] probes := by
  obtain ⟨hcode, hstor⟩ := deployment.initial
  exact ⟨hcode, by rw [hstor]; exact registryOn_deployedStor hp hapart⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
