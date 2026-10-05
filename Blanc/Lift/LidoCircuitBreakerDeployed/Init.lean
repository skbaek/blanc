import Blanc.Lift.LidoCircuitBreakerDeployed.History

/-!
# Satisfiability of the Lido CircuitBreaker checkpoint premise

The Lido history theorems (`lido_history_preserves_inv_concrete`, `lido_history_l1_l3`) carry
`lidoSpec.StateInv ca` (respectively the raw-slot form `RegistryZeroRaw`) at their checkpoint.
This module shows those premises are inhabited by an explicit concrete world: the account `ca`
holds the deployed CircuitBreaker runtime `code`, a zero ether balance and empty storage, and no
other account exists.

This proves satisfiability of the checkpoint premise, not deployment: it says nothing about how
a real chain reaches such a state.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

/-- The concrete world of a fresh Lido CircuitBreaker at `ca`: the deployed runtime code, zero
balance, empty storage, nonce zero, and no other account. -/
def lidoInitWorld (ca : Adr) : State :=
  (Std.TreeMap.empty : State).insert ca { Acct.nil with code := code }

theorem lidoInitWorld_getCode (ca : Adr) : (lidoInitWorld ca).getCode ca = code := by
  simp only [State.getCode, State.get, lidoInitWorld, Std.TreeMap.empty_eq_emptyc,
    Std.TreeMap.getD_insert_self]

theorem lidoInitWorld_getStor (ca : Adr) : (lidoInitWorld ca).getStor ca = Stor.empty := by
  simp only [State.getStor, State.get, lidoInitWorld, Std.TreeMap.empty_eq_emptyc, Acct.nil,
    Std.TreeMap.getD_insert_self]

/-- The empty storage satisfies the raw-slot Registry zero premise. -/
theorem registryZeroRaw_empty : RegistryZeroRaw Stor.empty := by
  refine ⟨by simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
    Std.TreeMap.getD_emptyc], fun p _ => ?_⟩
  simp only [addressSlotReadWord, Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
    Std.TreeMap.getD_emptyc, and_self, and_true]
  rfl

/-- **The Lido raw checkpoint premise is satisfiable.** -/
theorem lido_init_registryZeroRaw (ca : Adr) : RegistryZeroRaw ((lidoInitWorld ca).getStor ca) := by
  rw [lidoInitWorld_getStor]; exact registryZeroRaw_empty

/-- **The Lido checkpoint state invariant is satisfiable.**  `lidoInitWorld ca` (deployed
runtime code, empty storage) satisfies `lidoSpec.StateInv ca`. -/
theorem lido_init_stateInv (ca : Adr) : lidoSpec.StateInv ca (lidoInitWorld ca) :=
  stateInv_of_registryZeroRaw (by rw [lidoInitWorld_getCode]; rfl) (lido_init_registryZeroRaw ca)

end Blanc.Lift.LidoCircuitBreakerDeployed
