import Blanc.Lift.Sound
import Blanc.Lift.LidoCircuitBreakerDeployed.Check
import Blanc.Lift.LidoCircuitBreakerDeployed.Prog
import Blanc.Lift.LidoCircuitBreakerDeployed.RegistryLayout
import Blanc.StorageOnlySpec

/-!
# The Lido CircuitBreaker frame contract

`lidoSem` is the certified code semantics of the deployed Lido CircuitBreaker
runtime: its image is the deployed bytes and its run relation records that the
frame runs those bytes and, on a covered fork, the lifted program (`lift_sound`
over `cert_check`).
`lidoSpec` is the storage-only frame contract whose invariant is that the
contract's storage abstracts some Registry model state under `RegistryWitness`
applied to `solRegistryStorage`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.LidoCircuitBreaker

theorem code_toList_length : code.toList.length = 4584 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

/-- The certified semantics of the deployed Lido CircuitBreaker runtime. -/
def lidoSem : CodeSem where
  image := some code.toList
  Run sevm pre post :=
    sevm.code = code ∧ (CoveredFork sevm.benvStat.fork → SProg.Run prog sevm pre post)
  correct := by
    intro sevm pre post exc hcode
    have h : sevm.code.toList = code.toList := Option.some.inj hcode
    have hc : sevm.code = code := by
      cases hs : sevm.code with
      | mk d =>
        cases hk : code with
        | mk d' =>
          rw [hs, hk] at h
          rw [ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at h
          exact congrArg ByteArray.mk (Array.toList_inj.mp h)
    exact ⟨hc, fun hfork => lift_sound cert_check hc hfork exc⟩
  ne_nil := by
    intro l hl h
    have h' : code.toList = l := Option.some.inj hl
    have hlen := code_toList_length
    rw [h', h] at hlen
    exact absurd hlen (by decide)
  not_delegation := by
    intro c hc hdel
    have h : c.toList = code.toList := Option.some.inj hc
    have hlen : c.toList.length = 4584 := h ▸ code_toList_length
    rw [ByteArray.toList_eq_toList_data, Array.length_toList] at hlen
    have hsize : c.size = eoaDelegatedCodeLength := hdel.1
    have hsz : c.size = c.data.size := rfl
    rw [hsz, hlen] at hsize
    exact absurd hsize (by decide)

/-- The Lido CircuitBreaker frame contract: the storage abstracts some Registry model state. -/
def lidoSpec : ContractSpecSem where
  sem := lidoSem
  Inv := fun stor _ _ => ∃ entries, RegistryWitness (solRegistryStorage stor) entries
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub _ _ h_inv
    show ∃ entries, RegistryWitness (solRegistryStorage _) entries
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub _ _ h_inv
    show ∃ entries, RegistryWitness (solRegistryStorage _) entries
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show ∃ entries, RegistryWitness (solRegistryStorage _) entries
    rw [getStor_addBal]
    exact h_inv

theorem lidoSpec_inv :
    lidoSpec.Inv = fun stor _ _ => ∃ entries, RegistryWitness (solRegistryStorage stor) entries :=
  rfl

end Blanc.Lift.LidoCircuitBreakerDeployed
