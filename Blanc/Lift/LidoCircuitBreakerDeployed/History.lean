import Blanc.Lift.LidoCircuitBreakerDeployed.Pause
import Blanc.Lift.LidoCircuitBreakerDeployed.L2Frame
import Blanc.Lift.LidoCircuitBreakerDeployed.Corollaries

/-!
# The instantiated Lido history theorem, and its L1/L3 corollaries

`LidoWriterSpecsM lidoA` from the two writer walks, and the history rung over
the concrete per-frame premise `lidoA`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace
open scoped BigOperators

/-- Both Registry writers, with the concrete premise `lidoA`. -/
theorem lidoWriterSpecsM : LidoWriterSpecsM lidoA :=
  ⟨fun hfork hw hloc hA hmem hpre run =>
      registerPauser_wrapper_post hfork hw hloc hA hmem hpre run,
   fun hfork hcode hadm ih hw hloc hA hmem hpre run =>
      pause_wrapper_post hfork hcode hadm ih hw hloc hA hmem hpre run⟩

/-- **The instantiated Lido history theorem.**  A configured history whose
entered CircuitBreaker frames satisfy `lidoEntry lidoA` (`LocalApart`, and the
`lidoA` collision premise over every witness of the frame-entry storage)
preserves the state invariant: the deployed code and some Registry witness of
the contract's storage.

Superseded as a headline by `lido_history_l1_l3`, which states the raw-slot L1/L3 registry facts of the future storage. -/
theorem lido_history_preserves_inv_concrete
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry lidoA))
    (inv : lidoSpec.StateInv ca checkpoint.state) :
    lidoSpec.StateInv ca future.state :=
  lido_history_preserves_inv_mem lidoWriterSpecsM trace admitted inv

/-- The checkpoint premise in raw form gives the state invariant. -/
theorem stateInv_of_registryZeroRaw {ca : Adr} {w : Jaune.State}
    (hcode : some (w.getCode ca).toList = lidoSpec.sem.image)
    (hzero : RegistryZeroRaw (w.getStor ca)) : lidoSpec.StateInv ca w :=
  ⟨hcode, trivial, inv_of_registryZero (registryZero_of_raw hzero)⟩

/-- **L1 and L3 at the end of a history**, from the deployed code and the raw
zero Registry at the checkpoint (decision D2), in raw-slot form: there is a
witness `entries` of the future storage for which the assignment and index
slots are nonzero exactly for registered targets (and pin a found entry's
pauser, index and array word), every canonical pauser's count slot is its
number of assignments, the zero pauser's count is zero, and the counts of the
live pausers sum to the number of entries, which is the array length word. -/
theorem lido_history_l1_l3
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : trace.FrameAdmitted ca (lidoEntry lidoA))
    (hcode : some (checkpoint.state.getCode ca).toList = lidoSpec.sem.image)
    (hzero : RegistryZeroRaw (checkpoint.state.getStor ca)) :
    ∃ entries,
      (∀ {t : B256}, canonicalAddress t →
        (addressSlotReadWord ((future.state.getStor ca).get (mapSlot t 3)) ≠ 0 ↔
          t ∈ entries.map Prod.fst) ∧
        ((future.state.getStor ca).get (mapSlot t 4) ≠ 0 ↔
          t ∈ entries.map Prod.fst) ∧
        ∀ index pauser, findEntry entries t = some (index, pauser) →
          addressSlotReadWord ((future.state.getStor ca).get (mapSlot t 3)) = pauser ∧
          (future.state.getStor ca).get (mapSlot t 4) = Nat.toB256 (index + 1) ∧
          addressSlotReadWord ((future.state.getStor ca).get (registryArraySlot index)) = t) ∧
      (∀ p, canonicalAddress p →
        (future.state.getStor ca).get (mapSlot p 6) = Nat.toB256 (assignmentCount entries p)) ∧
      (future.state.getStor ca).get (mapSlot 0 6) = 0 ∧
      (∑ p ∈ (entries.map Prod.snd).toFinset,
        ((future.state.getStor ca).get (mapSlot p 6)).toNat) = entries.length ∧
      (future.state.getStor ca).get 5 = Nat.toB256 entries.length := by
  have h := (lido_history_preserves_inv_concrete trace admitted
    (stateInv_of_registryZeroRaw hcode hzero)).inv
  rw [lidoSpec_inv] at h
  obtain ⟨entries, hw⟩ := h
  obtain ⟨h3a, h3b, h3c⟩ := l3_count_sum_raw hw
  have hlen := hw.lengthWord
  rw [solRegistryStorage_length] at hlen
  exact ⟨entries, l1_membership_raw hw, h3a, h3b, h3c, hlen⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
