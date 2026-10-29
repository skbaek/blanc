import Blanc.Lift.BeaconDeposit.HistSafe
import Blanc.ExecutionHistoricalLadder

/-!
# The beacon deposit invariant at frame altitude over every historical fork

The historical counterpart of `Ladder.lean`'s frame rung: `beaconSpec_soundAdmittedIn HistFork`
from `deposit_frame_refinesH` (`HistSafe.lean`), and `beaconSpec_preservesAdmittedIn` from the
generic historical frame theorem `ContractSpecSem.preserves_inv_admitted_histFork`.

The selected-rule entry requires nondelegation only when the frame's actual fork enables
it. Fresh entry, short calldata and SHA warmth remain explicit. The old unconditional
entry and public theorem signatures are preserved by adapters to the same frame proof.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc
open Blanc.Lift

/-- The SHA-256 precompile is a precompile on every historical fork. -/
theorem isPrecomp_two_hist {sevm : Sevm} (hfork : HistFork sevm.benvStat.fork) :
    decide (sevm.benvStat.rules.isPrecomp 2) = true := by
  have key : ∀ f : Fork, HistFork f → decide ((Fork.ruleSet f).isPrecomp 2) = true := by
    intro f _
    cases f <;> decide
  exact key _ hfork

/-- Beacon entry facts under the actual selected delegation rule. -/
def beaconEntryRules (sevm : Sevm) (pre : Devm) : Prop :=
  sevm.data.length < 2 ^ 256 ∧
  (sevm.benvStat.rules.delegationEnabled = true →
    getDelegatedCodeAddress (pre.getCode 2) = none) ∧
  (2 : Adr) ∈ pre.accessedAddresses

/-- Fresh Beacon entry with selected-rule SHA readiness. -/
def beaconFrameEntryRules (sevm : Sevm) (pre : Devm) : Prop :=
  Exec.FreshEntry sevm pre ∧ beaconEntryRules sevm pre

/-- The existing stronger entry discharges the selected-rule entry. -/
theorem beaconEntry_toRules {sevm : Sevm} {pre : Devm}
    (entry : beaconEntry sevm pre) : beaconEntryRules sevm pre :=
  ⟨entry.1, fun _ => entry.2.1, entry.2.2⟩

/-- The existing fresh entry discharges the selected-rule fresh entry. -/
theorem beaconFrameEntry_toRules {sevm : Sevm} {pre : Devm}
    (entry : beaconFrameEntry sevm pre) : beaconFrameEntryRules sevm pre :=
  ⟨entry.1, beaconEntry_toRules entry.2⟩

private theorem beaconSpec_soundAdmittedIn_of_entry (ca : Adr)
    (entry : Sevm → Devm → Prop)
    (ready : ∀ sevm pre, entry sevm pre → beaconFrameEntryRules sevm pre) :
    beaconSpec.SoundAdmittedIn HistFork ca entry := by
  intro sevm pre post hfork execution hrun hca admitted _ _ hpre
  subst hca
  obtain ⟨⟨hstack, hmem⟩, hcd, hnodeleg, hwarm⟩ := ready _ _ (admitted.root rfl)
  obtain ⟨history, hinv⟩ := hpre.inv.left rfl
  have hsg : sevm.benvStat.rules.stateGas = none := HistFork.stateGas_none hfork
  have hbal : sevm.benvStat.rules.bal = none := HistFork.bal_none hfork
  have hsha : ShaReadyRules sevm pre := ⟨hnodeleg, hwarm, isPrecomp_two_hist hfork, hsg, hbal⟩
  have h := deposit_frame_refinesH_of_rules hrun hsg hbal hcd hstack hmem hsha hinv execution
  refine ⟨trivial, ?_⟩
  show ∃ history, SolInv (Devm.getStor post sevm.currentTarget) history
  by_cases hsel : Sevm.selector sevm = BeaconDeposit.depositSelector
  · obtain ⟨_, _, _, _, _, hinv', _⟩ := h.1 hsel
    exact ⟨_, hinv'⟩
  · rw [(h.2 hsel).1]
    exact ⟨history, hinv⟩

/-- Beacon soundness with readiness conditional on the actual delegation flag. -/
theorem beaconSpec_soundAdmittedIn_of_rules (ca : Adr) :
    beaconSpec.SoundAdmittedIn HistFork ca beaconFrameEntryRules :=
  beaconSpec_soundAdmittedIn_of_entry ca beaconFrameEntryRules (fun _ _ h => h)

/-- **Beacon frame soundness over every historical fork, trace-admitted**, from
`deposit_frame_refinesH`. -/
theorem beaconSpec_soundAdmittedIn (ca : Adr) :
    beaconSpec.SoundAdmittedIn HistFork ca beaconFrameEntry :=
  beaconSpec_soundAdmittedIn_of_entry ca beaconFrameEntry
    (fun _ _ h => beaconFrameEntry_toRules h)

/-- Historical frame preservation with selected-rule entry. -/
theorem beaconSpec_preservesAdmittedIn_of_rules (ca : Adr) :
    beaconSpec.PreservesAdmittedIn HistFork ca beaconFrameEntryRules :=
  beaconSpec.preserves_inv_admitted_histFork ca beaconFrameEntryRules
    (beaconSpec_soundAdmittedIn_of_rules ca)

/-- **Beacon frame preservation over every historical fork, trace-admitted**: the form the
historical message, transaction and history rungs consume. -/
theorem beaconSpec_preservesAdmittedIn (ca : Adr) :
    beaconSpec.PreservesAdmittedIn HistFork ca beaconFrameEntry :=
  beaconSpec.preserves_inv_admitted_histFork ca beaconFrameEntry (beaconSpec_soundAdmittedIn ca)

end Blanc.Lift.BeaconDeposit
