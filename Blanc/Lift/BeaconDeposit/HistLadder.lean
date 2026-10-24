import Blanc.Lift.BeaconDeposit.HistSafe
import Blanc.ExecutionHistoricalLadder

/-!
# The beacon deposit invariant at frame altitude over every historical fork

The historical counterpart of `Ladder.lean`'s frame rung: `beaconSpec_soundAdmittedIn HistFork`
from `deposit_frame_refinesH` (`HistSafe.lean`), and `beaconSpec_preservesAdmittedIn` from the
generic historical frame theorem `ContractSpecSem.preserves_inv_admitted_histFork`.

The entry is the modern one, `beaconFrameEntry`, unchanged: fresh entry, calldata length, the
precompile account's code is not a delegation, and the precompile is warm.  Every other premise
of `deposit_frame_refinesH` is discharged from the frame's fork: `rules.stateGas = none`
(`HistFork.stateGas_none`), `rules.bal = none` (`HistFork.bal_none`) and `isPrecomp 2`
(`isPrecomp_two_hist`, every fork of `histForks`).  No access schedule or delegation flag is
assumed: the SHA-256 `STATICCALL` inversion is cased on both.
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

/-- **Beacon frame soundness over every historical fork, trace-admitted**, from
`deposit_frame_refinesH`. -/
theorem beaconSpec_soundAdmittedIn (ca : Adr) :
    beaconSpec.SoundAdmittedIn HistFork ca beaconFrameEntry := by
  intro sevm pre post hfork execution hrun hca admitted _ _ hpre
  subst hca
  obtain ⟨⟨hstack, hmem⟩, hcd, hnodeleg, hwarm⟩ := admitted.root rfl
  obtain ⟨history, hinv⟩ := hpre.inv.left rfl
  have hsg : sevm.benvStat.rules.stateGas = none := HistFork.stateGas_none hfork
  have hbal : sevm.benvStat.rules.bal = none := HistFork.bal_none hfork
  have hsha : ShaReadyH sevm pre := ⟨hnodeleg, hwarm, isPrecomp_two_hist hfork, hsg, hbal⟩
  have h := deposit_frame_refinesH hrun hsg hbal hcd hstack hmem hsha hinv execution
  refine ⟨trivial, ?_⟩
  show ∃ history, SolInv (Devm.getStor post sevm.currentTarget) history
  by_cases hsel : Sevm.selector sevm = BeaconDeposit.depositSelector
  · obtain ⟨_, _, _, _, _, hinv', _⟩ := h.1 hsel
    exact ⟨_, hinv'⟩
  · rw [(h.2 hsel).1]
    exact ⟨history, hinv⟩

/-- **Beacon frame preservation over every historical fork, trace-admitted**: the form the
historical message, transaction and history rungs consume. -/
theorem beaconSpec_preservesAdmittedIn (ca : Adr) :
    beaconSpec.PreservesAdmittedIn HistFork ca beaconFrameEntry :=
  beaconSpec.preserves_inv_admitted_histFork ca beaconFrameEntry (beaconSpec_soundAdmittedIn ca)

end Blanc.Lift.BeaconDeposit
