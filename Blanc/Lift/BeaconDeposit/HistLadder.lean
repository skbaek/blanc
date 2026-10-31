import Blanc.Lift.BeaconDeposit.HistSafe
import Blanc.Lift.BeaconDeposit.CommittedExec
import Blanc.ExecutionHistoricalLadder

/-!
# The beacon deposit invariant at frame altitude over every historical fork

The historical counterpart of `Ladder.lean`'s frame rung: `beaconSpec_soundAdmittedIn HistFork`
from `deposit_frame_refinesH_of_rules` (`HistSafe.lean`), and `beaconSpec_preservesAdmittedIn` from the
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
`deposit_frame_refinesH_of_rules`. -/
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

/-! ## Frame tails -/

/-- One historical frame extends the storage abstraction by its accepted nodes. -/
theorem frame_solInvH_of_rules {sevm : Sevm} {pre post : Devm} {history : List B256}
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsha : ShaReadyRules sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (exc : Exec 0 sevm pre (.ok post)) :
    SolInv (Devm.getStor post sevm.currentTarget) (history ++ frameAccepted sevm) := by
  have hr := deposit_frame_refinesH_of_rules hcode hsg hbal hcd hstack hmem hsha hinv exc
  unfold frameAccepted
  by_cases hsel : Sevm.selector sevm = BeaconDeposit.depositSelector
  · rw [ite_eq_left hsel]
    obtain ⟨-, s', ev, hOk, hacc, hinv', -⟩ := hr.1 hsel
    refine ⟨hinv'.1, ?_⟩
    show BeaconDeposit.Inv Bytes.sha256 _ _
    rw [hacc]
    exact BeaconDeposit.deposit_inv Bytes.sha256 _ _ _ _ _ _ _ _ _ hinv.2 hOk
  · rw [ite_eq_right hsel, List.append_nil, (hr.2 hsel).1]
    exact hinv

/-- The event segment's mandatory `LOG1` forces a non-static frame on any successful run. -/
theorem event_suffix_nonstaticH {sevm : Sevm} {pre : Devm} {out : Outcome}
    (run : SFunc.Run prog sevm pre t_071c_c4 out) : sevm.isStatic = false := by
  cases static : sevm.isStatic with
  | false => rfl
  | true =>
    unfold t_071c_c4 at run
    cases run with
    | dest burn run =>
      iterate 22 (cases run; rename_i _ step run)
      cases run with
      | next step run =>
        obtain ⟨pc, logRun⟩ := of_run_reg step
        exact (Rinst.log_not_ok_of_static static logRun).elim

/-- A successful deployed deposit cannot run in a static historical frame. -/
theorem successful_deposit_not_staticH {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsel : Sevm.selector sevm = BeaconDeposit.depositSelector)
    (run : Exec 0 sevm pre (.ok post)) : sevm.isStatic = false := by
  obtain ⟨f, hf, lifted⟩ := lift_sound_noStateGas cert_check hcode hsg run
  have hf0 : prog[0]? = some t_0000_c0 := rfl
  rw [hf0] at hf
  cases hf
  rw [St.self hstack hmem] at lifted
  obtain ⟨k, G1, g, _, hk32, hg, lifted⟩ := safe_dispatch lifted
  have hk : k = 32 := hk32.mpr hsel
  subst k
  have hg32 : g = t_00a4_c32 := by
    have heq : prog[32]? = some t_00a4_c32 := rfl
    rw [heq] at hg
    exact (Option.some.inj hg).symm
  subst g
  obtain ⟨_, G2, d, body, _, _⟩ := safe_decoder hcd lifted
  obtain ⟨_, _, _, _, _, _, b1, M1, G3, _, memory, body⟩ := safe_guardsH hcd hbal body
  obtain ⟨b2, M2, G4, _, _, body⟩ := safe_event memory body
  exact event_suffix_nonstaticH body

/-- Static historical executions of the deployed deposit selector accept nothing. -/
theorem frameAccepted_eq_nil_of_staticH {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hbal : sevm.benvStat.rules.bal = none)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm pre (.ok post)) : frameAccepted sevm = [] := by
  unfold frameAccepted
  split
  next selected =>
    have impossible := successful_deposit_not_staticH hcode hsg hbal hcd hstack hmem selected run
    rw [static] at impossible
    cases impossible
  next => rfl

end Blanc.Lift.BeaconDeposit
