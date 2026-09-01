import Blanc.BeaconDepositBridgeCompiled
import Blanc.ContractAdmission
import Blanc.ExecutionFrameEntry
import Blanc.ExecutionHistoryEffects
import Blanc.ExecutionOccurrence

/-!
# Beacon deposit open-history specification

This module fixes the statement boundary for the Beacon deposit contract's
open-history theorem.  The storage predicate is relative to one caller-chosen
baseline and can only retain that baseline or extend it by a suffix.

Prague's SHA-256 precompile address is not, by itself, a permanent world-state
fact: an EIP-7702 delegation designator at address `0x2` disables precompile
dispatch.  The frame theorem therefore carries a trace-local admission fact
for every actually entered Beacon frame.  It says only that address `0x2` is
nondelegated there and that the selected fork rules designate it as a
precompile; it says nothing about the frame's result or poststate.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-- Storage carries the fixed baseline followed by some witnessed suffix.
The suffix may be empty, but the baseline can never be replaced. -/
def HistoryExtends (baseline : List B256) (stor : Stor) : Prop :=
  ∃ suffix, ArtifactInv stor (baseline ++ suffix)

theorem HistoryExtends.base {baseline : List B256} {stor : Stor}
    (artifact : ArtifactInv stor baseline) : HistoryExtends baseline stor := by
  exact ⟨[], by simpa using artifact⟩

theorem HistoryExtends.transAppend
    {baseline suffix : List B256} {stor : Stor}
    (history : HistoryExtends (baseline ++ suffix) stor) :
    HistoryExtends baseline stor := by
  rcases history with ⟨tail, artifact⟩
  refine ⟨suffix ++ tail, ?_⟩
  simpa only [List.append_assoc] using artifact

/-- Baseline history validity is extensional in observable storage words. -/
theorem HistoryExtends.of_get_eq
    {baseline : List B256} {before after : Stor}
    (equal : ∀ key, after.get key = before.get key)
    (history : HistoryExtends baseline before) :
    HistoryExtends baseline after := by
  rcases history with ⟨suffix, artifact⟩
  exact ⟨suffix, artifact.of_get_eq equal⟩

/-- The storage-only contract specification used by the history ladder.
Callvalue and balances are deliberately irrelevant; value movement cannot
change persistent storage. -/
def historySpec (baseline : List B256) : ContractSpec where
  prog := runtime
  Inv := fun stor _ _ => HistoryExtends baseline stor
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun history _ => history
  inv_recv := fun history _ => history
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro state state' caller callee ca value inflight sub callerNe _ history
    show HistoryExtends baseline _
    have storageEq : (state'.addBal callee value).getStor ca =
        state.getStor ca := by
      rcases State.of_subBal sub with ⟨_, stateEq⟩
      show ((state'.setBal callee _).get ca).stor = (state.get ca).stor
      rw [State.setBal_get_stor, stateEq, State.setBal_get_stor]
    rw [storageEq]
    exact history
  inv_recv_transfer := by
    intro state state' caller ca value sub callerNe _ history
    show HistoryExtends baseline _
    have storageEq : (state'.addBal ca value).getStor ca =
        state.getStor ca := by
      rcases State.of_subBal sub with ⟨_, stateEq⟩
      show ((state'.setBal ca _).get ca).stor = (state.get ca).stor
      rw [State.setBal_get_stor, stateEq, State.setBal_get_stor]
    rw [storageEq]
    exact history
  inv_addBal := by
    intro state ca address value inflight _ _ history
    show HistoryExtends baseline _
    have storageEq : (state.addBal address value).getStor ca =
        state.getStor ca := by
      show ((state.setBal address _).get ca).stor = (state.get ca).stor
      rw [State.setBal_get_stor]
    rw [storageEq]
    exact history

/-- The exact world/rules facts that make calls to address `0x2` use native
SHA-256 rather than delegated interpreted code.  Warmth is intentionally not
required: it changes gas cost, not the successful call's digest. -/
structure NativeShaEntry (sevm : Sevm) (pre : Devm) : Prop where
  nondelegated : getDelegatedCodeAddress (pre.getCode 2) = none
  precompile : decide (sevm.benvStat.rules.isPrecomp 2) = true

/-- Entry facts used by the source-level Beacon frame proof.  Native SHA is
the contract-specific external-execution boundary; fresh stack and memory are
facts of the actual entered frame, not assumptions about an arbitrary Devm. -/
def HistoryEntry (sevm : Sevm) (pre : Devm) : Prop :=
  NativeShaEntry sevm pre ∧ Exec.FreshEntry sevm pre

/-- Every actually entered frame executing at the Beacon storage owner has a
native SHA-256 boundary.  This is trace-local: unrelated frames need no such
fact, and no result or poststorage premise appears. -/
def Exec.NativeShaAdmitted
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (ca : Adr) (run : Exec pc sevm pre out) : Prop :=
  Exec.FrameAdmitted ca NativeShaEntry run

theorem Exec.NativeShaAdmitted.root
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {ca : Adr} {run : Exec pc sevm pre out}
    (admitted : Exec.NativeShaAdmitted ca run)
    (target : sevm.currentTarget = ca) : NativeShaEntry sevm pre := by
  exact Exec.FrameAdmitted.root admitted target

/-- Native SHA admission combined with the fresh machine state supplied by
the concrete frame-entry trace. -/
def Exec.HistoryAdmitted
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (ca : Adr) (run : Exec pc sevm pre out) : Prop :=
  Exec.FrameAdmitted ca HistoryEntry run

theorem Exec.HistoryAdmitted.root
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {ca : Adr} {run : Exec pc sevm pre out}
    (admitted : Exec.HistoryAdmitted ca run)
    (target : sevm.currentTarget = ca) : HistoryEntry sevm pre := by
  exact Exec.FrameAdmitted.root admitted target

/-- The open-frame preservation boundary used by Beacon history.  It is the
ordinary `ContractSpec.Preserves` statement with one additional piece of
positive evidence: native SHA admission for the concrete execution's actual
frame roots. -/
def HistoryPreserves (baseline : List B256) (ca : Adr) : Prop :=
  (historySpec baseline).PreservesAdmitted ca HistoryEntry

end Blanc.BeaconDeposit
