import Blanc.BeaconDepositDeploymentRoot
import Blanc.BeaconDepositHistorySound
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionTraceFresh

/-!
# Beacon deposit configured open history

The open-frame theorem is lifted through exact retained configured histories.
Native SHA admission remains positive evidence about the actual frame roots
in the retained trace; the generic history carrier supplies fresh-entry facts.
-/

namespace Blanc.BeaconDeposit

open Jaune
open ExecutionTrace

/-- Native SHA admission for an exact retained replay of a named configured
reachability proof.  This is entry evidence for actual frame roots, not a
poststate, settlement result, or future-invariant premise. -/
def ReachNativeShaAdmitted
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (reach : BlockChain.ReachUsing cfg checkpoint future) (ca : Adr) : Prop :=
  ∃ trace : ConfiguredHistoryTrace cfg checkpoint future,
    trace.toReachUsing = reach ∧
    trace.FrameAdmitted ca NativeShaEntry

/-- A retained configured history preserves one fixed baseline and may only
append a witnessed suffix to it. -/
theorem configuredHistory_extends
    {baseline : List B256} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {ca : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (native : trace.FrameAdmitted ca NativeShaEntry)
    (installed :
      some (checkpoint.state.getCode ca).toList = Prog.compile runtime)
    (artifact : ArtifactInv (checkpoint.state.getStor ca) baseline) :
    HistoryExtends baseline (future.state.getStor ca) := by
  have admitted : trace.FrameAdmitted ca HistoryEntry :=
    native.and (trace.freshFrameAdmitted ca)
  have initial : (historySpec baseline).StateInv ca checkpoint.state := by
    exact ⟨installed, trivial, HistoryExtends.base artifact⟩
  have result := trace.stateInv_admitted
    (historySpec_preserves baseline ca) admitted initial
  exact result.inv

/-- Schedule-parametric configured reachability theorem.  The future carries
the original baseline followed by one existentially witnessed suffix. -/
theorem reachUsing_history_extends
    {baseline : List B256} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {ca : Adr}
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (native : ReachNativeShaAdmitted reach ca)
    (installed :
      some (checkpoint.state.getCode ca).toList = Prog.compile runtime)
    (artifact : ArtifactInv (checkpoint.state.getStor ca) baseline) :
    ∃ suffix,
      ArtifactInv (future.state.getStor ca) (baseline ++ suffix) := by
  rcases native with ⟨trace, _projection, admitted⟩
  exact configuredHistory_extends trace admitted installed artifact

/-- The exact Prague-only schedule required by the deployment closure. -/
theorem pragueOnly_history_extends
    (chainId : UInt64) {baseline : List B256}
    {checkpoint future : BlockChain} {ca : Adr}
    (reach : BlockChain.ReachUsing (ChainConfig.pragueOnly chainId)
      checkpoint future)
    (native : ReachNativeShaAdmitted reach ca)
    (installed :
      some (checkpoint.state.getCode ca).toList = Prog.compile runtime)
    (artifact : ArtifactInv (checkpoint.state.getStor ca) baseline) :
    ∃ suffix,
      ArtifactInv (future.state.getStor ca) (baseline ++ suffix) :=
  reachUsing_history_extends reach native installed artifact

/-- Deployment-root rung: the constructor's empty history can only grow by a
suffix along any continuation of the root's own configured schedule. -/
theorem DeploymentRoot.future_history_extends
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future)
    (native : ReachNativeShaAdmitted reach ca) :
    ∃ suffix, ArtifactInv (future.state.getStor ca) suffix := by
  simpa only [List.nil_append] using
    reachUsing_history_extends reach native root.installed_compile
      root.artifact

/-- Reader-facing content of a baseline-relative history witness: concrete
count equality and monotonicity, strictness exactly for a nonempty suffix, and
the model mixed-root equation.  The suffix is existential and is not claimed
to be transaction-indexed or unique. -/
theorem HistoryExtends.exists_count_root
    {baseline : List B256} {stor : Stor}
    (history : HistoryExtends baseline stor) :
    ∃ suffix,
      ArtifactInv stor (baseline ++ suffix) ∧
      (stor.get depositCountSlot).toNat =
        baseline.length + suffix.length ∧
      baseline.length ≤ (stor.get depositCountSlot).toNat ∧
      (baseline.length < (stor.get depositCountSlot).toNat ↔
        suffix ≠ []) ∧
      Acc.root Bytes.sha256 (accOfStor stor) =
        mixedRootOf Bytes.sha256 (baseline ++ suffix) := by
  rcases history with ⟨suffix, artifact⟩
  have countEq :
      (stor.get depositCountSlot).toNat =
        baseline.length + suffix.length := by
    simpa only [accOfStor_count, List.length_append] using
      artifact.count_eq_history_length
  refine ⟨suffix, artifact, countEq, ?_, ?_, artifact.root_eq_mixedRootOf⟩
  · rw [countEq]
    omega
  · constructor
    · intro hlt heq
      rw [countEq] at hlt
      subst suffix
      simp only [List.length_nil, Nat.add_zero] at hlt
      omega
    · intro hne
      have hpos : 0 < suffix.length := List.length_pos_iff.mpr hne
      rw [countEq]
      omega

/-- Reader-facing count/root corollary at an arbitrary admitted configured
future. -/
theorem reachUsing_future_count_root
    {baseline : List B256} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {ca : Adr}
    (reach : BlockChain.ReachUsing cfg checkpoint future)
    (native : ReachNativeShaAdmitted reach ca)
    (installed :
      some (checkpoint.state.getCode ca).toList = Prog.compile runtime)
    (artifact : ArtifactInv (checkpoint.state.getStor ca) baseline) :
    ∃ suffix,
      ArtifactInv (future.state.getStor ca) (baseline ++ suffix) ∧
      ((future.state.getStor ca).get depositCountSlot).toNat =
        baseline.length + suffix.length ∧
      baseline.length ≤
        ((future.state.getStor ca).get depositCountSlot).toNat ∧
      (baseline.length <
          ((future.state.getStor ca).get depositCountSlot).toNat ↔
        suffix ≠ []) ∧
      Acc.root Bytes.sha256 (accOfStor (future.state.getStor ca)) =
        mixedRootOf Bytes.sha256 (baseline ++ suffix) :=
  HistoryExtends.exists_count_root
    (reachUsing_history_extends reach native installed artifact)

/-- Deployment-rooted headline: future count is the witnessed suffix length,
is positive exactly when that suffix is nonempty, and the concrete projection's
root is the model mixed root of the same suffix. -/
theorem DeploymentRoot.future_count_root
    {cfg : ChainConfig} {base deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg base deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future)
    (native : ReachNativeShaAdmitted reach ca) :
    ∃ suffix,
      ArtifactInv (future.state.getStor ca) suffix ∧
      ((future.state.getStor ca).get depositCountSlot).toNat =
        suffix.length ∧
      (0 < ((future.state.getStor ca).get depositCountSlot).toNat ↔
        suffix ≠ []) ∧
      Acc.root Bytes.sha256 (accOfStor (future.state.getStor ca)) =
        mixedRootOf Bytes.sha256 suffix := by
  rcases reachUsing_future_count_root reach native root.installed_compile
    root.artifact with
    ⟨suffix, artifact, countEq, _monotone, strict, rootEq⟩
  exact ⟨suffix, by simpa only [List.nil_append] using artifact,
    by simpa only [List.length_nil, Nat.zero_add] using countEq,
    by simpa only [List.length_nil] using strict,
    by simpa only [List.nil_append] using rootEq⟩

end Blanc.BeaconDeposit
