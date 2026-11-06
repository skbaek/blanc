import Blanc.Lift.Curve3Pool.RuntimeSafety
import Blanc.ExecutionWholeFrameAccountingIn
import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionRewardCredits

/-!
# Curve 3pool: the committed history over historical forks, over a frame refinement

`Ladder.lean` over `MidHistoryTraceIn HistFork`, the shape that starts right after the pool's
creation transaction. The carrier and the observation are the modern ones; only the fork premise of
the refinement and the ladder's domain change.

* `PoolFrameRefinesInH` — the refinement this file consumes, at `HistFork`;
* `poolLadderH` — the ladder, from `wholeFrameLadderIn`;
* `committedPoolFramesMid`, `pool_mid_history_entries` — the replay, over exactly the settled
  non-static pool frames of the mid history.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- `PoolFrameRefinesIn` at the historical fork domain. -/
def PoolFrameRefinesInH (Q : State → Prop) (E : Sevm → Devm → Prop) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)),
    sevm.code = code → HistFork sevm.benvStat.fork → E sevm pre →
    sevm.isStatic = false → pre.getCode sevm.currentTarget ≠ .empty → post.error = none →
    Checkpoint (pre.getStor sevm.currentTarget) s → Q s →
    ∃ e o, step s e (decodeCall sevm) = some o ∧ RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o

theorem poolSpec_preservesAdmittedH (pool : Adr) (E : Sevm → Devm → Prop) :
    poolSpec.PreservesAdmittedIn HistFork pool E :=
  ContractSpecSem.preserves_inv_admittedIn HistFork HistFork.stateGas_none poolSpec pool E
    (fun _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)

/-- The whole-frame obligation at the historical domain. -/
theorem pool_wholeFrameReplayH {Q : State → Prop} {E : Sevm → Devm → Prop}
    (hQ : StepKeeps Q) (refines : PoolFrameRefinesInH Q E) (pool : Adr) :
    Exec.CoreAccounting.WholeFrameReplayIn HistFork pool poolSem E (poolCarrier Q pool)
      (poolObservation Q pool) := by
  intro sevm pre post run committed codeEq target fork installed admitted _ nonstatic
  subst target
  have entry := admitted.root rfl
  have hpc : pre.getCode sevm.currentTarget ≠ .empty := code_ne_empty_of_image installed.1
  have herr : post.error = none := by
    simpa only [Execution.commits, Option.isNone_iff_eq_none] using committed
  refine ⟨[Exec.Frame.ofRun run committed], ?_, ?_⟩
  · intro s σ hview hc hq
    have hc' : Checkpoint (pre.getStor sevm.currentTarget) s := Checkpoint.of_get hview hc
    obtain ⟨e, o, hstep, hraw⟩ := refines run codeEq fork entry nonstatic hpc herr hc' hq
    obtain ⟨hpost, -⟩ := rawEffect_refines (D := ⟨0, sevm, pre, .ok post, run⟩) hc' hstep hraw
    refine ⟨[⟨Exec.Frame.ofRun run committed, e⟩], rfl, ?_, o.state,
      ⟨o, hstep, hraw, rfl⟩, ⟨hc', fun _ _ => trivial⟩, _, rfl, hpost, hQ hstep hq⟩
    intro i member
    rw [List.mem_singleton] at member
    subst member
    exact ⟨rfl, committed, rfl, nonstatic, hraw.env⟩
  · change [Exec.Frame.ofRun run committed].flatMap (poolSubtreeFrames sevm.currentTarget) = _
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl

/-- **The accounting ladder of the pool over historical forks.** -/
def poolLadderH {Q : State → Prop} {E : Sevm → Devm → Prop} (hQ : StepKeeps Q)
    (refines : PoolFrameRefinesInH Q E) (pool : Adr) :
    AccountingLadderAdmittedIn HistFork poolSpec pool E :=
  wholeFrameLadderIn HistFork.stateGas_none (c := poolSpec) (poolCarrier Q pool)
    (poolObservation Q pool)
    PoolReplay.append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => funext h) (fun _ h => poolFrameObs_static h)
    (fun _ h => poolFrameObs_foreign h)
    (pool_wholeFrameReplayH hQ refines pool) (poolSpec_preservesAdmittedH pool E)

/-- The settlement-committed non-static pool frames of a mid history, in trace order. -/
def committedPoolFramesMid {cfg : ChainConfig} {start : Benv} {future : BlockChain} (pool : Adr)
    (trace : MidHistoryTraceIn HistFork cfg start future) : List Exec.Frame :=
  trace.settledFrames.flatMap (poolFrameObs pool)

/-- **The committed mid history with entry checkpoints.** -/
theorem pool_mid_history_entries {Q : State → Prop} {E : Sevm → Devm → Prop}
    (hQ : StepKeeps Q) (refines : PoolFrameRefinesInH Q E)
    {pool : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain} {s₀ : State}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (start.state.getStor pool) s₀) (inv : Q s₀)
    (admitted : trace.FrameAdmitted pool E) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFramesMid pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧ PoolEntries s₀ invs ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token ∧
        Q s := by
  have capabilities := BodyStageCapabilities.historical
  have start' : poolSpec.StateInv pool start.state := ⟨installed, trivial, trivial⟩
  have rewards := trace.rewardCreditsFunded capabilities
  have finishInv := trace.stateInv_admitted_semIn (poolSpec_preservesAdmittedH pool E) capabilities
    admitted rewards start' pool_runtimeSafety rfl
  obtain ⟨frames, replay, observed⟩ :=
    (poolLadderH hQ refines pool).midHistoryIn trace admitted capabilities rewards start'
      pool_runtimeSafety rfl
  change PoolReplay Q pool (start.state.getStor pool).get frames
    (future.state.getStor pool).get at replay
  change frames.flatMap (poolSubtreeFrames pool) =
    trace.settledFrames.flatMap (poolFrameObs pool) at observed
  obtain ⟨invs, framesEq, auth, s, run, entries, σ', view, hc, hq⟩ := replay s₀ _ rfl initial inv
  obtain ⟨hcoins, htoken⟩ := run.coins_token
  refine ⟨finishInv.code, invs, ?_, auth, entries, s, run, run.runPool_eq,
    Checkpoint.of_get view hc, hcoins, htoken, hq⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

end Blanc.Lift.Curve3Pool
