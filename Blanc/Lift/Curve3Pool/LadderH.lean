import Blanc.Lift.Curve3Pool.RuntimeSafety
import Blanc.ExecutionWholeFrameAccountingIn
import Blanc.ExecutionMidHistoryInFacts
import Blanc.ExecutionRewardCredits
import Blanc.ExecutionTraceSettledForest

/-!
# Curve 3pool: the committed history over historical forks, over a frame refinement

`Ladder.lean` over `MidHistoryTraceIn HistFork`, the shape that starts right after the pool's
creation transaction. The carrier and the observation are the modern ones; only the fork premise of
the refinement and the ladder's domain change.

* `PoolFrameRefinesInH` — the refinement this file consumes, at `HistFork`, at the frames `A` allows;
* `poolCarrierIf`, `poolObservationIf` — the pool's replay, claimed when `A` holds of every frame it
  observes. So `A` is only ever asked of frames that settle: a frame inside a reverted parent is not observed;
* `poolLadderH` — the ladder, from `wholeFrameLadderIn`;
* `committedPoolFramesMid`, `pool_mid_history_entries` — the replay, over exactly the settled
  non-static pool frames of the mid history.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- `PoolFrameRefinesIn` at the historical fork domain, at a frame `A` allows. -/
def PoolFrameRefinesInH (Q : State → Prop) (E : Sevm → Devm → Prop) (A : Exec.Frame → Prop) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true),
    sevm.code = code → HistFork sevm.benvStat.fork → E sevm pre →
    sevm.isStatic = false → pre.getCode sevm.currentTarget ≠ .empty → post.error = none →
    Checkpoint (pre.getStor sevm.currentTarget) s → Q s → A (Exec.Frame.ofRun exc committed) →
    ∃ e o, step s e (decodeCall sevm) = some o ∧ RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o

theorem poolSpec_preservesAdmittedH (pool : Adr) (E : Sevm → Devm → Prop) :
    poolSpec.PreservesAdmittedIn HistFork pool E :=
  ContractSpecSem.preserves_inv_admittedIn HistFork HistFork.stateGas_none poolSpec pool E
    (fun _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)

/-- `PoolReplay`, claimed when `A` holds of every frame the steps observe. -/
def PoolReplayIf (Q : State → Prop) (pool : Adr) (A : Exec.Frame → Prop) (a : B256 → B256)
    (frames : List Exec.Frame) (b : B256 → B256) : Prop :=
  (∀ f ∈ frames.flatMap (poolSubtreeFrames pool), A f) → PoolReplay Q pool a frames b

theorem PoolReplayIf.append {Q : State → Prop} {pool : Adr} {A : Exec.Frame → Prop} {a b c : B256 → B256}
    {left right : List Exec.Frame} (first : PoolReplayIf Q pool A a left b)
    (second : PoolReplayIf Q pool A b right c) : PoolReplayIf Q pool A a (left ++ right) c := fun all =>
  (first fun f hf => all f (by rw [List.flatMap_append]; exact List.mem_append_left _ hf)).append
    (second fun f hf => all f (by rw [List.flatMap_append]; exact List.mem_append_right _ hf))

/-- `poolCarrier`, with the replay claimed at the frames `A` allows. -/
def poolCarrierIf (Q : State → Prop) (pool : Adr) (A : Exec.Frame → Prop) : ReplayCarrier pool :=
  { poolCarrier Q pool with
    Replay := PoolReplayIf Q pool A
    nil := fun view _ => PoolReplay.nil view
    credit := by
      intro _ pre post _ storage _ _
      refine ⟨[], fun _ => ?_⟩
      change PoolReplay Q pool (pre.getStor pool).get [] (post.getStor pool).get
      rw [storage]
      exact PoolReplay.nil _ }

/-- `poolObservation` over `poolCarrierIf`. -/
def poolObservationIf (Q : State → Prop) (pool : Adr) (A : Exec.Frame → Prop) :
    ReplayObservation (poolCarrierIf Q pool A) where
  O := Exec.Frame
  obs frames := frames.flatMap (poolSubtreeFrames pool)
  obs_nil := rfl
  obs_append := fun _ _ => List.flatMap_append
  frameObs := poolFrameObs pool
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], fun _ => ?_, rfl⟩
    change PoolReplay Q pool (pre.getStor pool).get [] (post.getStor pool).get
    rw [storage]
    exact PoolReplay.nil _

/-- The whole-frame obligation at the historical domain. -/
theorem pool_wholeFrameReplayH {Q : State → Prop} {E : Sevm → Devm → Prop} {A : Exec.Frame → Prop}
    (hQ : StepKeeps Q) (refines : PoolFrameRefinesInH Q E A) (pool : Adr) :
    Exec.CoreAccounting.WholeFrameReplayIn HistFork pool poolSem E (poolCarrierIf Q pool A)
      (poolObservationIf Q pool A) := by
  intro sevm pre post run committed codeEq target fork installed admitted _ nonstatic
  subst target
  have entry := admitted.root rfl
  have hpc : pre.getCode sevm.currentTarget ≠ .empty := code_ne_empty_of_image installed.1
  have herr : post.error = none := by
    simpa only [Execution.commits, Option.isNone_iff_eq_none] using committed
  refine ⟨[Exec.Frame.ofRun run committed], ?_, ?_⟩
  · intro all s σ hview hc hq
    have hc' : Checkpoint (pre.getStor sevm.currentTarget) s := Checkpoint.of_get hview hc
    have allowed : A (Exec.Frame.ofRun run committed) := all _ (by
      refine List.mem_flatMap.mpr ⟨_, List.mem_singleton.mpr rfl, ?_⟩
      unfold poolSubtreeFrames
      rw [Blanc.Exec.Frame.committedFrames_self, List.flatMap_cons]
      refine List.mem_append_left _ ?_
      rw [poolFrameObs, if_pos ⟨rfl, nonstatic⟩]
      exact List.mem_singleton.mpr rfl)
    obtain ⟨e, o, hstep, hraw⟩ := refines run committed codeEq fork entry nonstatic hpc herr hc' hq allowed
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
def poolLadderH {Q : State → Prop} {E : Sevm → Devm → Prop} {A : Exec.Frame → Prop} (hQ : StepKeeps Q)
    (refines : PoolFrameRefinesInH Q E A) (pool : Adr) :
    AccountingLadderAdmittedIn HistFork poolSpec pool E :=
  wholeFrameLadderIn HistFork.stateGas_none (c := poolSpec) (poolCarrierIf Q pool A)
    (poolObservationIf Q pool A)
    PoolReplayIf.append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => funext h) (fun _ h => poolFrameObs_static h)
    (fun _ h => poolFrameObs_foreign h)
    (pool_wholeFrameReplayH hQ refines pool) (poolSpec_preservesAdmittedH pool E)

/-- A frame a list's pool observation names is in the list, at the pool. -/
theorem mem_flatMap_poolFrameObs {pool : Adr} {fs : List Exec.Frame} {f : Exec.Frame}
    (member : f ∈ fs.flatMap (poolFrameObs pool)) : f ∈ fs ∧ f.sevm.currentTarget = pool := by
  obtain ⟨g, hg, hf⟩ := List.mem_flatMap.mp member
  unfold poolFrameObs at hf
  split at hf
  · rename_i h
    rw [List.mem_singleton] at hf
    subst hf
    exact ⟨hg, h.1⟩
  · exact absurd hf List.not_mem_nil

/-- The settlement-committed non-static pool frames of a mid history, in trace order. -/
def committedPoolFramesMid {cfg : ChainConfig} {start : Benv} {future : BlockChain} (pool : Adr)
    (trace : MidHistoryTraceIn HistFork cfg start future) : List Exec.Frame :=
  trace.settledFrames.flatMap (poolFrameObs pool)

/-- **The committed mid history with entry checkpoints.** -/
theorem pool_mid_history_entries {Q : State → Prop} {E : Sevm → Devm → Prop} {A : Exec.Frame → Prop}
    (hQ : StepKeeps Q) (refines : PoolFrameRefinesInH Q E A)
    {pool : Adr} {cfg : ChainConfig} {start : Benv} {future : BlockChain} {s₀ : State}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (installed : some (start.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (start.state.getStor pool) s₀) (inv : Q s₀)
    (admitted : trace.FrameAdmitted pool E)
    (allowed : ∀ f ∈ trace.settledFrames, f.sevm.currentTarget = pool → A f) :
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
  change PoolReplayIf Q pool A (start.state.getStor pool).get frames
    (future.state.getStor pool).get at replay
  change frames.flatMap (poolSubtreeFrames pool) =
    trace.settledFrames.flatMap (poolFrameObs pool) at observed
  obtain ⟨invs, framesEq, auth, s, run, entries, σ', view, hc, hq⟩ := replay (fun f hf => by
    rw [observed] at hf
    obtain ⟨member, target⟩ := mem_flatMap_poolFrameObs hf
    exact allowed f member target) s₀ _ rfl initial inv
  obtain ⟨hcoins, htoken⟩ := run.coins_token
  refine ⟨finishInv.code, invs, ?_, auth, entries, s, run, run.runPool_eq,
    Checkpoint.of_get view hc, hcoins, htoken, hq⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

end Blanc.Lift.Curve3Pool
