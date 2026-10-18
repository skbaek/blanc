import Blanc.Lift.Curve3Pool.CommittedReplay
import Blanc.Lift.Curve3Pool.SpawnKinds
import Blanc.ExecutionWholeFrameAccounting
import Blanc.ExecutionHistoryAdmission
import Blanc.StorageOnlySpec

/-!
# Curve 3pool: the committed-history ladder, over a frame-refinement hypothesis

The pool's storage after any configured history abstracts the model state obtained by replaying,
from the checkpoint's model state, one authentic invocation per *outermost* committed non-static
pool frame, in trace order (design §0.1, §2.1).  The route is the generic whole-frame ladder
(`ExecutionAccountingReplay.wholeFrameLadder`):

* `poolSem`, `pool_spawnKinds'` — the certified runtime as a code semantics; its frames spawn only by
  `CALL`/`STATICCALL`;
* `PoolFrameRefines E` — the per-frame refinement this file consumes as a hypothesis: every
  committed non-static pc-`0` frame of the runtime admitted by `E`, entered at a `Checkpoint`, is
  accepted by `Model.step` with its exact raw effect.  The all-selector frame theorem supplies it, so
  this file does not depend on it;
* `PoolReplay` — the replay carrier over the pool's storage view: from *every* incoming model state
  the view abstracts at a `Checkpoint`, authentic invocations over exactly the given frames replay to
  a state the outgoing view abstracts at a `Checkpoint`.  A pool frame nested inside a guarded frame
  starts with the lock set, so no `Checkpoint` exists at its entry and its obligation is vacuous; it is
  consumed inside its outer frame's step, whose children keep the pool's storage;
* `pool_wholeFrameReplay` — the ladder's whole-frame obligation, from `PoolFrameRefines`;
* `pool_history_committed_with` — the headline;
* `PoolFrameRefinesIn Q`, `pool_history_committed_in` — the same within a model invariant `Q` every
  accepted step keeps (`StepKeeps`): the replay carries `Q`, so the frame refinement is needed only
  on `Q`-states.  `Safe.lean` takes `Q` to fix the coins and the token, which lets the entry
  condition name them as fixed addresses.

The frame contract is the trivial storage-only spec over `poolSem`: the replay carries the
`Checkpoint`, so the contract's own invariant is only that the runtime stays installed.  Static pool
frames observe nothing (`poolFrameObs`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-! ## The code semantics -/

theorem code_toList_length : code.toList.length = 21199 := by
  rw [ByteArray.toList_eq_toList_data, Array.length_toList]
  decide +kernel

theorem code_eq_of_toList {c : ByteArray} (h : some c.toList = some code.toList) : c = code := by
  have dataList : c.data.toList = code.data.toList := by
    simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj h
  exact congrArg ByteArray.mk (Array.toList_inj.mp dataList)

/-- The certified 3pool runtime as a code semantics. -/
def poolSem : CodeSem where
  image := some code.toList
  Run sevm _ _ := sevm.code = code
  correct := fun _ hcode => code_eq_of_toList hcode
  ne_nil := by
    intro l hl h
    have hlen := code_toList_length
    rw [Option.some.inj hl, h] at hlen
    exact absurd hlen (by decide)
  not_delegation := by
    intro c hc hdel
    have hlen : c.toList.length = 21199 := (Option.some.inj hc) ▸ code_toList_length
    rw [ByteArray.toList_eq_toList_data, Array.length_toList] at hlen
    have hsize : c.size = eoaDelegatedCodeLength := hdel.1
    have hsz : c.size = c.data.size := rfl
    rw [hsz, hlen] at hsize
    exact absurd hsize (by decide)

theorem poolSem_image : poolSem.image = some code.toList := rfl

/-- Pool frames spawn only by `CALL`/`STATICCALL`. -/
theorem pool_spawnKinds' (pool : Adr) : SpawnKinds pool poolSem :=
  pool_spawnKinds (fun h => h)

/-- Code installed as the runtime image is the runtime, hence not empty. -/
theorem code_ne_empty_of_image {c : ByteArray} (h : some c.toList = poolSem.image) :
    c ≠ .empty := by
  intro hc
  have hlen := code_toList_length
  rw [← code_eq_of_toList h, hc] at hlen
  exact absurd hlen (by simp only [ByteArray.toList_empty, List.length_nil]; decide)

/-! ## The frame refinement this file consumes -/

/-- **The per-frame refinement hypothesis** (U2(a), parametric).  Every successful, committed,
non-static pc-`0` frame of the runtime on a covered fork, admitted by the entry condition `E`, whose
target carries code and whose storage is at a `Checkpoint` abstracting `s`, is accepted by
`Model.step` on its decoded call and some environment `e`, with the frame's exact raw effect (which
records `EnvOf`). -/
def PoolFrameRefines (E : Sevm → Devm → Prop) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)),
    sevm.code = code → CoveredFork sevm.benvStat.fork → E sevm pre →
    sevm.isStatic = false → pre.getCode sevm.currentTarget ≠ .empty → post.error = none →
    Checkpoint (pre.getStor sevm.currentTarget) s →
    ∃ e o, step s e (decodeCall sevm) = some o ∧ RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o

/-- **The per-frame refinement within a model invariant `Q`**: `PoolFrameRefines` for the frames
whose entry `Checkpoint` abstracts a state satisfying `Q`.  The replay carries `Q` (when every
accepted step keeps it), so an entry condition may name facts `Q` fixes, such as the coins and the
token. -/
def PoolFrameRefinesIn (Q : State → Prop) (E : Sevm → Devm → Prop) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm} {s : State} (exc : Exec 0 sevm pre (.ok post)),
    sevm.code = code → CoveredFork sevm.benvStat.fork → E sevm pre →
    sevm.isStatic = false → pre.getCode sevm.currentTarget ≠ .empty → post.error = none →
    Checkpoint (pre.getStor sevm.currentTarget) s → Q s →
    ∃ e o, step s e (decodeCall sevm) = some o ∧ RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post e o

theorem PoolFrameRefines.toIn {E : Sevm → Devm → Prop} (h : PoolFrameRefines E)
    (Q : State → Prop) : PoolFrameRefinesIn Q E :=
  fun exc hcode hfork he hs hpc herr hck _ => h exc hcode hfork he hs hpc herr hck

/-- A model invariant every accepted step keeps. -/
def StepKeeps (Q : State → Prop) : Prop :=
  ∀ {s : State} {e : Env} {c : Call} {o : Out}, step s e c = some o → Q s → Q o.state

theorem PoolRun.keeps {Q : State → Prop} (hQ : StepKeeps Q) :
    ∀ {s t : State} {invs : List PoolInvocation}, PoolRun s invs t → Q s → Q t
  | _, _, [], h, hs => by
    simp only [PoolRun] at h
    subst h
    exact hs
  | _, _, _ :: _, h, hs => by
    obtain ⟨o, hstep, -, rest⟩ := h
    exact PoolRun.keeps hQ rest (hQ hstep hs)

/-! ## The frame contract -/

/-- The storage-only pool frame contract: only the installed runtime (the replay carries the model
state). -/
def poolSpec : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly poolSem (fun _ => True)

theorem poolSpec_preservesAdmitted (pool : Adr) (E : Sevm → Devm → Prop) :
    poolSpec.PreservesAdmitted pool E :=
  poolSpec.preserves_inv_admitted pool E (fun _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)

/-! ## The `Checkpoint` reads storage only through its words -/

theorem Abstracts.of_get {σ σ' : Stor} {s : State} (h : σ.get = σ'.get) (hs : Abstracts σ s) :
    Abstracts σ' s where
  coins i := by rw [← h]; exact hs.coins i
  balances i := by rw [← h]; exact hs.balances i
  fee := by rw [← h]; exact hs.fee
  adminFee := by rw [← h]; exact hs.adminFee
  owner := by rw [← h]; exact hs.owner
  token := by rw [← h]; exact hs.token
  initialA := by rw [← h]; exact hs.initialA
  futureA := by rw [← h]; exact hs.futureA
  initialATime := by rw [← h]; exact hs.initialATime
  futureATime := by rw [← h]; exact hs.futureATime
  adminActionsDeadline := by rw [← h]; exact hs.adminActionsDeadline
  transferOwnershipDeadline := by rw [← h]; exact hs.transferOwnershipDeadline
  futureFee := by rw [← h]; exact hs.futureFee
  futureAdminFee := by rw [← h]; exact hs.futureAdminFee
  futureOwner := by rw [← h]; exact hs.futureOwner
  isKilled := by rw [← h]; exact hs.isKilled
  killDeadline := by rw [← h]; exact hs.killDeadline

theorem Checkpoint.of_get {σ σ' : Stor} {s : State} (h : σ.get = σ'.get) (hc : Checkpoint σ s) :
    Checkpoint σ' s :=
  ⟨Abstracts.of_get h hc.abs, by rw [← h]; exact hc.unlocked, hc.addr⟩

/-! ## Carrier and observation -/

/-- **Each invocation entered at a `Checkpoint` of the state its prefix reaches**: the frame's
own storage at its entry abstracts the replayed state, unlocked. -/
def PoolEntries : State → List PoolInvocation → Prop
  | _, [] => True
  | s, i :: rest => Checkpoint (i.frame.pre.getStor i.frame.sevm.currentTarget) s ∧
      ∀ o, step s i.env (decodeCall i.frame.sevm) = some o → PoolEntries o.state rest

theorem PoolEntries.append :
    ∀ {s m : State} {left right : List PoolInvocation},
      PoolRun s left m → PoolEntries s left → PoolEntries m right → PoolEntries s (left ++ right)
  | _, _, [], _, h, _, h₂ => by
    simp only [PoolRun] at h
    subst h
    exact h₂
  | _, _, _ :: _, _, h, h₁, h₂ => by
    obtain ⟨o, hstep, -, rest⟩ := h
    exact ⟨h₁.1, fun o' hstep' => by
      cases Option.some.inj (hstep.symm.trans hstep')
      exact PoolEntries.append rest (h₁.2 o hstep) h₂⟩

/-- **An invocation's entry checkpoint**: inside entries of `pre ++ i :: post`, `i`'s frame entered
at a `Checkpoint` of the state `pre` replays to. -/
theorem PoolEntries.split :
    ∀ {s m : State} {pre : List PoolInvocation} {i : PoolInvocation} {post : List PoolInvocation},
      PoolEntries s (pre ++ i :: post) → PoolRun s pre m →
      Checkpoint (i.frame.pre.getStor i.frame.sevm.currentTarget) m
  | _, _, [], _, _, h, hp => by
    simp only [PoolRun] at hp
    subst hp
    exact h.1
  | _, _, _ :: _, _, _, h, hp => by
    obtain ⟨o, hstep, -, rest⟩ := hp
    exact PoolEntries.split (h.2 o hstep) rest

/-- The replay of a list of frames between two storage views: from every model state the incoming
view abstracts at a `Checkpoint`, authentic invocations over exactly these frames, each entered at a
`Checkpoint` of the state its prefix reaches, replay to a state the outgoing view abstracts at a
`Checkpoint`. -/
def PoolReplay (Q : State → Prop) (pool : Adr) (a : B256 → B256) (frames : List Exec.Frame)
    (b : B256 → B256) : Prop :=
  ∀ (s : State) (σ : Stor), σ.get = a → Checkpoint σ s → Q s →
    ∃ invs : List PoolInvocation, invs.map PoolInvocation.frame = frames ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s', PoolRun s invs s' ∧ PoolEntries s invs ∧
        ∃ σ' : Stor, σ'.get = b ∧ Checkpoint σ' s' ∧ Q s'

theorem PoolReplay.nil {Q : State → Prop} {pool : Adr} (view : B256 → B256) :
    PoolReplay Q pool view [] view := by
  intro s σ hview hc hq
  exact ⟨[], rfl, fun _ h => absurd h List.not_mem_nil, s, PoolRun.nil s, trivial, σ, hview, hc,
    hq⟩

theorem PoolReplay.append {Q : State → Prop} {pool : Adr} {a b c : B256 → B256}
    {left right : List Exec.Frame}
    (first : PoolReplay Q pool a left b) (second : PoolReplay Q pool b right c) :
    PoolReplay Q pool a (left ++ right) c := by
  intro s σ hview hc hq
  obtain ⟨invs₁, frames₁, auth₁, m, run₁, ent₁, σ₁, view₁, hc₁, hq₁⟩ := first s σ hview hc hq
  obtain ⟨invs₂, frames₂, auth₂, t, run₂, ent₂, σ₂, view₂, hc₂, hq₂⟩ := second m σ₁ view₁ hc₁ hq₁
  refine ⟨invs₁ ++ invs₂, ?_, ?_, t, run₁.append run₂, PoolEntries.append run₁ ent₁ ent₂, σ₂, view₂,
    hc₂, hq₂⟩
  · rw [List.map_append, frames₁, frames₂]
  · intro i member
    rcases List.mem_append.mp member with h | h
    · exact auth₁ i h
    · exact auth₂ i h

/-- The pool's replay carrier over its storage view. -/
def poolCarrier (Q : State → Prop) (pool : Adr) : ReplayCarrier pool where
  Snap := B256 → B256
  Step := Exec.Frame
  Tag := Unit
  Replay := PoolReplay Q pool
  ofState world := (world.getStor pool).get
  frameEntry _ world := (world.getStor pool).get
  nil := PoolReplay.nil
  readsStorage := true
  silent := fun storage _ => by rw [storage rfl]
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], by rw [storage]; exact PoolReplay.nil _⟩
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    exact congrArg Stor.get
      (benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
        (fun h1 _ => Or.inl (caller_ne h1)))

/-- A frame's own observation: itself when it is a non-static pool frame. -/
def poolFrameObs (pool : Adr) (f : Exec.Frame) : List Exec.Frame :=
  if f.sevm.currentTarget = pool ∧ f.sevm.isStatic = false then [f] else []

/-- The committed non-static pool frames of a frame's subtree, in execution order. -/
def poolSubtreeFrames (pool : Adr) (f : Exec.Frame) : List Exec.Frame :=
  (Exec.committedFrames f.run).flatMap (poolFrameObs pool)

/-- The settlement-committed non-static pool frames of a history, in trace order. -/
def committedPoolFrames {cfg : ChainConfig} {checkpoint future : BlockChain} (pool : Adr)
    (trace : ConfiguredHistoryTrace cfg checkpoint future) : List Exec.Frame :=
  trace.settledFrames.flatMap (poolFrameObs pool)

theorem poolFrameObs_static {pool : Adr} {f : Exec.Frame} (h : f.sevm.isStatic = true) :
    poolFrameObs pool f = [] := by
  unfold poolFrameObs
  simp only [h, Bool.true_eq_false, and_false, ↓reduceIte]

theorem poolFrameObs_foreign {pool : Adr} {f : Exec.Frame}
    (h : f.sevm.currentTarget ≠ pool) : poolFrameObs pool f = [] := by
  unfold poolFrameObs
  simp only [h, false_and, ↓reduceIte]

/-- The pool's observation: every committed non-static pool frame of each step's subtree. -/
def poolObservation (Q : State → Prop) (pool : Adr) : ReplayObservation (poolCarrier Q pool) where
  O := Exec.Frame
  obs frames := frames.flatMap (poolSubtreeFrames pool)
  obs_nil := rfl
  obs_append := fun _ _ => List.flatMap_append
  frameObs := poolFrameObs pool
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    change PoolReplay Q pool (pre.getStor pool).get [] (post.getStor pool).get
    rw [storage]
    exact PoolReplay.nil _

/-! ## The whole-frame obligation and the ladder -/

/-- **The whole-frame obligation of the pool**: a committed non-static pool frame replays as one
authentic invocation whose observation is its committed subtree. -/
theorem pool_wholeFrameReplay {Q : State → Prop} {E : Sevm → Devm → Prop}
    (hQ : StepKeeps Q) (refines : PoolFrameRefinesIn Q E) (pool : Adr) :
    Exec.CoreAccounting.WholeFrameReplay pool poolSem E (poolCarrier Q pool)
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

/-- **The accounting ladder of the pool**, over the frame refinement. -/
def poolLadder {Q : State → Prop} {E : Sevm → Devm → Prop} (hQ : StepKeeps Q)
    (refines : PoolFrameRefinesIn Q E) (pool : Adr) :
    AccountingLadderAdmitted poolSpec pool E :=
  wholeFrameLadder (c := poolSpec) (poolCarrier Q pool) (poolObservation Q pool)
    PoolReplay.append (fun _ _ => ()) (fun _ _ => ()) (fun _ _ => rfl)
    (fun h => funext h) (fun _ h => poolFrameObs_static h)
    (fun _ h => poolFrameObs_foreign h) (pool_spawnKinds' pool)
    (pool_wholeFrameReplay hQ refines pool) (poolSpec_preservesAdmitted pool E)

/-! ## The committed history -/

/-- **The committed history with entry checkpoints**: `pool_history_committed_in`'s conclusion,
and every invocation entered at a `Checkpoint` of the state its prefix replays to
(`PoolEntries`). -/
theorem pool_history_committed_entries {Q : State → Prop} {E : Sevm → Devm → Prop}
    (hQ : StepKeeps Q) (refines : PoolFrameRefinesIn Q E)
    {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (inv : Q s₀)
    (admitted : trace.FrameAdmitted pool E) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧ PoolEntries s₀ invs ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token ∧
        Q s := by
  have start : poolSpec.StateInv pool checkpoint.state := ⟨installed, trivial, trivial⟩
  have finishInv := trace.stateInv_admitted_sem (poolSpec_preservesAdmitted pool E) admitted start
  obtain ⟨frames, replay, observed⟩ :=
    (poolLadder hQ refines pool).configuredHistory trace admitted start
  change PoolReplay Q pool (checkpoint.state.getStor pool).get frames
    (future.state.getStor pool).get at replay
  change frames.flatMap (poolSubtreeFrames pool) =
    trace.settledFrames.flatMap (poolFrameObs pool) at observed
  obtain ⟨invs, framesEq, auth, s, run, entries, σ', view, hc, hq⟩ := replay s₀ _ rfl initial inv
  obtain ⟨hcoins, htoken⟩ := run.coins_token
  refine ⟨finishInv.code, invs, ?_, auth, entries, s, run, run.runPool_eq,
    Checkpoint.of_get view hc, hcoins, htoken, hq⟩
  rw [← framesEq, List.flatMap_map] at observed
  exact observed

/-- **The committed history within a model invariant `Q`** (the general form of
`pool_history_committed_with`): when every accepted step keeps `Q` and the checkpoint's model state
satisfies it, a frame refinement on the `Q`-states suffices, and the replay ends in a `Q`-state. -/
theorem pool_history_committed_in {Q : State → Prop} {E : Sevm → Devm → Prop}
    (hQ : StepKeeps Q) (refines : PoolFrameRefinesIn Q E)
    {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀) (inv : Q s₀)
    (admitted : trace.FrameAdmitted pool E) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token ∧
        Q s := by
  obtain ⟨code, invs, obs, auth, -, rest⟩ :=
    pool_history_committed_entries hQ refines trace installed initial inv admitted
  exact ⟨code, invs, obs, auth, rest⟩

/-- **The pool model replays the committed history (U2(b)), over a frame refinement.**  In a
configured history from a checkpoint with the runtime installed at `pool` and the pool's storage at
a `Checkpoint` abstracting `s₀`, whose pool frames are admitted by an entry condition `E` under
which every pool frame refines the model (`PoolFrameRefines E`), the runtime is still installed, and
there is a list of invocations such that

* flattening each invocation's committed subtree gives *exactly* the settlement-committed
  non-static pool frames of the trace, in trace order (rolled-back frames are absent, static frames
  observe nothing): each invocation is an outermost committed pool frame, and every nested pool frame
  lies in exactly one invocation's subtree;
* every invocation is authentic (`PoolInvocation.Authentic`: committed, non-static, pc `0`, at the
  pool, with `EnvOf` evidence for its recorded environment);
* the invocations replay through `Model.step` from `s₀` (`PoolRun`, hence the deterministic fold
  `runPool`) to a state `s` that the future pool storage abstracts at a `Checkpoint`, with the coins
  and the token unchanged. -/
theorem pool_history_committed_with {E : Sevm → Devm → Prop} (refines : PoolFrameRefines E)
    {pool : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain} {s₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (admitted : trace.FrameAdmitted pool E) :
    some (future.state.getCode pool).toList = poolSem.image ∧
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      ∃ s, PoolRun s₀ invs s ∧ runPool s₀ invs = some s ∧
        Checkpoint (future.state.getStor pool) s ∧ s.coins = s₀.coins ∧ s.token = s₀.token := by
  obtain ⟨code, invs, obs, auth, s, run, fold, hc, hcoins, htoken, -⟩ :=
    pool_history_committed_in (Q := fun _ => True) (fun _ _ => trivial)
      (@PoolFrameRefines.toIn E refines _) trace installed initial trivial admitted
  exact ⟨code, invs, obs, auth, s, run, fold, hc, hcoins, htoken⟩

end Blanc.Lift.Curve3Pool
