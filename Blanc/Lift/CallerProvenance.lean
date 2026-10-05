import Blanc.ExecutionTraceSettledFrames
import Blanc.LadderBase

/-!
# Who called a committed frame: a fold over parents

Every recursive child frame either receives its parent's current target as caller, or keeps the
parent's current target as its own (`Evm.step_spawn_child_caller`).  So a committed frame that runs at
`ca` with caller `p` (`p ≠ ca`) was spawned either by a frame running at `p`, or by a frame running at
`ca` itself, or it is a message root.  This module folds that over committed frames:

* `Exec.childFrames run` — the direct, settlement-committed children of one frame (the same list as
  `Exec.descendantFrames` without descending into the children);
* `Exec.committedFrames_callerTarget` — if every direct child of a frame at `p` has a property `Q`
  whenever it runs at `ca` with caller `p` (`CallerTarget p ca Q`), and every direct child of a frame
  at `ca` that stays at `ca` is not called by `p`, then every committed frame of the derivation that
  runs at `ca` with caller `p` has `Q`, given the root does;
* `settledRoots` along every trace layer, with `settledFrames = settledRoots.flatMap committedFrames`,
  and the configured-history form `ConfiguredHistoryTrace.settledFrames_callerTarget`.

The fold is contract-neutral: `p`, `ca` and `Q` are arbitrary.
-/

namespace Blanc

open Jaune

/-- The direct children of a frame whose settlement commits, in execution order.  Unlike
`Exec.descendantFrames`, a child's own descendants are not listed. -/
def Exec.childFrames {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.childFrames next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.childFrames next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      (if h : Frame.settlementCommits frame raw = true then
        [Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits h)] else []) ++
        Exec.childFrames next

/-- A spawned child either receives the parent's current target as caller or keeps the parent's
current target. -/
theorem Evm.step_spawn_child_caller {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {f : Frame} {rsm : Resume} {cevm : Evm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc') (henter : f.enter = .run cevm) :
    cevm.sta.caller = sevm.currentTarget ∨ cevm.sta.currentTarget = sevm.currentTarget := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hstep
  have hcaller : cevm.sta.caller = f.inner.caller := by
    obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv henter
    rfl
  rw [hcaller, Frame.enter_run_currentTarget henter]
  exact Xinst.step_spawn_caller_eq_parent_or_target_eq_parent hx

/-- The fold's target property: a frame that runs at `ca` with caller `p` satisfies `Q`. -/
def CallerTarget (p ca : Adr) (Q : Sevm → Prop) (s : Sevm) : Prop :=
  s.currentTarget = ca → s.caller = p → Q s

/-- The parent-level obligations of the fold at one frame `sevm` with direct children `cs`. -/
def CallerIssuers (p ca : Adr) (Q : Sevm → Prop) (sevm : Sevm) (cs : List Exec.Frame) : Prop :=
  (sevm.currentTarget = p → ∀ c ∈ cs, CallerTarget p ca Q c.sevm) ∧
    (sevm.currentTarget = ca → ∀ c ∈ cs, c.sevm.currentTarget = ca → c.sevm.caller ≠ p)

theorem Exec.descendantFrames_callerTarget {p ca : Adr} {Q : Sevm → Prop} :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      CallerIssuers p ca Q sevm (Exec.childFrames run) →
      (∀ G ∈ Exec.descendantFrames run, CallerIssuers p ca Q G.sevm (Exec.childFrames G.run)) →
      ∀ F ∈ Exec.descendantFrames run, CallerTarget p ca Q F.sevm := by
  intro pc sevm pre out run
  induction run with
  | halt _ =>
      intro _ _ F member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont _ next ih =>
      intro here below
      simp only [Exec.descendantFrames, Exec.childFrames] at here below ⊢
      exact ih here below
  | doneErr _ _ _ =>
      intro _ _ F member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk _ _ _ next ih =>
      intro here below
      simp only [Exec.descendantFrames, Exec.childFrames] at here below ⊢
      exact ih here below
  | runErr _ _ _ _ =>
      intro _ _ F member
      simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | runOk hstep henter child hresume next childIh nextIh =>
      rename_i nodePc nodeSevm nodePre frame rsm nextPc cevm raw inter final
      intro here below
      by_cases hs : Frame.settlementCommits frame raw = true
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.Frame.ofRun child (Frame.raw_commits_of_settlementCommits hs) ::
              Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_left hs, List.singleton_append]
        rw [hchildren] at here
        rw [Exec.descendantFrames_runOk_of_settlementCommits hstep henter child hresume next hs]
          at below ⊢
        have childOk : CallerTarget p ca Q cevm.sta := by
          intro target caller
          rcases Evm.step_spawn_child_caller hstep henter with h | h
          · exact here.1 (h ▸ caller) _ List.mem_cons_self target caller
          · exact (here.2 (h ▸ target) _ List.mem_cons_self target caller).elim
        have childBelow := below _ List.mem_cons_self
        intro F member
        simp only [List.mem_cons, List.mem_append] at member
        rcases member with (hF | inChild) | inNext
        · rw [hF]
          exact childOk
        · exact childIh childBelow
            (fun G hG => below G (List.mem_cons_of_mem _ (List.mem_append_left _ hG))) F inChild
        · exact nextIh ⟨fun t c hc => here.1 t c (List.mem_cons_of_mem _ hc),
              fun t c hc => here.2 t c (List.mem_cons_of_mem _ hc)⟩
            (fun G hG => below G (List.mem_cons_of_mem _ (List.mem_append_right _ hG))) F inNext
      · have hchildren : Exec.childFrames (Exec.runOk hstep henter child hresume next) =
            Exec.childFrames next := by
          simp only [Exec.childFrames, dite_eq_right hs, List.nil_append]
        rw [hchildren] at here
        rw [Exec.descendantFrames_runOk_of_not_settlementCommits hstep henter child hresume next hs]
          at below ⊢
        exact nextIh here below

/-- **The fold over one committed derivation.**  If the root satisfies the target property, and every
committed frame meets the parent obligations (`CallerIssuers`), every committed frame satisfies the
target property. -/
theorem Exec.committedFrames_callerTarget {p ca : Adr} {Q : Sevm → Prop}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
    (root : CallerTarget p ca Q sevm)
    (issuers : ∀ G ∈ Exec.committedFrames run, CallerIssuers p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ F ∈ Exec.committedFrames run, CallerTarget p ca Q F.sevm := by
  unfold Exec.committedFrames at issuers ⊢
  split
  · rename_i committed
    rw [dite_eq_left committed] at issuers
    intro F member
    rcases List.mem_cons.mp member with rfl | below
    · exact root
    · exact Exec.descendantFrames_callerTarget run (issuers _ List.mem_cons_self)
        (fun G hG => issuers G (List.mem_cons_of_mem _ hG)) F below
  · intro F member
    simp only [List.not_mem_nil] at member

/-- The fold over a list of committed roots. -/
theorem Exec.Frame.roots_callerTarget {p ca : Adr} {Q : Sevm → Prop} (roots : List Exec.Frame)
    (rootOk : ∀ R ∈ roots, CallerTarget p ca Q R.sevm)
    (issuers : ∀ G ∈ roots.flatMap (fun R => Exec.committedFrames R.run),
      CallerIssuers p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ F ∈ roots.flatMap (fun R => Exec.committedFrames R.run), CallerTarget p ca Q F.sevm := by
  intro F member
  obtain ⟨R, hR, inR⟩ := List.mem_flatMap.mp member
  exact Exec.committedFrames_callerTarget R.run (rootOk R hR)
    (fun G hG => issuers G (List.mem_flatMap.mpr ⟨R, hR, hG⟩)) F inR

namespace ExecutionTrace

/-! ## The message roots of every trace layer -/

/-- The committed root of a retained slot. -/
def RetainedXlot.settledRoots {slot : Xlot} : RetainedXlot slot → List Exec.Frame
  | .none => []
  | .some (out := out) run =>
      if h : Execution.commits out = true then [Exec.Frame.ofRun run h] else []

def ProcessMessageTrace.settledRoots
    (trace : ProcessMessageTrace msg out) : List Exec.Frame :=
  match trace with
  | ⟨_, .none, _⟩ => []
  | ⟨_, @RetainedXlot.some pc sevm pre raw run, _⟩ =>
      if Frame.settlementCommits (Frame.ofCall msg) raw = true then
        (RetainedXlot.some run).settledRoots
      else []

def ProcessCreateMessageTrace.settledRoots
    (trace : ProcessCreateMessageTrace msg out) : List Exec.Frame :=
  match trace with
  | ⟨_, .none, _⟩ => []
  | ⟨_, @RetainedXlot.some pc sevm pre raw run, _⟩ =>
      if Frame.settlementCommits (Frame.ofCreate msg) raw = true then
        (RetainedXlot.some run).settledRoots
      else []

def MessageCallTrace.settledRoots :
    MessageCallTrace msg state out → List Exec.Frame
  | .createCollision .. => []
  | .createRun _ _ _ _core trace _ => trace.settledRoots
  | .callRun _ _ _ _ _ _ _ _core trace _ => trace.settledRoots

def TransactionTrace.settledRoots
    (trace : TransactionTrace benv bout tx index state bout') : List Exec.Frame :=
  trace.message.settledRoots

def ApplyTransactionsTrace.settledRoots :
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → List Exec.Frame
  | .nil _ _ => []
  | .cons head tail => head.settledRoots ++ tail.settledRoots

def SystemMessageTrace.settledRoots
    (trace : SystemMessageTrace benv target data state out) : List Exec.Frame :=
  trace.message.settledRoots

def RequestsTrace.settledRoots
    (trace : RequestsTrace benv bout state bout') : List Exec.Frame :=
  trace.withdrawal.settledRoots ++ trace.consolidation.settledRoots

def AppliedBodyTrace.settledRoots
    (trace : AppliedBodyTrace benv txs wds state bout) : List Exec.Frame :=
  trace.beacon.settledRoots ++ trace.history.settledRoots ++
    trace.transactions.settledRoots ++ trace.requests.settledRoots

def ConfiguredBlockTrace.settledRoots
    (trace : ConfiguredBlockTrace cfg pre post) : List Exec.Frame :=
  trace.bodyTrace.settledRoots

/-- The settled message roots of a configured history, in execution order. -/
def ConfiguredHistoryTrace.settledRoots :
    ConfiguredHistoryTrace cfg checkpoint future → List Exec.Frame
  | .refl _ _ _ => []
  | .step prior block => prior.settledRoots ++ block.settledRoots

/-- The committed frames below a list of roots. -/
abbrev rootFrames (roots : List Exec.Frame) : List Exec.Frame :=
  roots.flatMap fun R => Exec.committedFrames R.run

theorem RetainedXlot.settledFrames_eq {slot : Xlot} (retained : RetainedXlot slot) :
    retained.settledFrames = rootFrames retained.settledRoots := by
  cases retained with
  | none => rfl
  | some run =>
      simp only [RetainedXlot.settledFrames, RetainedXlot.settledRoots]
      split
      · simp only [rootFrames, List.flatMap_cons, List.flatMap_nil, List.append_nil]
        rfl
      · rename_i h
        simp only [rootFrames, List.flatMap_nil, Exec.committedFrames, dite_eq_right h]

theorem ProcessMessageTrace.settledFrames_eq (trace : ProcessMessageTrace msg out) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  rcases trace with ⟨_, _ | run, _⟩
  · rfl
  · simp only [ProcessMessageTrace.settledFrames, ProcessMessageTrace.settledRoots]
    split
    · exact (RetainedXlot.some run).settledFrames_eq
    · rfl

theorem ProcessCreateMessageTrace.settledFrames_eq (trace : ProcessCreateMessageTrace msg out) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  rcases trace with ⟨_, _ | run, _⟩
  · rfl
  · simp only [ProcessCreateMessageTrace.settledFrames, ProcessCreateMessageTrace.settledRoots]
    split
    · exact (RetainedXlot.some run).settledFrames_eq
    · rfl

theorem MessageCallTrace.settledFrames_eq (trace : MessageCallTrace msg state out) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  cases trace with
  | createCollision => rfl
  | createRun _ _ _ _ trace _ => exact trace.settledFrames_eq
  | callRun _ _ _ _ _ _ _ _ trace _ => exact trace.settledFrames_eq

theorem TransactionTrace.settledFrames_eq
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.settledFrames = rootFrames trace.settledRoots :=
  trace.message.settledFrames_eq

theorem ApplyTransactionsTrace.settledFrames_eq
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  induction trace with
  | nil => rfl
  | cons head tail ih =>
      simp only [ApplyTransactionsTrace.settledFrames, ApplyTransactionsTrace.settledRoots,
        rootFrames, List.flatMap_append]
      rw [head.settledFrames_eq, ih]

theorem SystemMessageTrace.settledFrames_eq
    (trace : SystemMessageTrace benv target data state out) :
    trace.settledFrames = rootFrames trace.settledRoots :=
  trace.message.settledFrames_eq

theorem RequestsTrace.settledFrames_eq (trace : RequestsTrace benv bout state bout') :
    trace.settledFrames = rootFrames trace.settledRoots := by
  simp only [RequestsTrace.settledFrames, RequestsTrace.settledRoots, rootFrames,
    List.flatMap_append]
  rw [trace.withdrawal.settledFrames_eq, trace.consolidation.settledFrames_eq]

theorem AppliedBodyTrace.settledFrames_eq (trace : AppliedBodyTrace benv txs wds state bout) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  simp only [AppliedBodyTrace.settledFrames, AppliedBodyTrace.settledRoots, rootFrames,
    List.flatMap_append]
  rw [trace.beacon.settledFrames_eq, trace.history.settledFrames_eq,
    trace.transactions.settledFrames_eq, trace.requests.settledFrames_eq]

theorem ConfiguredBlockTrace.settledFrames_eq (trace : ConfiguredBlockTrace cfg pre post) :
    trace.settledFrames = rootFrames trace.settledRoots :=
  trace.bodyTrace.settledFrames_eq

theorem ConfiguredHistoryTrace.settledFrames_eq
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    trace.settledFrames = rootFrames trace.settledRoots := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTrace.settledFrames, ConfiguredHistoryTrace.settledRoots,
        rootFrames, List.flatMap_append]
      rw [ih, block.settledFrames_eq]

/-- **The fold over a configured history.**  If no settled message root runs at `ca` with caller `p`
without `Q`, and every settled frame meets the parent obligations, then every settled frame that runs at
`ca` with caller `p` satisfies `Q`. -/
theorem ConfiguredHistoryTrace.settledFrames_callerTarget {p ca : Adr} {Q : Sevm → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca Q R.sevm)
    (issuers : ∀ G ∈ trace.settledFrames, CallerIssuers p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ F ∈ trace.settledFrames, CallerTarget p ca Q F.sevm := by
  rw [trace.settledFrames_eq] at issuers ⊢
  exact Exec.Frame.roots_callerTarget trace.settledRoots roots issuers

end ExecutionTrace

end Blanc
