import Blanc.ExecutionWholeFrameAccounting

/-!
# Positional accounting: the replay at the entry of every committed frame

`AccountingLadderAdmitted.root` replays a message root from its entry boundary to its committed post
boundary.  A consumer that reads one contract's ledger at an arbitrary frame of the run (a static read
of a token by a foreign contract, a foreign frame between two target steps) needs the boundary at that
frame's *entry* as a replay prefix.  This module adds, contract-neutrally:

* `Jaune.Exec.Frame.Encloses` and `PositionalLadder` (an `AccountingLadderAdmitted` with an `Opaque`
  frame predicate and the frame-level positional root law `rootAt`);
* `Exec.PositionalAccounting`, the descent invariant at every derivation node, proved for every
  admitted derivation by `Exec.positionalAccounting` (depth induction through `lift_core_sem`);
* the producers `modelPositionalLadder` (`Opaque := False`) and `wholeFramePositionalLadder`
  (`Opaque` = non-static target frames).

**The descent invariant.**  At a node of any pc, every split of the node's committed frames
`before ++ f :: after` whose `before` holds no opaque frame enclosing `f` gives a replay from the
node's boundary to `f`'s entry boundary that observes exactly `before`.  At a pc ≠ 0 node the head of
the committed frames is the pseudo-frame of the sub-run; only foreign nodes reach pc ≠ 0 (`CodeSem.At`
forces pc = 0 at the target), so that pseudo-frame observes nothing and is never opaque.
-/

namespace Blanc.ExecutionAccountingReplay

open Jaune Blanc.ExecutionTrace

/-- `A` encloses `f`: `f` is a committed frame entered (at any depth) below `A`. -/
def _root_.Jaune.Exec.Frame.Encloses (A f : Exec.Frame) : Prop :=
  f ∈ Exec.descendantFrames A.run

end Blanc.ExecutionAccountingReplay

namespace Blanc

open Jaune
open ExecutionAccountingReplay

/-- **The positional descent invariant** at one derivation node: at every split of the node's
committed frames whose earlier part has no opaque frame enclosing the selected frame, the node's
boundary replays to the selected frame's entry boundary, observing exactly the earlier frames. -/
def Exec.PositionalAccounting (ca : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (C : ReplayCarrier ca) (V : ReplayObservation C) (Opaque : Exec.Frame → Prop)
    (pc : Nat) (sevm : Sevm) (pre : Devm) (out : Execution) : Prop :=
  ∀ (run : Exec pc sevm pre out), Execution.commits out = true →
    CoveredFork sevm.benvStat.fork → sem.At ca pc sevm pre → Exec.FrameAdmitted ca entry run →
    sum pre.state.bal < 2 ^ 256 →
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      Exec.committedFrames run = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs

/-- A split of `X ++ Y` at one element lands in `X` or in `Y`. -/
theorem List.split_append_cons {α : Type} {X Y b a : List α} {f : α}
    (h : X ++ Y = b ++ f :: a) :
    (∃ m, X = b ++ f :: m ∧ a = m ++ Y) ∨ (∃ n, b = X ++ n ∧ Y = n ++ f :: a) := by
  rcases List.append_eq_append_iff.mp h with ⟨n, hb, hY⟩ | ⟨c, hX, hfa⟩
  · exact .inr ⟨n, hb, hY⟩
  · cases c with
    | nil =>
        rw [List.append_nil] at hX
        rw [List.nil_append] at hfa
        exact .inr ⟨[], by rw [hX, List.append_nil], hfa.symm⟩
    | cons g c =>
        rw [List.cons_append] at hfa
        obtain ⟨rfl, rfl⟩ := List.cons.inj hfa
        exact .inl ⟨c, hX, rfl⟩

/-- **Storage at every descendant entry of a static run.**  Every committed descendant frame of a
committed static run is entered with the run's storage at any account carrying code. -/
theorem Exec.descendantFrames_getStor_of_static {ca : Adr} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) :
    sevm.isStatic = true → Execution.commits out = true → CoveredFork sevm.benvStat.fork →
    (pre.getCode ca).toList ≠ [] →
    ∀ f ∈ Exec.descendantFrames run, f.pre.state.getStor ca = pre.state.getStor ca := by
  induction run with
  | halt step => intro _ _ _ _ f hf; simp only [Exec.descendantFrames, List.not_mem_nil] at hf
  | cont step next ih =>
      rename_i nextPre _
      intro hs committed fork codeNe f hf
      have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.cont step next) ca codeNe
      have nextNe : (Devm.getCode nextPre ca).toList ≠ [] := by rw [codeEq]; exact codeNe
      have e1 := Exec.getStor_committedPost_eq_of_static_protected (.cont step next) hs committed
        fork ca (State.Protected.of_code_ne_nil codeNe)
      have e2 := Exec.getStor_committedPost_eq_of_static_protected next hs committed fork ca
        (State.Protected.of_code_ne_nil nextNe)
      simp only [Exec.descendantFrames] at hf
      exact (ih hs committed fork nextNe f hf).trans (e2.symm.trans e1)
  | doneErr step enter resume => intro _ _ _ _ f hf; simp only [Exec.descendantFrames,
      List.not_mem_nil] at hf
  | doneOk step enter resume next ih =>
      rename_i nextPre _
      intro hs committed fork codeNe f hf
      have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve (.doneOk step enter resume next) ca
        codeNe
      have nextNe : (Devm.getCode nextPre ca).toList ≠ [] := by rw [codeEq]; exact codeNe
      have e1 := Exec.getStor_committedPost_eq_of_static_protected (.doneOk step enter resume next)
        hs committed fork ca (State.Protected.of_code_ne_nil codeNe)
      have e2 := Exec.getStor_committedPost_eq_of_static_protected next hs committed fork ca
        (State.Protected.of_code_ne_nil nextNe)
      simp only [Exec.descendantFrames] at hf
      exact (ih hs committed fork nextNe f hf).trans (e2.symm.trans e1)
  | runErr step enter child resume ih => intro _ _ _ _ f hf; simp only [Exec.descendantFrames,
      List.not_mem_nil] at hf
  | runOk step enter child resume next childIh nextIh =>
      rename_i frame _ _ cevm raw nextPre _
      intro hs committed fork codeNe f hf
      have protection := State.Protected.of_code_ne_nil codeNe
      have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve
        (.runOk step enter child resume next) ca codeNe
      have nextNe : (Devm.getCode nextPre ca).toList ≠ [] := by rw [codeEq]; exact codeNe
      obtain ⟨x, -, spawnStep, -⟩ := Evm.step_spawn_inv step
      have childStatic := (Frame.enter_run_isStatic enter).trans
        (Xinst.step_spawn_isStatic spawnStep hs)
      have childFork := Evm.step_spawn_child_fork step enter fork
      obtain ⟨-, childCode, -⟩ := Evm.step_spawn_child step enter
      have childNe : (Devm.getCode cevm.dyna ca).toList ≠ [] := by rw [childCode ca]; exact codeNe
      have entryEq := Evm.step_spawn_enter_getStor fork step enter ca protection
      have e1 := Exec.getStor_committedPost_eq_of_static_protected
        (.runOk step enter child resume next) hs committed fork ca protection
      have e2 := Exec.getStor_committedPost_eq_of_static_protected next hs committed fork ca
        (State.Protected.of_code_ne_nil nextNe)
      have nextCase : f ∈ Exec.descendantFrames next →
          f.pre.state.getStor ca = _ := fun member =>
        (nextIh hs committed fork nextNe f member).trans (e2.symm.trans e1)
      by_cases settles : Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next
          settles] at hf
        rcases List.mem_append.mp hf with hc | hn
        · rcases List.mem_cons.mp hc with rfl | hd
          · exact entryEq
          · exact (childIh childStatic (Frame.raw_commits_of_settlementCommits settles) childFork
              childNe f hd).trans entryEq
        · exact nextCase hn
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resume next
          settles] at hf
        exact nextCase hf

namespace Exec.PositionalAccounting

variable {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop} {C : ReplayCarrier ca}
  {V : ReplayObservation C} {Opaque : Exec.Frame → Prop}

theorem error {pc : Nat} {sevm : Sevm} {pre : Devm} {e : EvmError × Devm} :
    Exec.PositionalAccounting ca sem entry C V Opaque pc sevm pre (.error e) := by
  intro _ committed
  simp only [Execution.commits, Bool.false_eq_true] at committed

/-- The selected frame is the node's own (pseudo-)frame: nothing is replayed. -/
private theorem head {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {committed : Execution.commits out = true}
    {f : Exec.Frame} {after rest : List Exec.Frame}
    (split : Exec.Frame.ofRun run committed :: rest = [] ++ f :: after) :
    ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState f.pre.state) ∧
      V.obs steps = ([] : List Exec.Frame).flatMap V.frameObs := by
  obtain ⟨rfl, -⟩ := List.cons.inj split
  exact ⟨[], C.nil _, by rw [V.obs_nil, List.flatMap_nil]⟩

/-- At a foreign node, a split after the node's pseudo-frame shifts to a successor whose
committed frames are its own pseudo-frame followed by the same tail. -/
private theorem shift
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (opaqueTarget : ∀ A, Opaque A → A.sevm.currentTarget = ca)
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {out : Execution}
    {run : Exec pc sevm pre out} {next : Exec pc' sevm inter out}
    (committed : Execution.commits out = true) (targetNe : sevm.currentTarget ≠ ca)
    (storEq : inter.state.getStor ca = pre.state.getStor ca)
    {P f : Exec.Frame} {rest after : List Exec.Frame}
    (hP : Exec.Frame.ofRun run committed = P)
    (hdesc : Exec.descendantFrames next = rest ++ f :: after)
    (noOpaque : ∀ A ∈ P :: rest, A.Encloses f → ¬ Opaque A)
    (ih : ∀ (before : List Exec.Frame),
      Exec.committedFrames next = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState inter.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs) :
    ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState f.pre.state) ∧
      V.obs steps = (P :: rest).flatMap V.frameObs := by
  obtain ⟨steps, replay, observed⟩ := ih (Exec.Frame.ofRun next committed :: rest)
    (by rw [Exec.committedFrames, dite_eq_left committed, hdesc, List.cons_append])
    (by
      intro A member
      rcases List.mem_cons.mp member with rfl | member
      · exact fun _ op => targetNe (opaqueTarget _ op)
      · exact noOpaque A (List.mem_cons_of_mem _ member))
  have e : C.ofState pre.state = C.ofState inter.state :=
    ofStateGet fun k => congrArg (fun t => Stor.get t k) storEq.symm
  refine ⟨steps, by rw [e]; exact replay, ?_⟩
  subst hP
  rw [observed, List.flatMap_cons, List.flatMap_cons,
    obsForeign (Exec.Frame.ofRun next committed) targetNe,
    obsForeign (Exec.Frame.ofRun run committed) targetNe]

theorem nextNone
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (opaqueTarget : ∀ A, Opaque A → A.sevm.currentTarget = ca)
    {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst} {out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n .none (.ok inter))
    (next : Exec (pc + n.size) sevm inter out)
    (targetNe : sevm.currentTarget ≠ ca)
    (ih : Exec.PositionalAccounting ca sem entry C V Opaque (pc + n.size) sevm inter out) :
    Exec.PositionalAccounting ca sem entry C V Opaque pc sevm pre out := by
  intro run committed hfork installed admitted bound before f after split noOpaque
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    rw [Exec.committedFrames, dite_eq_left committed,
      Exec.descendantFrames_eq_of_nextNone hat step run next] at split
    cases before with
    | nil => exact head split
    | cons P rest =>
      rw [List.cons_append] at split
      obtain ⟨hP, hdesc⟩ := List.cons.inj split
      have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
        (sem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
      have codeEq := lift_core_sem.stepCode (xl := .none) trivial
        (by rw [Evm.step_next hat]; exact step) ca codeNe
      have interAt : sem.At ca (pc + n.size) sevm inter :=
        ⟨by rw [codeEq]; exact installed.1, fun target => (targetNe target).elim⟩
      have interAdmitted := admitted.of_descendants_of_ne targetNe
        (Exec.rawFrameDescendants_sub_of_stepNone hat step next run)
      have interBound : sum inter.state.bal < 2 ^ 256 :=
        Nat.lt_of_le_of_lt (Ninst.balance_effectRec n (xl := .none) trivial step) bound
      exact shift obsForeign ofStateGet opaqueTarget committed targetNe
        (Ninst.foreignNone_getStor_eq hfork step targetNe (State.Protected.of_image installed.1))
        hP hdesc noOpaque
        (fun before' split' noOpaque' => ih next committed hfork interAt interAdmitted interBound
          before' f after split' noOpaque')

theorem jump
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (opaqueTarget : ∀ A, Opaque A → A.sevm.currentTarget = ca)
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {j : Jinst} {out : Execution}
    (hat : Jinst.At sevm.code pc j)
    (step : Jinst.Run ⟨pc, sevm, pre⟩ j (.ok ⟨pc', inter⟩))
    (next : Exec pc' sevm inter out) (targetNe : sevm.currentTarget ≠ ca)
    (ih : Exec.PositionalAccounting ca sem entry C V Opaque pc' sevm inter out) :
    Exec.PositionalAccounting ca sem entry C V Opaque pc sevm pre out := by
  intro run committed hfork installed admitted bound before f after split noOpaque
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    rw [Exec.committedFrames, dite_eq_left committed,
      Exec.descendantFrames_eq_of_jump hat step run next] at split
    cases before with
    | nil => exact head split
    | cons P rest =>
      rw [List.cons_append] at split
      obtain ⟨hP, hdesc⟩ := List.cons.inj split
      have stateEq := Jinst.preserves_state step
      have interAt : sem.At ca pc' sevm inter :=
        ⟨by simpa only [Devm.getCode, Devm.getAcct, stateEq] using installed.1,
          fun target => (targetNe target).elim⟩
      have interAdmitted := admitted.of_descendants_of_ne targetNe
        (Exec.rawFrameDescendants_sub_of_jump hat step next run)
      exact shift obsForeign ofStateGet opaqueTarget committed targetNe
        (by rw [stateEq]) hP hdesc noOpaque
        (fun before' split' noOpaque' => ih next committed hfork interAt interAdmitted
          (by simpa only [stateEq] using bound) before' f after split' noOpaque')

theorem last {pc : Nat} {sevm : Sevm} {pre : Devm} {l : Linst} {out : Execution}
    (hat : Linst.At sevm.code pc l) :
    Exec.PositionalAccounting ca sem entry C V Opaque pc sevm pre out := by
  intro run committed _ _ _ _ before f after split _
  rw [Exec.committedFrames, dite_eq_left committed,
    Exec.descendantFrames_eq_nil_of_last hat run] at split
  cases before with
  | nil => exact head split
  | cons P rest =>
    rw [List.cons_append] at split
    obtain ⟨-, hdesc⟩ := List.cons.inj split
    exact absurd hdesc.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))

/-- A filled step at an external instruction is one spawn of the driver whose child entered the
slot's machine and whose resumption reached the step's result. -/
private theorem spawnOfStepRun {pc : Nat} {sevm : Sevm} {pre inter : Devm} {x : Xinst}
    {cevm : Evm} {raw : Execution}
    (hat : Ninst.At sevm.code pc (.exec x))
    (step : Ninst.StepRun pc sevm pre (.exec x) (.some ⟨cevm, raw⟩) (.ok inter)) :
    ∃ (frame : Jaune.Frame) (resume : Resume),
      Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume (pc + 1) ∧ frame.enter = .run cevm ∧
        resume.run (frame.settle raw) = .ok inter := by
  have hxrun := XStep.run_toStep.mp step
  cases spawnEq : Xinst.step sevm pre x with
  | done execution => simp only [XStep.Run, spawnEq, ExceptT.stM_eq, reduceCtorEq,
    false_and] at hxrun
  | spawn frame resume =>
    simp only [spawnEq, XStep.Run] at hxrun
    obtain ⟨result, frameRun, resumeRun⟩ := hxrun
    obtain ⟨enter, settle⟩ := RunFrame.some_inv frameRun
    refine ⟨frame, resume, ?_, enter, ?_⟩
    · rw [Evm.step_next hat]
      simp only [Ninst.step_exec, spawnEq, XStep.toStep]
    · rw [← settle]
      exact resumeRun.symm

/-- At a foreign spawn whose retained frames are the child part `X` then the continuation's `D`, a
split lands in the child (positional child replay) or in the continuation (whole child replay, then
the continuation's positional replay). -/
private theorem spawnSplit
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    {pre inter : State} {P f : Exec.Frame} {X D rest after : List Exec.Frame}
    (hP : P.sevm.currentTarget ≠ ca)
    (hdesc : X ++ D = rest ++ f :: after)
    (noOpaque : ∀ A ∈ P :: rest, A.Encloses f → ¬ Opaque A)
    (childPos : ∀ b m, X = b ++ f :: m → (∀ A ∈ b, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState pre) steps (C.ofState f.pre.state) ∧
        V.obs steps = b.flatMap V.frameObs)
    (childWhole : ∃ steps, C.Replay (C.ofState pre) steps (C.ofState inter) ∧
      V.obs steps = X.flatMap V.frameObs)
    (nextPos : ∀ b, D = b ++ f :: after → (∀ A ∈ b, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState inter) steps (C.ofState f.pre.state) ∧
        V.obs steps = b.flatMap V.frameObs) :
    ∃ steps, C.Replay (C.ofState pre) steps (C.ofState f.pre.state) ∧
      V.obs steps = (P :: rest).flatMap V.frameObs := by
  rw [List.flatMap_cons, obsForeign P hP, List.nil_append]
  rcases List.split_append_cons hdesc with ⟨m, hX, -⟩ | ⟨n, hrest, hD⟩
  · exact childPos rest m hX fun A member => noOpaque A (List.mem_cons_of_mem _ member)
  · obtain ⟨heads, headReplay, headObs⟩ := childWhole
    obtain ⟨tails, tailReplay, tailObs⟩ := nextPos n hD fun A member =>
      noOpaque A (List.mem_cons_of_mem _ (by rw [hrest]; exact List.mem_append_right _ member))
    refine ⟨heads ++ tails, append headReplay tailReplay, ?_⟩
    rw [V.obs_append, headObs, tailObs, hrest, List.flatMap_append]

theorem nextSome
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (opaqueTarget : ∀ A, Opaque A → A.sevm.currentTarget = ca)
    (core : Exec.Fa (Exec.WknSem ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)))
    {pc : Nat} {sevm : Sevm} {pre inter : Devm} {n : Ninst}
    {cevm : Evm} {raw out : Execution}
    (hat : Ninst.At sevm.code pc n)
    (step : Ninst.StepRun pc sevm pre n (.some ⟨cevm, raw⟩) (.ok inter))
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (next : Exec (pc + n.size) sevm inter out)
    (targetNe : sevm.currentTarget ≠ ca)
    (ihChild : Exec.PositionalAccounting ca sem entry C V Opaque cevm.pc cevm.sta cevm.dyna raw)
    (ihNext : Exec.PositionalAccounting ca sem entry C V Opaque (pc + n.size) sevm inter out) :
    Exec.PositionalAccounting ca sem entry C V Opaque pc sevm pre out := by
  cases n with
  | reg r => cases (Step.run_ofExecution.mp step).1
  | push xs length => cases (Step.run_ofExecution.mp step).1
  | dupn imm => cases (Step.run_ofExecution.mp step).1
  | swapn imm => cases (Step.run_ofExecution.mp step).1
  | exchange imm => cases (Step.run_ofExecution.mp step).1
  | exec x =>
  intro run committed hfork installed admitted bound before f after split noOpaque
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
  obtain ⟨frame, resume, hroot, enter, hres⟩ := spawnOfStepRun hat step
  have subsets := Exec.rawFrameDescendants_sub_of_stepSome hat step child next run
  have runEq : run = Exec.runOk hroot enter child hres next := Exec.unique _ _
  subst runEq
  rw [Exec.committedFrames, dite_eq_left committed] at split
  cases before with
  | nil => exact head split
  | cons P rest =>
  rw [List.cons_append] at split
  obtain ⟨hP, hdesc⟩ := List.cons.inj split
  have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
    (sem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
  have codeNe' : pre.getCode ca ≠ .empty := fun empty => codeNe (by
    rw [empty]; simp only [ByteArray.toList_empty])
  have protection := State.Protected.of_image installed.1
  obtain ⟨balLe, codeEq⟩ := Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode
    (.step (.runOk hroot enter child hres next) (.refl _))
  have interAt : sem.At ca (pc + 1) sevm inter :=
    ⟨by rw [codeEq ca codeNe]; exact installed.1, fun target => (targetNe target).elim⟩
  obtain ⟨pcZero, childCode, codeSource⟩ := Evm.step_spawn_child hroot enter
  have childAt : sem.At ca cevm.pc cevm.sta cevm.dyna := by
    refine ⟨by rw [childCode ca]; exact installed.1, fun childTarget => ⟨?_, pcZero⟩⟩
    rw [codeSource (by rw [childTarget]; exact targetNe) (by rw [childTarget]; exact codeNe')
      (by rw [childTarget]; exact sem.not_delegation installed.1), childTarget]
    exact installed.1
  have childFork := Evm.step_spawn_child_fork hroot enter hfork
  have childBound : sum cevm.dyna.state.bal < 2 ^ 256 :=
    Nat.lt_of_le_of_lt (Evm.step_spawn_child_world hfork hroot enter codeNe').2 bound
  have childAdmitted : Exec.FrameAdmitted ca entry child := admitted.mono fun root member =>
    List.mem_cons_of_mem _ (subsets.1 root member)
  have nextAdmitted := admitted.of_descendants_of_ne targetNe subsets.2
  obtain ⟨seamA, seamB⟩ := Exec.spawn_seam hfork hroot enter child hres
  have eEntry : C.ofState pre.state = C.ofState cevm.dyna.state :=
    ofStateGet fun k => congrArg (fun t => Stor.get t k)
      (Evm.step_spawn_enter_getStor hfork hroot enter ca protection).symm
  have nextPos : ∀ b, Exec.descendantFrames next = b ++ f :: after →
      (∀ A ∈ b, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState inter.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = b.flatMap V.frameObs := by
    intro b hD noOpaque'
    obtain ⟨steps, replay, observed⟩ := ihNext next committed hfork interAt nextAdmitted
      (Nat.lt_of_le_of_lt balLe bound) (Exec.Frame.ofRun next committed :: b) f after
      (by rw [Exec.committedFrames, dite_eq_left committed, hD, List.cons_append])
      (by
        intro A member
        rcases List.mem_cons.mp member with rfl | member
        · exact fun _ op => targetNe (opaqueTarget _ op)
        · exact noOpaque' A member)
    refine ⟨steps, replay, ?_⟩
    rw [observed, List.flatMap_cons, obsForeign (Exec.Frame.ofRun next committed) targetNe,
      List.nil_append]
  have hPfor : P.sevm.currentTarget ≠ ca := by rw [← hP]; exact targetNe
  by_cases settles : Frame.settlementCommits frame raw = true
  · have hraw := Frame.raw_commits_of_settlementCommits settles
    have cf : Exec.committedFrames child = Exec.Frame.ofRun child hraw :: Exec.descendantFrames child :=
      by rw [Exec.committedFrames, dite_eq_left hraw]
    rw [Exec.descendantFrames_runOk_of_settlementCommits hroot enter child hres next settles,
      ← cf] at hdesc
    refine spawnSplit obsForeign append hPfor hdesc noOpaque ?_ ?_ nextPos
    · intro b m hX noOpaque'
      obtain ⟨steps, replay, observed⟩ := ihChild child hraw childFork childAt childAdmitted
        childBound b f m hX noOpaque'
      exact ⟨steps, by rw [eEntry]; exact replay, observed⟩
    · obtain ⟨steps, replay, observed⟩ :=
        (core _ _ _ _ child childAt child hraw childFork childAt childAdmitted).2 childBound
      have e2 : C.ofState (Execution.committedPost raw hraw).state = C.ofState inter.state :=
        ofStateGet fun k => (seamA hraw settles ca k).symm
      rw [entryOfState, e2] at replay
      exact ⟨steps, by rw [eEntry]; exact replay, observed⟩
  · rw [Exec.descendantFrames_runOk_of_not_settlementCommits hroot enter child hres next
      settles] at hdesc
    refine spawnSplit (X := []) obsForeign append hPfor (by rw [List.nil_append]; exact hdesc)
      noOpaque ?_ ?_ nextPos
    · intro b m hX
      exact absurd hX.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
    · refine ⟨[], C.nilOfEq (ofStateGet fun k => seamB settles ca k), ?_⟩
      rw [V.obs_nil, List.flatMap_nil]

/-- **A static run is positional with nothing replayed.**  Its storage at the target is the same at
every committed frame entry and its frames observe nothing (`core`'s static clause). -/
theorem static
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (core : Exec.Fa (Exec.WknSem ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)))
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (hs : sevm.isStatic = true) :
    Exec.PositionalAccounting ca sem entry C V Opaque pc sevm pre out := by
  intro run committed fork installed admitted _ before f after split _
  have obsNil := (core _ _ _ _ run installed run committed fork installed admitted).1 hs
  rw [split, List.flatMap_append] at obsNil
  have codeNe : (pre.getCode ca).toList ≠ [] := fun empty =>
    (sem.ne_nil (installed.1.symm.trans (congrArg some empty))) rfl
  have member : f ∈ Exec.committedFrames run := by
    rw [split]; exact List.mem_append_right _ (List.mem_cons_self ..)
  rw [Exec.committedFrames, dite_eq_left committed] at member
  have stor : f.pre.state.getStor ca = pre.state.getStor ca := by
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · exact Exec.descendantFrames_getStor_of_static run hs committed fork codeNe f member
  refine ⟨[], C.nilOfEq (ofStateGet fun k => congrArg (fun t => Stor.get t k) stor), ?_⟩
  rw [V.obs_nil, (List.append_eq_nil_iff.mp obsNil).1]

/-- The child of a spawning node on a target frame's chain is entered deeper, at the contract's
code, and admitted. -/
private theorem spawnChildAt (kinds : SpawnKinds ca sem)
    {sevm₀ : Sevm} {pre₀ post₀ : Devm} (root : Exec 0 sevm₀ pre₀ (.ok post₀))
    (hrun : sem.Run sevm₀ pre₀ post₀) (target : sevm₀.currentTarget = ca)
    (fork : CoveredFork sevm₀.benvStat.fork) (installed : sem.At ca 0 sevm₀ pre₀)
    (admitted : Exec.FrameAdmitted ca entry root)
    {nodePc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out : Execution} {frame : Jaune.Frame}
    {rsm : Resume} {nextPc : Nat} {cevm : Evm} {raw : Execution} {inter : Devm}
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (resume : rsm.run (frame.settle raw) = .ok inter) (next : Exec nextPc nodeSevm inter out)
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩
      ⟨nodePc, nodeSevm, nodePre, out, .runOk step enter child resume next⟩) :
    cevm.sta.depth < sevm₀.depth ∧ sem.At ca cevm.pc cevm.sta cevm.dyna ∧
      Exec.FrameAdmitted ca entry child := by
  have sevmEq : nodeSevm = sevm₀ := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  obtain ⟨x, instruction, spawnStep, _⟩ := Evm.step_spawn_inv step
  have codeNe : (pre₀.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have nodeInstalled : some (nodePre.getCode ca).toList = sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode chain).2 ca codeNe]
    exact installed.1
  obtain ⟨pcZero, getCode, _⟩ := Evm.step_spawn_child step enter
  refine ⟨by rw [Frame.enter_run_depth enter, ← sevmEq]; exact Step.spawn_depth_lt step,
    ⟨by rw [getCode ca]; exact nodeInstalled, fun selected => ⟨?_, pcZero⟩⟩, ?_⟩
  · have sameTarget : frame.inner.currentTarget = nodeSevm.currentTarget := by
      rw [← Frame.enter_run_currentTarget enter, selected, sevmEq, target]
    have notDel : ¬ isValidDelegation (nodePre.getCode frame.inner.currentTarget) := by
      rw [← Frame.enter_run_currentTarget enter, selected]
      exact sem.not_delegation nodeInstalled
    rw [Frame.enter_run_code enter]
    rcases kinds root hrun target fork installed _ chain x instruction with rfl | rfl
    · rw [Xinst.step_call_sameTarget_code spawnStep sameTarget notDel,
        ← Frame.enter_run_currentTarget enter, selected]
      exact nodeInstalled
    · rw [Xinst.step_staticcall_sameTarget_code spawnStep sameTarget notDel,
        ← Frame.enter_run_currentTarget enter, selected]
      exact nodeInstalled
  · intro childRoot member selected
    refine admitted childRoot (List.mem_cons_of_mem _
      (Exec.mem_rawFrameDescendants_of_parentPrefix chain ?_)) selected
    simp only [Exec.rawFrameRoots, List.mem_cons] at member
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append]
    rcases member with rfl | member
    · exact Or.inl rfl
    · exact Or.inr (Or.inl member)

/-- **The settled children of a frame's spawning nodes are positional** (a child provider): at
every `runOk` node of the frame's own chain, a committed child entered under the world word bound
replays, from its entry storage, to the entry of each of its committed frames not enclosed by an
earlier opaque one.  The single-code handler supplies it from the lower-depth hypothesis; a code
family supplies it per spawn kind. -/
def ChildPositional (C : ReplayCarrier ca) (V : ReplayObservation C)
    (Opaque : Exec.Frame → Prop) {sevm₀ : Sevm} {pre₀ post₀ : Devm}
    (root : Exec 0 sevm₀ pre₀ (.ok post₀)) : Prop :=
  ∀ {nodePc : Nat} {nodeSevm : Sevm} {nodePre : Devm} {out : Execution} {frame : Jaune.Frame}
    {rsm : Resume} {nextPc : Nat} {cevm : Evm} {raw : Execution} {inter : Devm}
    (step : Evm.step ⟨nodePc, nodeSevm, nodePre⟩ = .spawn frame rsm nextPc)
    (enter : frame.enter = .run cevm) (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (resume : rsm.run (frame.settle raw) = .ok inter) (next : Exec nextPc nodeSevm inter out),
    Exec.Deriv.ParentPrefix ⟨0, sevm₀, pre₀, .ok post₀, root⟩
      ⟨nodePc, nodeSevm, nodePre, out, .runOk step enter child resume next⟩ →
    Execution.commits raw = true → sum cevm.dyna.state.bal < 2 ^ 256 →
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      Exec.committedFrames child = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState cevm.dyna.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs

/-- **The positional replay of a model frame from its own steps and its children's positional
replays.**  If `own` contributes the frame's own observation and takes the entry boundary to the
boundary of every node that decodes an external instruction, after which no later node decodes one,
then every committed frame of the frame lies in its single settled child, and the frame is
positional. -/
theorem modelFrameAt
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    {sevm : Sevm} {pre post : Devm} (run : Exec 0 sevm pre (.ok post))
    (committed : Execution.commits (.ok post) = true) (fork : CoveredFork sevm.benvStat.fork)
    (rootNonempty : (pre.getCode ca).toList ≠ []) (bound : sum pre.state.bal < 2 ^ 256)
    (children : ChildPositional C V Opaque run) (own : List C.Step)
    (hown : V.obs own = V.frameObs (Exec.Frame.ofRun run committed))
    (c12 : ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, .ok post, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) →
        C.Replay (C.ofState pre.state) own (C.ofState N.devm.state) ∧
        ∀ N', Exec.Deriv.ParentStep N' N →
          C.Replay (C.ofState N'.devm.state) [] (C.ofState post.state) ∧
          ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y)) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      Exec.committedFrames run = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque A) →
      ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState f.pre.state) ∧
        V.obs steps = before.flatMap V.frameObs := by
  intro before f after split noOpaque
  rw [Exec.committedFrames, dite_eq_left committed] at split
  cases before with
  | nil => exact head split
  | cons P rest =>
  rw [List.cons_append] at split
  obtain ⟨hP, hdesc⟩ := List.cons.inj split
  rcases Exec.Deriv.exists_firstExec_or_none run with none | ⟨Vn, hV⟩
  · rw [Exec.descendantFrames_eq_nil_of_noExec run none] at hdesc
    exact absurd hdesc.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  have hpV := hV.parentPrefix
  have dEq := hV.descendantFrames_eq
  obtain ⟨x, hx⟩ := hV.exec_at
  have hexn := Exec.Deriv.ParentPrefix.exn_eq hpV
  obtain ⟨vpc, vsevm, vd, vout, vrun⟩ := Vn
  dsimp only at hexn hx dEq
  subst hexn
  rw [dEq] at hdesc
  have nodeNonempty : (vd.getCode ca).toList ≠ [] := by
    rw [Blanc.Exec.Deriv.ParentPrefix.codePreserve hpV ca rootNonempty]
    exact rootNonempty
  cases vrun with
  | halt step =>
      rw [Evm.step_next hx] at step
      exact (Ninst.step_ne_halt_ok step).elim
  | cont step next =>
      have hdf := Exec.descendantFrames_eq_nil_of_noExec next
        ((c12 _ hpV x hx).2 _ (.cont step next)).2
      simp only [Exec.descendantFrames, hdf] at hdesc
      exact absurd hdesc.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | doneOk step enter resume next =>
      have hdf := Exec.descendantFrames_eq_nil_of_noExec next
        ((c12 _ hpV x hx).2 _ (.doneOk step enter resume next)).2
      simp only [Exec.descendantFrames, hdf] at hdesc
      exact absurd hdesc.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | runOk step enter child resume next =>
      rename_i frame rsm pc' cevm raw inter
      have hdf := Exec.descendantFrames_eq_nil_of_noExec next
        ((c12 _ hpV x hx).2 _ (.runOk step enter child resume next)).2
      have nodeFork : CoveredFork vsevm.benvStat.fork := by
        rw [show vsevm = sevm from Blanc.Exec.Deriv.ParentPrefix.sevm_eq hpV]
        exact fork
      have nodeCodeNe : vd.getCode ca ≠ .empty := fun empty =>
        nodeNonempty (by rw [empty]; simp only [ByteArray.toList_empty])
      by_cases settles : Frame.settlementCommits frame raw = true
      · have hraw := Frame.raw_commits_of_settlementCommits settles
        have cf : Exec.committedFrames child =
            Exec.Frame.ofRun child hraw :: Exec.descendantFrames child := by
          rw [Exec.committedFrames, dite_eq_left hraw]
        rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next settles,
          hdf, List.append_nil, ← cf] at hdesc
        have childBound : sum cevm.dyna.state.bal < 2 ^ 256 :=
          Nat.lt_of_le_of_lt
            ((Evm.step_spawn_child_world nodeFork step enter nodeCodeNe).2.trans
              (Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode hpV).1) bound
        obtain ⟨steps, replay, observed⟩ := children step enter child resume next hpV hraw
          childBound rest f after hdesc fun A member => noOpaque A (List.mem_cons_of_mem _ member)
        have c1 := (c12 _ hpV x hx).1
        have e1 : C.ofState vd.state = C.ofState cevm.dyna.state :=
          ofStateGet fun k => congrArg (fun t => Stor.get t k)
            (Evm.step_spawn_enter_getStor nodeFork step enter ca
              (State.Protected.of_code_ne_nil nodeNonempty)).symm
        rw [e1] at c1
        refine ⟨own ++ steps, append c1 replay, ?_⟩
        rw [V.obs_append, hown, observed, ← hP, List.flatMap_cons]
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resume next
          settles, hdf] at hdesc
        exact absurd hdesc.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))

/-- **The model target handler.**  A non-static target frame's own steps reach its first external
node, whose settled child holds every later frame; a static target frame replays nothing. -/
theorem modelTarget
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (kinds : SpawnKinds ca sem) (spawn : Exec.CoreAccounting.SpawnReplay ca sem entry C V)
    (core : Exec.Fa (Exec.WknSem ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)))
    {sevm : Sevm} {pre post : Devm} (hrun : sem.Run sevm pre post)
    (target : sevm.currentTarget = ca)
    (deeper : ForallDeeperAtSem sevm.depth ca sem
      (fun pc s d e _ => Exec.PositionalAccounting ca sem entry C V Opaque pc s d e)) :
    Exec.PositionalAccounting ca sem entry C V Opaque 0 sevm pre (.ok post) := by
  by_cases hs : sevm.isStatic = true
  · exact static ofStateGet core hs
  intro run committed fork installed admitted bound
  have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
  have rootNonempty : (pre.getCode ca).toList ≠ [] := fun empty =>
    sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  obtain ⟨own, hown, -, c12⟩ := spawn run committed hrun target fork installed admitted bound hs'
  rw [entryOfState] at c12
  refine modelFrameAt ofStateGet append run committed fork rootNonempty bound ?_ own hown c12
  intro _ nodeSevm _ _ _ _ _ _ _ _ step enter child resume next chain childCommitted childBound
  have nodeFork : CoveredFork nodeSevm.benvStat.fork := by
    rw [show nodeSevm = sevm from Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain]
    exact fork
  obtain ⟨childDepth, childAt, childAdmitted⟩ :=
    spawnChildAt kinds run hrun target fork installed admitted step enter child resume next chain
  exact deeper _ _ _ _ child childDepth childAt child childCommitted
    (Evm.step_spawn_child_fork step enter nodeFork) childAt childAdmitted childBound

/-- **The whole-frame target handler.**  A non-static target frame is opaque, so only its own
entry is selected; a static target frame replays nothing. -/
theorem wholeFrameTarget
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (core : Exec.Fa (Exec.WknSem ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)))
    {sevm : Sevm} {pre post : Devm} (target : sevm.currentTarget = ca) :
    Exec.PositionalAccounting ca sem entry C V
      (fun A => A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false) 0 sevm pre (.ok post) := by
  by_cases hs : sevm.isStatic = true
  · exact static ofStateGet core hs
  intro run committed _ _ _ _ before f after split noOpaque
  rw [Exec.committedFrames, dite_eq_left committed] at split
  cases before with
  | nil => exact head split
  | cons P rest =>
  rw [List.cons_append] at split
  obtain ⟨hP, hdesc⟩ := List.cons.inj split
  subst hP
  have hs' : sevm.isStatic = false := by simpa only [Bool.not_eq_true] using hs
  refine (noOpaque _ (List.mem_cons_self ..) ?_ ⟨target, hs'⟩).elim
  change f ∈ Exec.descendantFrames run
  rw [hdesc]
  exact List.mem_append_right _ (List.mem_cons_self ..)

end Exec.PositionalAccounting

/-- **Positional accounting of every admitted derivation**, from a target handler at the
contract's own frames: the foreign chain cases compose child and continuation replays. -/
theorem Exec.positionalAccounting {ca : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop}
    {C : ReplayCarrier ca} {V : ReplayObservation C} {Opaque : Exec.Frame → Prop}
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (opaqueTarget : ∀ A, Opaque A → A.sevm.currentTarget = ca)
    (core : Exec.Fa (Exec.WknSem ca sem
      (fun pc s d e _ => Exec.CoreAccounting ca sem entry C V pc s d e)))
    (targetHandler : ∀ {sevm pre post}, sem.Run sevm pre post → sevm.currentTarget = ca →
      ForallDeeperAtSem sevm.depth ca sem
        (fun pc s d e _ => Exec.PositionalAccounting ca sem entry C V Opaque pc s d e) →
      Exec.PositionalAccounting ca sem entry C V Opaque 0 sevm pre (.ok post)) :
    Exec.Fa (Exec.WknSem ca sem
      (fun pc s d e _ => Exec.PositionalAccounting ca sem entry C V Opaque pc s d e)) := by
  apply lift_core_sem
    (ε := fun pc sevm pre out => Exec.PositionalAccounting ca sem entry C V Opaque pc sevm pre out)
    (π := fun sevm pre post => Exec.PositionalAccounting ca sem entry C V Opaque 0 sevm pre (.ok post))
    (analog := fun h => h) (ca := ca) (sem := sem)
  · exact targetHandler
  · intro pc sevm pre error post target
    exact Exec.PositionalAccounting.error
  · intro pc sevm pre noneAt targetNe
    exact Exec.PositionalAccounting.error
  · intro pc sevm pre n error post hat step targetNe
    exact Exec.PositionalAccounting.error
  · intro pc sevm pre n childEvm childOut error post hat step child targetNe ihChild
    exact Exec.PositionalAccounting.error
  · intro pc sevm pre n inter out hat step next targetNe ihNext
    exact Exec.PositionalAccounting.nextNone obsForeign ofStateGet opaqueTarget hat step next
      targetNe ihNext
  · intro pc sevm pre n childEvm childOut inter out hat step child next targetNe ihChild ihNext
    exact Exec.PositionalAccounting.nextSome entryOfState ofStateGet obsForeign append
      opaqueTarget core hat step child next targetNe ihChild ihNext
  · intro pc sevm pre j error post hat step targetNe
    exact Exec.PositionalAccounting.error
  · intro pc sevm pre j pc' inter out hat step next targetNe ihNext
    exact Exec.PositionalAccounting.jump obsForeign ofStateGet opaqueTarget hat step next
      targetNe ihNext
  · intro pc sevm pre l out hat step targetNe
    exact Exec.PositionalAccounting.last hat


end Blanc

namespace Blanc.ExecutionAccountingReplay

open Jaune Blanc.ExecutionTrace

/-- A ladder whose replay is also **positional**: the boundary at the entry of every
committed frame of a root is the replay of exactly the observations of the committed frames
before it (pre-order), unless a frame before it that encloses it is `opaque` (a target frame
whose own step is the whole frame, so its boundary mid-frame is no replay prefix). -/
structure PositionalLadder (c : ContractSpecSem) (ca : Adr) (entry : Sevm → Devm → Prop)
    extends AccountingLadderAdmitted c ca entry where
  Opaque : Exec.Frame → Prop
  rootAt : ∀ (_blockIndex : Nat) (_transactionIndex : Option Nat)
    {msg : Msg} {entryBenv : Benv} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out),
    msg.benvAfterTransfer = .ok entryBenv →
    (⟨pc, sevm, pre⟩ : Evm) = initEvm (msg.withBenv entryBenv) →
    ∀ committed : Execution.commits out = true,
    Exec.FrameAdmitted ca entry run →
    c.MessageRunReady ca msg →
    (msg.currentTarget = ca → msg.caller ≠ ca) →
    CoveredFork sevm.benvStat.fork →
    sum msg.benv.state.bal < 2 ^ 256 →
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      Exec.committedFrames run = before ++ f :: after →
      (∀ A ∈ before, A.Encloses f → ¬ Opaque A) →
      ∃ steps, carrier.Replay (carrier.frameEntry sevm pre.state) steps
          (carrier.frameEntry f.sevm f.pre.state) ∧
        view.obs steps = before.flatMap view.frameObs

/-- The model ladder is positional everywhere (`SpawnReplay` already fixes the boundary at every
spawning node of a target frame).  Same arguments as `modelLadder`. -/
noncomputable def modelPositionalLadder {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (kinds : SpawnKinds ca c.sem) (spawn : Exec.CoreAccounting.SpawnReplay ca c.sem entry C V)
    (preserves : c.PreservesAdmitted ca entry) : PositionalLadder c ca entry :=
  { modelLadder C V append tag frameTag entryOfState ofStateGet obsStatic obsForeign kinds spawn
      preserves with
    Opaque := fun _ => False
    rootAt := by
      intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
        bound before f after split noOpaque
      obtain ⟨installed, entryBound⟩ :=
        Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
      have core := Exec.coreAccounting ca c.sem entry C V append frameTag
        (fun sevm state _ => entryOfState sevm state) obsForeign
        (fun hrun target deeper =>
          Exec.CoreAccounting.spawnReplayTarget entryOfState ofStateGet obsStatic append kinds
            spawn hrun target deeper)
      have pos := Exec.positionalAccounting (Opaque := fun _ => False) entryOfState ofStateGet
        obsForeign append (fun _ op => op.elim) core
        (fun hrun target deeper => Exec.PositionalAccounting.modelTarget entryOfState ofStateGet
          append kinds spawn core hrun target deeper)
      obtain ⟨steps, replay, observed⟩ := pos pc sevm pre out run installed run committed fork
        installed admitted entryBound before f after split noOpaque
      refine ⟨steps, ?_, observed⟩
      show C.Replay (C.frameEntry sevm pre.state) steps (C.frameEntry f.sevm f.pre.state)
      rw [entryOfState, entryOfState]
      exact replay }

/-- The whole-frame ladder is positional outside its own non-static target frames.  Same
arguments as `wholeFrameLadder`. -/
noncomputable def wholeFramePositionalLadder {c : ContractSpecSem} {ca : Adr}
    {entry : Sevm → Devm → Prop}
    (C : ReplayCarrier ca) (V : ReplayObservation C)
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    (tag : Nat → Option Nat → C.Tag) (frameTag : Sevm → Devm → C.Tag)
    (entryOfState : ∀ (sevm : Sevm) (state : State), C.frameEntry sevm state = C.ofState state)
    (ofStateGet : ∀ {s s' : State},
      (∀ k, (s.getStor ca).get k = (s'.getStor ca).get k) → C.ofState s = C.ofState s')
    (obsStatic : ∀ f : Exec.Frame, f.sevm.isStatic = true → V.frameObs f = [])
    (obsForeign : ∀ f : Exec.Frame, f.sevm.currentTarget ≠ ca → V.frameObs f = [])
    (kinds : SpawnKinds ca c.sem) (whole : Exec.CoreAccounting.WholeFrameReplay ca c.sem entry C V)
    (preserves : c.PreservesAdmitted ca entry) : PositionalLadder c ca entry :=
  { wholeFrameLadder C V append tag frameTag entryOfState ofStateGet obsStatic obsForeign kinds
      whole preserves with
    Opaque := fun A => A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false
    rootAt := by
      intro _ _ msg entryBenv pc sevm pre out run transfer evmEq committed admitted ready _ fork
        bound before f after split noOpaque
      obtain ⟨installed, entryBound⟩ :=
        Exec.CoreAccounting.messageRoot_facts transfer evmEq ready bound
      have core := Exec.coreAccounting ca c.sem entry C V append frameTag
        (fun sevm state _ => entryOfState sevm state) obsForeign
        (fun hrun target deeper =>
          Exec.CoreAccounting.wholeFrameTarget entryOfState ofStateGet obsStatic kinds whole hrun
            target deeper)
      have pos := Exec.positionalAccounting
        (Opaque := fun A => A.sevm.currentTarget = ca ∧ A.sevm.isStatic = false) entryOfState
        ofStateGet obsForeign append (fun _ op => op.1) core
        (fun _ target _ => Exec.PositionalAccounting.wholeFrameTarget ofStateGet core target)
      obtain ⟨steps, replay, observed⟩ := pos pc sevm pre out run installed run committed fork
        installed admitted entryBound before f after split noOpaque
      refine ⟨steps, ?_, observed⟩
      show C.Replay (C.frameEntry sevm pre.state) steps (C.frameEntry f.sevm f.pre.state)
      rw [entryOfState, entryOfState]
      exact replay }

end Blanc.ExecutionAccountingReplay
