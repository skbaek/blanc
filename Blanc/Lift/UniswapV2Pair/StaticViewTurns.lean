import Blanc.Lift.UniswapV2Pair.StaticViewSource
import Blanc.Lift.SegmentedHistory
import Blanc.ExecutionEntryAccounting
import Blanc.ExecutionTraceCalldata
import Blanc.Lift.TargetLogEvents

/-! Actual static getter executions supply invocation turns at the incoming checkpoint. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- A successful raw static view supplies one exact source invocation and extends only
its decoded finite footprint. Its actual sender, value, static flag and return bytes are retained. -/
theorem staticView_turn_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn : Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) frame.current.state)
    (fresh : WriterFreshKeys K (staticViewDecodedKeys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∃ view : StaticView,
      Blanc.Sevm.selector sevm = view.selector ∧
      view.argumentSize + 4 ≤ sevm.data.length ∧
      some post.output = getterResult frame.current.state (view.entry sevm) ∧
      WriterRep (WriterExtend K (staticViewDecodedKeys sevm))
        (post.getStor sevm.currentTarget) frame.current.state ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧
      (∀ (tail : Transcript) (out : TurnsResult),
        ExactTurns frame request (turn + 1) tail out →
        ExactTurns frame request turn
          (.invoke sevm.caller sevm.value sevm.isStatic (view.entry sevm) .done tail)
          { out with childReturns :=
              [{ context := childContext frame request turn sevm.caller sevm.value sevm.isStatic,
                 entry := view.entry sevm, status := .success post.output }] ++ out.childReturns }) := by
  let ctx := childContext frame request turn sevm.caller sevm.value sevm.isStatic
  obtain ⟨_, view, selector, length, result, storage, logs,
    _, _, consumed, _, _, _⟩ :=
    staticView_source_handler_inv rep fresh representable (ctx := ctx) rfl
      codeEq fork static run
  have extended : WriterRep (WriterExtend K (staticViewDecodedKeys sevm))
      (post.getStor sevm.currentTarget) frame.current.state := by
    rw [storage sevm.currentTarget]
    exact rep.extend fresh
  refine ⟨view, selector, length, result, extended, storage, logs, ?_⟩
  intro tail out rest
  have invoked := ExactTurns.invoke (frame := frame) (request := request)
    (turn := turn) consumed rest
  exact invoked

/-- A committing target-root view supplies the entire selected queue at its
original entering path. The source tail is constructed from the actual
singleton projection, and the physical context fields match this raw frame. -/
theorem staticView_target_turns_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn : Nat} {path : List Nat}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) frame.current.state)
    (fresh : WriterFreshKeys K (staticViewDecodedKeys sevm))
    (representable : sevm.data.length < 2 ^ 256)
    (pair : frame.context.pair = sevm.currentTarget)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (static : sevm.isStatic = true)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∃ view : StaticView,
      Blanc.Sevm.selector sevm = view.selector ∧
      view.argumentSize + 4 ≤ sevm.data.length ∧
      some post.output = getterResult frame.current.state (view.entry sevm) ∧
      WriterRep (WriterExtend K (staticViewDecodedKeys sevm))
        (post.getStor sevm.currentTarget) frame.current.state ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs ∧
      (∀ committed : Execution.commits (.ok post) = true,
        Exec.retainedTargetTurnsAt sevm.currentTarget path run =
          [.inr ⟨path, Exec.Frame.ofRun run committed⟩]) ∧
      childContext frame request turn sevm.caller sevm.value sevm.isStatic =
        { pair := sevm.currentTarget, sender := sevm.caller, value := sevm.value,
          timestamp := sevm.benvStat.time, isStatic := true,
          invocation := frame.context.invocation ++ [request.site.ordinal, turn] } ∧
      (∀ (tail : Transcript) (result : TurnsResult),
        ExactTurns frame request (turn + 1) tail result →
        ExactTurns frame request turn
          (.invoke sevm.caller sevm.value sevm.isStatic (view.entry sevm) .done tail)
          { result with childReturns :=
              [{ context := childContext frame request turn sevm.caller sevm.value sevm.isStatic,
                 entry := view.entry sevm, status := .success post.output }] ++ result.childReturns }) ∧
      ExactTurns frame request turn
        (.invoke sevm.caller sevm.value sevm.isStatic (view.entry sevm) .done .done)
        { complete := true, frame := frame,
          childReturns :=
            [{ context := childContext frame request turn sevm.caller sevm.value sevm.isStatic,
               entry := view.entry sevm, status := .success post.output }] } := by
  obtain ⟨view, selector, length, result, extended, storage, logs, consume⟩ :=
    staticView_turn_inv (request := request) (turn := turn)
      rep fresh representable codeEq fork static run
  refine ⟨view, selector, length, result, extended, storage, logs, ?_, ?_, consume, ?_⟩
  · intro committed
    rw [Exec.retainedTargetTurnsAt_eq_map_prefix,
      Exec.retainedTargetTurns_target_stop sevm.currentTarget run committed rfl]
    simp only [List.map_cons, List.map_nil, Exec.RetainedTargetTurn.rebase,
      List.append_nil]
  · simp only [childContext, pair, time, static, Bool.or_true]
  · exact consume .done { complete := true, frame := frame, childReturns := [] }
      (ExactTurns.done frame request (turn + 1))

/-- One actual retained frame paired with its derived static getter. -/
abbrev StaticViewTurn := Exec.LocatedFrame × StaticView

/-- A source transcript projection, in selected-frame order. This does not
traverse executions and keeps the supplied raw frame witnesses unchanged. -/
def staticViewTranscript : List StaticViewTurn → Transcript → Transcript
  | [], tail => tail
  | (located, view) :: rest, tail =>
      .invoke located.frame.sevm.caller located.frame.sevm.value
        located.frame.sevm.isStatic (view.entry located.frame.sevm) .done
        (staticViewTranscript rest tail)

/-- Source invocation ordinals advance independently of original raw paths. -/
def staticViewChildReturns (frame : Frame) (request : Request) :
    Nat → List StaticViewTurn → List ChildReturn
  | _, [] => []
  | turn, (located, view) :: rest =>
      { context := childContext frame request turn located.frame.sevm.caller
          located.frame.sevm.value located.frame.sevm.isStatic,
        entry := view.entry located.frame.sevm,
        status := .success (Execution.committedPost located.frame.out
          located.frame.committed).output } ::
        staticViewChildReturns frame request (turn + 1) rest

/-- The projected source context, selector and return belong to this SAME
retained frame, not an independently chosen calldata or context. -/
def StaticViewTurn.Authentic (frame : Frame) (picked : StaticViewTurn) : Prop :=
  picked.1.frame.sevm.currentTarget = frame.context.pair ∧
  picked.1.frame.pc = 0 ∧ picked.1.frame.sevm.code = code ∧
  picked.1.frame.sevm.isStatic = true ∧
  picked.1.frame.sevm.benvStat.time = frame.context.timestamp ∧
  Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
  picked.2.argumentSize + 4 ≤ picked.1.frame.sevm.data.length ∧
  some (Execution.committedPost picked.1.frame.out picked.1.frame.committed).output =
    getterResult frame.current.state (picked.2.entry picked.1.frame.sevm)

/-- Actual target selection derives its complete singleton fold and a
continuation that can compose with later retained frames at the same checkpoint. -/
theorem staticView_target_fold_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn : Nat} {path : List Nat} {counter pc : Nat}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (sem : CodeSem) (image : sem.image = some code.toList)
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (installed : sem.At frame.context.pair pc sevm pre)
    (target : sevm.currentTarget = frame.context.pair)
    (rep : WriterRep K (pre.getStor frame.context.pair) frame.current.state)
    (fresh : WriterFreshKeys K (staticViewDecodedKeys sevm))
    (entry : pre.stack = [] ∧ pre.memory = Mem.empty)
    (representable : sevm.data.length < 2 ^ 256)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    ∃ picked : StaticViewTurn,
      Exec.retainedTargetFramesFromAt frame.context.pair path counter run committed =
        [picked.1] ∧ picked.Authentic frame ∧
      ∀ (tail : Transcript) (result : TurnsResult),
        ExactTurns frame request (turn + 1) tail result →
        ExactTurns frame request turn (staticViewTranscript [picked] tail)
          { result with childReturns :=
              staticViewChildReturns frame request turn [picked] ++ result.childReturns } := by
  have pcZero := (installed.2 target).2
  subst pc
  have codeList : sevm.code.toList = code.toList :=
    Option.some.inj ((installed.2 target).1.trans image)
  have codeEq : sevm.code = code := by
    have dataList : sevm.code.data.toList = code.data.toList := by
      simpa only [ByteArray.toList_eq_toList_data] using codeList
    exact congrArg ByteArray.mk (Array.toList_inj.mp dataList)
  cases out with
  | error error =>
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have raw : Exec 0 sevm (St pre [] Mem.empty pre.gasLeft) (.ok post) := by
      rw [← St.self entry.1 entry.2]
      exact run
    have currentRep : WriterRep K (pre.getStor sevm.currentTarget) frame.current.state := by
      rw [target]
      exact rep
    obtain ⟨view, selector, length, returned, _, _, _, _, _, consume, _⟩ :=
      staticView_target_turns_inv (frame := frame) (request := request)
        (turn := turn) (path := path) currentRep fresh representable target.symm
          time codeEq fork static raw
    let located : Exec.LocatedFrame := ⟨path, Exec.Frame.ofRun run committed⟩
    refine ⟨(located, view), ?_, ?_, ?_⟩
    · exact Exec.retainedTargetFramesFromAt_target _ _ _ run committed target
    · exact ⟨target, rfl, codeEq, static, time.symm, selector, length, returned⟩
    · intro tail result rest
      simpa only [staticViewTranscript, staticViewChildReturns, Execution.committedPost,
        List.cons_append, List.nil_append, located, Exec.Frame.ofRun] using
        consume tail result rest

theorem staticViewTranscript_append (left right : List StaticViewTurn) (tail : Transcript) :
    staticViewTranscript (left ++ right) tail =
      staticViewTranscript left (staticViewTranscript right tail) := by
  induction left with
  | nil => rfl
  | cons picked left ih =>
    rcases picked with ⟨located, view⟩
    simp only [List.cons_append, staticViewTranscript, ih]

theorem staticViewChildReturns_append (frame : Frame) (request : Request)
    (turn : Nat) (left right : List StaticViewTurn) :
    staticViewChildReturns frame request turn (left ++ right) =
      staticViewChildReturns frame request turn left ++
        staticViewChildReturns frame request (turn + left.length) right := by
  induction left generalizing turn with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero, staticViewChildReturns]
  | cons picked left ih =>
    rcases picked with ⟨located, view⟩
    simp only [List.cons_append, staticViewChildReturns, ih, List.length_cons]
    have counterEq : turn + 1 + left.length = turn + (left.length + 1) := by omega
    rw [counterEq]

/-- A committing static parent edge transports the SAME finite source
representation and installed image to its actual foreign continuation. -/
theorem staticView_parent_rep {K : WriterKey → Prop} {frame : Frame}
    {pc pc' : Nat} {sevm : Sevm} {pre inter : Devm} {out : Execution}
    (sem : CodeSem) (run : Exec pc sevm pre out) (next : Exec pc' sevm inter out)
    (committed : Execution.commits out = true)
    (edge : Exec.Deriv.ParentStep ⟨pc', sevm, inter, out, next⟩
      ⟨pc, sevm, pre, out, run⟩)
    (installed : sem.At frame.context.pair pc sevm pre)
    (foreign : sevm.currentTarget ≠ frame.context.pair)
    (rep : WriterRep K (pre.getStor frame.context.pair) frame.current.state)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    sem.At frame.context.pair pc' sevm inter ∧
      WriterRep K (inter.getStor frame.context.pair) frame.current.state := by
  have nonempty : (pre.getCode frame.context.pair).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.1.symm.trans (congrArg some empty)) rfl
  have codeEq := Blanc.Exec.Deriv.ParentStep.codePreserve edge frame.context.pair nonempty
  have storageEq : Devm.getStor inter = Devm.getStor pre :=
    (Exec.getStor_committedPost_eq_of_static next static committed fork).symm.trans
      (Exec.getStor_committedPost_eq_of_static run static committed fork)
  refine ⟨⟨?_, fun target => (foreign target).elim⟩, ?_⟩
  · rw [codeEq]
    exact installed.1
  · rw [congrFun storageEq frame.context.pair]
    exact rep

/-- The supplied interpreted spawn opens on the same finite Pair representation
and authentic installed image. All entry and environment facts are raw equations. -/
theorem staticView_child_environment {K : WriterKey → Prop} {frame : Frame}
    {pc pc' : Nat} {sevm : Sevm} {pre : Devm}
    {callee : Jaune.Frame} {resume : Resume} {child : Evm}
    (sem : CodeSem)
    (step : Evm.step ⟨pc, sevm, pre⟩ = .spawn callee resume pc')
    (enter : callee.enter = .run child)
    (installed : sem.At frame.context.pair pc sevm pre)
    (foreign : sevm.currentTarget ≠ frame.context.pair)
    (rep : WriterRep K (pre.getStor frame.context.pair) frame.current.state)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    sem.At frame.context.pair child.pc child.sta child.dyna ∧
      WriterRep K (child.dyna.getStor frame.context.pair) frame.current.state ∧
      (child.dyna.stack = [] ∧ child.dyna.memory = Mem.empty) ∧
      child.sta.data.length < 2 ^ 256 ∧
      frame.context.timestamp = child.sta.benvStat.time ∧
      child.sta.isStatic = true ∧ CoveredFork child.sta.benvStat.fork := by
  have nonempty : pre.getCode frame.context.pair ≠ .empty := by
    intro empty
    have imageEmpty : sem.image = some [] := by
      rw [← installed.1, empty]
      rw [ByteArray.toList_empty]
    exact sem.ne_nil imageEmpty rfl
  obtain ⟨pcZero, codes, actualCode⟩ := Blanc.Evm.step_spawn_child step enter
  have childInstalled : sem.At frame.context.pair child.pc child.sta child.dyna := by
    refine ⟨?_, ?_⟩
    · rw [codes]
      exact installed.1
    · intro target
      have away : sevm.currentTarget ≠ child.sta.currentTarget := by
        rw [target]
        exact foreign
      have codeEq : child.sta.code = pre.getCode frame.context.pair := by
        rw [← target]
        exact actualCode away (by rw [target]; exact nonempty)
          (by rw [target]; exact sem.not_delegation installed.1)
      exact ⟨(congrArg (fun bytes : ByteArray => some bytes.toList) codeEq).trans
        installed.1, pcZero⟩
  have storageEq := (Blanc.Evm.step_spawn_child_world fork step enter nonempty).1
  change child.dyna.getStor frame.context.pair = pre.getStor frame.context.pair at storageEq
  have childRep : WriterRep K (child.dyna.getStor frame.context.pair) frame.current.state := by
    rw [storageEq]
    exact rep
  obtain ⟨short, childFork⟩ := Blanc.ExecutionTrace.Evm.step_spawn_child_data fork step enter
  have childStatic := Blanc.Evm.step_run_isStatic step enter static
  obtain ⟨x, _, spawn, _⟩ := Evm.step_spawn_inv step
  have statEq : child.sta.benvStat = sevm.benvStat :=
    (Jaune.Frame.enter_run_benvStat enter).trans (Xinst.step_spawn_benvStat spawn)
  refine ⟨childInstalled, childRep, ?_, short, ?_, childStatic, childFork⟩
  · obtain ⟨benv, _, rfl⟩ := Jaune.Frame.enter_run_inv enter
    exact ⟨rfl, rfl⟩
  · rw [statEq]
    exact time

/-- The actual selected root supplies the same list-shaped continuation used
by the foreign structural cases; its finite footprint is the actual decoder. -/
theorem staticView_selected_root_fold {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn counter pc : Nat} {path : List Nat}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (sem : CodeSem) (image : sem.image = some code.toList)
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (installed : sem.At frame.context.pair pc sevm pre)
    (target : sevm.currentTarget = frame.context.pair)
    (rep : WriterRep K (pre.getStor frame.context.pair) frame.current.state)
    (fresh : ∀ located ∈ Exec.retainedTargetFramesFromAt frame.context.pair path counter run committed,
      WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm))
    (entry : pre.stack = [] ∧ pre.memory = Mem.empty)
    (representable : sevm.data.length < 2 ^ 256)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    ∃ views : List StaticViewTurn,
      views.map Prod.fst = Exec.retainedTargetFramesFromAt frame.context.pair path counter run committed ∧
      (∀ picked ∈ views, picked.Authentic frame) ∧
      (∀ (tail : Transcript) (result : TurnsResult),
        ExactTurns frame request (turn + views.length) tail result →
        ExactTurns frame request turn (staticViewTranscript views tail)
          { result with childReturns := staticViewChildReturns frame request turn views ++ result.childReturns }) := by
  have rootFresh : WriterFreshKeys K (staticViewDecodedKeys sevm) := by
    apply fresh ⟨path, Exec.Frame.ofRun run committed⟩
    rw [Exec.retainedTargetFramesFromAt_target _ _ _ run committed target]
    exact List.mem_cons_self
  obtain ⟨picked, projection, authentic, consume⟩ :=
    staticView_target_fold_inv (turn := turn) sem image run committed installed target
      rep rootFresh entry representable time static fork
  refine ⟨[picked], ?_, ?_, ?_⟩
  · simpa only [List.map_cons, List.map_nil] using projection.symm
  · intro picked' member
    have same := List.mem_singleton.mp member
    subst picked'
    exact authentic
  · intro tail result rest
    exact consume tail result rest

/-- Every retained static Pair view in the supplied execution contributes one
authentic source invocation in the existing traversal's exact order. -/
theorem staticView_retained_fold_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn counter pc : Nat} {path : List Nat}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (sem : CodeSem) (image : sem.image = some code.toList)
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (installed : sem.At frame.context.pair pc sevm pre)
    (rep : WriterRep K (pre.getStor frame.context.pair) frame.current.state)
    (fresh : ∀ located ∈ Exec.retainedTargetFramesFromAt frame.context.pair path counter run committed,
      WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm))
    (entry : sevm.currentTarget = frame.context.pair → pre.stack = [] ∧ pre.memory = Mem.empty)
    (representable : sevm.data.length < 2 ^ 256)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    ∃ views : List StaticViewTurn,
      views.map Prod.fst = Exec.retainedTargetFramesFromAt frame.context.pair path counter run committed ∧
      (∀ picked ∈ views, picked.Authentic frame) ∧
      (∀ (tail : Transcript) (result : TurnsResult),
        ExactTurns frame request (turn + views.length) tail result →
        ExactTurns frame request turn (staticViewTranscript views tail)
          { result with childReturns := staticViewChildReturns frame request turn views ++ result.childReturns }) := by
  revert committed installed rep fresh entry representable time static fork
  induction run generalizing path counter turn with
  | @halt pc sevm pre out step =>
    intro committed installed rep fresh entry representable time static fork
    by_cases target : sevm.currentTarget = frame.context.pair
    · exact staticView_selected_root_fold sem image (.halt step) committed installed target
        rep fresh (entry target) representable time static fork
    · refine ⟨[], ?_, ?_, ?_⟩
      · exact (Exec.retainedTargetFramesFromAt_halt _ _ _ step committed target).symm
      · intro picked member
        simp only [List.not_mem_nil] at member
      · intro tail result rest
        simpa only [List.length_nil, Nat.add_zero, staticViewTranscript,
          staticViewChildReturns, List.nil_append] using rest
  | @cont pc sevm pre pc' inter out step next ih =>
    intro committed installed rep fresh entry representable time static fork
    by_cases target : sevm.currentTarget = frame.context.pair
    · exact staticView_selected_root_fold sem image (.cont step next) committed installed target
        rep fresh (entry target) representable time static fork
    · obtain ⟨nextInstalled, nextRep⟩ := staticView_parent_rep sem (.cont step next) next
        committed (.cont step next) installed target rep static fork
      have projection := Exec.retainedTargetFramesFromAt_cont frame.context.pair path counter
        step next committed target
      obtain ⟨views, mapped, authentic, consume⟩ := ih (path := path) (counter := counter)
        (turn := turn) committed nextInstalled nextRep
        (fun located member => fresh located (by rw [projection]; exact member))
        (fun same => (target same).elim) representable time static fork
      exact ⟨views, mapped.trans projection.symm, authentic, consume⟩
  | doneErr step enter resumed =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre callee resume pc' result inter out step enter resumed next ih =>
    intro committed installed rep fresh entry representable time static fork
    by_cases target : sevm.currentTarget = frame.context.pair
    · exact staticView_selected_root_fold sem image (.doneOk step enter resumed next) committed
        installed target rep fresh (entry target) representable time static fork
    · obtain ⟨nextInstalled, nextRep⟩ := staticView_parent_rep sem (.doneOk step enter resumed next)
        next committed (.doneOk step enter resumed next) installed target rep static fork
      have projection := Exec.retainedTargetFramesFromAt_doneOk frame.context.pair path counter
        step enter resumed next committed target
      obtain ⟨views, mapped, authentic, consume⟩ := ih (path := path) (counter := counter + 1)
        (turn := turn) committed nextInstalled nextRep
        (fun located member => fresh located (by rw [projection]; exact member))
        (fun same => (target same).elim) representable time static fork
      exact ⟨views, mapped.trans projection.symm, authentic, consume⟩
  | runErr step enter child resumed childIH =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre callee resume pc' childEvm raw inter out step enter child resumed next childIH nextIH =>
    intro committed installed rep fresh entry representable time static fork
    by_cases target : sevm.currentTarget = frame.context.pair
    · exact staticView_selected_root_fold sem image (.runOk step enter child resumed next) committed
        installed target rep fresh (entry target) representable time static fork
    · obtain ⟨nextInstalled, nextRep⟩ := staticView_parent_rep sem (.runOk step enter child resumed next)
        next committed (.runOk step enter child resumed next) installed target rep static fork
      have projection := Exec.retainedTargetFramesFromAt_runOk frame.context.pair path counter
        step enter child resumed next committed target
      by_cases settles : Jaune.Frame.settlementCommits callee raw = true
      · have retained : Execution.commits raw = true := Jaune.Frame.raw_commits_of_settlementCommits settles
        obtain ⟨childInstalled, childRep, childEntry, childShort, childTime, childStatic, childFork⟩ :=
          staticView_child_environment sem step enter installed target rep time static fork
        obtain ⟨childViews, childMapped, childAuthentic, childConsume⟩ :=
          childIH (path := path ++ [counter]) (counter := 0) (turn := turn)
            retained childInstalled childRep
            (fun located member => fresh located (by
              rw [projection, dite_eq_left settles]
              exact List.mem_append.mpr (Or.inl member)))
            (fun _ => childEntry) childShort childTime childStatic childFork
        obtain ⟨nextViews, nextMapped, nextAuthentic, nextConsume⟩ :=
          nextIH (path := path) (counter := counter + 1) (turn := turn + childViews.length)
            committed nextInstalled nextRep
            (fun located member => fresh located (by
              rw [projection, dite_eq_left settles]
              exact List.mem_append.mpr (Or.inr member)))
            (fun same => (target same).elim) representable time static fork
        refine ⟨childViews ++ nextViews, ?_, ?_, ?_⟩
        · rw [List.map_append, childMapped, nextMapped, projection, dite_eq_left settles]
        · intro picked member
          rcases List.mem_append.mp member with left | right
          · exact childAuthentic picked left
          · exact nextAuthentic picked right
        · intro tail result rest
          have shifted : ExactTurns frame request ((turn + childViews.length) + nextViews.length) tail result := by
            simpa only [List.length_append, Nat.add_assoc] using rest
          have afterNext := nextConsume tail result shifted
          have afterChild := childConsume (staticViewTranscript nextViews tail)
            { result with childReturns :=
                staticViewChildReturns frame request (turn + childViews.length) nextViews ++ result.childReturns } afterNext
          simpa only [staticViewTranscript_append, staticViewChildReturns_append, List.append_assoc] using afterChild
      · have suffix : Exec.retainedTargetFramesFromAt frame.context.pair path counter
            (.runOk step enter child resumed next) committed =
            Exec.retainedTargetFramesFromAt frame.context.pair path (counter + 1) next committed := by
          simpa only [dite_eq_right settles, List.nil_append] using projection
        obtain ⟨views, mapped, authentic, consume⟩ := nextIH (path := path) (counter := counter + 1)
          (turn := turn) committed nextInstalled nextRep
          (fun located member => fresh located (by rw [suffix]; exact member))
          (fun same => (target same).elim) representable time static fork
        exact ⟨views, mapped.trans suffix.symm, authentic, consume⟩

/-- The supplied raw run determines its entire selected static queue and an
internally finished source consumption. A noncommitting root retains no subtree. -/
theorem staticView_raw_retained_turns_inv {K : WriterKey → Prop} {frame : Frame}
    {request : Request} {turn pc : Nat} {path : List Nat}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (sem : CodeSem) (image : sem.image = some code.toList)
    (run : Exec pc sevm pre out)
    (installed : sem.At frame.context.pair pc sevm pre)
    (rep : WriterRep K (pre.getStor frame.context.pair) frame.current.state)
    (fresh : ∀ located ∈ (Exec.retainedTargetTurnsAt frame.context.pair path run).filterMap Sum.getRight?,
      WriterFreshKeys K (staticViewDecodedKeys located.frame.sevm))
    (entry : sevm.currentTarget = frame.context.pair → pre.stack = [] ∧ pre.memory = Mem.empty)
    (representable : sevm.data.length < 2 ^ 256)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (static : sevm.isStatic = true) (fork : CoveredFork sevm.benvStat.fork) :
    ∃ views : List StaticViewTurn,
      views.map Prod.fst =
        (Exec.retainedTargetTurnsAt frame.context.pair path run).filterMap Sum.getRight? ∧
      (∀ picked ∈ views, picked.Authentic frame) ∧
      ExactTurns frame request turn (staticViewTranscript views .done)
        { complete := true, frame := frame,
          childReturns := staticViewChildReturns frame request turn views } := by
  by_cases committed : Execution.commits out = true
  · have bridge := Exec.retainedTargetTurnsAt_filterMap_eq frame.context.pair path run committed
    obtain ⟨views, mapped, authentic, consume⟩ :=
      staticView_retained_fold_inv (turn := turn) (counter := 0) sem image run committed
        installed rep (fun located member => fresh located (by rw [bridge]; exact member))
        entry representable time static fork
    refine ⟨views, mapped.trans bridge.symm, authentic, ?_⟩
    have finished := consume .done
      { complete := true, frame := frame, childReturns := [] }
      (ExactTurns.done frame request (turn + views.length))
    simpa only [List.append_nil] using finished
  · have empty :
        (Exec.retainedTargetTurnsAt frame.context.pair path run).filterMap Sum.getRight? = [] := by
      simp only [Exec.retainedTargetTurnsAt, dite_eq_right committed, List.filterMap_nil]
    refine ⟨[], empty.symm, ?_, ?_⟩
    · intro picked member
      simp only [List.not_mem_nil] at member
    · exact ExactTurns.done frame request turn

/-- A static queue and its source consumption, indexed by the same primitive
call. This local packet does not assert an original parent-prefix occurrence. -/
structure PairStaticCallTrace (D : Exec.Deriv) (sevm : Sevm) (frame : Frame)
    (request : Request) (pre d : Devm) (target : B256) (views : List StaticViewTurn) where
  slot : Xlot
  run : Xinst.Run sevm pre .staticcall slot (.ok d)
  origin :
    (slot = .none ∧ views = [] ∧ sevm.benvStat.rules.isPrecomp target.toAdr) ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw),
        slot = .some ⟨child, raw⟩ ∧ Execution.commits raw = true ∧
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        views.map Prod.fst =
          (Exec.retainedTargetTurnsAt frame.context.pair [] childRun).filterMap Sum.getRight?
  authentic : ∀ picked ∈ views, picked.Authentic frame
  during : ExactTurns frame request 0 (staticViewTranscript views .done)
    { complete := true, frame := frame,
      childReturns := staticViewChildReturns frame request 0 views }

/-- The static-view turn queue of one actual STATICCALL at `target`: empty at an enabled precompile,
or exactly the retained static turns of `pair` of the actually committed child, whose raw frame roots
are among those of `D`. -/
def ViewQueueOrigin (D : Exec.Deriv) (sevm : Sevm) (pair target : Adr)
    (views : List StaticViewTurn) : Prop :=
  views = [] ∧ sevm.benvStat.rules.isPrecomp target ∨ ∃ (child : Evm) (raw : Execution)
    (childRun : Exec child.pc child.sta child.dyna raw),
    Execution.commits raw = true ∧
    (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
    views.map Prod.fst = (Exec.retainedTargetTurnsAt pair [] childRun).filterMap Sum.getRight?

/-- The provenance a static-view turn queue carries for one actual STATICCALL. -/
def PairViewProvenance (D : Exec.Deriv) (sevm : Sevm) (frame : Frame) (t : B256)
    (views : List StaticViewTurn) : Prop :=
  (∀ picked ∈ views, picked.Authentic frame) ∧
  ViewQueueOrigin D sevm frame.context.pair t.toAdr views

end Blanc.Lift.UniswapV2Pair
