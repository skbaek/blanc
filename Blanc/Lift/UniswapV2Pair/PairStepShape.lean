import Blanc.Lift.UniswapV2Pair.PairPositionalCalls
import Blanc.Lift.UniswapV2Pair.PairModelFix

/-!
# Shape of a consumed Pair step, from positional consumption

`PositionalConsumes.segInv` carries the model segment invariant (`SegInv`,
`Blanc/Lift/UniswapV2Pair/PairModelFix.lean`) along an actual positional consumption.  From a segment
satisfying it, and with no non-static frame at the Pair below the consumed span called by the factory
(the step-local form of H1):

* the consumed frame's final model state keeps the tokens and the factory, and an outer step ends
  unlocked;
* every mutable direct child is a `transfer` request to one of the two tokens or a callback to a
  non-token address (outer mode), and there is none in nested mode;
* every re-entered non-static frame at the Pair below the span has only static children.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace

/-! ## Generic frame facts -/

/-- A retained descendant of a retained descendant is a retained descendant. -/
theorem Exec.descendantFrames_trans :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out)
      {F D : Exec.Frame}, F ∈ Exec.descendantFrames run → D ∈ Exec.descendantFrames F.run →
        D ∈ Exec.descendantFrames run := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro F D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | cont _ _ ih =>
    intro F D member inner
    simp only [Exec.descendantFrames] at member ⊢
    exact ih member inner
  | doneErr _ _ _ => intro F D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | doneOk _ _ _ _ ih =>
    intro F D member inner
    simp only [Exec.descendantFrames] at member ⊢
    exact ih member inner
  | runErr _ _ _ _ => intro F D member; simp only [Exec.descendantFrames, List.not_mem_nil] at member
  | @runOk pc sevm devm frame rsm pc' cevm raw devm' ex step enter child resume next childIh nextIh =>
      intro F D member inner
      by_cases settles : Jaune.Frame.settlementCommits frame raw = true
      · rw [Exec.descendantFrames_runOk_of_settlementCommits step enter child resume next settles]
          at member ⊢
        simp only [List.mem_cons, List.mem_append] at member ⊢
        rcases member with (rfl | inChild) | inNext
        · exact Or.inl (Or.inr inner)
        · exact Or.inl (Or.inr (childIh inChild inner))
        · exact Or.inr (nextIh inNext inner)
      · rw [Exec.descendantFrames_runOk_of_not_settlementCommits step enter child resume next settles]
          at member ⊢
        exact nextIh member inner

/-- The continuation's retained frames are retained frames of the node. -/
theorem Exec.Deriv.ParentStep.descendantFrames_subset {N returned : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep returned N) :
    ∀ D ∈ Exec.descendantFrames returned.exc, D ∈ Exec.descendantFrames N.exc := by
  intro D member
  cases edge with
  | cont hstep next => simpa only [Exec.descendantFrames] using member
  | doneOk hstep henter hresume next => simpa only [Exec.descendantFrames] using member
  | runOk hstep henter child hresume next =>
      simp only [Exec.descendantFrames, List.mem_append]
      exact Or.inr member

/-! ## Exact turns of a static request leave the frame unchanged -/

theorem ExactConsumes.finished_frame {fr : Frame} {bytes : Bytes} {transcript : Transcript}
    {out : RunResult} (h : ExactConsumes (.finished fr bytes) transcript out) : out.frame = fr := by
  cases h
  rfl

theorem ExactConsumes.failed_frame {fr : Frame} {failure : Failure} {transcript : Transcript}
    {out : RunResult} (h : ExactConsumes (.failed fr failure) transcript out) : out.frame = fr := by
  cases h
  rfl

/-- Turns that only re-enter the Pair statically. -/
def Transcript.StaticInvokes : Transcript → Prop
  | .done => True
  | .invoke _ _ isStatic _ _ tail => isStatic = true ∧ tail.StaticInvokes
  | _ => False

theorem staticViewTranscript_staticInvokes {frame : Frame} :
    ∀ views : List StaticViewTurn, (∀ picked ∈ views, picked.Authentic frame) →
      (staticViewTranscript views .done).StaticInvokes
  | [], _ => trivial
  | picked :: rest, authentic =>
    ⟨(authentic picked List.mem_cons_self).2.2.2.1,
      staticViewTranscript_staticInvokes rest fun p member =>
        authentic p (List.mem_cons_of_mem _ member)⟩

/-- **Turns of a static request, or turns that re-enter only statically, leave the parent frame
unchanged**: every re-entered entry is static, hence terminal at the same checkpoint
(`startTyped_static`). -/
theorem ExactTurns.static_frame {frame : Frame} {request : Request} {turn : Nat}
    {turns : Transcript} {out : TurnsResult} (h : ExactTurns frame request turn turns out)
    (static : externalStatic frame request = true ∨ turns.StaticInvokes) : out.frame = frame := by
  refine ExactTurns.rec (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun frame request _ turns out _ =>
      externalStatic frame request = true ∨ turns.StaticInvokes → out.frame = frame)
    (fun _ _ => trivial) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) ?_ ?_ ?_ h static
  · intro frame request turn _
    rfl
  · intro frame request turn emitter topics data tail out mutable _ _ static
    rcases static with static | impossible
    · rw [mutable] at static
      cases static
    · exact impossible.elim
  · intro frame request turn sender value isStatic entry transcript tail child out selected rest
      _ ihRest static
    have childStatic : (childContext frame request turn sender value isStatic).isStatic = true := by
      rcases static with static | ⟨invokeStatic, -⟩
      · simp only [childContext, static, Bool.true_or]
      · simp only [childContext, invokeStatic, Bool.or_true]
    obtain ⟨terminal, current⟩ := startTyped_static (current := frame.current) entry childStatic
    have childFrame : child.frame =
        (startTyped frame.current (childContext frame request turn sender value isStatic)
          entry).frame := by
      revert selected terminal
      generalize startTyped frame.current (childContext frame request turn sender value isStatic)
        entry = segment
      intro selected terminal
      cases segment with
      | finished fr bytes => exact selected.finished_frame
      | failed fr failure => exact selected.failed_frame
      | suspended fr r c => exact terminal.elim
    have settled : ({ frame with current := child.frame.current } : Frame) = frame := by
      rw [childFrame, current]
    have restFrame := ihRest (by
      rw [settled]
      rcases static with static | ⟨-, tailStatic⟩
      · exact Or.inl static
      · exact Or.inr tailStatic)
    change out.frame = frame
    rw [restFrame, settled]

/-- A positional consumption of a terminal segment returns its frame. -/
theorem PositionalConsumes.terminal_frame {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (consumed : PositionalConsumes root start index segment transcript out)
    (terminal : segment.Terminal) : out.frame = segment.frame := by
  cases consumed with
  | finished => rfl
  | failed => rfl
  | nextCall => exact terminal.elim
  | nextMutableCall => exact terminal.elim

/-! ## Observed calls -/

/-- A Pair frame selected into a mutable call's event queue is the entered child or one of its
retained descendants, at the Pair. -/
theorem SourceSlotEvents.located_child {root : Exec.Deriv} {x : Xinst}
    {call : CallOccurrenceStep root x} {pair : Adr} {index : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)} (observed : SourceSlotEvents call pair index events)
    {located : Exec.LocatedFrame} (member : Sum.inr located ∈ events) :
    ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame) (resume : Resume) (pc' : Nat)
      (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (next : Exec pc' call.occurrence.node.sevm call.returned.devm call.occurrence.node.exn)
      (spawn : Evm.step ⟨call.occurrence.node.pc, call.occurrence.node.sevm,
        call.occurrence.node.devm⟩ = .spawn callee resume pc')
      (enter : callee.enter = .run childEvm)
      (resumed : resume.run (callee.settle raw) = .ok call.returned.devm)
      (settles : Jaune.Frame.settlementCommits callee raw = true),
      call.occurrence.node.exc = .runOk spawn enter childRun resumed next ∧
      (located.frame = Exec.Frame.ofRun childRun
          (Jaune.Frame.raw_commits_of_settlementCommits settles) ∨
        located.frame ∈ Exec.descendantFrames childRun) ∧
      located.frame.sevm.currentTarget = pair := by
  rcases observed with ⟨-, rfl⟩ |
    ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, -, run, rfl⟩
  · cases member
  by_cases settles : Jaune.Frame.settlementCommits callee raw = true
  · rw [dite_eq_left_of_eq_true (eq_true settles)] at member
    have selected : located ∈ (Exec.targetLogEventsFrom pair [index] 0 child
        (Jaune.Frame.raw_commits_of_settlementCommits settles)).filterMap Sum.getRight? :=
      List.mem_filterMap.mpr ⟨_, member, rfl⟩
    rw [Exec.targetLogEventsFrom_frames] at selected
    have spec := Exec.retainedTargetTurnsFrom_targets_spec pair [index] 0 child
      (Jaune.Frame.raw_commits_of_settlementCommits settles)
    have mapped := List.mem_map_of_mem (f := Exec.LocatedFrame.frame) (spec.1.subset selected)
    simp only [List.map_cons, Exec.descendantFramePaths_map_frame] at mapped
    exact ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, settles, run,
      List.mem_cons.mp mapped, spec.2.2.1 located selected⟩
  · rw [dite_eq_right_of_eq_false (eq_false settles)] at member
    cases member

/-- A Pair frame selected into a mutable call's event queue is a retained descendant of the calling
node, at the Pair. -/
theorem SourceSlotEvents.located_mem {root : Exec.Deriv} {x : Xinst}
    {call : CallOccurrenceStep root x} {pair : Adr} {index : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)} (observed : SourceSlotEvents call pair index events)
    {located : Exec.LocatedFrame} (member : Sum.inr located ∈ events) :
    located.frame ∈ Exec.descendantFrames call.occurrence.node.exc ∧
      located.frame.sevm.currentTarget = pair := by
  obtain ⟨_, _, _, _, _, child, next, spawn, enter, resumed, settles, run, inside, target⟩ :=
    observed.located_child member
  refine ⟨?_, target⟩
  rw [run, Exec.descendantFrames_runOk_of_settlementCommits spawn enter child resumed next settles]
  rcases inside with here | inner
  · rw [here]
    exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ inner)

/-- Below a static request, every selected Pair frame is static. -/
theorem SourceCallAt.located_static {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} (observed : SourceCallAt root frame request reply index)
    {events : List (Log ⊕ Exec.LocatedFrame)}
    (queue : SourceSlotEvents observed.call frame.context.pair index events)
    (static : externalStatic frame request = true) {located : Exec.LocatedFrame}
    (member : Sum.inr located ∈ events) : located.frame.sevm.isStatic = true := by
  obtain ⟨childEvm, _, callee, _, _, child, _, spawn, enter, _, _, _, inside, _⟩ :=
    queue.located_child member
  have same := spawn.symm.trans observed.spawned
  simp only [Step.spawn.injEq] at same
  obtain ⟨rfl, -, -⟩ := same
  have childStatic : childEvm.sta.isStatic = true := by
    rw [Frame.enter_run_isStatic enter]
    exact observed.static.trans static
  rcases inside with here | inner
  · rw [here]
    exact childStatic
  · exact Exec.descendantFrames_isStatic child childStatic _ inner

/-- A child entered at an observed call: the request's target, the Pair as caller, the request's
calldata and static flag. -/
theorem SourceCallAt.child_facts {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} (observed : SourceCallAt root frame request reply index)
    {c : Exec.Frame} {childEvm : Evm}
    (enter : (Jaune.Frame.ofCall observed.message).enter = .run childEvm)
    (sevmEq : c.sevm = childEvm.sta) :
    c.sevm.currentTarget = request.target ∧ c.sevm.caller = root.sevm.currentTarget ∧
      c.sevm.data = request.calldata ∧ c.sevm.isStatic = externalStatic frame request := by
  obtain ⟨x, kind, step⟩ := observed.xstep
  have target := Xinst.step_callKind_spawn_target kind step
  have targetEq : observed.message.currentTarget = request.target :=
    Option.some.inj ((target : observed.message.target = _).symm.trans observed.target)
  have pairEq := observed.pair_eq
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv enter
  rw [sevmEq]
  exact ⟨targetEq, observed.caller.trans pairEq, observed.calldata, observed.static⟩

/-! ## The invariant along a positional consumption -/

/-- A mutable child of the outer shape: a request of shape `ReqShape` at the request's target,
called by the Pair with the request's calldata. -/
def ShapedChild (t0 t1 pair : Adr) (c : Exec.Frame) : Prop :=
  ∃ request, ReqShape t0 t1 request ∧ c.sevm.currentTarget = request.target ∧
    c.sevm.caller = pair ∧ c.sevm.data = request.calldata

/-- No non-static frame at `pair` among `frames` is called by `f` (the step-local form of H1). -/
def FactoryQuiet (f pair : Adr) (frames : List Exec.Frame) : Prop :=
  ∀ D ∈ frames, D.sevm.currentTarget = pair → D.sevm.isStatic = false → D.sevm.caller ≠ f

/-- Every non-static frame at `pair` among `frames` has only static children. -/
def LockedBelow (pair : Adr) (frames : List Exec.Frame) : Prop :=
  ∀ D ∈ frames, D.sevm.currentTarget = pair → D.sevm.isStatic = false →
    ∀ c ∈ Exec.childFrames D.run, c.sevm.isStatic = true

/-- What a positional consumption from an invariant segment guarantees. -/
def ConsumedFix (nested : Bool) (t0 t1 f : Adr) (root start : Exec.Deriv) (out : RunResult) :
    Prop :=
  FrameFix nested t0 t1 f out.frame ∧
    (nested = false → ∀ bytes, out.status = .success bytes →
      out.frame.current.state.unlocked = 1) ∧
    (∀ c ∈ Exec.childFrames start.exc, c.sevm.isStatic = false →
      nested = false ∧ ShapedChild t0 t1 root.sevm.currentTarget c) ∧
    LockedBelow root.sevm.currentTarget (Exec.descendantFrames start.exc)

/-- What mutable turns guarantee about the parent frame and the selected Pair frames. -/
def TurnsFix (t0 t1 f : Adr) (frame : Frame) (request : Request)
    (events : List (Log ⊕ Exec.LocatedFrame)) (out : TurnsResult) : Prop :=
  TokensFix t0 t1 f out.frame.current.state ∧ out.frame.checkpoint = frame.checkpoint ∧
    (externalStatic frame request = false → out.frame.current.state.unlocked ≠ 1) ∧
    (externalStatic frame request = true → out.frame.current = frame.current) ∧
    ∀ located, Sum.inr located ∈ events →
      LockedBelow located.frame.sevm.currentTarget (Exec.committedFrames located.frame.run)

theorem frameFix_of_parts {nested : Bool} {t0 t1 f : Adr} {frame fr : Frame}
    (fix : FrameFix nested t0 t1 f frame) (tokens : TokensFix t0 t1 f fr.current.state)
    (checkpoint : fr.checkpoint = frame.checkpoint)
    (locked : nested = true → fr.current.state.unlocked ≠ 1) : FrameFix nested t0 t1 f fr := by
  obtain ⟨-, chk, lockedFix, openFix⟩ := fix
  refine ⟨tokens, checkpoint ▸ chk, fun h => ⟨locked h, ?_⟩, fun h => checkpoint ▸ openFix h⟩
  rw [checkpoint]
  exact (lockedFix h).2

/-- **The segment invariant along an actual positional consumption.** -/
theorem PositionalConsumes.segInv {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (consumed : PositionalConsumes root start index segment transcript out) :
    ∀ {nested : Bool} {t0 t1 f : Adr}, SegInv nested t0 t1 f segment →
      FactoryQuiet f root.sevm.currentTarget (Exec.descendantFrames start.exc) →
      ConsumedFix nested t0 t1 f root start out := by
  refine PositionalConsumes.rec
    (motive_1 := fun root start _ segment _ out _ =>
      ∀ {nested : Bool} {t0 t1 f : Adr}, SegInv nested t0 t1 f segment →
        FactoryQuiet f root.sevm.currentTarget (Exec.descendantFrames start.exc) →
        ConsumedFix nested t0 t1 f root start out)
    (motive_2 := fun frame request _ events _ out _ =>
      ∀ {t0 t1 f : Adr}, TokensFix t0 t1 f frame.current.state →
        (externalStatic frame request = false → frame.current.state.unlocked ≠ 1) →
        (externalStatic frame request = true →
          ∀ located, Sum.inr located ∈ events → located.frame.sevm.isStatic = true) →
        (∀ located, Sum.inr located ∈ events →
          FactoryQuiet f located.frame.sevm.currentTarget (Exec.committedFrames located.frame.run)) →
        TurnsFix t0 t1 f frame request events out) ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed
  · -- finished
    intro root start index frame bytes free nested t0 t1 f inv _
    obtain ⟨fix, opened⟩ := inv
    refine ⟨fix, fun h _ _ => opened h, ?_, ?_⟩
    · intro c member
      rw [Exec.childFrames_eq_nil_of_free start free] at member
      cases member
    · intro D member
      rw [Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt start.exc free] at member
      cases member
  · -- failed
    intro root start index frame failure genuine free nested t0 t1 f inv _
    refine ⟨inv, fun _ _ status => RunStatus.noConfusion status, ?_, ?_⟩
    · intro c member
      rw [Exec.childFrames_eq_nil_of_free start free] at member
      cases member
    · intro D member
      rw [Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt start.exc free] at member
      cases member
  · -- nextCall
    intro root start index frame request continuation reply turns tail executed out
      observed gap present noCodeTurns during rest ih nested t0 t1 f inv quiet
    obtain ⟨fix, contFix, shape, permitInv, postInv⟩ := inv
    have unchanged : executed.frame = frame := by
      cases during with
      | staticViews views mapped authentic consumed =>
        exact consumed.static_frame (Or.inr (staticViewTranscript_staticInvokes views authentic))
    have prior : (if reply.success then executed.frame
        else { executed.frame with current := frame.current }) = frame := by
      split <;> rw [unchanged]
    have restQuiet : FactoryQuiet f root.sevm.currentTarget
        (Exec.descendantFrames observed.call.returned.exc) := fun D member =>
      quiet D (by
        rw [gap.descendantFrames_eq]
        exact Exec.Deriv.ParentStep.descendantFrames_subset observed.call.edge D member)
    have resumed := resumeSegment_segInv (request := request) (reply := reply) fix contFix
      (fun h hn => (permitInv h).2 hn) postInv
    rw [← prior] at resumed
    obtain ⟨outFix, outOpen, outChildren, outLocked⟩ := ih resumed restQuiet
    refine ⟨outFix, outOpen, ?_, ?_⟩
    · intro c member mutable
      rw [gap.childFrames_eq] at member
      rcases Exec.Deriv.ParentStep.childFrames_spawn observed.call.edge observed.spawned c member with
        later | ⟨childEvm, enter, sevmEq, -⟩
      · exact outChildren c later mutable
      · obtain ⟨target, caller, data, static⟩ := observed.child_facts enter sevmEq
        obtain ⟨nestedFalse, reqShape⟩ := shape (static.symm.trans mutable)
        exact ⟨nestedFalse, request, reqShape, target, caller, data⟩
    · intro D member atRoot mutable
      rw [gap.descendantFrames_eq] at member
      rcases observed.descendant_split observed.queue D member atRoot with
        later | ⟨located, mem, -, inside⟩
      · exact outLocked D later atRoot mutable
      · cases during with
        | staticViews views mapped authentic consumed =>
          rw [← mapped] at mem
          obtain ⟨picked, pickedMem, rfl⟩ := List.mem_map.mp mem
          have static : picked.1.frame.sevm.isStatic = true := (authentic picked pickedMem).2.2.2.1
          rcases Exec.Frame.mem_committedFrames.mp inside with rfl | deeper
          · rw [static] at mutable; cases mutable
          · rw [Exec.descendantFrames_isStatic picked.1.frame.run static D deeper] at mutable
            cases mutable
  · -- nextMutableCall
    intro root start index frame request continuation reply turns tail executed out events
      observed gap queue present noCodeTurns during rest ihDuring ihRest nested t0 t1 f inv quiet
    obtain ⟨fix, contFix, shape, permitInv, postInv⟩ := inv
    have pairEq := observed.pair_eq
    have locatedQuiet : ∀ located, Sum.inr located ∈ events →
        FactoryQuiet f located.frame.sevm.currentTarget (Exec.committedFrames located.frame.run) := by
      intro located member D inside atLocated mutable
      obtain ⟨inNode, target⟩ := queue.located_mem member
      have inStart : D ∈ Exec.descendantFrames start.exc := by
        rw [gap.descendantFrames_eq]
        rcases Exec.Frame.mem_committedFrames.mp inside with rfl | deeper
        · exact inNode
        · exact Exec.descendantFrames_trans _ inNode deeper
      exact quiet D inStart (atLocated.trans (target.trans pairEq)) mutable
    have frameLock : externalStatic frame request = false → frame.current.state.unlocked ≠ 1 :=
      fun h => (postInv fun hp => absurd (h.symm.trans (permitInv hp).1) Bool.false_ne_true).2
    obtain ⟨exTokens, exChk, exLock, exStatic, exLocked⟩ :=
      ihDuring fix.1 frameLock (fun h located member => observed.located_static queue h member)
        locatedQuiet
    generalize hP : (if reply.success = true then executed.frame
      else { executed.frame with current := frame.current }) = P at ihRest
    have pChk : P.checkpoint = frame.checkpoint := by
      rw [← hP]
      split <;> exact exChk
    have pCur : P.current = executed.frame.current ∨ P.current = frame.current := by
      rw [← hP]
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    have priorFacts : FrameFix nested t0 t1 f P ∧
        (continuation.IsPermit → nested = false → P.current.state.unlocked = 1) ∧
        (¬ continuation.IsPermit → nested = false ∧ P.current.state.unlocked ≠ 1) := by
      by_cases hs : externalStatic frame request = true
      · have same : P.current = frame.current := by
          rcases pCur with h | h
          · rw [h, exStatic hs]
          · exact h
        refine ⟨frameFix_of_parts fix (by rw [same]; exact fix.1) pChk
          (fun h => by rw [same]; exact (fix.2.2.1 h).1), fun hp hn => ?_, fun hp => ?_⟩
        · rw [same]
          exact (permitInv hp).2 hn
        · rw [same]
          exact postInv hp
      · have mutable : externalStatic frame request = false := by
          simpa only [Bool.not_eq_true] using hs
        have notPermit : ¬ continuation.IsPermit := fun hp => hs (permitInv hp).1
        obtain ⟨nestedFalse, frameLocked⟩ := postInv notPermit
        have pTok : TokensFix t0 t1 f P.current.state := by
          rcases pCur with h | h
          · rw [h]; exact exTokens
          · rw [h]; exact fix.1
        have pLock : P.current.state.unlocked ≠ 1 := by
          rcases pCur with h | h
          · rw [h]; exact exLock mutable
          · rw [h]; exact frameLocked
        exact ⟨frameFix_of_parts fix pTok pChk
          (fun h => absurd (nestedFalse.symm.trans h) Bool.false_ne_true),
          fun hp => absurd hp notPermit, fun _ => ⟨nestedFalse, pLock⟩⟩
    have restQuiet : FactoryQuiet f root.sevm.currentTarget
        (Exec.descendantFrames observed.call.returned.exc) := fun D member =>
      quiet D (by
        rw [gap.descendantFrames_eq]
        exact Exec.Deriv.ParentStep.descendantFrames_subset observed.call.edge D member)
    obtain ⟨outFix, outOpen, outChildren, outLocked⟩ :=
      ihRest (resumeSegment_segInv (request := request) (reply := reply) priorFacts.1 contFix
        priorFacts.2.1 priorFacts.2.2) restQuiet
    refine ⟨outFix, outOpen, ?_, ?_⟩
    · intro c member mutable
      rw [gap.childFrames_eq] at member
      rcases Exec.Deriv.ParentStep.childFrames_spawn observed.call.edge observed.spawned c member with
        later | ⟨childEvm, enter, sevmEq, -⟩
      · exact outChildren c later mutable
      · obtain ⟨target, caller, data, static⟩ := observed.child_facts enter sevmEq
        obtain ⟨nestedFalse, reqShape⟩ := shape (static.symm.trans mutable)
        exact ⟨nestedFalse, request, reqShape, target, caller, data⟩
    · intro D member atRoot mutable
      rw [gap.descendantFrames_eq] at member
      rcases observed.descendant_split queue.queue D member atRoot with
        later | ⟨located, mem, locatedAt, inside⟩
      · exact outLocked D later atRoot mutable
      · have event : Sum.inr located ∈ events := by
          obtain ⟨event, eventMem, picked⟩ := List.mem_filterMap.mp mem
          cases event with
          | inl log => cases picked
          | inr located' =>
            cases picked
            exact eventMem
        exact exLocked located event D inside (atRoot.trans locatedAt.symm) mutable
  · -- done
    intro frame request turn t0 t1 f tokens lockP _ _
    exact ⟨tokens, rfl, lockP, fun _ => rfl, fun _ member => by cases member⟩
  · -- foreignLog
    intro frame request turn log events tail out mutable rest ih t0 t1 f tokens lockP staticLoc quiet
    obtain ⟨outTokens, outChk, outLock, outStatic, outLocked⟩ :=
      ih tokens lockP (fun h => absurd (mutable.symm.trans h) Bool.false_ne_true)
        (fun located member => quiet located (List.mem_cons_of_mem _ member))
    refine ⟨outTokens, outChk, outLock, fun h => absurd (mutable.symm.trans h) Bool.false_ne_true,
      fun located member => ?_⟩
    rcases List.mem_cons.mp member with impossible | later
    · cases impossible
    · exact outLocked located later
  · -- invoke
    intro frame request turn located entry events transcript tail child out selected output rest
      ihSelected ihRest t0 t1 f tokens lockP staticLoc quiet
    have headQuiet := quiet located List.mem_cons_self
    have tailQuiet : ∀ l, Sum.inr l ∈ events →
        FactoryQuiet f l.frame.sevm.currentTarget (Exec.committedFrames l.frame.run) :=
      fun l member => quiet l (List.mem_cons_of_mem _ member)
    by_cases hs : externalStatic frame request = true
    · have childStatic : (childContext frame request turn located.frame.sevm.caller
          located.frame.sevm.value located.frame.sevm.isStatic).isStatic = true := by
        simp only [childContext, hs, Bool.true_or]
      obtain ⟨terminal, current⟩ := startTyped_static (current := frame.current) entry childStatic
      have childFrame := selected.terminal_frame terminal
      have settled : ({ frame with current := child.frame.current } : Frame) = frame := by
        rw [childFrame, current]
      rw [settled] at ihRest
      obtain ⟨outTokens, outChk, outLock, outStatic, outLocked⟩ :=
        ihRest tokens lockP (fun h l member => staticLoc h l (List.mem_cons_of_mem _ member))
          tailQuiet
      refine ⟨outTokens, outChk, outLock, outStatic, fun l member => ?_⟩
      rcases List.mem_cons.mp member with same | later
      · cases same
        have locatedStatic := staticLoc hs located List.mem_cons_self
        intro D inside _ mutable
        rcases Exec.Frame.mem_committedFrames.mp inside with rfl | deeper
        · rw [locatedStatic] at mutable; cases mutable
        · rw [Exec.descendantFrames_isStatic located.frame.run locatedStatic D deeper] at mutable
          cases mutable
      · exact outLocked l later
    · have mutable : externalStatic frame request = false := by
        simpa only [Bool.not_eq_true] using hs
      have nestedInv := startTyped_segInv_nested (entry := entry) tokens (lockP mutable)
        (ctx := childContext frame request turn located.frame.sevm.caller located.frame.sevm.value
          located.frame.sevm.isStatic) (fun h =>
          headQuiet located.frame (Exec.Frame.mem_committedFrames.mpr (Or.inl rfl)) rfl
            (by simpa only [childContext, mutable, Bool.false_or] using h))
      obtain ⟨childFix, -, childChildren, childLocked⟩ :=
        ihSelected nestedInv (fun D member => headQuiet D
          (Exec.Frame.mem_committedFrames.mpr (Or.inr member)))
      obtain ⟨outTokens, outChk, outLock, -, outLocked⟩ :=
        ihRest childFix.1 (fun _ => (childFix.2.2.1 rfl).1)
          (fun h => absurd (mutable.symm.trans h) Bool.false_ne_true) tailQuiet
      refine ⟨outTokens, outChk, outLock, fun h => absurd (mutable.symm.trans h) Bool.false_ne_true,
        fun l member => ?_⟩
      rcases List.mem_cons.mp member with same | later
      · cases same
        intro D inside atLocated mutableD
        rcases Exec.Frame.mem_committedFrames.mp inside with rfl | deeper
        · intro c childMem
          cases hc : c.sevm.isStatic
          · exact Bool.noConfusion (childChildren c childMem hc).1
          · rfl
        · exact childLocked D deeper atLocated mutableD
      · exact outLocked l later

end Blanc.Lift.UniswapV2Pair
