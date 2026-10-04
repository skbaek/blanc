import Blanc.Lift.TargetLogEvents
import Blanc.Lift.UniswapV2Pair.ApproveSource

/-!
# Turn queues of a mutable external call

A non-static external call made by a Pair frame runs arbitrary callee code. Its source
turn queue is derived from the actual execution: in retained chronological order, every
actual successful LOG of a foreign frame becomes a `.foreignLog` turn, and every retained
frame of the Pair becomes one `.invoke` turn, consumed whole by a per-frame supply. Failed
or rolled-back Pair frames are not retained and never appear.

The fold is entry-parametric: `PairFrameSupply` says how ONE committed Pair frame at the
current checkpoint is consumed (which entries can commit, the storage representation it
transports, and its own raw logs). Skim's transfers instantiate it with the entries that
can commit while the Pair is locked; Burn's transfers and the swap callback can reuse the
fold with the same or another supply.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- One retained event of a mutable call as the source consumes it: an actual foreign LOG,
or a retained Pair frame with its source entry and nested transcript. -/
abbrev MutableTurn := Log ⊕ (Exec.LocatedFrame × Entry × Transcript)

/-- Forget the source choice of a turn. -/
def MutableTurn.event : MutableTurn → Log ⊕ Exec.LocatedFrame
  | .inl log => .inl log
  | .inr picked => .inr picked.1

/-- The source transcript projection of retained events, in order. -/
def mutableTranscript : List MutableTurn → Transcript → Transcript
  | [], tail => tail
  | .inl log :: rest, tail =>
      .foreignLog log.address log.topics log.data (mutableTranscript rest tail)
  | .inr (located, entry, nested) :: rest, tail =>
      .invoke located.frame.sevm.caller located.frame.sevm.value located.frame.sevm.isStatic
        entry nested (mutableTranscript rest tail)

theorem mutableTranscript_append (left right : List MutableTurn) (tail : Transcript) :
    mutableTranscript (left ++ right) tail =
      mutableTranscript left (mutableTranscript right tail) := by
  induction left with
  | nil => rfl
  | cons turn left ih =>
    rcases turn with log | ⟨located, entry, nested⟩
    · simp only [List.cons_append, mutableTranscript, ih]
    · simp only [List.cons_append, mutableTranscript, ih]

/-- The raw image of a pending source log; owned events are encoded by `owned`. -/
def PendingLog.rawWith (owned : Event → Option Log) : PendingLog → Option Log
  | .owned _ event => owned event
  | .foreign _ emitter topics data => some ⟨emitter, topics, data⟩

/-- How one committed root frame of the Pair at `pair`, entered at the current
checkpoint, is consumed: an exact source invocation, its storage transport under `Rep`,
and its own raw logs as the source's appended logs. `Good` is a trace-local admission of
the frame (for example its decoded keys lie in a separated universe); `Auth` ties the
source entry and nested transcript to the same raw frame. -/
def PairFrameSupply (pair : Adr) (Rep : State → Stor → Prop) (Good : Sevm → Prop)
    (Auth : Sevm → Devm → Entry → Transcript → Prop) (owned : Event → Option Log) : Prop :=
  ∀ (current : Checkpoint) (invocation : List Nat) {sevm : Sevm} {b post : Devm} {G : Nat},
    Exec 0 sevm (St b [] Mem.empty G) (.ok post) →
    sevm.currentTarget = pair → sevm.code = code → CoveredFork sevm.benvStat.fork →
    b.output = [] → sevm.data.length < 2 ^ 256 → Good sevm →
    Rep current.state (b.getStor pair) →
    ∃ (entry : Entry) (nested : Transcript) (child : RunResult) (added : List PendingLog)
      (L : List Log),
      Auth sevm post entry nested ∧
      ExactConsumes (startTyped current (writerContext sevm invocation) entry) nested child ∧
      Rep child.frame.current.state (post.getStor pair) ∧
      child.frame.current.logs = current.logs ++ added ∧
      post.logs = b.logs ++ L ∧ added.map (PendingLog.rawWith owned) = L.map some

/-- What the fold derives from one committed run, at the incoming frame and turn. -/
def MutableFoldResult (pair : Adr) (Rep : State → Stor → Prop)
    (Auth : Sevm → Devm → Entry → Transcript → Prop) (owned : Event → Option Log)
    (frame : Frame) (request : Request) (turn : Nat)
    (events : List (Log ⊕ Exec.LocatedFrame)) (pre post : Devm) : Prop :=
  ∃ (turns : List MutableTurn) (c : Checkpoint) (added : List PendingLog) (L : List Log)
    (rets : List ChildReturn),
    turns.map MutableTurn.event = events ∧
    (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
      Auth located.frame.sevm located.frame.post entry nested) ∧
    Rep c.state (post.getStor pair) ∧
    c.logs = frame.current.logs ++ added ∧
    post.logs = pre.logs ++ L ∧ added.map (PendingLog.rawWith owned) = L.map some ∧
    ∀ (tail : Transcript) (result : TurnsResult),
      ExactTurns { frame with current := c } request (turn + turns.length) tail result →
      ExactTurns frame request turn (mutableTranscript turns tail)
        { result with childReturns := rets ++ result.childReturns }

/-- The context of a source turn at the Pair is the raw frame's writer context. -/
theorem childContext_writer {frame : Frame} {request : Request} {turn : Nat} {sevm : Sevm}
    (mutable : externalStatic frame request = false)
    (pair : frame.context.pair = sevm.currentTarget)
    (time : frame.context.timestamp = sevm.benvStat.time) :
    childContext frame request turn sevm.caller sevm.value sevm.isStatic =
      writerContext sevm (frame.context.invocation ++ [request.site.ordinal, turn]) := by
  simp only [childContext, writerContext, mutable, Bool.false_or, pair, time]

/-- A selected Pair root is consumed whole by the supply. -/
theorem mutable_selected_root {pair : Adr} {Rep : State → Stor → Prop} {Good : Sevm → Prop}
    {Auth : Sevm → Devm → Entry → Transcript → Prop} {owned : Event → Option Log}
    (supply : PairFrameSupply pair Rep Good Auth owned)
    (sem : CodeSem) (image : sem.image = some code.toList)
    {frame : Frame} {request : Request} {turn : Nat} {path : List Nat} {counter pc : Nat}
    {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true)
    (target : sevm.currentTarget = pair)
    (pairEq : frame.context.pair = pair) (mutable : externalStatic frame request = false)
    (installed : sem.At pair pc sevm pre)
    (rep : Rep frame.current.state (pre.getStor pair))
    (entry : pre.stack = [] ∧ pre.memory = Mem.empty ∧ pre.output = [])
    (representable : sevm.data.length < 2 ^ 256)
    (time : frame.context.timestamp = sevm.benvStat.time)
    (fork : CoveredFork sevm.benvStat.fork) (good : Good sevm) :
    MutableFoldResult pair Rep Auth owned frame request turn
      (Exec.targetLogEventsFrom pair path counter run committed) pre
      (Execution.committedPost out committed) := by
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
      rw [← St.self entry.1 entry.2.1]
      exact run
    obtain ⟨chosen, nested, child, added, L, auth, consumed, childRep, childLogs, rawLogs,
        images⟩ :=
      supply frame.current (frame.context.invocation ++ [request.site.ordinal, turn]) raw
        target codeEq fork entry.2.2 representable good rep
    have context := childContext_writer (turn := turn) mutable (pairEq.trans target.symm) time
    let located : Exec.LocatedFrame := ⟨path, Exec.Frame.ofRun run committed⟩
    let ctx := childContext frame request turn sevm.caller sevm.value sevm.isStatic
    let ret : ChildReturn := { context := ctx, entry := chosen, status := child.status }
    refine ⟨[.inr (located, chosen, nested)], child.frame.current, added, L,
      child.childReturns ++ [ret], ?_, ?_, childRep, childLogs, rawLogs, images, ?_⟩
    · rw [Exec.targetLogEventsFrom_target _ _ _ _ committed target]
      rfl
    · intro located' entry' nested' member
      have same := List.mem_singleton.mp member
      cases same
      exact auth
    · intro tail result rest
      have selected : ExactConsumes (startTyped frame.current
          (childContext frame request turn sevm.caller sevm.value sevm.isStatic) chosen)
          nested child := by
        rw [context]
        exact consumed
      exact ExactTurns.invoke selected rest

/-- The fold over the actual retained events of one committed run of a mutable call. -/
theorem mutable_retained_fold_inv {pair : Adr} {Rep : State → Stor → Prop}
    {Good : Sevm → Prop} {Auth : Sevm → Devm → Entry → Transcript → Prop}
    {owned : Event → Option Log}
    (supply : PairFrameSupply pair Rep Good Auth owned)
    (repCongr : ∀ st (s s' : Stor), (∀ k, s'.get k = s.get k) → Rep st s → Rep st s')
    (sem : CodeSem) (image : sem.image = some code.toList)
    {request : Request} {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    ∀ (committed : Execution.commits out = true) (frame : Frame) (turn counter : Nat)
      (path : List Nat),
      frame.context.pair = pair → externalStatic frame request = false →
      sem.At pair pc sevm pre → Rep frame.current.state (pre.getStor pair) →
      (sevm.currentTarget = pair → pre.stack = [] ∧ pre.memory = Mem.empty ∧ pre.output = []) →
      sevm.data.length < 2 ^ 256 → frame.context.timestamp = sevm.benvStat.time →
      CoveredFork sevm.benvStat.fork →
      (∀ located ∈ Exec.retainedTargetFramesFromAt pair path counter run committed,
        Good located.frame.sevm) →
      MutableFoldResult pair Rep Auth owned frame request turn
        (Exec.targetLogEventsFrom pair path counter run committed) pre
        (Execution.committedPost out committed) := by
  induction run with
  | @halt pc sevm pre out step =>
    intro committed frame turn counter path pairEq mutable installed rep entry representable
      time fork good
    by_cases target : sevm.currentTarget = pair
    · exact mutable_selected_root supply sem image (.halt step) committed target pairEq mutable
        installed rep (entry target) representable time fork
        (good ⟨path, Exec.Frame.ofRun (.halt step) committed⟩ (by
          rw [Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
          exact List.mem_singleton_self _))
    · cases out with
      | error error => simp only [Execution.commits, Bool.false_eq_true] at committed
      | ok post =>
        have storage := Blanc.Lift.Evm.step_halt_getStor_eq step
        have logs := Exec.committed_logs_at (.halt step) committed fork [] 0
        simp only [Exec.stateBoundariesOfCommits, List.flatMap_cons, List.flatMap_nil,
          Exec.boundaryOwnLogs, Exec.stateBoundary, List.append_nil] at logs
        refine ⟨[], frame.current, [], [], [], ?_, ?_, ?_, (List.append_nil _).symm,
          (logs.trans (List.append_nil _).symm), rfl, ?_⟩
        · rw [Exec.targetLogEventsFrom_halt _ _ _ step committed target]
          rfl
        · intro located entry nested member
          simp only [List.not_mem_nil] at member
        · change Rep frame.current.state (post.getStor pair)
          rw [storage]
          exact rep
        · intro tail result rest
          simpa only [List.length_nil, Nat.add_zero, mutableTranscript, List.nil_append]
            using rest
  | @cont pc sevm pre pc' inter out step next ih =>
    intro committed frame turn counter path pairEq mutable installed rep entry representable
      time fork good
    by_cases target : sevm.currentTarget = pair
    · exact mutable_selected_root supply sem image (.cont step next) committed target pairEq
        mutable installed rep (entry target) representable time fork
        (good ⟨path, Exec.Frame.ofRun (.cont step next) committed⟩ (by
          rw [Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
          exact List.mem_singleton_self _))
    · have nextInstalled := CodeSem.At.parentStep (.cont step next) next (.cont step next)
        installed target
      have storage := Evm.step_cont_getStor_foreign fork step target
      have nextRep : Rep frame.current.state (inter.getStor pair) := by
        rw [storage]
        exact rep
      have logs := Exec.cont_logs_eq fork step next committed
      have projection := Exec.retainedTargetFramesFromAt_cont pair path counter step next
        committed target
      have nextGood : ∀ located ∈ Exec.retainedTargetFramesFromAt pair path counter next
          committed, Good located.frame.sevm := fun located member =>
        good located (by rw [projection]; exact member)
      rw [Exec.targetLogEventsFrom_cont _ _ _ step next committed target]
      cases logged : Exec.logAt? pc sevm pre with
      | none =>
        rw [logged, Option.toList_none, List.append_nil] at logs
        obtain ⟨turns, c, added, L, rets, events, auth, finalRep, cLogs, rawLogs, images,
            consume⟩ :=
          ih committed frame turn counter path pairEq mutable nextInstalled nextRep
            (fun same => (target same).elim) representable time fork nextGood
        refine ⟨turns, c, added, L, rets, ?_, auth, finalRep, cLogs, ?_, images, consume⟩
        · simpa only [Option.toList_none, List.map_nil, List.nil_append] using events
        · rw [rawLogs, logs]
      | some log =>
        rw [logged] at logs
        let origin : ExternalOrigin :=
          { invocation := frame.context.invocation, site := request.site, turn := turn }
        let pending : PendingLog := .foreign origin log.address log.topics log.data
        let logged' : Frame :=
          { frame with current := { frame.current with logs := frame.current.logs ++ [pending] } }
        obtain ⟨turns, c, added, L, rets, events, auth, finalRep, cLogs, rawLogs, images,
            consume⟩ :=
          ih committed logged' (turn + 1) counter path pairEq mutable nextInstalled nextRep
            (fun same => (target same).elim) representable time fork nextGood
        refine ⟨.inl log :: turns, c, pending :: added, log :: L, rets, ?_, ?_, finalRep, ?_,
          ?_, ?_, ?_⟩
        · simp only [List.map_cons, MutableTurn.event, events, Option.toList_some,
            List.map_cons, List.map_nil, List.singleton_append]
        · intro located entry nested member
          rcases List.mem_cons.mp member with head | tail
          · cases head
          · exact auth located entry nested tail
        · rw [cLogs]
          simp only [logged', List.append_assoc, List.singleton_append]
        · rw [rawLogs, logs, List.append_assoc]
          rfl
        · simp only [List.map_cons, images]
          rfl
        · intro tail result rest
          have shifted : ExactTurns { logged' with current := c } request
              (turn + 1 + turns.length) tail result := by
            simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 turns.length]
              using rest
          exact ExactTurns.foreignLog mutable (consume tail result shifted)
  | doneErr step enter resumed =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @doneOk pc sevm pre callee resume pc' result inter out step enter resumed next ih =>
    intro committed frame turn counter path pairEq mutable installed rep entry representable
      time fork good
    by_cases target : sevm.currentTarget = pair
    · exact mutable_selected_root supply sem image (.doneOk step enter resumed next) committed
        target pairEq mutable installed rep (entry target) representable time fork
        (good ⟨path, Exec.Frame.ofRun (.doneOk step enter resumed next) committed⟩ (by
          rw [Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
          exact List.mem_singleton_self _))
    · have nextInstalled := CodeSem.At.parentStep (.doneOk step enter resumed next) next
        (.doneOk step enter resumed next) installed target
      have storage := congrFun (Evm.step_done_getStor step enter resumed) pair
      have nextRep : Rep frame.current.state (inter.getStor pair) := by
        rw [storage]
        exact rep
      have logs := Exec.doneOk_logs_eq fork step enter resumed next committed
      have projection := Exec.retainedTargetFramesFromAt_doneOk pair path counter step enter
        resumed next committed target
      obtain ⟨turns, c, added, L, rets, events, auth, finalRep, cLogs, rawLogs, images,
          consume⟩ :=
        ih committed frame turn (counter + 1) path pairEq mutable nextInstalled nextRep
          (fun same => (target same).elim) representable time fork
          (fun located member => good located (by rw [projection]; exact member))
      rw [Exec.targetLogEventsFrom_doneOk _ _ _ step enter resumed next committed target]
      refine ⟨turns, c, added, L, rets, events, auth, finalRep, cLogs, ?_, images, consume⟩
      rw [rawLogs, logs]
  | runErr step enter child resumed childIH =>
    intro committed
    simp only [Execution.commits, Bool.false_eq_true] at committed
  | @runOk pc sevm pre callee resume pc' childEvm raw inter out step enter child resumed next
      childIH nextIH =>
    intro committed frame turn counter path pairEq mutable installed rep entry representable
      time fork good
    by_cases target : sevm.currentTarget = pair
    · exact mutable_selected_root supply sem image (.runOk step enter child resumed next)
        committed target pairEq mutable installed rep (entry target) representable time fork
        (good ⟨path, Exec.Frame.ofRun (.runOk step enter child resumed next) committed⟩ (by
          rw [Exec.retainedTargetFramesFromAt_target _ _ _ _ committed target]
          exact List.mem_singleton_self _))
    · have nextInstalled := CodeSem.At.parentStep (.runOk step enter child resumed next) next
        (.runOk step enter child resumed next) installed target
      have nonempty : pre.getCode pair ≠ .empty := by
        intro empty
        have imageEmpty : sem.image = some [] := by
          rw [← installed.1, empty, ByteArray.toList_empty]
        exact sem.ne_nil imageEmpty rfl
      obtain ⟨settledStorage, rolledStorage⟩ :=
        Evm.step_run_getStor fork step enter child resumed nonempty
      obtain ⟨settledLogs, rolledLogs⟩ :=
        Exec.runOk_logs_eq fork step enter child resumed next committed
      have projection := Exec.retainedTargetFramesFromAt_runOk pair path counter step enter
        child resumed next committed target
      rw [Exec.targetLogEventsFrom_runOk _ _ _ step enter child resumed next committed target]
      by_cases settles : Frame.settlementCommits callee raw = true
      · rw [dite_eq_left settles]
        rw [dite_eq_left settles] at projection
        have childCommitted := Frame.raw_commits_of_settlementCommits settles
        obtain ⟨childInstalled, childStorage, childEntry, childShort, childStat, childFork⟩ :=
          CodeSem.At.spawnChild step enter installed target fork
        have childRep : Rep frame.current.state (childEvm.dyna.getStor pair) := by
          rw [childStorage]
          exact rep
        obtain ⟨turns1, c1, added1, L1, rets1, events1, auth1, rep1, cLogs1, rawLogs1, images1,
            consume1⟩ :=
          childIH childCommitted frame turn 0 (path ++ [counter]) pairEq mutable childInstalled
            childRep (fun _ => childEntry) childShort (by rw [childStat]; exact time) childFork
            (fun located member => good located (by
              rw [projection]
              exact List.mem_append.mpr (Or.inl member)))
        obtain ⟨L, childLogs, interLogs⟩ := settledLogs settles
        have sameL : L = L1 := List.append_cancel_left (childLogs.symm.trans rawLogs1)
        subst sameL
        have interRep : Rep c1.state (inter.getStor pair) :=
          repCongr _ _ _ (settledStorage settles) rep1
        let frame1 : Frame := { frame with current := c1 }
        obtain ⟨turns2, c2, added2, L2, rets2, events2, auth2, rep2, cLogs2, rawLogs2, images2,
            consume2⟩ :=
          nextIH committed frame1 (turn + turns1.length) (counter + 1) path pairEq mutable
            nextInstalled interRep (fun same => (target same).elim) representable time fork
            (fun located member => good located (by
              rw [projection]
              exact List.mem_append.mpr (Or.inr member)))
        refine ⟨turns1 ++ turns2, c2, added1 ++ added2, L ++ L2, rets1 ++ rets2, ?_, ?_, rep2,
          ?_, ?_, ?_, ?_⟩
        · rw [List.map_append, events1, events2]
        · intro located entry nested member
          rcases List.mem_append.mp member with left | right
          · exact auth1 located entry nested left
          · exact auth2 located entry nested right
        · rw [cLogs2]
          change c1.logs ++ added2 = _
          rw [cLogs1, List.append_assoc]
        · rw [rawLogs2, interLogs, List.append_assoc]
        · rw [List.map_append, List.map_append, images1, images2]
        · intro tail result rest
          have shifted : ExactTurns { frame1 with current := c2 } request
              (turn + turns1.length + turns2.length) tail result := by
            simpa only [List.length_append, Nat.add_assoc] using rest
          have afterNext := consume2 tail result shifted
          have afterChild := consume1 (mutableTranscript turns2 tail)
            { result with childReturns := rets2 ++ result.childReturns } afterNext
          simpa only [mutableTranscript_append, List.append_assoc] using afterChild
      · rw [dite_eq_right settles, List.nil_append]
        rw [dite_eq_right settles, List.nil_append] at projection
        have interRep : Rep frame.current.state (inter.getStor pair) :=
          repCongr _ _ _ (rolledStorage settles) rep
        obtain ⟨turns, c, added, L, rets, events, auth, finalRep, cLogs, rawLogs, images,
            consume⟩ :=
          nextIH committed frame turn (counter + 1) path pairEq mutable nextInstalled interRep
            (fun same => (target same).elim) representable time fork
            (fun located member => good located (by rw [projection]; exact member))
        refine ⟨turns, c, added, L, rets, events, auth, finalRep, cLogs, ?_, images, consume⟩
        rw [rawLogs, rolledLogs settles]

end Blanc.Lift.UniswapV2Pair
