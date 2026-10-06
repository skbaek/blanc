import Blanc.Lift.UniswapV2Pair.Execution

/-! Recursive exact consumption of the reviewed typed source transitions. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune


mutual
  /-- Recursive exact consumption, with real source transitions and genuine terminal failures.
  The no-code shape is supplied by the authenticated producer, independently of driver success. -/
  inductive ExactConsumes : SegmentResult → Transcript → RunResult → Prop
    | finished (frame : Frame) (bytes : Bytes) :
        ExactConsumes (.finished frame bytes) .done
          { status := .success bytes, frame := frame, remaining := .done, childReturns := [] }
    | failed (frame : Frame) (failure : Failure) (genuine : failure ≠ .incompleteTranscript) :
        ExactConsumes (.failed frame failure) .done
          { status := .failed failure, frame := frame, remaining := .done, childReturns := [] }
    | nextMissing
        {frame : Frame} {request : Request} {continuation : Continuation}
        {result : ExternalResult} {tail : Transcript} {out : RunResult}
        (missing : (request.requiresCode && !result.codeExists) = true)
        (rest : ExactConsumes (resumeSegment frame request continuation result) tail out) :
        ExactConsumes (.suspended frame request continuation) (.next result .done tail) out
    | nextCall
        {frame : Frame} {request : Request} {continuation : Continuation}
        {result : ExternalResult} {turns tail : Transcript}
        {executed : TurnsResult} {out : RunResult}
        (present : (request.requiresCode && !result.codeExists) = false)
        (noCodeTurns : result.codeExists = false → turns = .done)
        (during : ExactTurns frame request 0 turns executed)
        (rest : ExactConsumes
          (resumeSegment
            (if result.success then executed.frame else { executed.frame with current := frame.current })
            request continuation result) tail out) :
        ExactConsumes (.suspended frame request continuation) (.next result turns tail)
          { out with childReturns := executed.childReturns ++ out.childReturns }

  inductive ExactTurns : Frame → Request → Nat → Transcript → TurnsResult → Prop
    | done (frame : Frame) (request : Request) (turn : Nat) :
        ExactTurns frame request turn .done { complete := true, frame := frame, childReturns := [] }
    | foreignLog
        {frame : Frame} {request : Request} {turn : Nat}
        {emitter : Adr} {topics : List B256} {data : Bytes}
        {tail : Transcript} {out : TurnsResult}
        (mutable : externalStatic frame request = false)
        (rest : ExactTurns
          { frame with current :=
            { frame.current with logs := frame.current.logs ++
              [.foreign { invocation := frame.context.invocation, site := request.site, turn := turn }
                emitter topics data] } }
          request (turn + 1) tail out) :
        ExactTurns frame request turn (.foreignLog emitter topics data tail) out
    | invoke
        {frame : Frame} {request : Request} {turn : Nat}
        {sender : Adr} {value : B256} {isStatic : Bool} {entry : Entry}
        {transcript tail : Transcript} {child : RunResult} {out : TurnsResult}
        (selected : ExactConsumes
          (startTyped frame.current (childContext frame request turn sender value isStatic) entry)
          transcript child)
        (rest : ExactTurns { frame with current := child.frame.current } request (turn + 1) tail out) :
        ExactTurns frame request turn (.invoke sender value isStatic entry transcript tail)
          { out with childReturns := child.childReturns ++
              [{ context := childContext frame request turn sender value isStatic,
                 entry := entry, status := child.status }] ++ out.childReturns }
end


/-- Every exact terminal result is exhausted and excludes both incomplete outcomes. -/
theorem ExactConsumes.closed {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (consumed : ExactConsumes segment transcript out) :
    out.remaining = .done ∧ out.status ≠ .incomplete ∧
      out.status ≠ .failed .incompleteTranscript := by
  refine ExactConsumes.rec
    (motive_1 := fun _ _ out _ => out.remaining = .done ∧ out.status ≠ .incomplete ∧
      out.status ≠ .failed .incompleteTranscript)
    (motive_2 := fun _ _ _ _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed
  · intro frame bytes
    exact ⟨rfl, (by intro rejected; cases rejected), (by intro rejected; cases rejected)⟩
  · intro frame failure genuine
    refine ⟨rfl, (by intro rejected; cases rejected), ?_⟩
    intro rejected
    have failureEq : failure = .incompleteTranscript := by cases rejected; rfl
    exact genuine failureEq
  · intro frame request continuation result tail out missing rest ih
    exact ih
  · intro frame request continuation result turns tail executed out present noCodeTurns during rest ihTurns ihRest
    exact ihRest
  · intro frame request turn
    exact True.intro
  · intro frame request turn emitter topics data tail out mutable rest ih
    exact True.intro
  · intro frame request turn sender value isStatic entry transcript tail child out selected rest ihSelected ihRest
    exact True.intro

/-- Every exact external-turn queue completes, including all selected children recursively. -/
theorem ExactTurns.closed {frame : Frame} {request : Request} {turn : Nat}
    {turns : Transcript} {out : TurnsResult} (consumed : ExactTurns frame request turn turns out) :
    out.complete = true := by
  refine ExactTurns.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ out _ => out.complete = true) ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed
  · intro frame bytes
    exact True.intro
  · intro frame failure genuine
    exact True.intro
  · intro frame request continuation result tail out missing rest ih
    exact True.intro
  · intro frame request continuation result turns tail executed out present noCodeTurns during rest ihTurns ihRest
    exact True.intro
  · intro frame request turn
    rfl
  · intro frame request turn emitter topics data tail out mutable rest ih
    exact ih
  · intro frame request turn sender value isStatic entry transcript tail child out selected rest ihSelected ihRest
    exact ihRest


mutual
  /-- The unchanged own-segment runner realizes an exact derivation at every adequate fuel. -/
  theorem ExactConsumes.realizes {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
      (consumed : ExactConsumes segment transcript out) (fuel : Nat)
      (enough : transcript.work + 1 ≤ fuel) : drive fuel segment transcript = out := by
    cases fuelEq : fuel with
    | zero =>
      rw [fuelEq] at enough
      exact False.elim (Nat.not_succ_le_zero _ enough)
    | succ fuel =>
      rw [fuelEq] at enough
      cases consumed with
      | finished frame bytes => rfl
      | failed frame failure genuine =>
        cases failure with
        | sourceGuard reason => rfl
        | emptyRevert => rfl
        | bubbledRevert bytes => rfl
        | divisionByZero => rfl
        | staticWrite => rfl
        | incompleteTranscript => exact False.elim (genuine rfl)
      | @nextMissing frame request continuation result tail out missing rest =>
        have tailEnough : tail.work + 1 ≤ fuel := by
          simpa only [Transcript.work, Nat.add_zero, Nat.add_comm 1 tail.work] using
            Nat.le_of_succ_le_succ enough
        rw [drive, ite_eq_left missing]
        exact ExactConsumes.realizes rest fuel tailEnough
      | @nextCall frame request continuation result turns tail executed out present noCodeTurns during rest =>
        have parentBound : 1 + turns.work + tail.work ≤ fuel := Nat.le_of_succ_le_succ enough
        have turnsEnough : turns.work + 1 ≤ fuel := by
          have contained : turns.work + 1 ≤ 1 + turns.work + tail.work := by
            simpa only [Nat.add_comm 1 turns.work] using
              Nat.le_add_right (turns.work + 1) tail.work
          exact contained.trans parentBound
        have tailEnough : tail.work + 1 ≤ fuel := by
          have contained : tail.work + 1 ≤ 1 + turns.work + tail.work := by
            simpa only [Nat.add_comm tail.work 1, Nat.add_assoc] using
              Nat.add_le_add_left (Nat.le_add_left tail.work turns.work) 1
          exact contained.trans parentBound
        rw [drive]
        simp only [present, Bool.false_eq_true, ite_false]
        rw [ExactTurns.realizes during fuel turnsEnough, ite_eq_left (ExactTurns.closed during)]
        rw [ExactConsumes.realizes rest fuel tailEnough]
  termination_by fuel
  decreasing_by
    all_goals
      rw [fuelEq]
      exact Nat.lt_succ_self _

  /-- The unchanged turn runner realizes every recursively exact child and diagnostic order. -/
  theorem ExactTurns.realizes {frame : Frame} {request : Request} {turn : Nat}
      {turns : Transcript} {out : TurnsResult} (consumed : ExactTurns frame request turn turns out)
      (fuel : Nat) (enough : turns.work + 1 ≤ fuel) :
      driveTurns fuel frame request turn turns = out := by
    cases fuelEq : fuel with
    | zero =>
      rw [fuelEq] at enough
      exact False.elim (Nat.not_succ_le_zero _ enough)
    | succ fuel =>
      rw [fuelEq] at enough
      cases consumed with
      | done frame request turn => rfl
      | @foreignLog frame request turn emitter topics data tail out mutable rest =>
        have tailEnough : tail.work + 1 ≤ fuel := by
          simpa only [Transcript.work, Nat.add_comm 1 tail.work] using
            Nat.le_of_succ_le_succ enough
        rw [driveTurns]
        simp only [mutable, Bool.false_eq_true, ite_false]
        exact ExactTurns.realizes rest fuel tailEnough
      | @invoke frame request turn sender value isStatic entry transcript tail child out selected rest =>
        have parentBound : 1 + transcript.work + tail.work ≤ fuel := Nat.le_of_succ_le_succ enough
        have childEnough : transcript.work + 1 ≤ fuel := by
          have contained : transcript.work + 1 ≤ 1 + transcript.work + tail.work := by
            simpa only [Nat.add_comm 1 transcript.work] using
              Nat.le_add_right (transcript.work + 1) tail.work
          exact contained.trans parentBound
        have tailEnough : tail.work + 1 ≤ fuel := by
          have contained : tail.work + 1 ≤ 1 + transcript.work + tail.work := by
            simpa only [Nat.add_comm tail.work 1, Nat.add_assoc] using
              Nat.add_le_add_left (Nat.le_add_left tail.work transcript.work) 1
          exact contained.trans parentBound
        rw [driveTurns, ExactConsumes.realizes selected fuel childEnough]
        have childClosed := ExactConsumes.closed selected
        cases status : child.status with
        | incomplete => exact False.elim (childClosed.2.1 status)
        | success bytes =>
          dsimp only []
          rw [ExactTurns.realizes rest fuel tailEnough]
        | failed failure =>
          dsimp only []
          rw [ExactTurns.realizes rest fuel tailEnough]
  termination_by fuel
  decreasing_by
    all_goals
      rw [fuelEq]
      exact Nat.lt_succ_self _
end


/-- The public work+2 runner consumes a fresh-root derivation without an endpoint premise. -/
theorem runTyped_of_exact {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript} {out : RunResult}
    (consumed : ExactConsumes
      (startTyped { state := st, logs := [], updates := [] } ctx entry) transcript out) :
    runTyped st ctx entry transcript = out ∧ out.remaining = .done ∧
      out.status ≠ .incomplete ∧ out.status ≠ .failed .incompleteTranscript := by
  exact ⟨ExactConsumes.realizes consumed (transcript.work + 2)
    (Nat.le_add_right (transcript.work + 1) 1), ExactConsumes.closed consumed⟩

end Blanc.Lift.UniswapV2Pair
