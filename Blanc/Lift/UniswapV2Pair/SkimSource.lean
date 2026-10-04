import Blanc.Lift.UniswapV2Pair.SyncWalk

/-! Source-side skim: the typed driver consumes the four ordered external observations
(balance0, transfer0, balance1, transfer1) with their recursively exact turn queues. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The source lock preserves the invocation checkpoint before the first observation. -/
def skimSourceLockedFrame (current : Checkpoint) (ctx : Context) (recipient : Adr) : Frame :=
  { Frame.enter current ctx (.skim recipient) with
    current := { current with state := { current.state with unlocked := 0 } } }

/-- The cached skim locals: recipient and the entry token fields. -/
def skimSourceLocals (current : Checkpoint) (recipient : Adr) : SkimLocals :=
  { recipient := recipient, token0 := current.state.token0, token1 := current.state.token1 }

def skimRequest0 (current : Checkpoint) (ctx : Context) : Request :=
  requestFor .skimBalance0 current.state.token0 (.balanceOf ctx.pair)

def skimRequest1 (current : Checkpoint) (recipient : Adr) (amount : B256) : Request :=
  requestFor .skimTransfer0 current.state.token0 (.transfer recipient amount)

def skimRequest2 (current : Checkpoint) (ctx : Context) : Request :=
  requestFor .skimBalance1 current.state.token1 (.balanceOf ctx.pair)

def skimRequest3 (current : Checkpoint) (recipient : Adr) (amount : B256) : Request :=
  requestFor .skimTransfer1 current.state.token1 (.transfer recipient amount)

theorem skim_startTyped_suspended {current : Checkpoint} {ctx : Context} {recipient : Adr}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (unlocked : current.state.unlocked = 1) :
    startTyped current ctx (.skim recipient) =
      .suspended (skimSourceLockedFrame current ctx recipient) (skimRequest0 current ctx)
        (.skimBalance0 (skimSourceLocals current recipient)) := by
  have opened : (Frame.enter current ctx (.skim recipient)).lock =
      .ok (skimSourceLockedFrame current ctx recipient) := by
    simp only [Frame.lock, Frame.enter, unlocked, nonstatic, ite_true, Bool.false_eq_true,
      ite_false, skimSourceLockedFrame]
  simp only [startTyped, startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
    getterResult, opened, Frame.suspend]
  rfl

/-- A balance answer of at least one word resumes with the checked surplus transfer. -/
theorem skim_resumeBalance0 {frame : Frame} {locals : SkimLocals} {result : ExternalResult}
    (codeExists : result.codeExists = true) (success : result.success = true)
    (long : 32 ≤ result.returndata.length)
    (cover : frame.current.state.reserve0.val ≤ (Bytes.toB256 (result.returndata.take 32)).toNat) :
    let request := requestFor .skimBalance0 locals.token0 (.balanceOf frame.context.pair)
    resumeSegment frame request (.skimBalance0 locals) result =
      .suspended (frame.beginResume request)
        (requestFor .skimTransfer0 locals.token0 (.transfer locals.recipient
          (Bytes.toB256 (result.returndata.take 32) - Nat.toB256 frame.current.state.reserve0.val)))
        (.skimTransfer0 locals) := by
  simp only [resumeSegment, decodeExternal, requestFor, codeExists, success,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    ite_eq_left long, Frame.suspend]
  exact ite_eq_left cover

/-- The optional-bool transfer acceptance of the raw helper is the source decoder's. -/
def SkimTransferAccepted (out : Bytes) : Prop :=
  out = [] ∨ (32 ≤ out.length ∧ Bytes.toB256 (out.take 32) ≠ 0)

theorem skim_decodeTransfer {request : Request} {recipient : Adr} {value : B256}
    {result : ExternalResult}
    (operation : request.operation = .transfer recipient value)
    (noCode : request.requiresCode = false)
    (success : result.success = true) (accepted : SkimTransferAccepted result.returndata) :
    decodeExternal request result = .ok .unit := by
  simp only [decodeExternal, noCode, Bool.false_and, Bool.false_eq_true, ite_false, operation,
    success, ite_true]
  rcases accepted with empty | ⟨long, nonzero⟩
  · rw [empty]
    rfl
  · have nonEmpty : result.returndata.length ≠ 0 := by omega
    simp only [nonEmpty, ite_false, ite_eq_left long]
    rw [ite_eq_left nonzero]

theorem skim_resumeTransfer0 {frame : Frame} {locals : SkimLocals} {amount : B256}
    {result : ExternalResult}
    (success : result.success = true) (accepted : SkimTransferAccepted result.returndata) :
    let request := requestFor .skimTransfer0 locals.token0 (.transfer locals.recipient amount)
    resumeSegment frame request (.skimTransfer0 locals) result =
      .suspended (frame.beginResume request)
        (requestFor .skimBalance1 locals.token1 (.balanceOf frame.context.pair))
        (.skimBalance1 locals) := by
  intro request
  have decoded : decodeExternal request result = .ok .unit :=
    skim_decodeTransfer rfl rfl success accepted
  simp only [resumeSegment, decoded, Frame.suspend, Frame.beginResume]

theorem skim_resumeBalance1 {frame : Frame} {locals : SkimLocals} {result : ExternalResult}
    (codeExists : result.codeExists = true) (success : result.success = true)
    (long : 32 ≤ result.returndata.length)
    (cover : frame.current.state.reserve1.val ≤ (Bytes.toB256 (result.returndata.take 32)).toNat) :
    let request := requestFor .skimBalance1 locals.token1 (.balanceOf frame.context.pair)
    resumeSegment frame request (.skimBalance1 locals) result =
      .suspended (frame.beginResume request)
        (requestFor .skimTransfer1 locals.token1 (.transfer locals.recipient
          (Bytes.toB256 (result.returndata.take 32) - Nat.toB256 frame.current.state.reserve1.val)))
        (.skimTransfer1 locals) := by
  simp only [resumeSegment, decodeExternal, requestFor, codeExists, success,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true,
    ite_eq_left long, Frame.suspend]
  exact ite_eq_left cover

/-- The final source segment restores the lock and appends no owned log or update. -/
def skimSourceFinalFrame (frame : Frame) : Frame :=
  frame.withEvents { frame.current.state with unlocked := 1 } []

theorem skim_resumeTransfer1 {frame : Frame} {locals : SkimLocals} {amount : B256}
    {result : ExternalResult}
    (success : result.success = true) (accepted : SkimTransferAccepted result.returndata) :
    let request := requestFor .skimTransfer1 locals.token1 (.transfer locals.recipient amount)
    resumeSegment frame request (.skimTransfer1 locals) result =
      .finished (skimSourceFinalFrame (frame.beginResume request)) [] := by
  intro request
  have decoded : decodeExternal request result = .ok .unit :=
    skim_decodeTransfer rfl rfl success accepted
  simp only [resumeSegment, decoded, Frame.finishLocked, Frame.finish, skimSourceFinalFrame]

/-- Nested turns change only the frame's current checkpoint. -/
theorem driveTurns_frame_shape (fuel : Nat) (frame : Frame) (request : Request) (turn : Nat)
    (turns : Transcript) :
    ∃ c, (driveTurns fuel frame request turn turns).frame = { frame with current := c } := by
  induction fuel generalizing frame turn turns with
  | zero => exact ⟨frame.current, rfl⟩
  | succ fuel ih =>
    cases turns with
    | done => exact ⟨frame.current, rfl⟩
    | next result children tail => exact ⟨frame.current, rfl⟩
    | foreignLog emitter topics data tail =>
      rw [driveTurns]
      cases externalStatic frame request with
      | true => exact ⟨frame.current, rfl⟩
      | false =>
        obtain ⟨c, eq⟩ := ih _ (turn + 1) tail
        exact ⟨c, eq⟩
    | invoke sender value isStatic entry transcript tail =>
      rw [driveTurns]
      cases (drive fuel (startTyped frame.current
          (childContext frame request turn sender value isStatic) entry) transcript).status with
      | incomplete => exact ⟨frame.current, rfl⟩
      | success returndata =>
        obtain ⟨c, eq⟩ := ih _ (turn + 1) tail
        exact ⟨c, eq⟩
      | failed failure =>
        obtain ⟨c, eq⟩ := ih _ (turn + 1) tail
        exact ⟨c, eq⟩

theorem ExactTurns.frame_shape {frame : Frame} {request : Request} {turn : Nat}
    {turns : Transcript} {executed : TurnsResult}
    (during : ExactTurns frame request turn turns executed) :
    ∃ c, executed.frame = { frame with current := c } := by
  rw [← ExactTurns.realizes during (turns.work + 1) (Nat.le_refl _)]
  exact driveTurns_frame_shape _ _ _ _ _

/-- Four recursively exact turn queues and four successful observations consume the
source skim handler. Transfer children may run arbitrary nested Pair turns; the balance
children are static. The final frame and ordered child returns are conclusions. -/
theorem skim_source_exact_consumption {current : Checkpoint} {ctx : Context} {recipient : Adr}
    {result0 result1 result2 result3 : ExternalResult}
    {turns0 turns1 turns2 turns3 : Transcript}
    {executed0 executed1 executed2 executed3 : TurnsResult}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (unlocked : current.state.unlocked = 1)
    (code0 : result0.codeExists = true) (success0 : result0.success = true)
    (long0 : 32 ≤ result0.returndata.length)
    (cover0 : current.state.reserve0.val ≤ (Bytes.toB256 (result0.returndata.take 32)).toNat)
    (during0 : ExactTurns (skimSourceLockedFrame current ctx recipient)
      (skimRequest0 current ctx) 0 turns0 executed0)
    (success1 : result1.success = true) (accepted1 : SkimTransferAccepted result1.returndata)
    (noCode1 : result1.codeExists = false → turns1 = .done)
    (during1 : ExactTurns ((skimSourceLockedFrame current ctx recipient).beginResume
        (skimRequest0 current ctx))
      (skimRequest1 current recipient
        (Bytes.toB256 (result0.returndata.take 32) - Nat.toB256 current.state.reserve0.val))
      0 turns1 executed1)
    (code2 : result2.codeExists = true) (success2 : result2.success = true)
    (long2 : 32 ≤ result2.returndata.length)
    (cover1 : executed1.frame.current.state.reserve1.val ≤
      (Bytes.toB256 (result2.returndata.take 32)).toNat)
    (during2 : ExactTurns (executed1.frame.beginResume (skimRequest1 current recipient
        (Bytes.toB256 (result0.returndata.take 32) - Nat.toB256 current.state.reserve0.val)))
      (skimRequest2 current ctx) 0 turns2 executed2)
    (success3 : result3.success = true) (accepted3 : SkimTransferAccepted result3.returndata)
    (noCode3 : result3.codeExists = false → turns3 = .done)
    (during3 : ExactTurns ((executed1.frame.beginResume (skimRequest1 current recipient
          (Bytes.toB256 (result0.returndata.take 32) - Nat.toB256 current.state.reserve0.val))).beginResume
          (skimRequest2 current ctx))
      (skimRequest3 current recipient
        (Bytes.toB256 (result2.returndata.take 32) - Nat.toB256 executed1.frame.current.state.reserve1.val))
      0 turns3 executed3) :
    ExactConsumes (startTyped current ctx (.skim recipient))
      (.next result0 turns0 (.next result1 turns1 (.next result2 turns2 (.next result3 turns3 .done))))
      { status := .success [],
        frame := skimSourceFinalFrame (executed3.frame.beginResume (skimRequest3 current recipient
          (Bytes.toB256 (result2.returndata.take 32) - Nat.toB256 executed1.frame.current.state.reserve1.val))),
        remaining := .done,
        childReturns := executed0.childReturns ++ (executed1.childReturns ++
          (executed2.childReturns ++ executed3.childReturns)) } := by
  let locals := skimSourceLocals current recipient
  let frame0 := skimSourceLockedFrame current ctx recipient
  let request0 := skimRequest0 current ctx
  let amount0 := Bytes.toB256 (result0.returndata.take 32) - Nat.toB256 current.state.reserve0.val
  let request1 := skimRequest1 current recipient amount0
  let frame2 := executed1.frame.beginResume request1
  let request2 := skimRequest2 current ctx
  let amount1 := Bytes.toB256 (result2.returndata.take 32) -
    Nat.toB256 executed1.frame.current.state.reserve1.val
  let request3 := skimRequest3 current recipient amount1
  have kept0 : executed0.frame = frame0 := syncBalanceTurns_frame during0
  obtain ⟨c1, shape1⟩ := ExactTurns.frame_shape during1
  have context1 : executed1.frame.context = ctx := by rw [shape1]; rfl
  have kept2 : executed2.frame = frame2 :=
    syncBalanceTurns_frame (site := .skimBalance1) (target := current.state.token1)
      (by rw [show frame2.context = ctx from context1]; exact during2)
  have resumed0 : resumeSegment frame0 request0 (.skimBalance0 locals) result0 =
      .suspended (frame0.beginResume request0) request1 (.skimTransfer0 locals) :=
    skim_resumeBalance0 code0 success0 long0 cover0
  have resumed1 : resumeSegment executed1.frame request1 (.skimTransfer0 locals) result1 =
      .suspended frame2 request2 (.skimBalance1 locals) := by
    have step := skim_resumeTransfer0 (frame := executed1.frame) (locals := locals)
      (amount := amount0) success1 accepted1
    rw [context1] at step
    exact step
  have resumed2 : resumeSegment frame2 request2 (.skimBalance1 locals) result2 =
      .suspended (frame2.beginResume request2) request3 (.skimTransfer1 locals) := by
    have step := skim_resumeBalance1 (frame := frame2) (locals := locals) code2 success2 long2 cover1
    rw [show frame2.context = ctx from context1] at step
    exact step
  have resumed3 : resumeSegment executed3.frame request3 (.skimTransfer1 locals) result3 =
      .finished (skimSourceFinalFrame (executed3.frame.beginResume request3)) [] :=
    skim_resumeTransfer1 success3 accepted3
  have terminal := ExactConsumes.finished
    (skimSourceFinalFrame (executed3.frame.beginResume request3)) []
  rw [← resumed3] at terminal
  have fourth := ExactConsumes.nextCall (frame := frame2.beginResume request2) (request := request3)
    (continuation := .skimTransfer1 locals) (result := result3)
    (by simp only [request3, skimRequest3, requestFor, Bool.false_and]) noCode3 during3
    (by simpa only [success3, ite_true] using terminal)
  rw [← resumed2] at fourth
  have third := ExactConsumes.nextCall (frame := frame2) (request := request2)
    (continuation := .skimBalance1 locals) (result := result2)
    (by simp only [request2, skimRequest2, requestFor, code2, Bool.not_true, Bool.and_false])
    (by intro absent; rw [code2] at absent; cases absent) during2
    (by simpa only [success2, ite_true, kept2] using fourth)
  rw [← resumed1] at third
  have second := ExactConsumes.nextCall (frame := frame0.beginResume request0) (request := request1)
    (continuation := .skimTransfer0 locals) (result := result1)
    (by simp only [request1, skimRequest1, requestFor, Bool.false_and]) noCode1 during1
    (by simpa only [success1, ite_true] using third)
  rw [← resumed0] at second
  have first := ExactConsumes.nextCall (frame := frame0) (request := request0)
    (continuation := .skimBalance0 locals) (result := result0)
    (by simp only [request0, skimRequest0, requestFor, code0, Bool.not_true, Bool.and_false])
    (by intro absent; rw [code0] at absent; cases absent) during0
    (by simpa only [success0, ite_true, kept0] using second)
  rw [skim_startTyped_suspended value nonstatic unlocked]
  simpa only [List.append_nil] using first

/-- Transfer0's nested turns run under the held lock, so the model reserve1 read by the
second balance resumption is the entry reserve1. -/
theorem skim_transfer0_reserve1 {current : Checkpoint} {ctx : Context} {recipient : Adr}
    {amount : B256} {turns : Transcript} {executed : TurnsResult}
    (during : ExactTurns ((skimSourceLockedFrame current ctx recipient).beginResume
        (skimRequest0 current ctx))
      (skimRequest1 current recipient amount) 0 turns executed) :
    executed.frame.current.state.reserve1 = current.state.reserve1 := by
  have core := driveTurns_locked_core (turns.work + 1)
    ((skimSourceLockedFrame current ctx recipient).beginResume (skimRequest0 current ctx))
    (skimRequest1 current recipient amount) 0 turns rfl
  rw [ExactTurns.realizes during (turns.work + 1) (Nat.le_refl _)] at core
  exact congrArg (fun c => c.2.1.2) core

/-- The consumed source skim preserves supply and both reserves (the final frame of
`skim_source_exact_consumption` against the existing driver law). -/
theorem skim_source_liquidity {current : Checkpoint} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {out : RunResult}
    (consumed : ExactConsumes (startTyped current ctx (.skim recipient)) transcript out)
    (success : out.status = .success []) :
    out.frame.current.state.liquidityCore = current.state.liquidityCore := by
  have realized := ExactConsumes.realizes consumed (transcript.work + 1) (Nat.le_refl _)
  rw [← realized] at success ⊢
  exact drive_startTyped_skim_liquidity success

end Blanc.Lift.UniswapV2Pair
