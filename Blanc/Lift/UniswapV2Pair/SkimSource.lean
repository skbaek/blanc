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

/-- The consumed source skim preserves supply and both reserves, by the driver law. -/
theorem skim_source_liquidity {current : Checkpoint} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {out : RunResult}
    (consumed : ExactConsumes (startTyped current ctx (.skim recipient)) transcript out)
    (success : out.status = .success []) :
    out.frame.current.state.liquidityCore = current.state.liquidityCore := by
  have realized := ExactConsumes.realizes consumed (transcript.work + 1) (Nat.le_refl _)
  rw [← realized] at success ⊢
  exact drive_startTyped_skim_liquidity success

end Blanc.Lift.UniswapV2Pair
