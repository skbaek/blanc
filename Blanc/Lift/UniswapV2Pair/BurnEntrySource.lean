import Blanc.Lift.UniswapV2Pair.Execution
import Blanc.Lift.UniswapV2Pair.FeeMintSource

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The entry checkpoint is retained while the first Burn segment holds the lock. -/
def burnSourceLockedFrame (current : Checkpoint) (ctx : Context) (recipient : Adr) : Frame :=
  { Frame.enter current ctx (.burn recipient) with
    current := { current with state := { current.state with unlocked := 0 } } }

/-- Actual successful entry guards select the first balance suspension. -/
theorem burn_startTyped_suspended {current : Checkpoint} {ctx : Context} {recipient : Adr}
    (value : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (unlocked : current.state.unlocked = 1) :
    startTyped current ctx (.burn recipient) =
      .suspended (burnSourceLockedFrame current ctx recipient)
        (requestFor .burnInitialBalance0 current.state.token0 (.balanceOf ctx.pair))
        (.burnInitialBalance0 ⟨recipient, current.state.cachedReserves,
          current.state.token0, current.state.token1⟩) := by
  have opened : (Frame.enter current ctx (.burn recipient)).lock =
      .ok (burnSourceLockedFrame current ctx recipient) := by
    simp only [Frame.lock, Frame.enter, unlocked, nonstatic, ite_true,
      Bool.false_eq_true, ite_false, burnSourceLockedFrame]
  simp only [startTyped, startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad value),
    getterResult, opened, Frame.suspend]
  rfl

theorem burn_resumeInitialBalance0 {frame : Frame} {locals : BurnLocals} {out : Bytes}
    (long : 32 ≤ out.length) :
    resumeSegment frame (requestFor .burnInitialBalance0 locals.token0 (.balanceOf frame.context.pair))
        (.burnInitialBalance0 locals) (feeObservedResult out) =
      .suspended
        (frame.beginResume (requestFor .burnInitialBalance0 locals.token0 (.balanceOf frame.context.pair)))
        (requestFor .burnInitialBalance1 locals.token1 (.balanceOf frame.context.pair))
        (.burnInitialBalance1 locals (Bytes.toB256 (out.take 32))) := by
  simp only [resumeSegment, decodeExternal, requestFor, feeObservedResult,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true, long]
  rfl

theorem burn_resumeInitialBalance1 {frame : Frame} {locals : BurnLocals} {out : Bytes}
    {balance0 : B256} (long : 32 ≤ out.length) :
    resumeSegment frame (requestFor .burnInitialBalance1 locals.token1 (.balanceOf frame.context.pair))
        (.burnInitialBalance1 locals balance0) (feeObservedResult out) =
      .suspended
        (frame.beginResume (requestFor .burnInitialBalance1 locals.token1 (.balanceOf frame.context.pair)))
        (requestFor .burnFeeTo frame.current.state.factory .feeTo)
        (.burnFee ⟨locals, balance0, Bytes.toB256 (out.take 32),
          frame.current.state.balanceOf frame.context.pair⟩) := by
  simp only [resumeSegment, decodeExternal, requestFor, feeObservedResult,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true, long]
  rfl

end Blanc.Lift.UniswapV2Pair
