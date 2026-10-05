import Blanc.Lift.UniswapV2Pair.Consumption

/-! The typed swap front (`startTyped` and `resumeSegment`, Execution.lean) from the lock to the
`balance0` suspension, as exact consumption over optional transfer and callback turns. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- `S` exactly consumes the front transcript `T rest` whenever the later segment `S'` exactly
consumes `rest`, adding the child returns `R` in front. -/
def SwapFrontReaches (S : SegmentResult) (T : Transcript → Transcript) (R : List ChildReturn)
    (S' : SegmentResult) : Prop :=
  ∀ rest out, ExactConsumes S' rest out →
    ExactConsumes S (T rest) { out with childReturns := R ++ out.childReturns }

theorem SwapFrontReaches.refl (S : SegmentResult) : SwapFrontReaches S id [] S := by
  intro rest out consumed
  cases out
  exact consumed

theorem SwapFrontReaches.trans {S S' S'' : SegmentResult} {T T' : Transcript → Transcript}
    {R R' : List ChildReturn} (first : SwapFrontReaches S T R S')
    (second : SwapFrontReaches S' T' R' S'') :
    SwapFrontReaches S (T ∘ T') (R ++ R') S'' := by
  intro rest out consumed
  have h := first _ _ (second rest out consumed)
  rw [List.append_assoc]
  exact h

/-- One consumed successful external call: its turns run the frame to checkpoint `c`, and the
resumed segment then reaches `S'`. -/
theorem SwapFrontReaches.call {frame : Frame} {request : Request} {continuation : Continuation}
    {result : ExternalResult} {turns : Transcript} {c : Checkpoint} {rets : List ChildReturn}
    {T : Transcript → Transcript} {R : List ChildReturn} {S' : SegmentResult}
    (during : ExactTurns frame request 0 turns
      { complete := true, frame := { frame with current := c }, childReturns := rets })
    (success : result.success = true)
    (present : (request.requiresCode && !result.codeExists) = false)
    (noCodeTurns : result.codeExists = false → turns = .done)
    (rest : SwapFrontReaches (resumeSegment { frame with current := c } request continuation result)
      T R S') :
    SwapFrontReaches (.suspended frame request continuation) (fun tail => .next result turns (T tail))
      (rets ++ R) S' := by
  intro tail out consumed
  have h := ExactConsumes.nextCall present noCodeTurns during
    (by simp only [success, ↓reduceIte]; exact rest tail out consumed)
  rw [List.append_assoc]
  exact h

/-- The swap frame after the lock, before any suspension. -/
def swapLockedFrame (current : Checkpoint) (ctx : Context) (entry : Entry) : Frame :=
  { Frame.enter current ctx entry with current :=
    { current with state := { current.state with unlocked := 0 } } }

/-- The swap locals the source fixes at the lock. -/
def swapSourceLocals (st : State) (amount0Out amount1Out : B256) (recipient : Adr)
    (data : Bytes) : SwapLocals :=
  { recipient := recipient, reserves := st.cachedReserves, token0 := st.token0,
    token1 := st.token1, amount0Out := amount0Out, amount1Out := amount1Out, data := data }

/-- `startTyped` for a swap that passes the lock and the three source guards: the first
optional transfer, else the rest of the front. -/
theorem swap_startTyped {current : Checkpoint} {ctx : Context} {amount0Out amount1Out : B256}
    {recipient : Adr} {data : Bytes}
    (paid : ctx.value = 0) (nonstatic : ctx.isStatic = false)
    (unlocked : current.state.unlocked = 1)
    (output : amount0Out > 0 ∨ amount1Out > 0)
    (liquidity0 : amount0Out.toNat < current.state.reserve0.val)
    (liquidity1 : amount1Out.toNat < current.state.reserve1.val)
    (to0 : recipient ≠ current.state.token0) (to1 : recipient ≠ current.state.token1) :
    let entry := Entry.swap amount0Out amount1Out recipient data
    let locked := swapLockedFrame current ctx entry
    let locals := swapSourceLocals current.state amount0Out amount1Out recipient data
    startTyped current ctx entry =
      if amount0Out > 0 then
        locked.suspend .swapTransfer0 locals.token0 (.transfer recipient amount0Out)
          (.swapTransfer0 locals)
      else locked.afterSwapTransfer0 locals := by
  intro entry locked locals
  have immediate : startImmediate current ctx entry = none := by
    simp only [startImmediate, ite_eq_right (fun (bad : ctx.value ≠ 0) => bad paid), getterResult, entry]
  have lock : (Frame.enter current ctx entry).lock = .ok locked := by
    simp only [Frame.lock, Frame.enter, unlocked, ite_true, nonstatic, Bool.false_eq_true, ite_false]
    rfl
  simp only [startTyped, immediate, entry]
  rw [lock]
  have guards : amount0Out.toNat < locked.current.state.cachedReserves.reserve0.val ∧
      amount1Out.toNat < locked.current.state.cachedReserves.reserve1.val := ⟨liquidity0, liquidity1⟩
  have tos : recipient ≠ locked.current.state.token0 ∧ recipient ≠ locked.current.state.token1 :=
    ⟨to0, to1⟩
  dsimp only
  simp only [output, guards, tos.1, tos.2, ne_eq, not_false_eq_true, and_self, ite_true]
  rfl

/-- An accepted transfer reply: success with an empty or nonzero-first-word return. -/
def swapTransferReply (out : Bytes) : ExternalResult :=
  { success := true, returndata := out, codeExists := true, recoveryOutput := 0 }

/-- A successful callback reply with the actual code bit (present: the body checked it). -/
def swapCallbackReply (out : Bytes) : ExternalResult :=
  { success := true, returndata := out, codeExists := true, recoveryOutput := 0 }

theorem swap_transfer_decoded {site : CallSite} {token recipient : Adr} {amount : B256}
    {out : Bytes}
    (accepted : out = [] ∨ (32 ≤ out.length ∧ Bytes.toB256 (out.sliceD 0 32 0) ≠ 0)) :
    decodeExternal (requestFor site token (.transfer recipient amount)) (swapTransferReply out) =
      .ok .unit := by
  have take : 32 ≤ out.length → out.sliceD 0 32 0 = out.take 32 := by
    intro long
    unfold List.sliceD
    rw [List.drop_zero, List.takeD_eq_take _ long]
  rcases accepted with empty | ⟨long, head⟩
  · simp only [decodeExternal, requestFor, swapTransferReply, empty, Bool.false_and,
      Bool.false_eq_true, ite_false, ite_true, List.length_nil]
  · have nonempty : out.length ≠ 0 := by omega
    rw [take long] at head
    simp only [decodeExternal, requestFor, swapTransferReply, Bool.false_and, Bool.false_eq_true,
      ite_false, ite_true, nonempty, long, head, ne_eq, not_false_eq_true]

theorem swap_resume_transfer0 {frame : Frame} {locals : SwapLocals} {out : Bytes}
    (accepted : out = [] ∨ (32 ≤ out.length ∧ Bytes.toB256 (out.sliceD 0 32 0) ≠ 0)) :
    let request := requestFor .swapTransfer0 locals.token0 (.transfer locals.recipient locals.amount0Out)
    resumeSegment frame request (.swapTransfer0 locals) (swapTransferReply out) =
      (frame.beginResume request).afterSwapTransfer0 locals := by
  intro request
  simp only [resumeSegment, request, swap_transfer_decoded accepted]

theorem swap_resume_transfer1 {frame : Frame} {locals : SwapLocals} {out : Bytes}
    (accepted : out = [] ∨ (32 ≤ out.length ∧ Bytes.toB256 (out.sliceD 0 32 0) ≠ 0)) :
    let request := requestFor .swapTransfer1 locals.token1 (.transfer locals.recipient locals.amount1Out)
    resumeSegment frame request (.swapTransfer1 locals) (swapTransferReply out) =
      (frame.beginResume request).afterSwapTransfer1 locals := by
  intro request
  simp only [resumeSegment, request, swap_transfer_decoded accepted]

theorem swap_resume_callback {frame : Frame} {locals : SwapLocals} {out : Bytes} :
    let request := requestFor .swapCallback locals.recipient
      (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)
    resumeSegment frame request (.swapCallback locals) (swapCallbackReply out) =
      (frame.beginResume request).suspend .swapBalance0 locals.token0
        (.balanceOf frame.context.pair) (.swapBalance0 locals) := by
  intro request
  simp only [resumeSegment, request, decodeExternal, requestFor, swapCallbackReply, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
  rfl

end Blanc.Lift.UniswapV2Pair
