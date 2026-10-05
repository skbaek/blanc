import Blanc.Lift.UniswapV2Pair.Execution

/-!
# Arithmetic-parameterised Pair driver and the goal's model mutants

The production driver in `Execution` fixes three priced arithmetic functions: the
mint quotient `mintAmount`, the burn payout `burnAmounts` and the swap invariant
check `swapCheck`. This module clones only the driver pieces that call them
(`Frame.mintAfterFee`, `Frame.burnAfterFee`, the three resuming continuations and
the finite mutual driver that resumes segments), parameterised by an `Arithmetic`
record. Every other segment delegates to the production `resumeSegment`, and the
entry segment is the production `startTyped`, at the root and at every nested
invocation.

`runTypedWith_production` is the compatibility evidence: at the production record
the parameterised driver is production `runTyped`, for all inputs.

The mutants keep every original guard and failure, and change only an accepted
result: `mintRoundUp` (later-mint quotients round up; first mint unchanged),
`burnRoundUp` (payouts round toward the user) and `feeMutant fee` (the swap check
with input charge `fee` per thousand; production is `fee = 3`, i.e. 997).
-/

namespace Blanc.Lift.UniswapV2Pair.ModelMutants

open Jaune

/-- The priced arithmetic the Pair driver consumes. -/
structure Arithmetic where
  mintAmount : B256 → B256 → B256 → Nat → Nat → Except Failure Nat
  burnAmounts : B256 → B256 → B256 → B256 → Except Failure (Nat × Nat)
  swapCheck : B256 → B256 → Nat → Nat → Nat → Nat → Except Failure Unit

/-- The production arithmetic of `Model`. -/
def production : Arithmetic :=
  { mintAmount := mintAmount, burnAmounts := burnAmounts, swapCheck := swapCheck }

/-- Ceiling division, the upward-rounding counterpart of `/`. -/
def ceilDiv (numerator denominator : Nat) : Nat := (numerator + denominator - 1) / denominator

/-- Later-mint issuance with both proportional quotients rounded up. -/
def mintLiquidityUp (amount0 amount1 supply reserve0 reserve1 : Nat) : Nat :=
  min (ceilDiv (amount0 * supply) reserve0) (ceilDiv (amount1 * supply) reserve1)

/-- Same guards and first-mint result as `mintAmount`; accepted later quotients round up. -/
def mintAmountUp (amount0 amount1 supply : B256) (reserve0 reserve1 : Nat) : Except Failure Nat :=
  match mintAmount amount0 amount1 supply reserve0 reserve1 with
  | .error failure => .error failure
  | .ok liquidity =>
    .ok (if supply = 0 then liquidity
      else mintLiquidityUp amount0.toNat amount1.toNat supply.toNat reserve0 reserve1)

/-- Same guards as `burnAmounts`; accepted payouts round toward the user. -/
def burnAmountsUp (liquidity balance0 balance1 supply : B256) : Except Failure (Nat × Nat) :=
  match burnAmounts liquidity balance0 balance1 supply with
  | .error failure => .error failure
  | .ok _ =>
    .ok (ceilDiv (liquidity.toNat * balance0.toNat) supply.toNat,
      ceilDiv (liquidity.toNat * balance1.toNat) supply.toNat)

/-- `swapCheck` with the input charge `fee` per thousand in place of the source's 3. -/
def swapCheckFee (fee : Nat) (balance0 balance1 : B256) (amount0In amount1In reserve0 reserve1 : Nat) :
    Except Failure Unit :=
  if amount0In > 0 ∨ amount1In > 0 then
    if balance0.toNat * 1000 < 2 ^ 256 ∧ amount0In * fee < 2 ^ 256 then
      if amount0In * fee ≤ balance0.toNat * 1000 then
        if balance1.toNat * 1000 < 2 ^ 256 ∧ amount1In * fee < 2 ^ 256 then
          if amount1In * fee ≤ balance1.toNat * 1000 then
            let adjusted0 := balance0.toNat * 1000 - amount0In * fee
            let adjusted1 := balance1.toNat * 1000 - amount1In * fee
            if adjusted0 * adjusted1 < 2 ^ 256 then
              if reserve0 * reserve1 * 1000 ^ 2 ≤ adjusted0 * adjusted1 then .ok ()
              else .error (.sourceGuard "UniswapV2: K")
            else .error (.sourceGuard "ds-math-mul-overflow")
          else .error (.sourceGuard "ds-math-sub-underflow")
        else .error (.sourceGuard "ds-math-mul-overflow")
      else .error (.sourceGuard "ds-math-sub-underflow")
    else .error (.sourceGuard "ds-math-mul-overflow")
  else .error (.sourceGuard "UniswapV2: INSUFFICIENT_INPUT_AMOUNT")

/-- The source's swap check is the fee-parameterised check at 3 (the 997 constant). -/
theorem swapCheckFee_three : swapCheckFee 3 = swapCheck := rfl

/-- Goal mutant U3(ii): successful later-mint quotients round up. -/
def mintRoundUp : Arithmetic := { production with mintAmount := mintAmountUp }

/-- Goal mutant U2: the floor in `burn` rounds toward the user. -/
def burnRoundUp : Arithmetic := { production with burnAmounts := burnAmountsUp }

/-- Goal mutant U2: fee constant 997 changed to `1000 - fee` (998 is `fee = 2`). -/
def feeMutant (fee : Nat) : Arithmetic := { production with swapCheck := swapCheckFee fee }

/-- The first mint is unchanged by the upward mutant. -/
theorem mintAmountUp_initial {amount0 amount1 supply : B256} {reserve0 reserve1 : Nat}
    (zeroSupply : supply = 0) :
    mintAmountUp amount0 amount1 supply reserve0 reserve1 =
      mintAmount amount0 amount1 supply reserve0 reserve1 := by
  rw [mintAmountUp]
  cases mintAmount amount0 amount1 supply reserve0 reserve1 with
  | error failure => rfl
  | ok liquidity => exact congrArg Except.ok (ite_eq_left zeroSupply)

namespace Frame

/-- `Frame.mintAfterFee` with the pricing function supplied by `A`. -/
def mintAfterFeeWith (A : Arithmetic) (frame : Frame) (observed : MintObserved) (fee : FeeResult) :
    SegmentResult :=
  let charged := frame.withEvents fee.state fee.events
  let supply := fee.state.totalSupply
  match A.mintAmount observed.amount0 observed.amount1 supply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | .error failure => charged.fail failure
  | .ok liquidity =>
    let initial : Except Failure (State × List Event) :=
      if supply = 0 then fee.state.mintLP 0 1000 else .ok (fee.state, [])
    match initial with
    | .error failure => charged.fail failure
    | .ok (postMinimum, minimumEvents) =>
      let minimum := charged.withEvents postMinimum minimumEvents
      if liquidity > 0 then
        match postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | .error failure => minimum.fail failure
        | .ok (post, events) =>
          (minimum.withEvents post events).finishUpdated observed.balance0 observed.balance1
            observed.reserves fee.feeOn
            (some (.mint frame.context.sender observed.amount0 observed.amount1))
            (encodeWords [Nat.toB256 liquidity])
      else minimum.fail (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY_MINTED")

/-- `Frame.burnAfterFee` with the payout function supplied by `A`. -/
def burnAfterFeeWith (A : Arithmetic) (frame : Frame) (observed : BurnObserved) (fee : FeeResult) :
    SegmentResult :=
  let charged := frame.withEvents fee.state fee.events
  let supply := fee.state.totalSupply
  match A.burnAmounts observed.liquidity observed.balance0 observed.balance1 supply with
  | .error failure => charged.fail failure
  | .ok (amount0, amount1) =>
    if amount0 > 0 ∧ amount1 > 0 then
      match fee.state.burnLP frame.context.pair observed.liquidity with
      | .error failure => charged.fail failure
      | .ok (post, events) =>
        let priced : BurnPriced :=
          { observed := observed, feeOn := fee.feeOn, feeMinted := fee.minted,
            supply := supply, amount0 := Nat.toB256 amount0, amount1 := Nat.toB256 amount1 }
        (charged.withEvents post events).suspend .burnTransfer0 observed.locals.token0
          (.transfer observed.locals.recipient priced.amount0) (.burnTransfer0 priced)
    else charged.fail (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY_BURNED")

end Frame

/-- `resumeSegment` with the three priced continuations computed by `A`; every other
continuation is the production segment. -/
def resumeWith (A : Arithmetic) (prior : Frame) (request : Request) (continuation : Continuation)
    (result : ExternalResult) : SegmentResult :=
  match continuation with
  | .mintFee observed =>
    let frame := prior.beginResume request
    match decodeExternal request result with
    | .error failure => frame.fail failure
    | .ok (.address feeTo) =>
      match mintFee frame.current.state feeTo observed.reserves.reserve0.val
          observed.reserves.reserve1.val with
      | .error failure => frame.fail failure
      | .ok fee => Frame.mintAfterFeeWith A frame observed fee
    | .ok _ => frame.fail .incompleteTranscript
  | .burnFee observed =>
    let frame := prior.beginResume request
    match decodeExternal request result with
    | .error failure => frame.fail failure
    | .ok (.address feeTo) =>
      match mintFee frame.current.state feeTo observed.locals.reserves.reserve0.val
          observed.locals.reserves.reserve1.val with
      | .error failure => frame.fail failure
      | .ok fee => Frame.burnAfterFeeWith A frame observed fee
    | .ok _ => frame.fail .incompleteTranscript
  | .swapBalance1 locals balance0 =>
    let frame := prior.beginResume request
    match decodeExternal request result with
    | .error failure => frame.fail failure
    | .ok (.word balance1) =>
      let (amount0In, amount1In) := swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val
      match A.swapCheck balance0 balance1 amount0In amount1In locals.reserves.reserve0.val
          locals.reserves.reserve1.val with
      | .error failure => frame.fail failure
      | .ok () =>
        frame.finishUpdated balance0 balance1 locals.reserves false
          (some (.swap frame.context.sender (Nat.toB256 amount0In) (Nat.toB256 amount1In)
            locals.amount0Out locals.amount1Out locals.recipient)) []
    | .ok _ => frame.fail .incompleteTranscript
  | _ => resumeSegment prior request continuation result

mutual

/-- `drive` resuming through `resumeWith A`; entries, nested ones included, start with
the production `startTyped`. -/
def driveWith (A : Arithmetic) (fuel : Nat) (segment : SegmentResult) (transcript : Transcript) :
    RunResult :=
  match fuel with
  | 0 => { status := .incomplete, frame := segment.frame, remaining := transcript, childReturns := [] }
  | fuel + 1 =>
    match segment with
    | .finished frame returndata =>
      { status := .success returndata, frame := frame, remaining := transcript, childReturns := [] }
    | .failed frame .incompleteTranscript =>
      { status := .incomplete, frame := frame, remaining := transcript, childReturns := [] }
    | .failed frame failure =>
      { status := .failed failure, frame := frame, remaining := transcript, childReturns := [] }
    | .suspended frame request continuation =>
      match transcript with
      | .done => { status := .incomplete, frame := frame, remaining := .done, childReturns := [] }
      | .next result turns tail =>
        if request.requiresCode && !result.codeExists then
          driveWith A fuel (resumeWith A frame request continuation result) tail
        else
          let executed := driveTurnsWith A fuel frame request 0 turns
          if executed.complete then
            let settled := if result.success then executed.frame
              else { executed.frame with current := frame.current }
            let resumed := driveWith A fuel (resumeWith A settled request continuation result) tail
            { resumed with childReturns := executed.childReturns ++ resumed.childReturns }
          else
            { status := .incomplete, frame := executed.frame, remaining := tail,
              childReturns := executed.childReturns }
      | _ => { status := .incomplete, frame := frame, remaining := transcript, childReturns := [] }

/-- `driveTurns` whose nested Pair invocations run `driveWith A`. -/
def driveTurnsWith (A : Arithmetic) (fuel : Nat) (frame : Frame) (request : Request) (turn : Nat)
    (turns : Transcript) : TurnsResult :=
  match fuel with
  | 0 => { complete := false, frame := frame, childReturns := [] }
  | fuel + 1 =>
    match turns with
    | .done => { complete := true, frame := frame, childReturns := [] }
    | .foreignLog emitter topics data tail =>
      if externalStatic frame request then
        { complete := false, frame := frame, childReturns := [] }
      else
        let origin : ExternalOrigin :=
          { invocation := frame.context.invocation, site := request.site, turn := turn }
        let logged : Frame := { frame with current :=
          { frame.current with logs := frame.current.logs ++ [.foreign origin emitter topics data] } }
        driveTurnsWith A fuel logged request (turn + 1) tail
    | .invoke sender value isStatic entry transcript tail =>
      let context := childContext frame request turn sender value isStatic
      let child := driveWith A fuel (startTyped frame.current context entry) transcript
      match child.status with
      | .incomplete => { complete := false, frame := frame, childReturns := child.childReturns }
      | _ =>
        let settled := { frame with current := child.frame.current }
        let remaining := driveTurnsWith A fuel settled request (turn + 1) tail
        { remaining with childReturns := child.childReturns ++
          [{ context := context, entry := entry, status := child.status }] ++ remaining.childReturns }
    | .next _ _ _ => { complete := false, frame := frame, childReturns := [] }

end

/-- `runTyped` over the arithmetic `A`, with the production fuel. -/
def runTypedWith (A : Arithmetic) (st : State) (ctx : Context) (entry : Entry)
    (transcript : Transcript) : RunResult :=
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  driveWith A (transcript.work + 2) (startTyped current ctx entry) transcript

/-- At the production record the parameterised resume is production `resumeSegment`. -/
theorem resumeWith_production : resumeWith production = resumeSegment := by
  funext prior request continuation result
  cases continuation
  case mintFee observed =>
    rw [resumeWith, resumeSegment]
    cases decodeExternal request result with
    | error failure => rfl
    | ok decoded => cases decoded <;> rfl
  case burnFee observed =>
    rw [resumeWith, resumeSegment]
    cases decodeExternal request result with
    | error failure => rfl
    | ok decoded => cases decoded <;> rfl
  case swapBalance1 locals balance0 =>
    rw [resumeWith, resumeSegment]
    cases decodeExternal request result with
    | error failure => rfl
    | ok decoded => cases decoded <;> rfl
  all_goals rfl

/-- At the production record the parameterised driver is the production driver. -/
theorem driveWith_production (fuel : Nat) :
    (∀ segment transcript, driveWith production fuel segment transcript = drive fuel segment transcript) ∧
    (∀ frame request turn turns,
      driveTurnsWith production fuel frame request turn turns = driveTurns fuel frame request turn turns) := by
  induction fuel with
  | zero =>
    exact ⟨fun segment transcript => by rw [driveWith.eq_def, drive.eq_def],
      fun frame request turn turns => by rw [driveTurnsWith.eq_def, driveTurns.eq_def]⟩
  | succ fuel ih =>
    refine ⟨fun segment transcript => ?_, fun frame request turn turns => ?_⟩
    · rw [driveWith.eq_def, drive.eq_def]
      simp only [resumeWith_production, ih.1, ih.2]
      rfl
    · rw [driveTurnsWith.eq_def, driveTurns.eq_def]
      simp only [ih.1, ih.2]
      rfl

/-- Compatibility evidence: the production record reproduces production `runTyped` exactly. -/
theorem runTypedWith_production : runTypedWith production = runTyped := by
  funext st ctx entry transcript
  rw [runTypedWith, runTyped, (driveWith_production _).1]

end Blanc.Lift.UniswapV2Pair.ModelMutants
