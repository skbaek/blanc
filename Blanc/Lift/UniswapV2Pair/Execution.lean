import Blanc.Lift.UniswapV2Pair.Model

/-!
# Typed Pair execution interfaces

The interfaces below retain source continuations and return images. Exact raw
dispatch, storage, precompile output memory, frame history and gas correspondence
remain separate obligations. External observations contain no Pair-state patch.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

def permitTypehash : B256 :=
  0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9

def encodeWords (words : List B256) : Bytes := words.flatMap B256.toBytes

/-- Standard return image for one dynamic string; no input-decoder restriction. -/
def encodeString (data : Bytes) : Bytes :=
  encodeWords [32, Nat.toB256 data.length] ++ data ++
    List.replicate ((32 - data.length % 32) % 32) 0

/-- The seventeen source getters retain their return bytes in static frames. -/
def getterResult (st : State) : Entry → Option Bytes
  | .name => some (encodeString [0x55, 0x6e, 0x69, 0x73, 0x77, 0x61, 0x70, 0x20, 0x56, 0x32])
  | .symbol => some (encodeString [0x55, 0x4e, 0x49, 0x2d, 0x56, 0x32])
  | .decimals => some (encodeWords [18])
  | .minimumLiquidity => some (encodeWords [1000])
  | .permitTypehash => some (encodeWords [permitTypehash])
  | .totalSupply => some (encodeWords [st.totalSupply])
  | .balanceOf owner => some (encodeWords [st.balanceOf owner])
  | .allowance owner spender => some (encodeWords [st.allowance owner spender])
  | .domainSeparator => some (encodeWords [st.domainSeparator])
  | .nonces owner => some (encodeWords [st.nonces owner])
  | .factory => some (encodeWords [st.factory.toB256])
  | .token0 => some (encodeWords [st.token0.toB256])
  | .token1 => some (encodeWords [st.token1.toB256])
  | .getReserves => some (encodeWords [Nat.toB256 st.reserve0.val,
      Nat.toB256 st.reserve1.val, st.blockTimestampLast.toB256])
  | .price0CumulativeLast => some (encodeWords [st.price0CumulativeLast])
  | .price1CumulativeLast => some (encodeWords [st.price1CumulativeLast])
  | .kLast => some (encodeWords [st.kLast])
  | _ => none

inductive CallKind
  | call | staticCall
  deriving DecidableEq

/-- Source yield identity, distinct even for identical ABI payloads. -/
inductive CallSite
  | mintBalance0 | mintBalance1 | mintFeeTo
  | burnInitialBalance0 | burnInitialBalance1 | burnFeeTo
  | burnTransfer0 | burnTransfer1 | burnFinalBalance0 | burnFinalBalance1
  | swapTransfer0 | swapTransfer1 | swapCallback | swapBalance0 | swapBalance1
  | skimBalance0 | skimTransfer0 | skimBalance1 | skimTransfer1
  | syncBalance0 | syncBalance1 | permitRecovery
  deriving DecidableEq

inductive ExternalOperation
  | balanceOf (owner : Adr)
  | feeTo
  | transfer (recipient : Adr) (value : B256)
  | callback (sender : Adr) (amount0Out amount1Out : B256) (data : Bytes)
  | recover (digest : B256) (v : UInt8) (r s : B256)

/-- The payload is retained rather than replaced by a numeric oracle answer. -/
structure Request where
  site : CallSite
  kind : CallKind
  target : Adr
  value : B256
  operation : ExternalOperation
  calldata : Bytes
  requiresCode : Bool

/-- Raw callee observations; precompile output memory has a separate adapter seam. -/
structure ExternalResult where
  success : Bool
  returndata : Bytes
  codeExists : Bool
  recoveryOutput : B256

/-- Every cached reserve argument is bounded at its point of origin. -/
structure CachedReserves where
  reserve0 : Fin (2 ^ 112)
  reserve1 : Fin (2 ^ 112)

def State.cachedReserves (st : State) : CachedReserves :=
  { reserve0 := st.reserve0, reserve1 := st.reserve1 }

structure MintObserved where
  recipient : Adr
  reserves : CachedReserves
  balance0 : B256
  balance1 : B256
  amount0 : B256
  amount1 : B256

structure BurnLocals where
  recipient : Adr
  reserves : CachedReserves
  token0 : Adr
  token1 : Adr

structure BurnObserved where
  locals : BurnLocals
  balance0 : B256
  balance1 : B256
  liquidity : B256

structure BurnPriced where
  observed : BurnObserved
  feeOn : Bool
  feeMinted : Nat
  supply : B256
  amount0 : B256
  amount1 : B256

structure SwapLocals where
  recipient : Adr
  reserves : CachedReserves
  token0 : Adr
  token1 : Adr
  amount0Out : B256
  amount1Out : B256
  data : Bytes

structure SkimLocals where
  recipient : Adr
  token0 : Adr
  token1 : Adr

/-- Constructor fields are the exact locals surviving each external suspension. -/
inductive Continuation
  | mintBalance0 (recipient : Adr) (reserves : CachedReserves)
  | mintBalance1 (recipient : Adr) (reserves : CachedReserves) (balance0 : B256)
  | mintFee (observed : MintObserved)
  | burnInitialBalance0 (locals : BurnLocals)
  | burnInitialBalance1 (locals : BurnLocals) (balance0 : B256)
  | burnFee (observed : BurnObserved)
  | burnTransfer0 (priced : BurnPriced)
  | burnTransfer1 (priced : BurnPriced)
  | burnFinalBalance0 (priced : BurnPriced)
  | burnFinalBalance1 (priced : BurnPriced) (balance0 : B256)
  | swapTransfer0 (locals : SwapLocals)
  | swapTransfer1 (locals : SwapLocals)
  | swapCallback (locals : SwapLocals)
  | swapBalance0 (locals : SwapLocals)
  | swapBalance1 (locals : SwapLocals) (balance0 : B256)
  | skimBalance0 (locals : SkimLocals)
  | skimTransfer0 (locals : SkimLocals)
  | skimBalance1 (locals : SkimLocals)
  | skimTransfer1 (locals : SkimLocals)
  | syncBalance0 (reserves : CachedReserves)
  | syncBalance1 (reserves : CachedReserves) (balance0 : B256)
  | permitRecovery (owner spender : Adr) (value : B256)

/-- Owned receipt provenance includes the configured root's invocation prefix. -/
structure ReceiptOrigin where
  invocation : List Nat
  segment : Nat
  afterCall : Option CallSite

structure TaggedOracleUpdate where
  origin : ReceiptOrigin
  update : OracleUpdate

structure ExternalOrigin where
  invocation : List Nat
  site : CallSite
  turn : Nat

/-- Pending logs are chronological; an uncommitted ancestor discards descendants. -/
inductive PendingLog
  | owned (origin : ReceiptOrigin) (event : Event)
  | foreign (origin : ExternalOrigin) (emitter : Adr) (topics : List B256) (data : Bytes)

/-- An external call's checkpoint is later than its Pair parent's entry checkpoint. -/
structure Checkpoint where
  state : State
  logs : List PendingLog
  updates : List TaggedOracleUpdate

structure Frame where
  context : Context
  entry : Entry
  checkpoint : Checkpoint
  current : Checkpoint
  segment : Nat
  afterCall : Option CallSite

inductive SegmentResult
  | finished (frame : Frame) (returndata : Bytes)
  | failed (frame : Frame) (failure : Failure)
  | suspended (frame : Frame) (request : Request) (continuation : Continuation)


namespace Frame

def enter (current : Checkpoint) (context : Context) (entry : Entry) : Frame :=
  { context := context, entry := entry, checkpoint := current, current := current,
    segment := 0, afterCall := none }

def origin (frame : Frame) : ReceiptOrigin :=
  { invocation := frame.context.invocation, segment := frame.segment, afterCall := frame.afterCall }

def beginResume (frame : Frame) (request : Request) : Frame :=
  { frame with segment := frame.segment + 1, afterCall := some request.site }

/-- Restore the whole frame, including previously settled descendants. -/
def fail (frame : Frame) (failure : Failure) : SegmentResult :=
  .failed { frame with current := frame.checkpoint } failure

def finish (frame : Frame) (returndata : Bytes) : SegmentResult :=
  .finished frame returndata

def withEvents (frame : Frame) (post : State) (events : List Event) : Frame :=
  { frame with current := { frame.current with state := post, logs := frame.current.logs ++ events.map (PendingLog.owned frame.origin) } }

def finishLP (frame : Frame) (result : Except Failure (State × List Event))
    (returndata : Bytes) : SegmentResult :=
  match result with
  | .error failure => frame.fail failure
  | .ok (post, events) => (frame.withEvents post events).finish returndata

def withUpdate (frame : Frame) (post : State) (event : Event) (update : OracleUpdate) : Frame :=
  { frame with current :=
    { state := post, logs := frame.current.logs ++ [.owned frame.origin event],
      updates := frame.current.updates ++ [{ origin := frame.origin, update := update }] } }

end Frame

/-- Entries without an external suspension; the full driver consumes this prefix. -/
def startImmediate (current : Checkpoint) (ctx : Context) (entry : Entry) :
    Option SegmentResult :=
  let frame := Frame.enter current ctx entry
  if ctx.value ≠ 0 then some (frame.fail .emptyRevert)
  else
    match getterResult current.state entry with
    | some returndata => some (frame.finish returndata)
    | none =>
      let st := current.state
      match entry with
      | .approve spender value =>
        some (frame.finishLP (st.approveLP ctx ctx.sender spender value) (encodeWords [1]))
      | .transfer recipient value =>
        some (frame.finishLP (st.transferLP ctx ctx.sender recipient value) (encodeWords [1]))
      | .transferFrom source recipient value =>
        some (frame.finishLP (st.transferFromLP ctx source recipient value) (encodeWords [1]))
      | .initialize token0 token1 =>
        if ctx.sender = st.factory then
          if ctx.isStatic then some (frame.fail .staticWrite)
          else
            let post := { st with token0 := token0, token1 := token1 }
            some ((frame.withEvents post []).finish [])
        else some (frame.fail (.sourceGuard "UniswapV2: FORBIDDEN"))
      | _ => none


/-- Source ABI payloads; raw caller-calldata decoding is independent. -/
def ExternalOperation.encode : ExternalOperation → Bytes
  | .balanceOf owner => [0x70, 0xa0, 0x82, 0x31] ++ encodeWords [owner.toB256]
  | .feeTo => [0x01, 0x7e, 0x7e, 0x58]
  | .transfer recipient value =>
    [0xa9, 0x05, 0x9c, 0xbb] ++ encodeWords [recipient.toB256, value]
  | .callback sender amount0Out amount1Out data =>
    [0x10, 0xd1, 0xe8, 0x5c] ++
      encodeWords [sender.toB256, amount0Out, amount1Out, 128, Nat.toB256 data.length] ++
      data ++ List.replicate ((32 - data.length % 32) % 32) 0
  | .recover digest v r s => encodeWords [digest, v.toB256, r, s]

def requestFor (site : CallSite) (target : Adr) (operation : ExternalOperation) : Request :=
  let kind := match operation with
    | .transfer _ _ | .callback _ _ _ _ => CallKind.call
    | _ => CallKind.staticCall
  let requiresCode := match operation with
    | .transfer _ _ | .recover _ _ _ _ => false
    | _ => true
  { site := site, kind := kind, target := target, value := 0,
    operation := operation, calldata := operation.encode, requiresCode := requiresCode }

/-- The nonce supplied here is the old value, before the wrapped postincrement. -/
def permitDigest (st : State) (owner spender : Adr) (value nonce deadline : B256) : B256 :=
  let inner := (encodeWords [permitTypehash, owner.toB256, spender.toB256,
    value, nonce, deadline]).keccak
  Bytes.keccak ([0x19, 0x01] ++ st.domainSeparator.toBytes ++ inner.toBytes)

namespace Frame

def suspend (frame : Frame) (site : CallSite) (target : Adr)
    (operation : ExternalOperation) (continuation : Continuation) : SegmentResult :=
  .suspended frame (requestFor site target operation) continuation

/-- Lock failure precedes the attempted write's static fault. -/
def lock (frame : Frame) : Except Failure Frame :=
  if frame.current.state.unlocked = 1 then
    if frame.context.isStatic then .error .staticWrite
    else .ok { frame with current :=
      { frame.current with state := { frame.current.state with unlocked := 0 } } }
  else .error (.sourceGuard "UniswapV2: LOCKED")

end Frame

/-- First owned segment of every typed entry; no external answer is constrained. -/
def startTyped (current : Checkpoint) (ctx : Context) (entry : Entry) : SegmentResult :=
  match startImmediate current ctx entry with
  | some result => result
  | none =>
    let frame := Frame.enter current ctx entry
    let st := current.state
    match entry with
    | .permit owner spender value deadline v r s =>
      if ctx.timestamp ≤ deadline then
        if ctx.isStatic then frame.fail .staticWrite
        else
          let nonce := st.nonces owner
          let digest := permitDigest st owner spender value nonce deadline
          let post := { st with nonces := Function.update st.nonces owner (nonce + 1) }
          (frame.withEvents post []).suspend .permitRecovery 1 (.recover digest v r s)
            (.permitRecovery owner spender value)
      else frame.fail (.sourceGuard "UniswapV2: EXPIRED")
    | _ =>
      match frame.lock with
      | .error failure => frame.fail failure
      | .ok locked =>
        let st := locked.current.state
        let reserves := st.cachedReserves
        match entry with
        | .mint recipient =>
          locked.suspend .mintBalance0 st.token0 (.balanceOf ctx.pair)
            (.mintBalance0 recipient reserves)
        | .burn recipient =>
          let locals : BurnLocals :=
            { recipient := recipient, reserves := reserves, token0 := st.token0, token1 := st.token1 }
          locked.suspend .burnInitialBalance0 locals.token0 (.balanceOf ctx.pair)
            (.burnInitialBalance0 locals)
        | .swap amount0Out amount1Out recipient data =>
          if amount0Out > 0 ∨ amount1Out > 0 then
            if amount0Out.toNat < reserves.reserve0.val ∧ amount1Out.toNat < reserves.reserve1.val then
              if recipient ≠ st.token0 ∧ recipient ≠ st.token1 then
                let locals : SwapLocals :=
                  { recipient := recipient, reserves := reserves, token0 := st.token0,
                    token1 := st.token1, amount0Out := amount0Out, amount1Out := amount1Out, data := data }
                if amount0Out > 0 then
                  locked.suspend .swapTransfer0 locals.token0 (.transfer recipient amount0Out)
                    (.swapTransfer0 locals)
                else if amount1Out > 0 then
                  locked.suspend .swapTransfer1 locals.token1 (.transfer recipient amount1Out)
                    (.swapTransfer1 locals)
                else if data.length > 0 then
                  locked.suspend .swapCallback recipient (.callback ctx.sender amount0Out amount1Out data)
                    (.swapCallback locals)
                else locked.suspend .swapBalance0 locals.token0 (.balanceOf ctx.pair)
                  (.swapBalance0 locals)
              else locked.fail (.sourceGuard "UniswapV2: INVALID_TO")
            else locked.fail (.sourceGuard "UniswapV2: INSUFFICIENT_LIQUIDITY")
          else locked.fail (.sourceGuard "UniswapV2: INSUFFICIENT_OUTPUT_AMOUNT")
        | .skim recipient =>
          let locals : SkimLocals := { recipient := recipient, token0 := st.token0, token1 := st.token1 }
          locked.suspend .skimBalance0 locals.token0 (.balanceOf ctx.pair) (.skimBalance0 locals)
        | .sync =>
          locked.suspend .syncBalance0 st.token0 (.balanceOf ctx.pair) (.syncBalance0 reserves)
        | _ => locked.fail .incompleteTranscript


inductive DecodedResult
  | word (value : B256)
  | address (value : Adr)
  | unit

/-- Actual first-word return rules; no canonical Boolean-one premise is imposed. -/
def decodeExternal (request : Request) (result : ExternalResult) : Except Failure DecodedResult :=
  if request.requiresCode && !result.codeExists then .error .emptyRevert
  else
    match request.operation with
    | .transfer _ _ =>
      if result.success then
        if result.returndata.length = 0 then .ok .unit
        else if 32 ≤ result.returndata.length then
          if (Bytes.toB256 (result.returndata.take 32)) ≠ 0 then .ok .unit
          else .error (.sourceGuard "UniswapV2: TRANSFER_FAILED")
        else .error .emptyRevert
      else .error (.sourceGuard "UniswapV2: TRANSFER_FAILED")
    | _ =>
      if result.success then
        match request.operation with
        | .balanceOf _ =>
          if 32 ≤ result.returndata.length then .ok (.word (Bytes.toB256 (result.returndata.take 32)))
          else .error .emptyRevert
        | .feeTo =>
          if 32 ≤ result.returndata.length then .ok (.address (Bytes.toB256 (result.returndata.take 32)).toAdr)
          else .error .emptyRevert
        | .callback _ _ _ _ => .ok .unit
        | .recover _ _ _ _ => .ok (.address result.recoveryOutput.toAdr)
        | .transfer _ _ => .error .incompleteTranscript
      else .error (.bubbledRevert result.returndata)

namespace Frame

def finishLocked (frame : Frame) (returndata : Bytes) : SegmentResult :=
  let post := { frame.current.state with unlocked := 1 }
  (frame.withEvents post []).finish returndata

def finishUpdated (frame : Frame) (balance0 balance1 : B256) (reserves : CachedReserves)
    (feeOn : Bool) (lastEvent : Option Event) (returndata : Bytes) : SegmentResult :=
  match frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | .error failure => frame.fail failure
  | .ok (post, event, update) =>
    let post := if feeOn then
      { post with kLast := Nat.toB256 (post.reserve0.val * post.reserve1.val) }
      else post
    let updated := frame.withUpdate post event update
    let finalFrame := match lastEvent with
      | none => updated
      | some extra => updated.withEvents post [extra]
    finalFrame.finishLocked returndata

def afterSwapTransfer1 (frame : Frame) (locals : SwapLocals) : SegmentResult :=
  if locals.data.length > 0 then
    frame.suspend .swapCallback locals.recipient
      (.callback frame.context.sender locals.amount0Out locals.amount1Out locals.data)
      (.swapCallback locals)
  else frame.suspend .swapBalance0 locals.token0 (.balanceOf frame.context.pair)
    (.swapBalance0 locals)

def afterSwapTransfer0 (frame : Frame) (locals : SwapLocals) : SegmentResult :=
  if locals.amount1Out > 0 then
    frame.suspend .swapTransfer1 locals.token1 (.transfer locals.recipient locals.amount1Out)
      (.swapTransfer1 locals)
  else frame.afterSwapTransfer1 locals

end Frame


namespace Frame

def mintAfterFee (frame : Frame) (observed : MintObserved) (fee : FeeResult) : SegmentResult :=
  let charged := frame.withEvents fee.state fee.events
  let supply := fee.state.totalSupply
  match mintAmount observed.amount0 observed.amount1 supply
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

def burnAfterFee (frame : Frame) (observed : BurnObserved) (fee : FeeResult) : SegmentResult :=
  let charged := frame.withEvents fee.state fee.events
  let supply := fee.state.totalSupply
  match burnAmounts observed.liquidity observed.balance0 observed.balance1 supply with
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

/-- Resume one owned segment. Child state can enter only through the finite driver. -/
def resumeSegment (prior : Frame) (request : Request) (continuation : Continuation)
    (result : ExternalResult) : SegmentResult :=
  let frame := prior.beginResume request
  match decodeExternal request result with
  | .error failure => frame.fail failure
  | .ok decoded =>
    let st := frame.current.state
    match continuation, decoded with
    | .mintBalance0 recipient reserves, .word balance0 =>
      frame.suspend .mintBalance1 st.token1 (.balanceOf frame.context.pair)
        (.mintBalance1 recipient reserves balance0)
    | .mintBalance1 recipient reserves balance0, .word balance1 =>
      if reserves.reserve0.val ≤ balance0.toNat ∧ reserves.reserve1.val ≤ balance1.toNat then
        let observed : MintObserved :=
          { recipient := recipient, reserves := reserves, balance0 := balance0, balance1 := balance1,
            amount0 := balance0 - Nat.toB256 reserves.reserve0.val,
            amount1 := balance1 - Nat.toB256 reserves.reserve1.val }
        frame.suspend .mintFeeTo st.factory .feeTo (.mintFee observed)
      else frame.fail (.sourceGuard "ds-math-sub-underflow")
    | .mintFee observed, .address feeTo =>
      match mintFee st feeTo observed.reserves.reserve0.val observed.reserves.reserve1.val with
      | .error failure => frame.fail failure
      | .ok fee => frame.mintAfterFee observed fee
    | .burnInitialBalance0 locals, .word balance0 =>
      frame.suspend .burnInitialBalance1 locals.token1 (.balanceOf frame.context.pair)
        (.burnInitialBalance1 locals balance0)
    | .burnInitialBalance1 locals balance0, .word balance1 =>
      let observed : BurnObserved :=
        { locals := locals, balance0 := balance0, balance1 := balance1,
          liquidity := st.balanceOf frame.context.pair }
      frame.suspend .burnFeeTo st.factory .feeTo (.burnFee observed)
    | .burnFee observed, .address feeTo =>
      match mintFee st feeTo observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val with
      | .error failure => frame.fail failure
      | .ok fee => frame.burnAfterFee observed fee
    | .burnTransfer0 priced, .unit =>
      frame.suspend .burnTransfer1 priced.observed.locals.token1
        (.transfer priced.observed.locals.recipient priced.amount1) (.burnTransfer1 priced)
    | .burnTransfer1 priced, .unit =>
      frame.suspend .burnFinalBalance0 priced.observed.locals.token0 (.balanceOf frame.context.pair)
        (.burnFinalBalance0 priced)
    | .burnFinalBalance0 priced, .word balance0 =>
      frame.suspend .burnFinalBalance1 priced.observed.locals.token1 (.balanceOf frame.context.pair)
        (.burnFinalBalance1 priced balance0)
    | .burnFinalBalance1 priced balance0, .word balance1 =>
      frame.finishUpdated balance0 balance1 priced.observed.locals.reserves priced.feeOn
        (some (.burn frame.context.sender priced.amount0 priced.amount1 priced.observed.locals.recipient))
        (encodeWords [priced.amount0, priced.amount1])
    | .swapTransfer0 locals, .unit => frame.afterSwapTransfer0 locals
    | .swapTransfer1 locals, .unit => frame.afterSwapTransfer1 locals
    | .swapCallback locals, .unit =>
      frame.suspend .swapBalance0 locals.token0 (.balanceOf frame.context.pair) (.swapBalance0 locals)
    | .swapBalance0 locals, .word balance0 =>
      frame.suspend .swapBalance1 locals.token1 (.balanceOf frame.context.pair) (.swapBalance1 locals balance0)
    | .swapBalance1 locals balance0, .word balance1 =>
      let (amount0In, amount1In) := swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val
      match swapCheck balance0 balance1 amount0In amount1In locals.reserves.reserve0.val locals.reserves.reserve1.val with
      | .error failure => frame.fail failure
      | .ok () =>
        frame.finishUpdated balance0 balance1 locals.reserves false
          (some (.swap frame.context.sender (Nat.toB256 amount0In) (Nat.toB256 amount1In)
            locals.amount0Out locals.amount1Out locals.recipient)) []
    | .skimBalance0 locals, .word balance0 =>
      if st.reserve0.val ≤ balance0.toNat then
        frame.suspend .skimTransfer0 locals.token0
          (.transfer locals.recipient (balance0 - Nat.toB256 st.reserve0.val)) (.skimTransfer0 locals)
      else frame.fail (.sourceGuard "ds-math-sub-underflow")
    | .skimTransfer0 locals, .unit =>
      frame.suspend .skimBalance1 locals.token1 (.balanceOf frame.context.pair) (.skimBalance1 locals)
    | .skimBalance1 locals, .word balance1 =>
      if st.reserve1.val ≤ balance1.toNat then
        frame.suspend .skimTransfer1 locals.token1
          (.transfer locals.recipient (balance1 - Nat.toB256 st.reserve1.val)) (.skimTransfer1 locals)
      else frame.fail (.sourceGuard "ds-math-sub-underflow")
    | .skimTransfer1 _, .unit => frame.finishLocked []
    | .syncBalance0 reserves, .word balance0 =>
      frame.suspend .syncBalance1 st.token1 (.balanceOf frame.context.pair) (.syncBalance1 reserves balance0)
    | .syncBalance1 reserves balance0, .word balance1 =>
      frame.finishUpdated balance0 balance1 reserves false none []
    | .permitRecovery owner spender value, .address recovered =>
      if recovered ≠ 0 ∧ recovered = owner then
        frame.finishLP (st.approveLP frame.context owner spender value) []
      else frame.fail (.sourceGuard "UniswapV2: INVALID_SIGNATURE")
    | _, _ => frame.fail .incompleteTranscript


def CallSite.ordinal : CallSite → Nat
  | .mintBalance0 => 0 | .mintBalance1 => 1 | .mintFeeTo => 2
  | .burnInitialBalance0 => 3 | .burnInitialBalance1 => 4 | .burnFeeTo => 5
  | .burnTransfer0 => 6 | .burnTransfer1 => 7 | .burnFinalBalance0 => 8 | .burnFinalBalance1 => 9
  | .swapTransfer0 => 10 | .swapTransfer1 => 11 | .swapCallback => 12
  | .swapBalance0 => 13 | .swapBalance1 => 14
  | .skimBalance0 => 15 | .skimTransfer0 => 16 | .skimBalance1 => 17 | .skimTransfer1 => 18
  | .syncBalance0 => 19 | .syncBalance1 => 20 | .permitRecovery => 21

/-- Finite observations, not an arbitrary Pair-state or log suffix patch. -/
inductive Transcript
  | done
  | next (result : ExternalResult) (turns : Transcript) (tail : Transcript)
  | foreignLog (emitter : Adr) (topics : List B256) (data : Bytes) (tail : Transcript)
  | invoke (sender : Adr) (value : B256) (isStatic : Bool) (entry : Entry)
      (transcript : Transcript) (tail : Transcript)

/-- Count syntax nodes structurally, without inspecting word or returndata magnitudes. -/
def Transcript.work : Transcript → Nat
  | .done => 0
  | .next _ turns tail => 1 + turns.work + tail.work
  | .foreignLog _ _ _ tail => 1 + tail.work
  | .invoke _ _ _ _ transcript tail => 1 + transcript.work + tail.work

inductive RunStatus
  | success (returndata : Bytes)
  | failed (failure : Failure)
  | incomplete

/-- Return observations survive as trace facts; pending state effects obey rollback. -/
structure ChildReturn where
  context : Context
  entry : Entry
  status : RunStatus

structure RunResult where
  status : RunStatus
  frame : Frame
  remaining : Transcript
  childReturns : List ChildReturn

structure TurnsResult where
  complete : Bool
  frame : Frame
  childReturns : List ChildReturn

def SegmentResult.frame : SegmentResult → Frame
  | .finished frame _ | .failed frame _ | .suspended frame _ _ => frame

def externalStatic (frame : Frame) (request : Request) : Bool :=
  frame.context.isStatic || request.kind == .staticCall

/-- Prefixing by the configured root and source call site separates message roots. -/
def childContext (frame : Frame) (request : Request) (turn : Nat) (sender : Adr)
    (value : B256) (isStatic : Bool) : Context :=
  { frame.context with
    sender := sender
    value := value
    isStatic := externalStatic frame request || isStatic
    invocation := frame.context.invocation ++ [request.site.ordinal, turn] }

mutual

def drive (fuel : Nat) (segment : SegmentResult) (transcript : Transcript) : RunResult :=
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
          drive fuel (resumeSegment frame request continuation result) tail
        else
          let executed := driveTurns fuel frame request 0 turns
          if executed.complete then
            let settled := if result.success then executed.frame
              else { executed.frame with current := frame.current }
            let resumed := drive fuel (resumeSegment settled request continuation result) tail
            { resumed with childReturns := executed.childReturns ++ resumed.childReturns }
          else
            { status := .incomplete, frame := executed.frame, remaining := tail,
              childReturns := executed.childReturns }
      | _ => { status := .incomplete, frame := frame, remaining := transcript, childReturns := [] }

def driveTurns (fuel : Nat) (frame : Frame) (request : Request) (turn : Nat)
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
        driveTurns fuel logged request (turn + 1) tail
    | .invoke sender value isStatic entry transcript tail =>
      let context := childContext frame request turn sender value isStatic
      let child := drive fuel (startTyped frame.current context entry) transcript
      match child.status with
      | .incomplete => { complete := false, frame := frame, childReturns := child.childReturns }
      | _ =>
        let settled := { frame with current := child.frame.current }
        let remaining := driveTurns fuel settled request (turn + 1) tail
        { remaining with childReturns := child.childReturns ++
          [{ context := context, entry := entry, status := child.status }] ++ remaining.childReturns }
    | .next _ _ _ => { complete := false, frame := frame, childReturns := [] }

end

/-- Fuel is derived from the finite input syntax, not a caller/callee acceptance premise. -/
def runTyped (st : State) (ctx : Context) (entry : Entry) (transcript : Transcript) : RunResult :=
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  drive (transcript.work + 2) (startTyped current ctx entry) transcript

end Blanc.Lift.UniswapV2Pair
