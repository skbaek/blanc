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
  deriving DecidableEq

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

/-- Pending logs are chronological; an uncommitted ancestor discards descendants. -/
inductive PendingLog
  | owned (event : Event)
  | foreign (emitter : Adr) (topics : List B256) (data : Bytes)

/-- An external call's checkpoint is later than its Pair parent's entry checkpoint. -/
structure Checkpoint where
  state : State
  logs : List PendingLog
  updates : List OracleUpdate

structure Frame where
  context : Context
  entry : Entry
  checkpoint : Checkpoint
  current : Checkpoint

inductive SegmentResult
  | finished (frame : Frame) (returndata : Bytes)
  | failed (frame : Frame) (failure : Failure)
  | suspended (frame : Frame) (request : Request) (continuation : Continuation)


namespace Frame

def enter (current : Checkpoint) (context : Context) (entry : Entry) : Frame :=
  { context := context, entry := entry, checkpoint := current, current := current }

/-- Restore the whole frame, including previously settled descendants. -/
def fail (frame : Frame) (failure : Failure) : SegmentResult :=
  .failed { frame with current := frame.checkpoint } failure

def finish (frame : Frame) (returndata : Bytes) : SegmentResult :=
  .finished frame returndata

def withEvents (frame : Frame) (post : State) (events : List Event) : Frame :=
  { frame with current := { frame.current with state := post, logs := frame.current.logs ++ events.map PendingLog.owned } }

def finishLP (frame : Frame) (result : Except Failure (State × List Event))
    (returndata : Bytes) : SegmentResult :=
  match result with
  | .error failure => frame.fail failure
  | .ok (post, events) => (frame.withEvents post events).finish returndata

def withUpdate (frame : Frame) (post : State) (event : Event) (update : OracleUpdate) : Frame :=
  { frame with current :=
    { state := post, logs := frame.current.logs ++ [.owned event],
      updates := frame.current.updates ++ [update] } }

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

end Blanc.Lift.UniswapV2Pair
