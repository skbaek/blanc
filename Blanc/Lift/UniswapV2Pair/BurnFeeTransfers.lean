import Blanc.Lift.UniswapV2Pair.BurnLogImage
import Blanc.Lift.UniswapV2Pair.BurnEntrySource
import Blanc.Lift.UniswapV2Pair.BurnPricingTurns
import Blanc.Lift.UniswapV2Pair.BurnTransferTurns

/-! The actual fee/pricing producer feeds the Burn transfer/source consumer. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Every reply the Burn source consumes, in call order: the two initial
`balanceOf(pair)` replies, the factory `feeTo` reply, the two token `transfer`
replies with their frame-entry bits, and the two final `balanceOf(pair)` replies,
each with the Pair turns its child re-entered. -/
structure BurnAnswers where
  balance0 : Bytes
  views0 : List StaticViewTurn
  balance1 : Bytes
  views1 : List StaticViewTurn
  feeTo : Bytes
  viewsF : List StaticViewTurn
  reply0 : Bytes
  entered0 : Bool
  turns0 : List MutableTurn
  reply1 : Bytes
  entered1 : Bool
  turns1 : List MutableTurn
  final0 : Bytes
  finalViews0 : List StaticViewTurn
  final1 : Bytes
  finalViews1 : List StaticViewTurn

/-- The Burn source transcript built from its answers, in call order. -/
def BurnAnswers.transcript (a : BurnAnswers) : Transcript :=
  .next (feeObservedResult a.balance0) (staticViewTranscript a.views0 .done)
    (.next (feeObservedResult a.balance1) (staticViewTranscript a.views1 .done)
      (.next (feeObservedResult a.feeTo) (staticViewTranscript a.viewsF .done)
        (burnTransferTranscript a.reply0 a.entered0 a.turns0 a.reply1 a.entered1 a.turns1
          a.final0 a.finalViews0 a.final1 a.finalViews1)))

/-- **Burn call provenance.** Each answer is what an actual external call step
of the derivation `D` returned: the token and factory targets are the addresses
stored in the Pair's entry storage `entry` (slots 6, 7, 5), the balance and fee
calls carry their callee answers to the exact ABI inputs, the transfer CALLs carry
the exact `transfer(recipient, amount)` input with the calldata recipient, and
every queue of re-entered Pair turns is the one the same call's committed child
produced (static views) or the legal locked turns of the child (mutable calls).
Like the sibling families' provenance, each step is a `StepIn D` step; it does
not assert an occurrence in `D`'s parent prefix. -/
def BurnCallProvenance (D : Exec.Deriv) (entry : Stor) (amount0 amount1 : B256)
    (a : BurnAnswers) : Prop :=
  let token0 := (entry.get 6).toAdr.toB256
  let token1 := (entry.get 7).toAdr.toB256
  let factory := (entry.get 5).toAdr.toB256
  let balanceOf := ExternalOperation.encode (.balanceOf D.sevm.currentTarget)
  let payee := (Sevm.dataWord D.sevm 4).toAdr.toB256
  BurnStaticAnswer D D.sevm token0 balanceOf a.balance0 ∧
  PairViewOrigin D D.sevm token0 a.views0 ∧
  BurnStaticAnswer D D.sevm token1 balanceOf a.balance1 ∧
  PairViewOrigin D D.sevm token1 a.views1 ∧
  BurnStaticAnswer D D.sevm factory (ExternalOperation.encode .feeTo) a.feeTo ∧
  PairViewOrigin D D.sevm factory a.viewsF ∧
  BurnTransferAnswer D D.sevm token0 payee amount0 a.reply0 ∧
  PairMutableProvenance D D.sevm token0 a.entered0 a.turns0 ∧
  BurnTransferAnswer D D.sevm token1 payee amount1 a.reply1 ∧
  PairMutableProvenance D D.sevm token1 a.entered1 a.turns1 ∧
  BurnStaticAnswer D D.sevm token0 balanceOf a.final0 ∧
  PairViewOrigin D D.sevm token0 a.finalViews0 ∧
  BurnStaticAnswer D D.sevm token1 balanceOf a.final1 ∧
  PairViewOrigin D D.sevm token1 a.finalViews1

/-- The Burn arm of a Pair frame's transcript authentication: the transcript is
the one built from answers whose provenance is the frame's own call steps, read
against the frame's own entry storage. -/
def BurnFrameAuth (D : Exec.Deriv) (transcript : Transcript) : Prop :=
  ∃ (a : BurnAnswers) (amount0 amount1 : B256), transcript = a.transcript ∧
    BurnCallProvenance D (D.devm.getStor D.sevm.currentTarget) amount0 amount1 a

/-- The full observable Burn result whose consumed transcript is fixed by the
actual call answers before any model state is chosen, with incoming footprint
growth. -/
def BurnEntryAuthenticFinished (U K : WriterKey → Prop) (current : Checkpoint) (D : Exec.Deriv)
    (b : Devm) (o : Outcome) (invocation : List Nat) : Prop :=
  let ctx := writerContext D.sevm invocation
  let recipient := ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord D.sevm 4).toAdr
  ∃ (a : BurnAnswers) (amount0 amount1 : B256),
    BurnCallProvenance D (b.getStor D.sevm.currentTarget) amount0 amount1 a ∧
    ∃ (K' : WriterKey → Prop) (final : Frame) (rets : List ChildReturn) (publicPost : Devm)
      (added : List PendingLog) (rawLogs : List Log),
      (∀ k, K' k → U k) ∧ (∀ k, K k → K' k) ∧
      ExactConsumes (startTyped current ctx (.burn recipient)) a.transcript
        { status := .success (encodeWords [amount0, amount1]), frame := final,
          remaining := .done, childReturns := rets } ∧
      o = .halted publicPost ∧ publicPost.output = encodeWords [amount0, amount1] ∧
      WriterRep K' (publicPost.getStor D.sevm.currentTarget) final.current.state ∧
      final.checkpoint = current ∧ final.context = ctx ∧ final.current.state.unlocked = 1 ∧
      final.current.logs = current.logs ++ added ∧ publicPost.logs = b.logs ++ rawLogs ∧
      added.map (PendingLog.rawWith (burnOwnedRaw D.sevm.currentTarget)) = rawLogs.map some

end Blanc.Lift.UniswapV2Pair
