import Blanc.Lift.UniswapV2Pair.BurnFinalTurns
import Blanc.Lift.UniswapV2Pair.LockedSupply
import Blanc.Lift.UniswapV2Pair.SkimSource

/-! Actual mutable transfer queues for the Burn source continuation. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A successful mutable call either executes an enabled precompile without a
code frame, or its committed child supplies exactly the retained ordered turns.
The Boolean records this distinction for the source's no-code turn control. -/
def PairMutableProvenance (D : Exec.Deriv) (sevm : Sevm) (token : B256)
    (entered : Bool) (turns : List MutableTurn) : Prop :=
  (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns →
    LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
  ((entered = false ∧ turns = [] ∧ sevm.benvStat.rules.isPrecomp token.toAdr) ∨
    (entered = true ∧ ∃ (child : Evm) (raw : Execution)
      (childRun : Exec child.pc child.sta child.dyna raw)
      (committed : Execution.commits raw = true),
      (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
      turns.map MutableTurn.event = Exec.targetLogEventsFrom sevm.currentTarget [] 0 childRun committed))

/-- A transfer result retains the actual complete reply and frame-entry bit. -/
def burnTransferResult (out : Bytes) (entered : Bool) : ExternalResult :=
  { success := true, returndata := out, codeExists := entered, recoveryOutput := 0 }

def burnTransferRequest0 (priced : BurnPriced) : Request :=
  requestFor .burnTransfer0 priced.observed.locals.token0
    (.transfer priced.observed.locals.recipient priced.amount0)

def burnTransferRequest1 (priced : BurnPriced) : Request :=
  requestFor .burnTransfer1 priced.observed.locals.token1
    (.transfer priced.observed.locals.recipient priced.amount1)

theorem burn_resumeTransfer0 {frame : Frame} {priced : BurnPriced}
    {out : Bytes} {entered : Bool} (accepted : SkimTransferAccepted out) :
    resumeSegment frame (burnTransferRequest0 priced) (.burnTransfer0 priced)
        (burnTransferResult out entered) =
      .suspended (frame.beginResume (burnTransferRequest0 priced))
        (burnTransferRequest1 priced) (.burnTransfer1 priced) := by
  have decoded : decodeExternal (burnTransferRequest0 priced) (burnTransferResult out entered) =
      .ok .unit := skim_decodeTransfer rfl rfl rfl accepted
  simp only [resumeSegment, decoded, Frame.suspend, burnTransferRequest1]

theorem burn_resumeTransfer1 {frame : Frame} {priced : BurnPriced}
    {out : Bytes} {entered : Bool} (accepted : SkimTransferAccepted out) :
    resumeSegment frame (burnTransferRequest1 priced) (.burnTransfer1 priced)
        (burnTransferResult out entered) =
      .suspended (frame.beginResume (burnTransferRequest1 priced))
        (burnFinalRequest0 (frame.beginResume (burnTransferRequest1 priced)) priced)
        (.burnFinalBalance0 priced) := by
  have decoded : decodeExternal (burnTransferRequest1 priced) (burnTransferResult out entered) =
      .ok .unit := skim_decodeTransfer rfl rfl rfl accepted
  simp only [resumeSegment, decoded, Frame.suspend, burnFinalRequest0]

/-- The pre-transfer frame shares the cached final locals and initial pointer,
with the Pair lock still held and the transfer decoder's zero sentinel intact. -/
structure BurnTransferCut (K : WriterKey → Prop) (frame : Frame) (priced : BurnPriced)
    (sevm : Sevm) (b : Devm) (w : BurnFinalWords) (M : Mem) : Prop
    extends BurnFinalCut K frame priced sevm b w 128 192 M where
  locked : frame.current.state.unlocked = 0
  nonstatic : frame.context.isStatic = false
  sentinel : memWord M 96 = 0

/-- One actual STATICCALL of a Burn frame: a call step of the same derivation
staged at `target`, its returned bytes, and the callee's answer to `input` in the
step's own world. -/
def BurnStaticAnswer (D : Exec.Deriv) (sevm : Sevm) (target : B256) (input out : Bytes) : Prop :=
  ∃ (w d : Devm) (gw : B256) (S : List B256) (M : Mem) (g : Nat),
    StepIn D sevm (St w (gw :: target :: S) M g) (.exec .staticcall) d ∧
    d.returnData = out ∧ StaticAnswered sevm w target.toAdr input out

/-- The static Pair turns of one actual STATICCALL, stated without the model
frame: each is a static Pair frame running the selector it decodes, and the queue
is empty at an enabled precompile or exactly the retained static Pair turns of the
committed child. -/
def PairViewOrigin (D : Exec.Deriv) (sevm : Sevm) (t : B256) (views : List StaticViewTurn) :
    Prop :=
  (∀ picked ∈ views, Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
    picked.1.frame.sevm.currentTarget = sevm.currentTarget ∧
    picked.1.frame.sevm.isStatic = true) ∧
  ViewQueueOrigin D sevm sevm.currentTarget t.toAdr views

/-- One actual mutable `transfer` CALL of a Burn frame: a call step of the same
derivation staged at `token` with zero value, its exact 68-byte ABI input, and its
returned bytes. -/
def BurnTransferAnswer (D : Exec.Deriv) (sevm : Sevm) (token payee amount : B256) (reply : Bytes) :
    Prop :=
  ∃ (w d : Devm) (gw ii oi os : B256) (S : List B256) (M : Mem) (g : Nat),
    StepIn D sevm (St w (gw :: token :: 0 :: ii :: 68 :: oi :: os :: S) M g) (.exec .call) d ∧
    (M.read ii.toNat 68).1 = abiSelectorBytes 0xa9059cbb ++ payee.toBytes ++ amount.toBytes ∧
    d.returnData = reply

/-- The source transcript of the two transfers and the two final balance queries. -/
def burnTransferTranscript (reply0 : Bytes) (entered0 : Bool) (turns0 : List MutableTurn)
    (reply1 : Bytes) (entered1 : Bool) (turns1 : List MutableTurn)
    (final0 : Bytes) (views0 : List StaticViewTurn) (final1 : Bytes)
    (views1 : List StaticViewTurn) : Transcript :=
  .next (burnTransferResult reply0 entered0) (mutableTranscript turns0 .done)
    (.next (burnTransferResult reply1 entered1) (mutableTranscript turns1 .done)
      (.next (feeObservedResult final0) (staticViewTranscript views0 .done)
        (.next (feeObservedResult final1) (staticViewTranscript views1 .done) .done)))

end Blanc.Lift.UniswapV2Pair
