import Blanc.Lift.UniswapV2Pair.SwapFrontCanonical
import Blanc.Lift.UniswapV2Pair.SwapBackTurns
import Blanc.Lift.UniswapV2Pair.SkimCanonical

/-!
# Canonical swap frame interfaces

Trace-local writer rows, event images and per-call source authorization used by the positional
canonical swap route. The root-determined HASH-T universe extends the incoming tracked rows by
`swapTraceKeys root`; mutable children and static views are admitted on their actual call positions
by the positional front and back modules.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- HASH-T rows of a swap run: the decoded rows of every actually entered Pair frame. Swap
writes no LP row of its own, so these are exactly skim's root-determined rows. -/
def swapTraceKeys (root : Exec.Deriv) : List WriterKey :=
  skimTraceKeys root

/-- Raw images of the Pair-owned events of a swap frame: the nested lock-free writers'
`Transfer`/`Approval`, and the frame's own `Sync` and `Swap`. -/
def swapOwnedRaw (pair : Adr) : Event → Option Log
  | .transfer source recipient value => some (transferRawLog pair source recipient value)
  | .approval owner spender value => some (approvalRawLog pair owner spender value)
  | .sync reserve0 reserve1 => some (swapSyncLog pair reserve0.toB256 reserve1.toB256)
  | .swap sender in0 in1 out0 out1 recipient =>
      some ⟨pair, [swapEventTopic, sender.toB256, recipient.toB256],
        in0.toBytes ++ in1.toBytes ++ out0.toBytes ++ out1.toBytes⟩
  | _ => none

theorem swapOwnedRaw_of_locked {pair : Adr} {e : Event} {l : Log}
    (image : lockedOwnedRaw pair e = some l) : swapOwnedRaw pair e = some l := by
  cases e with
  | transfer source recipient value => exact image
  | approval owner spender value => exact image
  | sync reserve0 reserve1 => cases image
  | mint sender amount0 amount1 => cases image
  | burn sender amount0 amount1 recipient => cases image
  | swap sender in0 in1 out0 out1 recipient => cases image

theorem swap_rawWith_images {added : List PendingLog} {L : List Log} {pair : Adr}
    (images : added.map (PendingLog.rawWith (lockedOwnedRaw pair)) = L.map some) :
    added.map (PendingLog.rawWith (swapOwnedRaw pair)) = L.map some := by
  induction added generalizing L with
  | nil => exact images
  | cons log rest ih =>
    cases L with
    | nil => cases images
    | cons raw tail =>
      rw [List.map_cons, List.map_cons] at images
      obtain ⟨head, tailEq⟩ := List.cons.inj images
      rw [List.map_cons, List.map_cons, ih tailEq]
      cases log with
      | owned origin event => exact congrArg (· :: List.map some tail) (swapOwnedRaw_of_locked head)
      | foreign origin emitter topics data => exact congrArg (· :: List.map some tail) head

/-- The wrapper's `STOP` at `0x0257` keeps the returned body world. -/
theorem swap_stop_inv {D : Exec.Deriv} {sevm : Sevm} {x y : Devm} {R : List B256} {M : Mem}
    {G : Nat}
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm [] (St x R M G) t_0257_c99 (.done (.halted y))) :
    ∃ G', y = St x R M G' := by
  unfold t_0257_c99 at run
  obtain ⟨G', run⟩ := ric_destP run
  cases run with
  | last hr => exact ⟨G', (Except.ok.inj hr).symm⟩

/-- What the canonical swap frame derives from one successful raw swap run `run`, with `Own`
a predicate on the post-callback world `d`: the actual optional transfer and callback steps
in their six shapes, the two actual post-callback balance STATICCALLs (at the world the
callback left), exact typed consumption of the whole transcript, the final frame, the Pair
storage representation, the uint112 bound of both observed balances, the exact raw log list
and the typed pending logs mapping onto it, empty output, the nested Pair turns'
authentication and the per-call static-view provenance. -/
def SwapCanonicalBody (Own : Devm → Prop) (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) : Prop :=
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  let ctx := writerContext sevm invocation
  let locals := swapFrontLocals sevm current.state
  let w := swapCutWords sevm current.state
  let S := swapCutStack w 0x257 [0x022c0d9f]
  sevm.value = 0 ∧ sevm.isStatic = false ∧
  ∃ (frame : Frame) (T0 T1 TC : Transcript → Transcript) (turns0 turns1 turnsC : List MutableTurn)
    (b1 b2 d d0 d1 : Devm) (M1 M2 M : Mem) (p1 p : B256) (out0 out1 : Bytes)
    (views0 views1 : List StaticViewTurn) (final : Frame) (rets : List ChildReturn)
    (K' : WriterKey → Prop) (added : List PendingLog),
    SwapTransferOpt root sevm (swapPrefixWorld sevm b) S getterInitMemory 128
      (swapAmount0Out sevm) (swapRecipientWord sevm) current.state.token0.toB256 0x8d0 b1 M1 p1 ∧
    SwapTransferOpt root sevm b1 S M1 p1
      (swapAmount1Out sevm) (swapRecipientWord sevm) current.state.token1.toB256 0x8e1 b2 M2 p ∧
    SwapCallbackOpt root sevm b2 S M2 p (swapRecipientWord sevm) (swapAmount0Out sevm)
      (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) d M ∧
    ((swapAmount0Out sevm = 0 ∧ T0 = id) ∨ (swapAmount0Out sevm ≠ 0 ∧
      T0 = (fun tail => .next (swapTransferReply b1.returnData) (mutableTranscript turns0 .done) tail) ∧
      SwapCallProvenance sevm.currentTarget root sevm (swapPrefixWorld sevm b) b1 turns0)) ∧
    ((swapAmount1Out sevm = 0 ∧ T1 = id) ∨ (swapAmount1Out sevm ≠ 0 ∧
      T1 = (fun tail => .next (swapTransferReply b2.returnData) (mutableTranscript turns1 .done) tail) ∧
      SwapCallProvenance sevm.currentTarget root sevm b1 b2 turns1)) ∧
    ((swapDataLength sevm = 0 ∧ TC = id) ∨ (swapDataLength sevm ≠ 0 ∧
      TC = (fun tail => .next (swapCallbackReply d.returnData) (mutableTranscript turnsC .done) tail) ∧
      SwapCallProvenance sevm.currentTarget root sevm b2 d turnsC)) ∧
    SwapBalanceCall root sevm d M p w.token0
      (w.token1 :: w.token0 :: 0 :: 0 :: w.reserve1 :: w.reserve0 :: w.dataLength ::
        w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 :: [0x022c0d9f]) d0 out0 ∧
    SwapBalanceCall root sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
      (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: w.reserve1 :: w.reserve0 ::
        w.dataLength :: w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 ::
        [0x022c0d9f]) d1 out1 ∧
    ExactConsumes (startTyped current ctx (swapDecodedEntry sevm))
      (((T0 ∘ T1) ∘ TC)
        (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
          (.next (feeObservedResult out1) (staticViewTranscript views1 .done) .done)))
      { status := .success [], frame := final, remaining := .done, childReturns := rets } ∧
    frame.checkpoint = current ∧ frame.context = ctx ∧
    final.checkpoint = current ∧ final.context = ctx ∧ final.current.state.unlocked = 1 ∧
    (∀ k, K' k → WriterExtend K (swapTraceKeys root) k) ∧
    WriterRep K' (post.getStor sevm.currentTarget) final.current.state ∧
    (swapBalanceWord out0).toNat < 2 ^ 112 ∧ (swapBalanceWord out1).toNat < 2 ^ 112 ∧
    final.current.logs = current.logs ++ added ∧
    (∃ L : List Log, d.logs = b.logs ++ L ∧
      post.logs = b.logs ++ L ++
        [swapSyncLog sevm.currentTarget (swapBalanceWord out0) (swapBalanceWord out1),
         swapEventLog sevm
          (swapInWord (swapBalanceWord out0) w.reserve0 w.amount0Out)
          (swapInWord (swapBalanceWord out1) w.reserve1 w.amount1Out)
          w.amount0Out w.amount1Out w.recipient] ∧
      added.map (PendingLog.rawWith (swapOwnedRaw sevm.currentTarget)) =
        (L ++ [swapSyncLog sevm.currentTarget (swapBalanceWord out0) (swapBalanceWord out1),
         swapEventLog sevm
          (swapInWord (swapBalanceWord out0) w.reserve0 w.amount0Out)
          (swapInWord (swapBalanceWord out1) w.reserve1 w.amount1Out)
          w.amount0Out w.amount1Out w.recipient]).map some) ∧
    post.output = [] ∧
    (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns0 ++ turns1 ++ turnsC →
      LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
    PairViewProvenance root sevm frame (swapTokenWord w.token0) views0 ∧
    PairViewProvenance root sevm (frame.beginResume (swapRequest0 frame locals))
      (swapTokenWord w.token1) views1 ∧
    Own d

/-- The sync image of the typed `Sync` at both observed balances. -/
theorem swap_sync_image {pair : Adr} {bal0 bal1 : B256} (bound0 : bal0.toNat < 2 ^ 112)
    (bound1 : bal1.toNat < 2 ^ 112) :
    swapOwnedRaw pair (.sync bal0.toNat bal1.toNat) = some (swapSyncLog pair bal0 bal1) := by
  have back0 : Nat.toB256 bal0.toNat = bal0 :=
    B256.toNat_inj _ _ (B256.toNat_toB256_of_lt (by omega))
  have back1 : Nat.toB256 bal1.toNat = bal1 :=
    B256.toNat_inj _ _ (B256.toNat_toB256_of_lt (by omega))
  change some (swapSyncLog pair (Nat.toB256 bal0.toNat) (Nat.toB256 bal1.toNat)) = _
  rw [back0, back1]

/-- The source input inference at the cut words is the actual ternary word. -/
theorem swap_input_word {bal amountOut : B256} {r : Nat} (bound : r < 2 ^ 112)
    (out : amountOut.toNat < r) :
    Nat.toB256 (bal.toNat - (r - amountOut.toNat)) = swapInWord bal (Nat.toB256 r) amountOut := by
  apply B256.toNat_inj
  have small := B256.toNat_lt bal
  rw [swapInWord_source bound out, B256.toNat_toB256_of_lt (by omega)]

end Blanc.Lift.UniswapV2Pair
