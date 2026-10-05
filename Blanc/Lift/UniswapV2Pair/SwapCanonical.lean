import Blanc.Lift.UniswapV2Pair.SwapFrontCanonical
import Blanc.Lift.UniswapV2Pair.SwapBackTurns
import Blanc.Lift.UniswapV2Pair.SkimCanonical

/-!
# Canonical swap frame

Every successful raw swap run at the Pair code (selector `0x022c0d9f`) consumes the typed
source swap over the actual optional transfers, the optional callback and the two
post-callback `balanceOf(pair)` observations, in all six successful transcript shapes. The
front half (`swap_bytecode_front_cut_code`) reaches the post-callback join with `SwapCut`; the
back half (`swapBack_exact_consumes_bounds`) consumes the cut. The trace-local HASH-T universe
is `WriterExtend K (swapTraceKeys root)`, a function of the tracked rows and the root execution
alone; the front's universe parameter, the lock-free supply admission and the back's static-view
admission are discharged from it here.
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
    SwapViewProvenance root sevm frame (swapTokenWord w.token0) views0 ∧
    SwapViewProvenance root sevm (frame.beginResume (swapRequest0 frame locals))
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

/-- The swap image of the typed `Swap` event at the cut. -/
theorem swap_event_image {K : WriterKey → Prop} {frame : Frame} {locals : SwapLocals}
    {sevm : Sevm} {d : Devm} {w : SwapCutWords} {p : B256} {n : Nat} {M : Mem} {bal0 bal1 : B256}
    (cut : SwapCut K frame locals sevm d w p n M)
    (recipient : swapTokenWord w.recipient = locals.recipient.toB256) :
    swapOwnedRaw sevm.currentTarget (swapSourceEvent frame locals bal0 bal1) =
      some (swapEventLog sevm (swapInWord bal0 w.reserve0 w.amount0Out)
        (swapInWord bal1 w.reserve1 w.amount1Out) w.amount0Out w.amount1Out w.recipient) := by
  simp only [swapSourceEvent, swapOwnedRaw, swapEventLog, swapInputs]
  rw [cut.reserve0, cut.reserve1, cut.amount0Out, cut.amount1Out,
    ← swap_input_word locals.reserves.reserve0.isLt cut.out0,
    ← swap_input_word locals.reserves.reserve1.isLt cut.out1, cut.sender, recipient]

/-- **Canonical swap frame, with foreign storage.** Every successful raw swap run of the
original bytes, under trace-local HASH-T over `WriterExtend K (swapTraceKeys root)` and the
CALL reply bound `short`, satisfies `SwapCanonicalBody` with the foreign-storage silence of the
post-callback tail: every account other than the Pair keeps, at the end, the storage the
callback (or the last taken transfer) left; and the lock prefix before the first external call
touches no foreign account. Between those points foreign storage changes only inside the
actual transfer/callback CALL steps the body names.
CROSS-HOST: conditional on `SwapCallReplyShort`. -/
theorem swap_bytecode_exact_consumes_own {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (short : SwapCallReplyShort ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm) :
    (∀ a, a ≠ sevm.currentTarget → (swapPrefixWorld sevm b).getStor a = b.getStor a) ∧
    SwapCanonicalBody (fun d => ∀ a, a ≠ sevm.currentTarget → post.getStor a = d.getStor a)
      K current invocation run := by
  refine ⟨fun a foreign => ?_, ?_⟩
  · unfold swapPrefixWorld mintLockedWorld
    rw [afterSload_getStor, afterSload_getStor, afterSload_getStor,
      afterSstore_getStor_ne _ _ _ _ _ (Ne.symm foreign), afterSload_getStor]
  unfold SwapCanonicalBody
  intro root ctx locals w S
  let U := WriterExtend K (swapTraceKeys root)
  have sub : ∀ k, K k → U k := fun k tracked => Or.inl tracked
  have staticGood : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = sevm.currentTarget → ∀ k ∈ staticViewDecodedKeys F.sevm, U k :=
    fun F member target k touched => Or.inr ((skimTraceKeys_contains member target).2 k touched)
  have lockedGood : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F := by
    intro F member target F' inner same k touched
    have deep := Exec.rawFrameRoots_trans member inner
    rcases List.mem_append.mp touched with pairKey | viewKey
    · exact Or.inr ((skimTraceKeys_contains deep (same.trans target)).1 k pairKey)
    · exact Or.inr ((skimTraceKeys_contains deep (same.trans target)).2 k viewKey)
  obtain ⟨value, nonstatic, frame, T0, T1, TC, R, turns0, turns1, turnsC, K', b1, b2, d, M1, M2, p1,
    p, n, M, gas, calleePost, opt0, opt1, optC, shape0, shape1, shapeC, reach, checkpoint, context,
    sub', cut, ⟨added, L, frameLogs, cutLogs, images⟩, auth, body, tail, codeD⟩ :=
    swap_bytecode_front_cut_code invocation rep sem image installed freshOutput codeEq fork selector
      run hashTInj hashTApart sub lockedGood short
  have installedD : some (d.getCode sevm.currentTarget).toList = sem.image := by
    rw [codeD]
    exact installed
  have pairEq : frame.context.pair = sevm.currentTarget := by
    rw [context]
    rfl
  obtain ⟨out0, out1, views0, views1, final, rets, post', M', G', d0, d1, call0, call1, _, _,
      recipient, consumed, prov0, prov1, returned, finalCheckpoint, finalContext, unlocked, wrep,
      foreign, ⟨origin, finalLogs⟩, postLogs, postOutput, bound0, bound1⟩ :=
    swapBack_exact_consumes_bounds hashTInj hashTApart sub' sem image installedD fork cut
      (fun F member target => staticGood F member (target.trans pairEq))
      (SFunc.runP_iff_runCutP_nil.mp body)
  obtain rfl := Outcome.returned.inj returned
  obtain ⟨G'', postEq⟩ := swap_stop_inv tail
  subst postEq
  have request0 : swapRequest0 frame locals =
      requestFor .swapBalance0 locals.token0 (.balanceOf ctx.pair) := by
    unfold swapRequest0
    rw [context]
  rw [request0] at consumed
  refine ⟨value, nonstatic, frame, T0, T1, TC, turns0, turns1, turnsC, b1, b2, d, d0, d1, M1, M2, M,
    p1, p, out0, out1, views0, views1, final, R ++ rets, K',
    added ++ [.owned origin (.sync (swapBalanceWord out0).toNat (swapBalanceWord out1).toNat),
      .owned origin (swapSourceEvent frame locals (swapBalanceWord out0) (swapBalanceWord out1))],
    opt0, opt1, optC, shape0, shape1, shapeC, call0, call1, reach _ _ consumed, checkpoint, context,
    finalCheckpoint.trans checkpoint, finalContext.trans context, unlocked, sub', wrep, bound0,
    bound1, ?_, ⟨L, cutLogs, ?_, ?_⟩, postOutput, auth, prov0, ?_, foreign⟩
  · rw [finalLogs, frameLogs, List.append_assoc]
  · change post'.logs = _
    rw [postLogs, cutLogs]
  · rw [List.map_append, List.map_append, swap_rawWith_images images]
    simp only [List.map_cons, List.map_nil, PendingLog.rawWith, swap_sync_image bound0 bound1]
    exact congrArg (fun x => List.map some L ++ [some _, x])
      (swap_event_image (bal0 := swapBalanceWord out0) (bal1 := swapBalanceWord out1) cut recipient)
  · exact prov1

/-- **Canonical swap frame.** Every successful raw swap run of the original bytes consumes the
typed source swap over the actual transcript, in all six successful shapes (each optimistic
transfer present iff its amount is nonzero, the callback present iff the data is nonempty),
under trace-local HASH-T over `WriterExtend K (swapTraceKeys root)` and the explicit CALL reply
bound `short` (every actual CALL step of this derivation returns fewer than `2^160` bytes).
CROSS-HOST: conditional on `SwapCallReplyShort`. -/
theorem swap_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (short : SwapCallReplyShort ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm) :
    SwapCanonicalBody (fun _ => True) K current invocation run := by
  obtain ⟨_, value, nonstatic, frame, T0, T1, TC, turns0, turns1, turnsC, b1, b2, d, d0, d1, M1, M2,
    M, p1, p, out0, out1, views0, views1, final, rets, K', added, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, _⟩ :=
    swap_bytecode_exact_consumes_own invocation rep sem image installed freshOutput codeEq fork
      selector run hashTInj hashTApart short
  exact ⟨value, nonstatic, frame, T0, T1, TC, turns0, turns1, turnsC, b1, b2, d, d0, d1, M1, M2,
    M, p1, p, out0, out1, views0, views1, final, rets, K', added, c1, c2, c3, c4, c5, c6, c7, c8, c9,
    c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, trivial⟩

end Blanc.Lift.UniswapV2Pair
