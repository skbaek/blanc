import Blanc.Lift.UniswapV2Pair.SwapFrontTurns
import Blanc.Lift.UniswapV2Pair.SwapCut

/-! The swap front half, pc 0 to the post-callback join `t_09c3_c5`: every successful raw swap
run reaches the join with the back half's cut predicate `SwapCut`, and the typed source swap
exactly consumes the actual optional transfer and callback turns up to its `balance0`
suspension. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The eleven body words at the join, as the source names them. -/
def swapCutWords (sevm : Sevm) (st : State) : SwapCutWords :=
  { token1 := st.token1.toB256, token0 := st.token0.toB256,
    reserve1 := Nat.toB256 st.reserve1.val, reserve0 := Nat.toB256 st.reserve0.val,
    dataLength := swapDataLength sevm, dataOffset := swapDataStart sevm,
    recipient := swapRecipientWord sevm, amount1Out := swapAmount1Out sevm,
    amount0Out := swapAmount0Out sevm }

/-- The source swap locals of a decoded swap at the entry state. -/
def swapFrontLocals (sevm : Sevm) (st : State) : SwapLocals :=
  swapSourceLocals st (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm) (swapData sevm)

theorem swapRecipientWord_eq (sevm : Sevm) :
    swapRecipientWord sevm = (swapRecipient sevm).toB256 := by
  rw [swapRecipientWord, B256.and_comm]
  exact ff20_and_word _

/-- **Swap front half.** A successful raw swap run of the original bytes, under trace-local
HASH-T (a separated universe `U ⊇ K` admitting every raw Pair frame) and the CALL reply bound,
reaches the post-callback join with `SwapCut` for the source swap's `balance0` suspension, and
the typed swap exactly consumes the actual transfer/callback turns up to it. In all six
successful shapes each optional call is either skipped with its source guard false, or is one
actual CALL step of this derivation with its actual reply and retained turns. The front also
leaves the installed Pair code unchanged, so the back half's code premise holds at the cut
world. Each taken transfer's reply bound is derived from its own actual 68-byte CALL
(`swapTransferCall_replyShort`). -/
theorem swap_bytecode_front_cut_code {K U : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (good : ∀ F ∈ Exec.rawFrameRoots (⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ : Exec.Deriv).exc,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let ctx := writerContext sevm invocation
    let locals := swapFrontLocals sevm current.state
    let w := swapCutWords sevm current.state
    let S := swapCutStack w 0x257 [0x022c0d9f]
    sevm.value = 0 ∧ sevm.isStatic = false ∧
    ∃ (frame : Frame) (T0 T1 TC : Transcript → Transcript) (R : List ChildReturn)
      (turns0 turns1 turnsC : List MutableTurn) (K' : WriterKey → Prop)
      (b1 b2 d : Devm) (M1 M2 : Mem) (p1 p : B256)
      (n : Nat) (M : Mem) (gas : Nat) (calleePost : Devm),
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
      SwapFrontReaches (startTyped current ctx (swapDecodedEntry sevm)) ((T0 ∘ T1) ∘ TC) R
        (.suspended frame (requestFor .swapBalance0 locals.token0 (.balanceOf ctx.pair))
          (.swapBalance0 locals)) ∧
      frame.checkpoint = current ∧ frame.context = ctx ∧
      (∀ k, K' k → U k) ∧ SwapCut K' frame locals sevm d w p n M ∧
      (∃ (added : List PendingLog) (L : List Log), frame.current.logs = current.logs ++ added ∧
        d.logs = b.logs ++ L ∧
        added.map (PendingLog.rawWith (lockedOwnedRaw sevm.currentTarget)) = L.map some) ∧
      (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns0 ++ turns1 ++ turnsC →
        LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
      SFunc.RunP (StepIn root) cert.prog sevm (St d S M gas)
        t_09c3_c5 (.returned calleePost) ∧
      SFunc.RunCutP (StepIn root) cert.prog sevm [] calleePost t_0257_c99 (.done (.halted post)) ∧
      d.getCode sevm.currentTarget = b.getCode sevm.currentTarget := by
  intro root ctx locals w S
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, _, guards, calleeGas, calleePost, body, tail⟩ := swapPc0_inv selector derived
  obtain ⟨unlocked, nonstatic, output, lt0, lt1, ne0, ne1, g1, run1⟩ :=
    swapBody_prefix_inv fork rep (SFunc.runP_iff_runCutP_nil.mp body)
  unfold swapLocalsStack swapBodyStack at run1
  obtain ⟨b1, M1, p1, b2, M2, p2, n2, g2, opt0, opt1, ptr2, lower2, upper2, run2⟩ :=
    swapTransfers_inv fork getterInitMemory_ptr run1
  have shortLen : (swapDataLength sevm).toNat ≤ 2 ^ 32 := guards.length
  obtain ⟨b3, M3, m3, g3, optC, ptr3, run3⟩ := swapCallback_inv fork ptr2 lower2 upper2 shortLen run2
  -- the typed front
  let st := current.state
  let entry := swapDecodedEntry sevm
  let locked := swapLockedFrame current ctx entry
  have env : SwapCallEnv U root sevm sem :=
    ⟨lockedPairSupply inj apart sem image sevm.currentTarget, image, fork, good⟩
  have pairEq : ctx.pair = sevm.currentTarget := rfl
  have time : ctx.timestamp = sevm.benvStat.time := rfl
  have ctxStatic : ctx.isStatic = false := nonstatic
  have inv0 : SwapFrontState U sevm.currentTarget ctx current b locked (swapPrefixWorld sevm b) := by
    exact swap_prefix_source_invariant rep sub
  obtain ⟨F0, T0, R0, turns0, reach0, inv1, auth0, shape0⟩ :=
    swapTransfer0_phase (locals := locals) env installed pairEq time ctxStatic inv0 opt0
  obtain ⟨F1, T1, R1, turns1, reach1, inv2, auth1, shape1⟩ :=
    swapTransfer1_phase (locals := locals) env installed pairEq time ctxStatic inv1 opt1
  obtain ⟨F2, TC, RC, turnsC, reachC, inv3, authC, shapeC⟩ :=
    swapCallback_phase (locals := locals) env installed pairEq time ctxStatic inv2 rfl optC
  have start := swap_startTyped (current := current) (ctx := ctx) (data := swapData sevm) value
    nonstatic unlocked (output.imp swap_pos_of_ne swap_pos_of_ne) lt0 lt1 ne0 ne1
  have reach : SwapFrontReaches (startTyped current ctx entry) ((T0 ∘ T1) ∘ TC) ((R0 ++ R1) ++ RC)
      (.suspended F2 (requestFor .swapBalance0 locals.token0 (.balanceOf ctx.pair))
        (.swapBalance0 locals)) := by
    have start' : startTyped current ctx entry = _ := start
    rw [start']
    exact (reach0.trans reach1).trans reachC
  obtain ⟨K', sub', wrep', locked'⟩ := inv3.rep
  refine ⟨value, nonstatic, F2, T0, T1, TC, _, turns0, turns1, turnsC, K', b1, b2, b3, M1, M2, p1, p2,
    m3, M3, g3, calleePost, opt0, opt1, optC, shape0, shape1, shapeC, reach, inv3.checkpoint, inv3.context, sub', ⟨ptr3, lower2, by omega, ?_, wrep', locked', (by rw [inv3.context]; rfl), (by rw [inv3.context]; rfl),
      (by rw [inv3.context]; rfl), rfl, rfl, rfl, rfl, swapRecipientWord_eq sevm, rfl, rfl, lt0, lt1⟩, inv3.logs, ?_,
    SFunc.runP_iff_runCutP_nil.mpr run3, tail, inv3.code⟩
  · rw [inv3.output, freshOutput]
  · intro located entry nested member
    rcases List.mem_append.mp member with left | right
    · rcases List.mem_append.mp left with l0 | l1
      · exact auth0 located entry nested l0
      · exact auth1 located entry nested l1
    · exact authC located entry nested right

end Blanc.Lift.UniswapV2Pair
