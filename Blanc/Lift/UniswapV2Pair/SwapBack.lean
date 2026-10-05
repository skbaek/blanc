import Blanc.Lift.UniswapV2Pair.SwapUpdateWalk
import Blanc.Lift.UniswapV2Pair.MintSource

/-! The swap body's back half, from the post-callback cut `t_09c3_c5` to the
body's return: both authentic balance queries in the same derivation, input
inference, the SafeMath `K` check, `_update`, the `Swap` log and the unlock. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The balance word a successful query decodes. -/
def swapBalanceWord (out : Bytes) : B256 := Bytes.toB256 (out.take 32)

/-- Everything the successful raw back half exposes, over the cut words. -/
def SwapBackRaw (D : Exec.Deriv) (sevm : Sevm) (d : Devm) (M : Mem) (p : B256)
    (w : SwapCutWords) (ρ : B256) (R : List B256) (o : Outcome) : Prop :=
  let R0 := w.reserve1 :: w.reserve0 :: w.dataLength :: w.dataOffset :: w.recipient ::
    w.amount1Out :: w.amount0Out :: ρ :: R
  ∃ (d0 d1 : Devm) (out0 out1 : Bytes),
    SwapBalanceCall D sevm d M p w.token0 (w.token1 :: w.token0 :: 0 :: 0 :: R0) d0 out0 ∧
    SwapBalanceCall D sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
      (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: R0) d1 out1 ∧
    let bal0 := swapBalanceWord out0
    let bal1 := swapBalanceWord out1
    let in0 := swapInWord bal0 w.reserve0 w.amount0Out
    let in1 := swapInWord bal1 w.reserve1 w.amount1Out
    (0 < in0 ∨ 0 < in1) ∧ SwapKFacts bal0 bal1 in0 in1 w.reserve0 w.reserve1 ∧
    bal0.toNat < 2 ^ 112 ∧ bal1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
    ∃ M' G', o = .returned (St (afterSstore sevm
      ((updateWorld sevm d1 w.reserve0 w.reserve1 bal0 bal1).addLog
        (swapEventLog sevm in0 in1 w.amount0Out w.amount1Out w.recipient)) 12 1) R M' G')

/-- **Raw back-half inversion.** A successful run of the actual body from the
post-callback cut returns exactly through both queries, the checked pricing,
`_update`, the `Swap` log and the unlock. -/
theorem swapBack_raw_inv {D : Exec.Deriv} {sevm : Sevm} {d : Devm} {R : List B256}
    {M : Mem} {G n : Nat} {p ρ : B256} {w : SwapCutWords} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St d (swapCutStack w ρ R) M G) t_09c3_c5 (.done o)) :
    SwapBackRaw D sevm d M p w ρ R o := by
  obtain ⟨d0, out0, _, call0, run⟩ := swapFirstBalance_inv fork mem lower width run
  have long0 : 32 ≤ out0.length := by
    obtain ⟨_, _, _, _, _, long, _⟩ := call0
    exact long
  have reply0 := swapBalanceReply_ptr (pair := sevm.currentTarget) out0 mem lower width
  obtain ⟨d1, out1, _, call1, run⟩ :=
    swapSecondBalance_inv fork mem lower width long0 run
  have long1 : 32 ≤ out1.length := by
    obtain ⟨_, _, _, _, _, long, _⟩ := call1
    exact long
  have reply1 := swapBalanceReply_ptr (pair := sevm.currentTarget) out1 reply0 lower width
  have cover := swapRequestSize_cover reply0
  have plain := SFunc.Run.cut ((SFunc.runP_iff_runCutP_nil.mpr run).mono StepIn.toRun)
  obtain ⟨guard, _, plain⟩ := swapInputs_inv
    (swapBalanceReply_word reply0.wf out1 long1) (reply1.read_self cover) plain
  obtain ⟨k, _, plain⟩ := swapK_inv plain
  obtain ⟨bound0, bound1, static, M', G', returned⟩ := swapTail_inv fork reply1 lower width plain
  exact ⟨d0, d1, out0, out1, call0, call1, guard, k, bound0, bound1, static, M', G', returned⟩

/-- A bounded cached reserve survives the reserve mask. -/
theorem swapMask_reserve {r : Nat} (bound : r < 2 ^ 112) :
    reserveMask112 &&& Nat.toB256 r = Nat.toB256 r := by
  have small : (Nat.toB256 r).toNat < 2 ^ 112 := by
    rw [B256.toNat_toB256_of_lt (by omega)]
    exact bound
  rw [B256.and_comm, show reserveMask112 = (2 ^ 112 - 1).toB256 from rfl,
    PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) small]

/-- The actual ternary is the source's truncated input inference. -/
theorem swapInWord_source {balance amountOut : B256} {r : Nat} (bound : r < 2 ^ 112)
    (out : amountOut.toNat < r) :
    (swapInWord balance (Nat.toB256 r) amountOut).toNat = balance.toNat - (r - amountOut.toNat) := by
  have rNat : (Nat.toB256 r).toNat = r := B256.toNat_toB256_of_lt (by omega)
  have le : amountOut ≤ Nat.toB256 r := by
    rw [B256.le_iff_toNat_le_toNat, rNat]
    omega
  have diff : (Nat.toB256 r - amountOut).toNat = r - amountOut.toNat := by
    rw [B256.toNat_sub_eq_of_le _ _ le, rNat]
  unfold swapInWord
  rw [swapMask_reserve bound]
  by_cases above : Nat.toB256 r - amountOut < balance
  · rw [if_pos above, B256.toNat_sub_eq_of_le _ _ (B256.le_of_lt above), diff]
  · rw [if_neg above]
    rw [B256.lt_iff_toNat_lt_toNat, diff] at above
    change 0 = _
    omega

/-- The raw input guard and SafeMath `K` facts are exactly source acceptance of
`swapCheck`, at the source inputs `swapInputs` infers (fee as `1000·b − 3·in`). -/
theorem swapCheck_source {bal0 bal1 a0 a1 : B256} {r0 r1 : Nat}
    (bound0 : r0 < 2 ^ 112) (bound1 : r1 < 2 ^ 112)
    (out0 : a0.toNat < r0) (out1 : a1.toNat < r1)
    (guard : 0 < swapInWord bal0 (Nat.toB256 r0) a0 ∨ 0 < swapInWord bal1 (Nat.toB256 r1) a1)
    (k : SwapKFacts bal0 bal1 (swapInWord bal0 (Nat.toB256 r0) a0)
      (swapInWord bal1 (Nat.toB256 r1) a1) (Nat.toB256 r0) (Nat.toB256 r1)) :
    swapCheck bal0 bal1 (swapInputs bal0 bal1 a0 a1 r0 r1).1
      (swapInputs bal0 bal1 a0 a1 r0 r1).2 r0 r1 = .ok () := by
  have in0 := swapInWord_source (balance := bal0) bound0 out0
  have in1 := swapInWord_source (balance := bal1) bound1 out1
  generalize swapInWord bal0 (Nat.toB256 r0) a0 = x0 at in0 guard k
  generalize swapInWord bal1 (Nat.toB256 r1) a1 = x1 at in1 guard k
  obtain ⟨m0, b0, c0, m1, b1, c1, adj, kk⟩ := k
  unfold B256.Nofm at m0 b0 m1 b1 adj
  rw [show (3 : B256).toNat = 3 from rfl] at m0 m1
  rw [show (1000 : B256).toNat = 1000 from rfl] at b0 b1
  have e3 : ∀ x : B256, x.toNat * 3 < 2 ^ 256 → (x * 3).toNat = x.toNat * 3 := fun x h =>
    B256.toNat_mul_eq_of_nofm h
  have e1000 : ∀ x : B256, x.toNat * 1000 < 2 ^ 256 → (x * 1000).toNat = x.toNat * 1000 :=
    fun x h => B256.toNat_mul_eq_of_nofm h
  rw [B256.le_iff_toNat_le_toNat, e3 x0 m0, e1000 bal0 b0] at c0
  rw [B256.le_iff_toNat_le_toNat, e3 x1 m1, e1000 bal1 b1] at c1
  have s0 : (bal0 * 1000 - x0 * 3).toNat = bal0.toNat * 1000 - x0.toNat * 3 := by
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by
      rw [e3 x0 m0, e1000 bal0 b0]; exact c0)), e3 x0 m0, e1000 bal0 b0]
  have s1 : (bal1 * 1000 - x1 * 3).toNat = bal1.toNat * 1000 - x1.toNat * 3 := by
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by
      rw [e3 x1 m1, e1000 bal1 b1]; exact c1)), e3 x1 m1, e1000 bal1 b1]
  rw [s0, s1] at adj
  have h6 : (1000000 : B256).toNat = 1000000 := by decide
  have rNat0 : (Nat.toB256 r0).toNat = r0 := B256.toNat_toB256_of_lt (by omega)
  have rNat1 : (Nat.toB256 r1).toNat = r1 := B256.toNat_toB256_of_lt (by omega)
  have prodBound : r0 * r1 < 2 ^ 224 := by
    have := Nat.mul_lt_mul'' bound0 bound1
    simpa only [show 2 ^ 112 * 2 ^ 112 = 2 ^ 224 from by decide] using this
  have resProd : ((reserveMask112 &&& Nat.toB256 r0) * (Nat.toB256 r1 &&& reserveMask112) *
      1000000).toNat = r0 * r1 * 1000000 := by
    rw [swapMask_reserve bound0, B256.and_comm, swapMask_reserve bound1]
    have first : (Nat.toB256 r0 * Nat.toB256 r1).toNat = r0 * r1 := by
      rw [B256.toNat_mul_eq_of_nofm (by unfold B256.Nofm; rw [rNat0, rNat1]; omega), rNat0, rNat1]
    have fits : r0 * r1 * 1000000 < 2 ^ 256 :=
      lt_trans (Nat.mul_lt_mul_of_pos_right prodBound (by decide : 0 < 1000000)) (by decide)
    rw [B256.toNat_mul_eq_of_nofm (by unfold B256.Nofm; rw [first, h6]; exact fits), first, h6]
  rw [B256.lt_iff_toNat_lt_toNat, resProd, B256.toNat_mul_eq_of_nofm (by unfold B256.Nofm; rw [s0, s1]; exact adj),
    s0, s1] at kk
  rw [B256.lt_iff_toNat_lt_toNat, B256.lt_iff_toNat_lt_toNat] at guard
  change 0 < x0.toNat ∨ 0 < x1.toNat at guard
  unfold swapInputs swapCheck
  dsimp only
  rw [← in0, ← in1]
  rw [if_pos guard, if_pos ⟨b0, m0⟩, if_pos c0, if_pos ⟨b1, m1⟩, if_pos c1, if_pos adj,
    if_pos (by rw [show (1000 : Nat) ^ 2 = 1000000 from rfl]; omega)]

/-- The source request for the first post-callback balance. -/
def swapRequest0 (frame : Frame) (locals : SwapLocals) : Request :=
  requestFor .swapBalance0 locals.token0 (.balanceOf frame.context.pair)

/-- The source request for the second post-callback balance. -/
def swapRequest1 (frame : Frame) (locals : SwapLocals) : Request :=
  requestFor .swapBalance1 locals.token1 (.balanceOf frame.context.pair)

/-- The source swap event at the inputs inferred from both observations. -/
def swapSourceEvent (frame : Frame) (locals : SwapLocals) (bal0 bal1 : B256) : Event :=
  .swap frame.context.sender
    (Nat.toB256 (swapInputs bal0 bal1 locals.amount0Out locals.amount1Out
      locals.reserves.reserve0.val locals.reserves.reserve1.val).1)
    (Nat.toB256 (swapInputs bal0 bal1 locals.amount0Out locals.amount1Out
      locals.reserves.reserve0.val locals.reserves.reserve1.val).2)
    locals.amount0Out locals.amount1Out locals.recipient

/-- The finished frame after the accepted update, the Swap event and the unlock. -/
def swapFinishedFrame (frame : Frame) (post : State) (event : Event) (oracle : OracleUpdate)
    (swap : Event) : Frame :=
  (((frame.withUpdate post event oracle).withEvents post [swap]).withEvents
    { post with unlocked := 1 } [])

/-- The first full token reply suspends for the second, caching `balance0`. -/
theorem swap_resumeBalance0 {frame : Frame} {locals : SwapLocals} {out : Bytes}
    (long : 32 ≤ out.length) :
    resumeSegment frame (swapRequest0 frame locals) (.swapBalance0 locals) (feeObservedResult out) =
      .suspended (frame.beginResume (swapRequest0 frame locals))
        (swapRequest1 (frame.beginResume (swapRequest0 frame locals)) locals)
        (.swapBalance1 locals (swapBalanceWord out)) := by
  simp only [resumeSegment, decodeExternal, swapRequest0, swapRequest1, requestFor,
    feeObservedResult, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
  simp only [long, ite_true]
  rfl

/-- The second reply, the accepted pricing check and the accepted update finish
the swap frame with no return bytes. -/
theorem swap_resumeBalance1 {frame : Frame} {locals : SwapLocals} {bal0 : B256} {out : Bytes}
    {post : State} {event : Event} {oracle : OracleUpdate}
    (long : 32 ≤ out.length)
    (check : swapCheck bal0 (swapBalanceWord out)
      (swapInputs bal0 (swapBalanceWord out) locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).1
      (swapInputs bal0 (swapBalanceWord out) locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).2
      locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok ())
    (accepted : frame.current.state.update frame.context bal0 (swapBalanceWord out)
      locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok (post, event, oracle)) :
    resumeSegment frame (swapRequest1 frame locals) (.swapBalance1 locals bal0)
        (feeObservedResult out) =
      .finished (swapFinishedFrame (frame.beginResume (swapRequest1 frame locals)) post event oracle
        (swapSourceEvent frame locals bal0 (swapBalanceWord out))) [] := by
  simp only [resumeSegment, decodeExternal, swapRequest1, requestFor,
    feeObservedResult, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, ite_true]
  simp only [long, ite_true]
  rw [show Bytes.toB256 (out.take 32) = swapBalanceWord out from rfl, check]
  dsimp only
  unfold Frame.finishUpdated
  have accepted' : (frame.beginResume (swapRequest1 frame locals)).current.state.update
      (frame.beginResume (swapRequest1 frame locals)).context bal0 (swapBalanceWord out)
      locals.reserves.reserve0.val locals.reserves.reserve1.val = .ok (post, event, oracle) :=
    accepted
  unfold swapRequest1 requestFor at accepted'
  rw [accepted']
  rfl

end Blanc.Lift.UniswapV2Pair
