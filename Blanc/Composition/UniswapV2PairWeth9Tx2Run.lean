import Blanc.Composition.UniswapV2PairWeth9Tx2Frame

/-!
# The swap frame of `tx2` runs

`tx2_frame_success`: from an entry machine satisfying `Tx2Frame` (the Pair's code and `W0`'s Pair
storage, WETH9's and `X`'s code and touched slots, cold keys, `X` and WETH9 not yet accessed, gas
`278020`), the Pair's frame for `swap(0, swapOut, trader, "")` succeeds with exactly `172795` gas
left, refund counter `2800`, the logs `Transfer`, `Sync`, `Swap`, and the world `tx2PostState`.

This is the frame-level swap liveness (`swapBody_exact` and the pc-zero schedule `swapPc0_exact`,
lifted by the certified `lift_exact`) with the callee records discharged by WETH9's code
(`swapWethLeg1_spec`, `swapWethRead1_spec`) and Token20's (`xBalanceCall_spec`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint

/-- **The back half's callee records for `tx2`.** -/
noncomputable def tx2Callee {sevm : Sevm} {b : Devm} (h : Tx2Frame sevm b) :
    SwapBackCalleeEnv sevm (tx2RW sevm b) (tx2RM sevm b) (tx2RM sevm b).size (tx2RP sevm b)
      (swapCutWords sevm tx2St) 0x257 [0x022c0d9f] (tx2G + 1) where
  d0 := tx2D0 sevm b
  d1 := (tx2Rd sevm b).1
  callGas0 := tx2Cg0
  callGas1 := (tx2Rd sevm b).2
  first := tx2_first h
  second := tx2_second h
  sentries := tx2_sentries h
  unlock := by
    unfold gCallStipend tx2G
    omega

/-- The Pair checker accepts `W0`'s Pair storage (kernel evaluation). -/
theorem w0_checkPair : UniswapV2Pair.checkPair w0PairRows w0PairStor w0Base = true := by
  decide +kernel

section Run

variable {sevm : Sevm} {b : Devm} (h : Tx2Frame sevm b)
include h

theorem tx2Callee_gas : (tx2Callee h).gas = tx2Gc := by
  unfold SwapBackCalleeEnv.gas
  change tx2Cg0 + 5 + swapRequestCharge (tx2RW sevm b) (tx2RM sevm b).size (tx2RP sevm b)
    (swapCutWords sevm tx2St).token0 72 + 16 = tx2Gc
  unfold tx2RW tx2RM tx2RP
  rw [tx2_cutWorld h, tx2_cutMem h, tx2_cutPtr h, tx2_cutWords h, tx2_reqCharge0 h (tx2D_view h)]
  rfl

theorem tx2Rd_eq1 : ∃ g k f r, (tx2Rd sevm b).1 = callChildPost (balParent sevm (tx2D0 sevm b)
    (readStack tx2W 0x257 [0x022c0d9f] (tx2D0 sevm b)) (readMem sevm tx2M tx2P (tx2D0 sevm b)) tx2P
    tx2W.token1 g k)
    (weth9BalancePost (initSevm (balMsg sevm (tx2D0 sevm b) (readStack tx2W 0x257 [0x022c0d9f]
      (tx2D0 sevm b)) (readMem sevm tx2M tx2P (tx2D0 sevm b)) tx2P tx2W.token1 g k f))
      (initDevm (balMsg sevm (tx2D0 sevm b) (readStack tx2W 0x257 [0x022c0d9f] (tx2D0 sevm b))
        (readMem sevm tx2M tx2P (tx2D0 sevm b)) tx2P tx2W.token1 g k f)) r) tx2P.toNat
    (32 : B256).toNat := by
  rw [tx2Rd_eq h]
  exact ⟨_, _, _, _, rfl⟩

theorem tx2Rd_view : DView b (tx2Rd sevm b).1 tx2K1 tx2A1 (tx2SD b) (4800 + 0 + 0)
    (([wethTransferLog] ++ []) ++ []) := by
  obtain ⟨_, _, _, _, e⟩ := tx2Rd_eq1 h
  rw [e]
  exact tx2_wAt_view h (tx2D0_view h) (tx2D0_returnData h) _ _ _ _

theorem tx2Rd_returnData : (tx2Rd sevm b).1.returnData = (999004 : B256).toBytes := by
  obtain ⟨_, _, _, _, e⟩ := tx2Rd_eq1 h
  rw [e]
  exact tx2_wAt_returnData h (tx2D0_view h) (tx2D0_returnData h) _ _ _ _

theorem tx2D1_returnData : (tx2D1 sevm b).returnData = (1 : B256).toBytes := rfl

theorem tx2_leg1Need : leg1Need sevm b tx2St b 0 tx2Gc = 232652 := by
  unfold leg1Need swapFrontCallbackGas
  rw [tx2_leg1Skel h, ite_eq_left (tx2_dataLength h.data), tx2_leg1Mem h, tx2_leg1Ptr h, tx2D1_returnData h]
  decide +kernel

theorem tx2_cg1 : (swapWethLeg1 sevm b tx2St b 0 tx2Gc).2 = 265214 := by
  change leg1Need sevm b tx2St b 0 tx2Gc + (xferAcc (leg1World sevm b b) tx2St.token1.toB256 +
    xferExt (leg1World sevm b b) (swapLocalsStack sevm tx2St) (leg1Mem sevm b) (leg1Ptr sevm b)
      (swapAmount1Out sevm) (swapRecipientWord sevm) tx2St.token1.toB256 0x8e1 +
    leg1Used sevm b tx2St b) = 265214
  rw [tx2_leg1Need h, tx2_leg1Used h, tx2_leg1World h, tx2_leg1Mem h, tx2_leg1Ptr h,
    tx2_amount1 h.data, tx2_recipientWord h.data, tx2St_token1, tx2_xferAcc h, tx2_xferExt h]

theorem tx2_frontGas :
    swapFrontTransferGas sevm b b (tx2D sevm b) 0 265214 0 tx2Gc = 265906 := by
  unfold swapFrontTransferGas swapOptGas swapOptMem swapOptPtr
  rw [tx2_amount0 h.data, ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl, tx2_amount1 h.data, ite_eq_right (by decide),
    show safeTransferPreCharge getterInitMemory.size 128 = 629 by decide +kernel]

theorem tx2_front : SwapFrontForwardEnv sevm b tx2St b (tx2D sevm b) b 0 265214 0 tx2Gc := by
  have vp := tx2_prefix_view h
  refine ⟨fun hne => absurd (tx2_amount0 h.data) hne, fun _ => ?_,
    fun hne => absurd (tx2_dataLength h.data) hne, ?_⟩
  · have spec := swapWethLeg1_spec (sevm := sevm) (b := b) (st := tx2St) (d0 := b) (cgC := 0)
      (Gc := tx2Gc) (tx2_fork h) h.static (by rw [h.depth]; decide) (tx2_amount0 h.data)
      (by rw [vp.state, tx2St_token1, tx2PrefixState, State.setStorVal_getCode]; exact h.wethCode)
      (tx2_notPrecomp h _ (Or.inr rfl))
      (by rw [tx2_amount1 h.data, vp.getStorVal, h.target, tx2St_token1, tx2PrefixState_weth,
            h.wethPair]; decide)
      (by rw [tx2_cg1 h]; decide)
      (by rw [tx2_leg1Used h, tx2_leg1Need h]; decide)
    rw [tx2_cg1 h] at spec
    exact spec
  · rw [tx2_frontGas h]
    unfold gCallStipend
    omega

theorem tx2_conditions : SwapModelConditions tx2St (swapAmount0Out sevm) (swapAmount1Out sevm)
    (swapRecipient sevm) (swapBalanceWord (tx2Callee h).d0.returnData)
    (swapBalanceWord (tx2Callee h).d1.returnData) := by
  change SwapModelConditions tx2St (swapAmount0Out sevm) (swapAmount1Out sevm) (swapRecipient sevm)
    (swapBalanceWord (tx2D0 sevm b).returnData) (swapBalanceWord (tx2Rd sevm b).1.returnData)
  rw [tx2_amount0 h.data, tx2_amount1 h.data, tx2_recipient h.data, tx2D0_returnData h,
    tx2Rd_returnData h, swapBalanceWord_toBytes, swapBalanceWord_toBytes]
  unfold SwapModelConditions
  decide +kernel

theorem tx2_rep : WriterRep (UniswapV2Pair.pairKeys w0PairRows) (b.getStor sevm.currentTarget) tx2St := by
  rw [h.target, getStor_eq', h.pairStor]
  exact UniswapV2Pair.checkPair_sound w0_checkPair

/-- The frame's pc-zero run, at the closed gas. -/
theorem tx2_frame_exec :
    exec ⟨0, sevm, b⟩ = .ok (St (tx2Callee h).post [0x022c0d9f] (tx2Callee h).memory tx2G) := by
  obtain ⟨back, hgas, hpost, hmem⟩ := (tx2Callee h).accepted (tx2_conditions h) h.static
  have front := tx2_front h
  rw [← tx2Callee_gas h, ← hgas] at front
  have body := swapBody_exact (tx2_fork h) (tx2_rep h) rfl h.static
    (Or.inr (by rw [tx2_amount1 h.data]; decide)) (by rw [tx2_amount0 h.data]; decide)
    (by rw [tx2_amount1 h.data]; decide) (by rw [tx2_recipient h.data]; decide +kernel)
    (by rw [tx2_recipient h.data]; decide +kernel) (tx2_guards h.data) back front
  have pc0 := swapPc0_exact h.value (tx2_size h.data) (tx2_selector h.data) (tx2_guards h.data) body
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok h.code (tx2_fork h) ⟨t_0000_c0, rfl, pc0⟩
  rw [hgas, tx2Callee_gas h, tx2_frontGas h, tx2_prefix_gas h, hpost, hmem,
    show 265906 + 11669 + 279 + 166 = b.gasLeft by rw [h.gas], ← St.self h.stack h.memory] at run
  exact (exec_iff_exec_eq 0 sevm b _).mp ⟨run⟩

theorem tx2Callee_post_view : ∃ K, DView b (tx2Callee h).post K tx2A1 (tx2PostState b) 2800
    [wethTransferLog, tx2SyncLog, tx2SwapLog] := by
  change ∃ K, DView b (Blanc.afterSstore sevm (swapLoggedWorld sevm (tx2Rd sevm b).1
    (swapCutWords sevm tx2St).reserve0 (swapCutWords sevm tx2St).reserve1
    (swapBalanceWord (tx2D0 sevm b).returnData) (swapBalanceWord (tx2Rd sevm b).1.returnData)
    (swapInWord (swapBalanceWord (tx2D0 sevm b).returnData) (swapCutWords sevm tx2St).reserve0
      (swapCutWords sevm tx2St).amount0Out)
    (swapInWord (swapBalanceWord (tx2Rd sevm b).1.returnData) (swapCutWords sevm tx2St).reserve1
      (swapCutWords sevm tx2St).amount1Out)
    (swapCutWords sevm tx2St).amount0Out (swapCutWords sevm tx2St).amount1Out
    (swapCutWords sevm tx2St).recipient) 12 1) K tx2A1 (tx2PostState b) 2800
    [wethTransferLog, tx2SyncLog, tx2SwapLog]
  rw [tx2_cutWords h, tx2D0_returnData h, tx2Rd_returnData h, swapBalanceWord_toBytes,
    swapBalanceWord_toBytes,
    show swapInWord 1001000 tx2W.reserve0 tx2W.amount0Out = 1000 by decide +kernel,
    show swapInWord 999004 tx2W.reserve1 tx2W.amount1Out = 0 by decide +kernel]
  exact tx2_post_view h (tx2Rd_view h)

/-- **The swap frame of `tx2` succeeds**, with `172795` gas left, refund counter `2800`, the
`Transfer`, `Sync` and `Swap` logs, no deletion, and the world `tx2PostState`. -/
theorem tx2_frame_success : ∃ post, exec ⟨0, sevm, b⟩ = .ok post ∧ post.gasLeft = 172795 ∧
    post.error = none ∧ post.refundCounter = 2800 ∧ (∀ a, a ∉ post.accountsToDelete) ∧
    post.logs = [wethTransferLog, tx2SyncLog, tx2SwapLog] ∧ post.state = tx2PostState b := by
  obtain ⟨K, v⟩ := tx2Callee_post_view h
  have v' := v.St [0x022c0d9f] (tx2Callee h).memory tx2G
  exact ⟨_, tx2_frame_exec h, rfl, v'.error, v'.refund, v'.deleted, v'.logs, v'.state⟩

end Run

end Blanc.Composition.UniswapV2PairWeth9Instance
