import Blanc.Composition.UniswapV2PairWeth9Tx2Post

/-!
# The swap frame of `tx2`: the callee records and their gas, closed

The Pair's swap liveness (`swapBody_exact`) takes the callee frames as records.  For `tx2` they are
WETH9's `transfer` (`swapWethLeg1`, at the join gas `tx2Gc`), Token20's `balanceOf` (`xBalanceCall`
at `tx2Cg0`) and WETH9's `balanceOf` (`swapWethRead1`), with the frame returning `tx2G`.  This file fixes the transfer result `tx2D`, identifies the swap's raw join indices with the
closed staging (`tx2_cutWorld`, …) and evaluates the read leg's call gas.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint

/-- The gas the swap frame returns with: `278020` (tx2's gas less its intrinsic `21980`) less the
frame's `105225`. -/
def tx2G : Nat := 172795

/-- The join gas (the back half's entry gas). -/
def tx2Gc : Nat := 232373

/-- The first query's call gas. -/
def tx2Cg0 : Nat := 229641

/-- The WETH9 `transfer` CALL's result. -/
noncomputable abbrev tx2D (sevm : Sevm) (b : Devm) : Devm := (swapWethLeg1 sevm b tx2St b 0 tx2Gc).1

theorem swapBalanceWord_toBytes (x : B256) : swapBalanceWord x.toBytes = x := by
  rw [swapBalanceWord, List.take_of_length_le (by rw [B256.length_toBytes]), B256.toB256_toBytes]

section Raw

variable {sevm : Sevm} {b : Devm} (h : Tx2Frame sevm b)
include h

theorem tx2D_eq : ∃ y, tx2D sevm b = (tx2D1 sevm b).withGasLeft y := by
  unfold tx2D swapWethLeg1 wethTransferCall
  rw [wethTransferCallAt_eq, tx2_leg1World h, tx2_leg1Mem h, tx2_leg1Ptr h, tx2_amount1 h.data,
    tx2_recipientWord h.data, tx2St_token1]
  exact ⟨_, rfl⟩

theorem tx2D_view :
    DView b (tx2D sevm b) tx2KD [weth, weth] (tx2SD b) 4800 [wethTransferLog] := by
  obtain ⟨y, e⟩ := tx2D_eq h
  rw [e]
  have v := (tx2_D1_view h).withGasLeft y
  rw [Int.add_zero, List.nil_append] at v
  exact v

theorem tx2D_returnData : (tx2D sevm b).returnData = (1 : B256).toBytes := by
  obtain ⟨y, e⟩ := tx2D_eq h
  rw [e, withGasLeft_returnData]
  rfl

theorem tx2_cutWorld : swapFrontCutWorld sevm b b (tx2D sevm b) b = tx2D sevm b := by
  unfold swapFrontCutWorld swapFrontTransferWorld swapOptWorld
  rw [if_pos (tx2_dataLength h.data), tx2_amount1 h.data, tx2_amount0 h.data, if_neg (by decide)]

theorem tx2_cutMem : swapFrontCutMem sevm b (tx2D sevm b) b = tx2M := by
  unfold swapFrontCutMem swapFrontTransferMem swapOptMem swapOptPtr
  rw [if_pos (tx2_dataLength h.data), tx2_amount1 h.data, tx2_amount0 h.data, if_neg (by decide),
    if_pos rfl, if_pos rfl, tx2_recipientWord h.data, tx2D_returnData h]

theorem tx2_cutPtr : swapFrontPtr sevm b (tx2D sevm b) = tx2P := by
  unfold swapFrontPtr swapOptPtr
  rw [tx2_amount1 h.data, tx2_amount0 h.data, if_neg (by decide), if_pos rfl, tx2D_returnData h]

end Raw

/-! ## The closed charges of the back half's staging and of the WETH9 query leg -/

section Charges

variable {sevm : Sevm} {b D d0 : Devm} (h : Tx2Frame sevm b)
include h

theorem tx2_reqCharge0 (vD : DView b D tx2KD [weth, weth] (tx2SD b) 4800 [wethTransferLog]) :
    swapRequestCharge D tx2M.size tx2P tx2W.token0 72 = 2711 := by
  unfold swapRequestCharge temporalAccountAccessCost
  rw [show (swapTokenWord tx2W.token0).toAdr = tokenX from balTok_tx2W0, tx2M_size]
  simp only [vD.addrs, List.mem_cons, List.not_mem_nil, or_false,
    show tokenX ≠ weth from weth_ne_tokenX.symm, h.coldX, or_self, ite_false]
  decide +kernel

theorem tx2_reqCharge1
    (v0 : DView b d0 tx2K0 tx2A0 (tx2SD b) (4800 + 0) ([wethTransferLog] ++ [])) :
    swapRequestCharge d0 (swapRequestSize tx2M.size tx2P) tx2P tx2W.token1 83 = 222 := by
  unfold swapRequestCharge temporalAccountAccessCost
  rw [show (swapTokenWord tx2W.token1).toAdr = weth from balTok_tx2W1, tx2M_size]
  simp only [v0.addrs, List.mem_cons, List.mem_append, true_or, or_true, ite_true]
  decide +kernel

theorem tx2_readGas (v0 : DView b d0 tx2K0 tx2A0 (tx2SD b) (4800 + 0) ([wethTransferLog] ++ []))
    (r0 : d0.returnData = (1001000 : B256).toBytes) (D : Devm) (G : Nat) :
    (swapWethRead1 sevm D tx2M tx2M.size tx2P tx2W 0x257 [0x022c0d9f] G d0).2 = G + 54227 := by
  unfold swapWethRead1 readNeed readCharge readSkel wethBalanceSkel
  dsimp only
  rw [tx2_wAcc h v0 r0, tx2_wExt h v0 r0, tx2_wUsed h v0 r0, r0, swapBalanceWord_toBytes,
    tx2_wAt_returnData h v0 r0, swapBalanceWord_toBytes,
    tx2_backPostGas h (tx2_wAt_view h v0 r0 0 0 0 0)]

theorem tx2_readNeed (v0 : DView b d0 tx2K0 tx2A0 (tx2SD b) (4800 + 0) ([wethTransferLog] ++ []))
    (r0 : d0.returnData = (1001000 : B256).toBytes) (G : Nat) :
    readNeed sevm tx2M tx2M.size tx2P tx2W 0x257 [0x022c0d9f] G d0 = G + 53593 := by
  unfold readNeed readSkel wethBalanceSkel
  rw [r0, swapBalanceWord_toBytes, tx2_wAt_returnData h v0 r0, swapBalanceWord_toBytes,
    tx2_backPostGas h (tx2_wAt_view h v0 r0 0 0 0 0)]

end Charges

/-! ## The raw join indices -/

/-- The swap's join world, memory and pointer, as `swapBody_exact` names them. -/
noncomputable abbrev tx2RW (sevm : Sevm) (b : Devm) : Devm :=
  swapFrontCutWorld sevm b b (tx2D sevm b) b
noncomputable abbrev tx2RM (sevm : Sevm) (b : Devm) : Mem :=
  swapFrontCutMem sevm b (tx2D sevm b) b
noncomputable abbrev tx2RP (sevm : Sevm) (b : Devm) : B256 :=
  swapFrontPtr sevm b (tx2D sevm b)

/-- The first query's result. -/
noncomputable abbrev tx2D0 (sevm : Sevm) (b : Devm) : Devm :=
  xBalanceCall sevm (tx2RW sevm b)
    ((swapCutWords sevm tx2St).token1 :: (swapCutWords sevm tx2St).token0 :: 0 :: 0 ::
      swapCutTail (swapCutWords sevm tx2St) 0x257 [0x022c0d9f])
    (tx2RM sevm b) (tx2RP sevm b) (swapCutWords sevm tx2St).token0 tx2Cg0

/-- The second query (WETH9's), with its call gas. -/
noncomputable abbrev tx2Rd (sevm : Sevm) (b : Devm) : Devm × Nat :=
  swapWethRead1 sevm (tx2RW sevm b) (tx2RM sevm b) (tx2RM sevm b).size (tx2RP sevm b)
    (swapCutWords sevm tx2St) 0x257 [0x022c0d9f] (tx2G + 1) (tx2D0 sevm b)

theorem swapEventRunGas_gt (G m : Nat) (p : B256) (uc : Nat) :
    gCallStipend < swapEventRunGas G m p uc := by
  unfold swapEventRunGas gCallStipend
  omega

section Closed

variable {sevm : Sevm} {b : Devm} (h : Tx2Frame sevm b)
include h

theorem tx2D0_eq :
    tx2D0 sevm b = xBalanceCall sevm (tx2D sevm b) tx2S0 tx2M tx2P tx2W.token0 tx2Cg0 := by
  unfold tx2D0 tx2RW tx2RM tx2RP
  rw [tx2_cutWorld h, tx2_cutMem h, tx2_cutPtr h, tx2_cutWords h]

theorem tx2D0_view :
    DView b (tx2D0 sevm b) tx2K0 tx2A0 (tx2SD b) (4800 + 0) ([wethTransferLog] ++ []) := by
  rw [tx2D0_eq h]
  exact tx2_x_view h (tx2D_view h) _

theorem tx2D0_returnData : (tx2D0 sevm b).returnData = (1001000 : B256).toBytes := by
  rw [tx2D0_eq h]
  exact tx2_x_returnData h (tx2D_view h) _

theorem tx2Rd_eq :
    tx2Rd sevm b = swapWethRead1 sevm (tx2D sevm b) tx2M tx2M.size tx2P tx2W 0x257 [0x022c0d9f]
      (tx2G + 1) (tx2D0 sevm b) := by
  unfold tx2Rd tx2RW tx2RM tx2RP
  rw [tx2_cutWorld h, tx2_cutMem h, tx2_cutPtr h, tx2_cutWords h]

theorem tx2Rd_gas : (tx2Rd sevm b).2 = 227023 := by
  rw [tx2Rd_eq h, tx2_readGas h (tx2D0_view h) (tx2D0_returnData h)]
  rfl

theorem tx2_fork : CoveredFork sevm.benvStat.fork := h.fork ▸ .bpo2

theorem tx2_notPrecomp (a : Adr) (ha : a = tokenX ∨ a = weth) :
    sevm.benvStat.rules.isPrecomp a = false := by
  rw [rules_bpo2 h.fork]
  rcases ha with rfl | rfl <;> decide +kernel

/-- **The first query's record** (Token20's `balanceOf(pair)`). -/
theorem tx2_first : SwapBalanceEnv sevm (tx2RW sevm b) (tx2RM sevm b) (tx2RP sevm b)
    (swapCutWords sevm tx2St).token0
    ((swapCutWords sevm tx2St).token1 :: (swapCutWords sevm tx2St).token0 :: 0 :: 0 ::
      swapCutTail (swapCutWords sevm tx2St) 0x257 [0x022c0d9f])
    (tx2D0 sevm b) tx2Cg0 ((tx2Rd sevm b).2 + 5 + swapRequestCharge (tx2D0 sevm b)
      (swapRequestSize (tx2RM sevm b).size (tx2RP sevm b)) (tx2RP sevm b)
      (swapCutWords sevm tx2St).token1 83 + 21) := by
  rw [tx2Rd_gas h, tx2D0_eq h]
  unfold tx2RW tx2RM tx2RP
  rw [tx2_cutWorld h, tx2_cutMem h, tx2_cutPtr h, tx2_cutWords h]
  have vD := tx2D_view h (sevm := sevm)
  have spec := xBalanceCall_spec (sevm := sevm) (B := tx2D sevm b) (S := tx2S0) (M := tx2M)
    (p := tx2P) (t := tx2W.token0) (cg := tx2Cg0) (tx2_fork h)
    (by rw [vD.state, tx2SD_code, balTok_tx2W0]; exact h.xCode)
    (by rw [h.depth]; decide) (by rw [balTok_tx2W0]; exact tx2_notPrecomp h _ (Or.inl rfl))
    (by decide) tx2M_wf tx2P_width (by decide)
    (by rw [tx2_xAcc h vD, tx2_xExt h vD]; decide)
    (by rw [tx2_xAcc h vD, tx2_xExt h vD, tx2_xUsed h vD]; decide)
  obtain ⟨call, stack, ret, gas⟩ := spec
  refine ⟨?_, call, stack, ?_, ?_⟩
  · change ((tx2D sevm b).state.getCode (swapTokenWord tx2W.token0).toAdr).size.toB256 ≠ 0
    rw [vD.state, tx2SD_code, show (swapTokenWord tx2W.token0).toAdr = tokenX from balTok_tx2W0,
      h.xCode]
    decide +kernel
  · rw [ret, B256.length_toBytes]
  · rw [gas, tx2_xAcc h vD, tx2_xExt h vD, tx2_xUsed h vD,
      tx2_reqCharge1 h (tx2_x_view h vD tx2Cg0)]
    rfl

/-- **The second query's record** (WETH9's `balanceOf(pair)`). -/
theorem tx2_second : SwapBalanceEnv sevm (tx2D0 sevm b)
    (swapBalanceReply (tx2RM sevm b) (tx2RP sevm b) sevm.currentTarget (tx2D0 sevm b).returnData)
    (tx2RP sevm b) (swapCutWords sevm tx2St).token1
    ((swapCutWords sevm tx2St).token1 :: (swapCutWords sevm tx2St).token0 :: 0 ::
      swapBalanceWord (tx2D0 sevm b).returnData :: swapCutTail (swapCutWords sevm tx2St) 0x257 [0x022c0d9f])
    (tx2Rd sevm b).1 (tx2Rd sevm b).2
    (swapBackPostGas sevm (tx2Rd sevm b).1
      (swapRequestSize (swapRequestSize (tx2RM sevm b).size (tx2RP sevm b)) (tx2RP sevm b)) (tx2RP sevm b)
      (swapCutWords sevm tx2St) (swapBalanceWord (tx2D0 sevm b).returnData)
      (swapBalanceWord (tx2Rd sevm b).1.returnData) (tx2G + 1)) := by
  have v0 := tx2D0_view h (sevm := sevm)
  have r0 := tx2D0_returnData h (sevm := sevm)
  refine swapWethRead1_spec (tx2_fork h) (by rw [h.depth]; decide) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [tx2_cutWords h, v0.state, tx2SD_code, show (swapTokenWord tx2W.token1).toAdr = weth from
      balTok_tx2W1, h.wethCode]
  · rw [tx2_cutWords h, show (swapTokenWord tx2W.token1).toAdr = weth from balTok_tx2W1]
    exact tx2_notPrecomp h _ (Or.inr rfl)
  · unfold tx2RM
    rw [tx2_cutMem h]
    exact tx2M_wf
  · unfold tx2RP
    rw [tx2_cutPtr h]
    exact tx2P_width
  · rw [tx2_cutWords h]
    decide
  · change (tx2Rd sevm b).2 < 2 ^ 256
    rw [tx2Rd_gas h]
    decide
  · unfold tx2RM tx2RP
    rw [tx2_cutMem h, tx2_cutPtr h, tx2_cutWords h, tx2_wUsed h v0 r0, tx2_readNeed h v0 r0]
    unfold tx2G
    decide

/-- The `_update` store sentries. -/
theorem tx2_sentries : SwapUpdateSentries sevm (tx2Rd sevm b).1
    (swapRequestSize (swapRequestSize (tx2RM sevm b).size (tx2RP sevm b)) (tx2RP sevm b))
    (tx2RP sevm b) (swapCutWords sevm tx2St).reserve0 (swapCutWords sevm tx2St).reserve1
    (swapBalanceWord (tx2D0 sevm b).returnData) (swapBalanceWord (tx2Rd sevm b).1.returnData)
    (swapEventRunGas (tx2G + 1)
      (swapSyncSize (swapRequestSize (swapRequestSize (tx2RM sevm b).size (tx2RP sevm b)) (tx2RP sevm b))
        (tx2RP sevm b)) (tx2RP sevm b)
      (swapUnlockCost sevm (tx2Rd sevm b).1 (swapCutWords sevm tx2St).reserve0
        (swapCutWords sevm tx2St).reserve1 (swapBalanceWord (tx2D0 sevm b).returnData)
        (swapBalanceWord (tx2Rd sevm b).1.returnData)
        (swapInWord (swapBalanceWord (tx2D0 sevm b).returnData) (swapCutWords sevm tx2St).reserve0
          (swapCutWords sevm tx2St).amount0Out)
        (swapInWord (swapBalanceWord (tx2Rd sevm b).1.returnData) (swapCutWords sevm tx2St).reserve1
          (swapCutWords sevm tx2St).amount1Out)
        (swapCutWords sevm tx2St).amount0Out (swapCutWords sevm tx2St).amount1Out
        (swapCutWords sevm tx2St).recipient)) := by
  refine ⟨?_, fun _ => ?_, fun _ => ?_⟩ <;>
  · have := swapEventRunGas_gt (tx2G + 1)
      (swapSyncSize (swapRequestSize (swapRequestSize (tx2RM sevm b).size (tx2RP sevm b)) (tx2RP sevm b))
        (tx2RP sevm b)) (tx2RP sevm b)
      (swapUnlockCost sevm (tx2Rd sevm b).1 (swapCutWords sevm tx2St).reserve0
        (swapCutWords sevm tx2St).reserve1 (swapBalanceWord (tx2D0 sevm b).returnData)
        (swapBalanceWord (tx2Rd sevm b).1.returnData)
        (swapInWord (swapBalanceWord (tx2D0 sevm b).returnData) (swapCutWords sevm tx2St).reserve0
          (swapCutWords sevm tx2St).amount0Out)
        (swapInWord (swapBalanceWord (tx2Rd sevm b).1.returnData) (swapCutWords sevm tx2St).reserve1
          (swapCutWords sevm tx2St).amount1Out)
        (swapCutWords sevm tx2St).amount0Out (swapCutWords sevm tx2St).amount1Out
        (swapCutWords sevm tx2St).recipient)
    omega

end Closed

end Blanc.Composition.UniswapV2PairWeth9Instance
