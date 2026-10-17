import Blanc.Composition.UniswapV2PairWeth9Tx2Leg

/-!
# The swap frame of `tx2`: the two post-transfer balance queries, viewed

After WETH9's `transfer`, the Pair queries `X.balanceOf(pair)` (Token20, cold) and
`WETH9.balanceOf(pair)` (warm).  This file carries both `STATICCALL` results through `DView`
(`balParent_view`, `balanceOfPost_view`, `weth9BalancePost_view`), fixes the closed staging words
(`tx2W`, the cut memory `tx2M` at pointer `tx2P`), and evaluates the queries' charges.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint
open Blanc.Lift.VyperNonreentrantDeployed.Token20 (balanceOfGas balanceOfPost boHolder retPost)

/-! ## Generic balance-query views -/

section Bal

variable {b B : Devm} {K : List (Adr × B256)} {A : List Adr} {S : Jaune.State} {rc : Int}
  {Lg : List Log} {sevm : Sevm} {T : List B256} {M : Mem} {p t : B256}

theorem balParent_view (h : DView b B K A S rc Lg) (g k : Nat) :
    DView b (balParent sevm B T M p t g k) K (balTok t :: balTok t :: A) S rc Lg :=
  ((((h.temporalAccountAccessBase _).setMach _).addAccessedAddress _).memExtends _).withReturnData _

theorem balMsg_devm_view (h : DView b B K A S rc Lg) (hsg : sevm.benvStat.rules.stateGas = none)
    (g k f : Nat) :
    DView b (initDevm (balMsg sevm B T M p t g k f)) K (balTok t :: balTok t :: A) S 0 [] :=
  (balParent_view h g k).initDevm_callMsg hsg _ _ _ _ _ _ _ _ _ _

theorem balMsg_sevm_target (g k f : Nat) :
    (initSevm (balMsg sevm B T M p t g k f)).currentTarget = balTok t := rfl

theorem balMsg_sevm_benvStat (g k f : Nat) :
    (initSevm (balMsg sevm B T M p t g k f)).benvStat = sevm.benvStat := rfl

theorem balMsg_holder (g k f : Nat) (wf : Mem.Wf M) (width : p.toNat + 260 < 2 ^ 256) :
    (Sevm.dataWord (initSevm (balMsg sevm B T M p t g k f)) 4).toAdr = sevm.currentTarget := by
  rw [(dataWord_oneWord (e := initSevm (balMsg sevm B T M p t g k f))
    (balMsg_data (sevm := sevm) (B := B) (S := T) (t := t) g k f wf width)).1, toAdr_toB256]

end Bal

/-- A Token20 `balanceOf` frame warms the holder's slot and changes nothing else viewed. -/
theorem balanceOfPost_view {b d : Devm} {K : List (Adr × B256)} {A : List Adr} {S : Jaune.State}
    {rc : Int} {Lg : List Log} {s : Sevm} {a x : Adr} (ht : s.currentTarget = a)
    (hx : (Sevm.dataWord s 4).toAdr = x) (h : DView b d K A S rc Lg) (G : Nat) :
    DView b (balanceOfPost s d G)
      ((a, VyperNonreentrantDeployed.Token20.balSlot x) :: K) A S rc Lg := by
  unfold balanceOfPost retPost
  rw [boHolder, hx]
  exact (((h.afterSload ht _).St _ _ _).memRead _ _).withOutput _

/-- A WETH9 `balanceOf` frame warms the holder's slot and changes nothing else viewed. -/
theorem weth9BalancePost_view {b d : Devm} {K : List (Adr × B256)} {A : List Adr} {S : Jaune.State}
    {rc : Int} {Lg : List Log} {s : Sevm} {a x : Adr} (ht : s.currentTarget = a)
    (hx : (Sevm.dataWord s 4).toAdr = x) (h : DView b d K A S rc Lg) (G : Nat) :
    DView b (weth9BalancePost s d G) ((a, Weth9.balSlot x) :: K) A S rc Lg := by
  unfold weth9BalancePost wordTailPost
  rw [hx]
  exact (((h.afterSload ht _).St _ _ _).memRead _ _).withOutput _

/-! ## The closed staging of the back half -/

/-- The body words at the join, for `tx2`. -/
def tx2W : SwapCutWords :=
  { token1 := weth.toB256, token0 := tokenX.toB256, reserve1 := Nat.toB256 1000000,
    reserve0 := Nat.toB256 1000000, dataLength := 0, dataOffset := 164, recipient := trader.toB256,
    amount1Out := swapOut, amount0Out := 0 }

/-- The memory at the join. -/
abbrev tx2M : Mem := swapTransferMemory getterInitMemory 128 swapOut trader.toB256 (B256.toBytes 1)

/-- The free pointer at the join. -/
abbrev tx2P : B256 := swapMovedPointer 128 (B256.toBytes 1)

/-- The words under the first query's operands. -/
abbrev tx2S0 : List B256 := tx2W.token1 :: tx2W.token0 :: 0 :: 0 :: swapCutTail tx2W 0x257 [0x022c0d9f]

theorem tx2M_wf : Mem.Wf tx2M := by unfold Mem.Wf; decide +kernel
theorem tx2M_size : tx2M.size = 416 := by decide +kernel
theorem tx2P_width : tx2P.toNat + 260 < 2 ^ 256 := by decide +kernel
theorem tx2P_eq : tx2P = 356 := by decide +kernel

theorem balTok_tokenX : balTok tokenX.toB256 = tokenX := by decide +kernel
theorem balTok_weth : balTok weth.toB256 = weth := by decide +kernel
theorem balTok_tx2W0 : balTok tx2W.token0 = tokenX := by decide +kernel
theorem balTok_tx2W1 : balTok tx2W.token1 = weth := by decide +kernel

section X

variable {sevm : Sevm} {b : Devm} (h : Tx2Frame sevm b)
include h

theorem tx2_cutWords : swapCutWords sevm tx2St = tx2W := by
  unfold swapCutWords tx2W
  rw [tx2_dataLength h.data, tx2_recipientWord h.data, tx2_amount1 h.data, tx2_amount0 h.data,
    show swapDataStart sevm = 164 by
      simp only [swapDataStart, swapDataOffset, Sevm.dataWord, h.data, tx2Data]
      decide +kernel]
  rfl

end X

/-- The transfer result's warm keys. -/
abbrev tx2KD : List (Adr × B256) := tx2PrefixKeys ++ wethTransferKeys tx2PrefixKeys

/-- The transfer result's world. -/
abbrev tx2SD (b : Devm) : Jaune.State := wethTransferWrites (tx2PrefixState b)

theorem tx2SD_tokenX (b : Devm) : (tx2SD b).getStor tokenX = b.state.getStor tokenX := by
  unfold tx2SD wethTransferWrites tx2PrefixState
  rw [State.setStorVal_getStor_ne _ weth_ne_tokenX, State.setStorVal_getStor_ne _ weth_ne_tokenX,
    State.setStorVal_getStor_ne _ pair_ne_tokenX]

theorem tx2SD_code (b : Devm) (a : Adr) : (tx2SD b).getCode a = b.state.getCode a := by
  unfold tx2SD wethTransferWrites tx2PrefixState
  rw [State.setStorVal_getCode, State.setStorVal_getCode, State.setStorVal_getCode]

section XQuery

variable {sevm : Sevm} {b D : Devm} (h : Tx2Frame sevm b)
  (vD : DView b D tx2KD [weth, weth] (tx2SD b) 4800 [wethTransferLog])
include h vD

theorem tx2_xAcc : balAcc D tx2W.token0 = 100 := by
  unfold balAcc
  rw [((vD.temporalAccountAccessBase _)).accessCost]
  simp only [List.mem_cons, true_or, ite_true]
  rfl

theorem tx2_xExt : balExt sevm D tx2S0 tx2M tx2P tx2W.token0 = 0 := by
  unfold balExt balPopped Devm.extCost
  rw [Devm.setMach_memory, h.target]
  dsimp only
  decide +kernel

theorem tx2_xUsed : xBalUsed sevm D tx2S0 tx2M tx2P tx2W.token0 = 2206 := by
  unfold xBalUsed balanceOfGas
  have v := balMsg_devm_view (sevm := sevm) (T := tx2S0) (M := tx2M) (p := tx2P) (t := tx2W.token0)
    vD (tx2_hsg h) 0 0 0
  rw [boHolder, balMsg_holder 0 0 0 tx2M_wf tx2P_width, h.target,
    v.sloadCost (balMsg_sevm_target (sevm := sevm) (B := D) (T := tx2S0) (M := tx2M) (p := tx2P)
      (t := tx2W.token0) 0 0 0)]
  decide +kernel

/-- The first query's warm keys. -/
abbrev tx2K0 : List (Adr × B256) :=
  tx2KD ++ ((tokenX, VyperNonreentrantDeployed.Token20.balSlot pair) :: tx2KD)

/-- The first query's warm addresses. -/
abbrev tx2A0 : List Adr := [tokenX, tokenX, weth, weth] ++ [tokenX, tokenX, weth, weth]

theorem tx2_x_view (cg : Nat) :
    DView b (xBalanceCall sevm D tx2S0 tx2M tx2P tx2W.token0 cg) tx2K0 tx2A0 (tx2SD b) (4800 + 0)
      ([wethTransferLog] ++ []) := by
  unfold xBalanceCall xBalanceCallAt
  have vp := balParent_view (sevm := sevm) (T := tx2S0) (M := tx2M) (p := tx2P) (t := tx2W.token0) vD
    cg ((balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).1 + balExt sevm D tx2S0 tx2M tx2P tx2W.token0)
  have vc := balMsg_devm_view (sevm := sevm) (T := tx2S0) (M := tx2M) (p := tx2P) (t := tx2W.token0) vD
    (tx2_hsg h) cg ((balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).1 +
      balExt sevm D tx2S0 tx2M tx2P tx2W.token0) (balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).2
  have vb := balanceOfPost_view
    (balMsg_sevm_target (sevm := sevm) (B := D) (T := tx2S0) (M := tx2M) (p := tx2P)
      (t := tx2W.token0) cg ((balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).1 +
        balExt sevm D tx2S0 tx2M tx2P tx2W.token0) (balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).2)
    (balMsg_holder (sevm := sevm) (B := D) (T := tx2S0) (t := tx2W.token0) cg
      ((balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).1 + balExt sevm D tx2S0 tx2M tx2P tx2W.token0)
      (balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).2 tx2M_wf tx2P_width) vc
    ((balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).2 - xBalUsed sevm D tx2S0 tx2M tx2P tx2W.token0)
  rw [h.target, balTok_tx2W0] at vb
  rw [balTok_tx2W0] at vp
  exact vp.callChildPost vb _ _

theorem tx2_x_returnData (cg : Nat) :
    (xBalanceCall sevm D tx2S0 tx2M tx2P tx2W.token0 cg).returnData = (1001000 : B256).toBytes := by
  unfold xBalanceCall xBalanceCallAt
  rw [callChildPost_returnData]
  have vc := balMsg_devm_view (sevm := sevm) (T := tx2S0) (M := tx2M) (p := tx2P) (t := tx2W.token0) vD
    (tx2_hsg h) cg ((balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).1 +
      balExt sevm D tx2S0 tx2M tx2P tx2W.token0) (balSplit sevm D tx2S0 tx2M tx2P tx2W.token0 cg).2
  simp only [balanceOfPost, retPost, Devm.withOutput_output]
  rw [boHolder, balMsg_holder _ _ _ tx2M_wf tx2P_width, vc.getStorVal, balMsg_sevm_target,
    balTok_tx2W0, h.target, tx2SD_tokenX, h.xPair]

end XQuery

/-! ## The WETH9 query, at the first query's result `d0` -/

theorem tx2SD_wethPair (b : Devm) :
    ((tx2SD b).getStor weth).get (Weth9.balSlot pair) = 999004 := by
  unfold tx2SD wethTransferWrites
  rw [State.setStorVal_getStor_self, Stor.get_set_ne _ weth_balSlot_trader_ne_pair,
    State.setStorVal_getStor_self, Stor.get_set_self]

/-- The second query's warm keys. -/
abbrev tx2K1 : List (Adr × B256) := tx2K0 ++ ((weth, Weth9.balSlot pair) :: tx2K0)

/-- The second query's warm addresses. -/
abbrev tx2A1 : List Adr := (weth :: weth :: tx2A0) ++ (weth :: weth :: tx2A0)

section WQuery

variable {sevm : Sevm} {b d0 : Devm} (h : Tx2Frame sevm b)
  (v0 : DView b d0 tx2K0 tx2A0 (tx2SD b) (4800 + 0) ([wethTransferLog] ++ []))
  (r0 : d0.returnData = (1001000 : B256).toBytes)
include h v0 r0

theorem tx2_wAcc : balAcc d0 tx2W.token1 = 100 := by
  unfold balAcc
  rw [((v0.temporalAccountAccessBase _)).accessCost]
  simp only [List.mem_cons, true_or, ite_true]
  rfl

theorem tx2_wExt : balExt sevm d0 (readStack tx2W 0x257 [0x022c0d9f] d0) (readMem sevm tx2M tx2P d0) tx2P
    tx2W.token1 = 0 := by
  unfold balExt balPopped Devm.extCost readMem
  rw [Devm.setMach_memory, h.target, r0]
  dsimp only
  decide +kernel

theorem tx2_wUsed : readUsed sevm tx2M tx2P tx2W 0x257 [0x022c0d9f] d0 = 534 := by
  unfold readUsed balUsed weth9BalanceGas
  have v := balMsg_devm_view (sevm := sevm) (T := readStack tx2W 0x257 [0x022c0d9f] d0)
    (M := readMem sevm tx2M tx2P d0) (p := tx2P) (t := tx2W.token1) v0 (tx2_hsg h) 0 0 0
  have wf : Mem.Wf (readMem sevm tx2M tx2P d0) := swapBalanceReply_wf tx2M_wf
  rw [balMsg_holder 0 0 0 wf tx2P_width, h.target]
  simp only [v.keys, balMsg_sevm_target, balTok_tx2W1]
  decide +kernel

theorem tx2_wAt_view (g k f r : Nat) :
    DView b (callChildPost (balParent sevm d0 (readStack tx2W 0x257 [0x022c0d9f] d0)
        (readMem sevm tx2M tx2P d0) tx2P tx2W.token1 g k)
      (weth9BalancePost (initSevm (balMsg sevm d0 (readStack tx2W 0x257 [0x022c0d9f] d0)
          (readMem sevm tx2M tx2P d0) tx2P tx2W.token1 g k f))
        (initDevm (balMsg sevm d0 (readStack tx2W 0x257 [0x022c0d9f] d0)
          (readMem sevm tx2M tx2P d0) tx2P tx2W.token1 g k f)) r) tx2P.toNat (32 : B256).toNat)
      tx2K1 tx2A1 (tx2SD b) (4800 + 0 + 0) (([wethTransferLog] ++ []) ++ []) := by
  have wf : Mem.Wf (readMem sevm tx2M tx2P d0) := swapBalanceReply_wf tx2M_wf
  have vp := balParent_view (sevm := sevm) (T := readStack tx2W 0x257 [0x022c0d9f] d0)
    (M := readMem sevm tx2M tx2P d0) (p := tx2P) (t := tx2W.token1) v0 g k
  have vc := balMsg_devm_view (sevm := sevm) (T := readStack tx2W 0x257 [0x022c0d9f] d0)
    (M := readMem sevm tx2M tx2P d0) (p := tx2P) (t := tx2W.token1) v0 (tx2_hsg h) g k f
  have vb := weth9BalancePost_view
    (balMsg_sevm_target (sevm := sevm) (B := d0) (T := readStack tx2W 0x257 [0x022c0d9f] d0)
      (M := readMem sevm tx2M tx2P d0) (p := tx2P) (t := tx2W.token1) g k f)
    (balMsg_holder (sevm := sevm) (B := d0) (T := readStack tx2W 0x257 [0x022c0d9f] d0)
      (t := tx2W.token1) g k f wf tx2P_width) vc r
  rw [h.target, balTok_tx2W1] at vb
  rw [balTok_tx2W1] at vp
  exact vp.callChildPost vb _ _

theorem tx2_wAt_returnData (g k f r : Nat) :
    (callChildPost (balParent sevm d0 (readStack tx2W 0x257 [0x022c0d9f] d0)
        (readMem sevm tx2M tx2P d0) tx2P tx2W.token1 g k)
      (weth9BalancePost (initSevm (balMsg sevm d0 (readStack tx2W 0x257 [0x022c0d9f] d0)
          (readMem sevm tx2M tx2P d0) tx2P tx2W.token1 g k f))
        (initDevm (balMsg sevm d0 (readStack tx2W 0x257 [0x022c0d9f] d0)
          (readMem sevm tx2M tx2P d0) tx2P tx2W.token1 g k f)) r) tx2P.toNat
          (32 : B256).toNat).returnData = (999004 : B256).toBytes := by
  have wf : Mem.Wf (readMem sevm tx2M tx2P d0) := swapBalanceReply_wf tx2M_wf
  have vc := balMsg_devm_view (sevm := sevm) (T := readStack tx2W 0x257 [0x022c0d9f] d0)
    (M := readMem sevm tx2M tx2P d0) (p := tx2P) (t := tx2W.token1) v0 (tx2_hsg h) g k f
  rw [callChildPost_returnData, weth9BalancePost_output, weth9BalanceAnswer,
    balMsg_holder _ _ _ wf tx2P_width, vc.getStorVal, balMsg_sevm_target, balTok_tx2W1, h.target,
    tx2SD_wethPair]

end WQuery

end Blanc.Composition.UniswapV2PairWeth9Instance
