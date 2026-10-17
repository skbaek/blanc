import Blanc.Composition.UniswapV2PairWeth9Tx2View

/-!
# The swap frame of `tx2`: the prefix and the WETH9 `transfer` leg, viewed

The swap's prefix (lock, reserve and token loads) and its WETH9 `transfer(trader, swapOut)` CALL,
carried through `DView`: the prefix world `swapPrefixWorld`, the CALL's gas-free result skeleton
`leg1Skel`, and their exact charges.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Joint

theorem rules_bpo2 {s : BenvStat} (h : s.fork = .bpo2) : s.rules = Fork.bpo2.ruleSet := by
  unfold BenvStat.rules
  rw [h]

section Prefix

variable {sevm : Sevm} {b : Devm} (h : Tx2Frame sevm b)
include h

/-- The world after the prefix: the lock cleared. -/
def tx2PrefixState (b : Devm) : Jaune.State := b.state.setStorVal pair 12 0

/-- The prefix's warm keys. -/
def tx2PrefixKeys : List (Adr × B256) := [(pair, 7), (pair, 6), (pair, 8), (pair, 12), (pair, 12)]

theorem tx2_prefix_view :
    DView b (swapPrefixWorld sevm b) tx2PrefixKeys [] (tx2PrefixState b) 4800 [] := by
  have v := (((((DView.entry h).afterSload h.target 12).afterSstore h.target h.createdPair 12 0
    ).afterSload h.target 8).afterSload h.target 6).afterSload h.target 7
  have hs : ((b.state.getStor pair).get 12) = 1 := by rw [h.pairStor, w0PairStor_12]
  rw [h.origPair, w0PairStor_12, hs, rules_bpo2 h.fork] at v
  exact v

theorem tx2_prefix_gas : swapPrefixGas sevm b (swapAmount0Out sevm) = 11669 := by
  have v0 := DView.entry h
  have v1 := v0.afterSload h.target 12
  have v2 := v1.afterSstore h.target h.createdPair 12 0
  have v3 := v2.afterSload h.target 8
  have v4 := v3.afterSload h.target 6
  unfold swapPrefixGas mintLockedWorld
  dsimp only
  rw [v0.sloadCost h.target, v1.sstoreCost h.target h.createdPair, v2.sloadCost h.target,
    v3.sloadCost h.target, v4.sloadCost h.target, tx2_amount0 h.data, h.origPair, w0PairStor_12,
    h.pairStor, w0PairStor_12]
  decide +kernel

end Prefix

/-! ## WETH9's `transfer(trader, swapOut)` child frame -/

/-- The `Transfer(pair, trader, swapOut)` event, emitted at `a`. -/
def wethTransferLogAt (a : Adr) : Log :=
  { address := a,
    topics := [Bytes.toB256
        [221, 242, 82, 173, 27, 226, 200, 155, 105, 194, 176, 104, 252, 55, 141, 170, 149, 43,
          167, 241, 99, 196, 161, 22, 40, 245, 90, 77, 245, 35, 179, 239],
      pair.toB256, trader.toB256],
    data := swapOut.toBytes }

/-- The `Transfer(pair, trader, swapOut)` event WETH9 emits. -/
def wethTransferLog : Log := wethTransferLogAt weth

/-- WETH9's two balance writes. -/
def wethTransferWrites (S : Jaune.State) : Jaune.State :=
  (S.setStorVal weth (Weth9.balSlot pair) 999004).setStorVal weth (Weth9.balSlot trader) 996

theorem refund_update {g : GasSchedule} {rc : Int} :
    sstoreNewRefundCounter g 999004 1000000 1000000 rc = rc := by
  unfold sstoreNewRefundCounter
  simp only [show (1000000 : B256) ≠ 999004 from by decide, show (1000000 : B256) ≠ 0 from by decide,
    show (999004 : B256) ≠ 0 from by decide, ne_eq, not_false_eq_true, and_false, ↓reduceIte]

theorem refund_set {g : GasSchedule} {rc : Int} : sstoreNewRefundCounter g 996 0 0 rc = rc := by
  unfold sstoreNewRefundCounter
  simp only [show (0 : B256) ≠ 996 from by decide, ne_eq, not_false_eq_true, ↓reduceIte,
    not_true_eq_false, false_and, and_false]

section Child

variable {b : Devm} {s : Sevm} {d : Devm} {K : List (Adr × B256)} {A : List Adr} {S : Jaune.State}
  {rc : Int}
  (hT : s.currentTarget = weth) (hC : s.caller = pair)
  (h4 : (Sevm.dataWord s 4).toAdr = trader) (h36 : Sevm.dataWord s 36 = swapOut)
  (hcr : weth ∉ b.createdAccounts) (v : DView b d K A S rc [])
  (hP : (S.getStor weth).get (Weth9.balSlot pair) = 1000000)
  (hTr : (S.getStor weth).get (Weth9.balSlot trader) = 0)
  (oP : (s.benvStat.origState.getStor weth).get (Weth9.balSlot pair) = 1000000)
  (oT : (s.benvStat.origState.getStor weth).get (Weth9.balSlot trader) = 0)
include hT hC h4 h36 hcr v hP hTr oP oT

/-- The keys WETH9's `transfer` warms on top of the entry's. -/
def wethTransferKeys (K : List (Adr × B256)) : List (Adr × B256) :=
  (weth, Weth9.balSlot trader) :: (weth, Weth9.balSlot trader) :: (weth, Weth9.balSlot pair) ::
    (weth, Weth9.balSlot pair) :: (weth, Weth9.balSlot pair) :: K

theorem weth9TransferPost_view (G : Nat) :
    DView b (weth9TransferPost s d G) (wethTransferKeys K) A (wethTransferWrites S) rc
      [wethTransferLog] := by
  have v1 := v.afterSload hT (Weth9.balSlot pair)
  have v2 := v1.afterSload hT (Weth9.balSlot pair)
  have v3 := v2.afterSstore hT hcr (Weth9.balSlot pair) (1000000 - swapOut)
  have v4 := v3.afterSload hT (Weth9.balSlot trader)
  have v5 := v4.afterSstore hT hcr (Weth9.balSlot trader) (0 + swapOut)
  have v6 := v5.addLog (wethTransferLogAt s.currentTarget)
  rw [State.setStorVal_getStor_self, Stor.get_set_ne _ weth_balSlot_trader_ne_pair.symm, hP, hTr,
    oP, oT, show (1000000 : B256) - swapOut = 999004 from by decide,
    show (0 : B256) + swapOut = 996 from by decide, refund_update, refund_set] at v6
  have e : weth9TransferPost s d G = ((St (Blanc.afterSstore s (Blanc.afterSload s (Blanc.afterSstore s
      (Blanc.afterSload s (Blanc.afterSload s d (Weth9.balSlot pair)) (Weth9.balSlot pair))
      (Weth9.balSlot pair) 999004) (Weth9.balSlot trader)) (Weth9.balSlot trader) 996 |>.addLog
      (wethTransferLogAt s.currentTarget)) [Sevm.selector s] ((transferBodyMem s).write 96 (B256.toBytes 1))
      G).memRead (B256.toNat 96) (B256.toNat 32)).2.withOutput (B256.toBytes 1) := by
    unfold weth9TransferPost transferWrapperPost xferTailPost Weth9.tT3 Weth9.tT2 Weth9.tT1
      Weth9.tV2 Weth9.tV1 Weth9.pB1
    have hP' : (S.getStor s.currentTarget).get (Weth9.balSlot pair) = 1000000 := by rw [hT]; exact hP
    have hT' : ((S.setStorVal weth (Weth9.balSlot pair) (1000000 - swapOut)).getStor
        s.currentTarget).get (Weth9.balSlot trader) = 0 := by
      rw [hT, State.setStorVal_getStor_self, Stor.get_set_ne _ weth_balSlot_trader_ne_pair.symm, hTr]
    unfold Weth9.tT2 Weth9.tT1 Weth9.tV1
    rw [hC, h4, h36, v1.getStorVal, hP', v3.getStorVal, hT', show (1000000 : B256) - swapOut = 999004 from by decide,
      show (0 : B256) + swapOut = 996 from by decide]
    rfl
  rw [e]
  have v7 := ((v6.St [Sevm.selector s] ((transferBodyMem s).write 96 (B256.toBytes 1)) G).memRead
    (B256.toNat 96) (B256.toNat 32)).withOutput (B256.toBytes 1)
  have hl : ([] ++ [wethTransferLogAt s.currentTarget] : List Log) = [wethTransferLog] := by
    rw [hT]
    rfl
  rw [hl] at v7
  exact v7

theorem weth9TransferGas_view (hkP : (weth, Weth9.balSlot pair) ∉ K)
    (hkT : (weth, Weth9.balSlot trader) ∉ K) : Weth9.transferGas s d = 29962 := by
  have v1 := v.afterSload hT (Weth9.balSlot pair)
  have v2 := v1.afterSload hT (Weth9.balSlot pair)
  have v3 := v2.afterSstore hT hcr (Weth9.balSlot pair) (1000000 - swapOut)
  have v4 := v3.afterSload hT (Weth9.balSlot trader)
  have hP' : (S.getStor s.currentTarget).get (Weth9.balSlot pair) = 1000000 := by rw [hT]; exact hP
  have hT' : ((S.setStorVal weth (Weth9.balSlot pair) (1000000 - swapOut)).getStor
      s.currentTarget).get (Weth9.balSlot trader) = 0 := by
    rw [hT, State.setStorVal_getStor_self, Stor.get_set_ne _ weth_balSlot_trader_ne_pair.symm, hTr]
  unfold Weth9.transferGas Weth9.xferGasSelf Weth9.xfTailGas Weth9.tT3 Weth9.tV2 Weth9.pB1
  unfold Weth9.tT2 Weth9.tT1 Weth9.tV1
  rw [hC, h4, h36, v1.getStorVal, hP', v3.getStorVal, hT', v.sloadCost hT,
    v4.sstoreCost hT hcr, v3.sloadCost hT, v2.sstoreCost hT hcr, v1.sloadCost hT,
    State.setStorVal_getStor_self, Stor.get_set_ne _ weth_balSlot_trader_ne_pair.symm, hP, hTr,
    oP, oT]
  simp only [List.mem_cons, hkP, hkT, Prod.mk.injEq, true_and, true_or, or_false,
    weth_balSlot_trader_ne_pair, ite_true, ite_false]
  decide +kernel

end Child

/-! ## The `transfer` CALL's message and result -/

section Call

variable {sevm : Sevm} {b W : Devm} {K : List (Adr × B256)} {A : List Adr} {S : Jaune.State}
  {rc : Int} {Lg : List Log} {L : List B256} {M : Mem} {p amount toWord token rho : B256}

theorem xferParent_view (h : DView b W K A S rc Lg) (g k : Nat) :
    DView b (xferParent W L M p amount toWord token rho g k) K ((tokenMask token).toAdr :: A) S rc Lg :=
  ((((h.setMach _).addAccessedAddress _).setMach _).memExtends _).withReturnData _

theorem xferMsg_eq (g k f : Nat) :
    xferMsg sevm W L M p amount toWord token rho g k f =
      callMsg sevm (xferParent W L M p amount toWord token rho g k) f 0 sevm.currentTarget
        (tokenMask token).toAdr (tokenMask token).toAdr true false
        ((xferParent W L M p amount toWord token rho g k).memory.data.sliceD (p + 164).toNat
          (68 : B256).toNat 0) (W.state.getCode (tokenMask token).toAdr) false := by
  unfold xferMsg
  rw [callChildMsg_zero]
  rfl

theorem xferMsg_devm_view (h : DView b W K A S rc Lg) (hsg : sevm.benvStat.rules.stateGas = none)
    (g k f : Nat) :
    DView b (initDevm (xferMsg sevm W L M p amount toWord token rho g k f)) K
      ((tokenMask token).toAdr :: A) S 0 [] := by
  rw [xferMsg_eq]
  exact (xferParent_view h g k).initDevm_callMsg hsg _ _ _ _ _ _ _ _ _ _

end Call

/-! ## The instance's `transfer` leg -/

theorem tx2St_token1 : tx2St.token1 = weth := rfl
theorem tx2St_token0 : tx2St.token0 = tokenX := rfl

/-- The `transfer` child's entry machine. -/
abbrev tx2XferSevm (sevm : Sevm) (b : Devm) : Sevm :=
  initSevm (xferMsg sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm tx2St) getterInitMemory 128
    swapOut trader.toB256 weth.toB256 0x8e1 0 0 0)

abbrev tx2XferDevm (sevm : Sevm) (b : Devm) : Devm :=
  initDevm (xferMsg sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm tx2St) getterInitMemory 128
    swapOut trader.toB256 weth.toB256 0x8e1 0 0 0)

theorem tokenMask_weth : (tokenMask weth.toB256).toAdr = weth := tokenMask_toAdr weth

theorem tx2_xfer_words : (Sevm.dataWord (tx2XferSevm sevm b) 4).toAdr = trader ∧
    Sevm.dataWord (tx2XferSevm sevm b) 36 = swapOut := by
  have hd := xferMsg_data (sevm := sevm) (W := swapPrefixWorld sevm b) (L := swapLocalsStack sevm tx2St)
    (M := getterInitMemory) (p := 128) (amount := swapOut) (toWord := trader.toB256)
    (token := weth.toB256) (rho := 0x8e1) 0 0 0 getterInitMemory_ptr.wf (by decide) (by decide)
  obtain ⟨w4, w36, -⟩ := dataWord_twoWords (e := tx2XferSevm sevm b) hd
  refine ⟨?_, w36⟩
  rw [w4]
  decide +kernel

theorem tx2PrefixState_weth : (tx2PrefixState b).getStor weth = b.state.getStor weth :=
  State.setStorVal_getStor_ne _ pair_ne_weth _ _

/-- The `transfer` CALL's gas-free result. -/
abbrev tx2D1 (sevm : Sevm) (b : Devm) : Devm :=
  wethTransferSkel sevm (swapPrefixWorld sevm b) (swapLocalsStack sevm tx2St) getterInitMemory 128
    swapOut trader.toB256 weth.toB256 0x8e1


section Leg

variable {sevm : Sevm} {b : Devm} (h : Tx2Frame sevm b)
include h

theorem tx2_leg1World : leg1World sevm b b = swapPrefixWorld sevm b := by
  unfold leg1World swapOptWorld
  rw [ite_eq_left (tx2_amount0 h.data)]

theorem tx2_leg1Mem : leg1Mem sevm b = getterInitMemory := by
  unfold leg1Mem swapOptMem
  rw [ite_eq_left (tx2_amount0 h.data)]

theorem tx2_leg1Ptr : leg1Ptr sevm b = 128 := by
  unfold leg1Ptr swapOptPtr
  rw [ite_eq_left (tx2_amount0 h.data)]

theorem tx2_hsg : sevm.benvStat.rules.stateGas = none := by
  rw [rules_bpo2 h.fork]
  rfl

theorem tx2_xfer_view :
    DView b (tx2XferDevm sevm b) tx2PrefixKeys [weth] (tx2PrefixState b) 0 [] := by
  have v := xferMsg_devm_view (L := swapLocalsStack sevm tx2St) (M := getterInitMemory) (p := 128)
    (amount := swapOut) (toWord := trader.toB256) (token := weth.toB256) (rho := 0x8e1)
    (tx2_prefix_view h) (tx2_hsg h) 0 0 0
  rw [tokenMask_weth] at v
  exact v

theorem tx2_leg1Skel : leg1Skel sevm b tx2St b = tx2D1 sevm b := by
  unfold leg1Skel
  rw [tx2_leg1World h, tx2_leg1Mem h, tx2_leg1Ptr h, tx2_amount1 h.data, tx2_recipientWord h.data,
    tx2St_token1]

theorem tx2_D1_view :
    DView b (tx2D1 sevm b) (tx2PrefixKeys ++ wethTransferKeys tx2PrefixKeys) ([weth] ++ [weth])
      (wethTransferWrites (tx2PrefixState b)) (4800 + 0) ([] ++ [wethTransferLog]) := by
  have vp := xferParent_view (L := swapLocalsStack sevm tx2St) (M := getterInitMemory) (p := 128)
    (amount := swapOut) (toWord := trader.toB256) (token := weth.toB256) (rho := 0x8e1)
    (tx2_prefix_view h) 0 0
  rw [tokenMask_weth] at vp
  obtain ⟨w4, w36⟩ := tx2_xfer_words (sevm := sevm) (b := b)
  have vc := weth9TransferPost_view (G := 0) (s := tx2XferSevm sevm b) (d := tx2XferDevm sevm b)
    (by change (tokenMask weth.toB256).toAdr = weth; exact tokenMask_weth) (h.target) w4 w36
    h.createdWeth (tx2_xfer_view h)
    (by rw [tx2PrefixState_weth]; exact h.wethPair) (by rw [tx2PrefixState_weth]; exact h.wethTrader)
    h.origWethPair h.origWethTrader
  exact vp.callChildPost vc _ _

theorem tx2_leg1Used : leg1Used sevm b tx2St b = 29962 := by
  unfold leg1Used xferUsed xferUsedAt
  rw [tx2_leg1World h, tx2_leg1Mem h, tx2_leg1Ptr h, tx2_amount1 h.data, tx2_recipientWord h.data,
    tx2St_token1]
  obtain ⟨w4, w36⟩ := tx2_xfer_words (sevm := sevm) (b := b)
  exact weth9TransferGas_view tokenMask_weth h.target w4 w36 h.createdWeth (tx2_xfer_view h)
    (by rw [tx2PrefixState_weth]; exact h.wethPair) (by rw [tx2PrefixState_weth]; exact h.wethTrader)
    h.origWethPair h.origWethTrader (by decide +kernel) (by decide +kernel)

theorem tx2_xferAcc : xferAcc (swapPrefixWorld sevm b) weth.toB256 = 2600 := by
  unfold xferAcc
  rw [tokenMask_weth, (tx2_prefix_view h).accessCost]
  simp only [List.not_mem_nil, h.coldWeth, or_self, ite_false]
  rfl

theorem tx2_xferExt : xferExt (swapPrefixWorld sevm b) (swapLocalsStack sevm tx2St) getterInitMemory
    128 swapOut trader.toB256 weth.toB256 0x8e1 = 0 := by
  unfold xferExt xferPopped Devm.extCost
  rw [Devm.setMach_memory]
  dsimp only
  decide +kernel

end Leg


end Blanc.Composition.UniswapV2PairWeth9Instance
