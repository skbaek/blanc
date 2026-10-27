import Blanc.Lift.UniswapV2Factory.CreatePairWalk
import Blanc.Lift.UniswapV2Factory.CreatePairSpawns
import Blanc.Lift.HistSstoreRefund
import Blanc.Lift.UniswapV2Factory.CallShape

/-!
# The factory's `createPair(WETH, USDC)` frame, assembled

`createPair_frame`: under Muir Glacier, a frame running the certified factory runtime at the
factory address with the recorded calldata, no value and at least 2,600,000 gas, from a world where
the Pair's `CREATE2` address has nonce zero and no code, and `getPair[USDC][WETH]` is unset, runs (gas-exactly,
`SProg.RunExact`) to a machine that holds the certified Pair runtime at the Pair address with
storage at the initialized checkpoint over the factory, the domain separator of the frame's chain id
and that address, and the sorted tokens (USDC, WETH). The frame's error, its accounts to delete
(at the Pair address) and the non-negativity of its refund counter are those of the world it
started from.

The walk is the segments of `CreatePairWalk` joined by the two spawns of `CreatePairSpawns`.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc.Lift

/-! ## What the storage suffix keeps -/

section Suffix

variable (sevm : Sevm) (q : Devm)

theorem sfxB10_state_ne {a : Adr} (ha : a ≠ sevm.currentTarget) :
    (sfxB10 sevm q).state.get a = q.state.get a := by
  show (sfxB9 sevm q).state.get a = _
  simp only [sfxB9, sfxB8, sfxB7, sfxB6, sfxB5, sfxB4, sfxB3, sfxB2, sfxB1, afterSloadH_state,
    afterSstoreH_state, State.setStorVal_get_ne _ (Ne.symm ha)]

theorem sfxB10_error : (sfxB10 sevm q).error = q.error := by
  show (sfxB9 sevm q).error = _
  simp only [sfxB9, sfxB8, sfxB7, sfxB6, sfxB5, sfxB4, sfxB3, sfxB2, sfxB1, afterSloadH_error,
    afterSstoreH_error]

theorem sfxB10_accountsToDelete : (sfxB10 sevm q).accountsToDelete = q.accountsToDelete := by
  show (sfxB9 sevm q).accountsToDelete = _
  simp only [sfxB9, sfxB8, sfxB7, sfxB6, sfxB5, sfxB4, sfxB3, sfxB2, sfxB1,
    afterSloadH_accountsToDelete, afterSstoreH_accountsToDelete]

/-- The suffix's refund counter does not fall when each of its four stores meets the condition of
`afterSstoreH_refundCounter_ge`. -/
theorem sfxB10_refundCounter_ge
    (hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000)
    (h1 : (sfxB1 sevm q).getOrigStorVal sevm sevm.currentTarget fk2 = 0 ∨
      (sfxB1 sevm q).getStorVal sevm.currentTarget fk2 ≠ 0)
    (h2 : (sfxB3 sevm q).getOrigStorVal sevm sevm.currentTarget fk5 = 0 ∨
      (sfxB3 sevm q).getStorVal sevm.currentTarget fk5 ≠ 0)
    (h3 : (sfxB5 sevm q).getOrigStorVal sevm sevm.currentTarget 3 = 0 ∨
      (sfxB5 sevm q).getStorVal sevm.currentTarget 3 ≠ 0)
    (h4 : (sfxB7 sevm q).getOrigStorVal sevm sevm.currentTarget (sfxSlot sevm q) = 0 ∨
      (sfxB7 sevm q).getStorVal sevm.currentTarget (sfxSlot sevm q) ≠ 0) :
    q.refundCounter ≤ (sfxB10 sevm q).refundCounter := by
  have r1 := afterSstoreH_refundCounter_ge sevm (sfxB1 sevm q) fk2
    (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) hflat h1
  have r2 := afterSstoreH_refundCounter_ge sevm (sfxB3 sevm q) fk5 (sfxMerge (sfxW10 sevm q))
    hflat h2
  have r3 := afterSstoreH_refundCounter_ge sevm (sfxB5 sevm q) 3 (sfxN sevm q + 1) hflat h3
  have r4 := afterSstoreH_refundCounter_ge sevm (sfxB7 sevm q) (sfxSlot sevm q)
    (sfxMerge (sfxWAll sevm q)) hflat h4
  have e1 : (sfxB1 sevm q).refundCounter = q.refundCounter := afterSloadH_refundCounter _ _ _
  have e3 : (sfxB3 sevm q).refundCounter = (sfxB2 sevm q).refundCounter :=
    afterSloadH_refundCounter _ _ _
  have e5 : (sfxB5 sevm q).refundCounter = (sfxB4 sevm q).refundCounter :=
    afterSloadH_refundCounter _ _ _
  have e7 : (sfxB7 sevm q).refundCounter = (sfxB6 sevm q).refundCounter :=
    afterSloadH_refundCounter _ _ _
  have e9 : (sfxB9 sevm q).refundCounter = (sfxB8 sevm q).refundCounter :=
    afterSloadH_refundCounter _ _ _
  have e10 : (sfxB10 sevm q).refundCounter = (sfxB9 sevm q).refundCounter := rfl
  have d2 : (sfxB2 sevm q) = afterSstoreH sevm (sfxB1 sevm q) fk2
    (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) := rfl
  have d4 : (sfxB4 sevm q) = afterSstoreH sevm (sfxB3 sevm q) fk5 (sfxMerge (sfxW10 sevm q)) := rfl
  have d6 : (sfxB6 sevm q) = afterSstoreH sevm (sfxB5 sevm q) 3 (sfxN sevm q + 1) := rfl
  have d8 : (sfxB8 sevm q) = afterSstoreH sevm (sfxB7 sevm q) (sfxSlot sevm q)
    (sfxMerge (sfxWAll sevm q)) := rfl
  rw [← d2] at r1
  rw [← d4] at r2
  rw [← d6] at r3
  rw [← d8] at r4
  omega

end Suffix

/-- The stack below the `CREATE2` operands. -/
abbrev belowCreate2 : List B256 :=
  [fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0x0 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)]

/-- The stack below the `CALL` operands. -/
abbrev belowCall : List B256 :=
  [(0x2eac : B256), (0x485cc955 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), fk3, (0x80 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256), (0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256),
    (0x95 : B256), (0xc9c65396 : B256)]

/-- The frame's world after `CREATE2`, from the frame's base `b` and initial gas `G0`. -/
def frameP (sevm : Sevm) (b : Devm) (G0 : Nat) : Devm :=
  pairCreate2Post sevm (afterSloadH sevm b fk2) belowCreate2 (G0 - 225 - 3920 - 34184)

/-- The gas at the `initialize` `CALL`. -/
def frameX (sevm : Sevm) (b : Devm) (G0 : Nat) : Nat := (frameP sevm b G0).gasLeft - 883 - 2

/-- The frame's world after the `initialize` call. -/
def frameQ (sevm : Sevm) (b : Devm) (G0 : Nat) : Devm :=
  initCallPost sevm (frameP sevm b G0) belowCall (frameX sevm b G0)

/-- The storage suffix's total charge from the world `q`. -/
def sfxCost (sevm : Sevm) (q : Devm) : Nat :=
  2904 + sfxCost4 sevm q + 848 + sfxCost3 sevm q + 818 + sfxCost2 sevm q + 938 +
    sfxCost1 sevm q + 1032

/-- The frame's gas when the body returns. -/
def frameGf (sevm : Sevm) (b : Devm) (G0 : Nat) : Nat :=
  (frameQ sevm b G0).gasLeft - sfxCost sevm (frameQ sevm b G0)

/-- The frame's final machine. -/
def framePost (sevm : Sevm) (b : Devm) (G0 : Nat) : Devm :=
  returnPost (St (sfxB10 sevm (frameQ sevm b G0)) [(0x2e68 : B256), (0x20 : B256), (0xc9c65396 : B256)]
    (fm26 (sfxNEv sevm (frameQ sevm b G0))) (frameGf sevm b G0 - 52)) (0x2e68 : B256)
    (0x20 : B256) [(0xc9c65396 : B256)]

theorem create2ChargeH_muir {sevm : Sevm} (hfork : sevm.benvStat.fork = .muirGlacier) :
    create2ChargeH sevm fm12 0xa0 0x2d74 = 34184 := by
  unfold create2ChargeH
  rw [muirRules hfork, fm12_size]
  decide

/-- **The `createPair` frame runs.**  Given the gas and world facts at the two spawns (supplied by
`createPair_frame` from the frame's start), the certified factory runtime runs gas-exactly from
pc `0` to `framePost`. -/
theorem createPair_frame_run {sevm : Sevm} {b : Devm} {G0 : Nat}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hcode : sevm.code = code)
    (htarget : sevm.currentTarget = UniswapV2Pair.Creation.factory)
    (hvalue : sevm.value = 0) (hdata : sevm.data = createPairData)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hv1 : b.getStorVal sevm.currentTarget fk2 = 0)
    (hnonce : ((afterSloadH sevm b fk2).state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hfresh : Create2TargetNoCollision (create2Prepared sevm (afterSloadH sevm b fk2) belowCreate2 fm12
      (G0 - 225 - 3920 - 34184) 0xa0 0x2d74 UniswapV2Pair.Creation.pairAddress)
      UniswapV2Pair.Creation.pairAddress)
    (hG0 : 225 + 3920 + 34184 ≤ G0)
    (hgasY : 2338600 ≤ except64th (G0 - 225 - 3920 - 34184))
    {chainWord : B256}
    (hcodeP : (frameP sevm b G0).state.getCode UniswapV2Pair.Creation.pairAddress =
      UniswapV2Pair.code)
    (hstorP : (frameP sevm b G0).getStor UniswapV2Pair.Creation.pairAddress =
      UniswapV2Pair.Creation.ctorStor chainWord UniswapV2Pair.Creation.pairAddress
        UniswapV2Pair.Creation.factory Stor.empty)
    (hsizeP : ((frameP sevm b G0).getCode ((0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) : B256).toAdr).size.toB256 = 0x2c1d)
    (hPgas : 885 ≤ (frameP sevm b G0).gasLeft)
    (hX : frameX sevm b G0 < 2 ^ 256) (h700 : 700 ≤ frameX sevm b G0)
    (hgasQ : initCallCharge sevm (frameP sevm b G0) belowCall (frameX sevm b G0) + 377 + 2400 ≤
      except64th (frameX sevm b G0 - 700))
    (hv2Q : (frameQ sevm b G0).getStorVal sevm.currentTarget fk2 = 0)
    (hQgas : sfxCost sevm (frameQ sevm b G0) + 2300 + 52 ≤ (frameQ sevm b G0).gasLeft) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty G0) (framePost sevm b G0) := by
  have rules := muirRules hfork
  have hshifts : sevm.benvStat.rules.op.shifts = true := by rw [rules]; rfl
  have hsize : sevm.data.length.toB256 = 0x44 := by rw [hdata]; decide
  have hword0 : Sevm.dataWord sevm 0 =
      0xc9c65396000000000000000000000000c02aaa39b223fe8d0a0e5c4f27ead908 := by
    unfold Sevm.dataWord; rw [hdata]; decide
  have hword4 : Sevm.dataWord sevm 4 = 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 := by
    unfold Sevm.dataWord; rw [hdata]; decide
  have hword24 : Sevm.dataWord sevm 0x24 = 0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 := by
    unfold Sevm.dataWord; rw [hdata]; decide
  obtain ⟨hPst0, hPmem0, -, -, -, -, -, -⟩ := pairCreate2Post_facts sevm (afterSloadH sevm b fk2)
    belowCreate2 (G0 - 225 - 3920 - 34184)
  have hPst : (frameP sevm b G0).stack = _ := hPst0
  have hPmem : (frameP sevm b G0).memory = fm12 := hPmem0
  obtain ⟨hQst0, hQmem0, -, -, -, -, -⟩ := initCallPost_facts sevm (frameP sevm b G0) belowCall
    (frameX sevm b G0)
  have hQst : (frameQ sevm b G0).stack = _ := hQst0
  have hQmem : (frameQ sevm b G0).memory = fm15 := hQmem0
  have hret := createPair_return (sevm := sevm) (b := sfxB10 sevm (frameQ sevm b G0))
    (G := frameGf sevm b G0 - 52) (v := sfxNEv sevm (frameQ sevm b G0))
  rw [show frameGf sevm b G0 - 52 + 52 = frameGf sevm b G0 by unfold frameGf; omega] at hret
  refine ⟨t_0000_c0, rfl, ?_⟩
  rw [show St b [] Mem.empty G0 = St b [] Mem.empty ((G0 - 225) + 225) by
    congr 1; omega]
  refine createPair_dispatch hvalue hsize hword0 hword4 hword24 hshifts ?_ hret
  have hc2 := create2ChargeH_muir hfork
  rw [show St b [(0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)] fm1 (G0 - 225) =
    St b [(0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48 : B256), (0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2 : B256), (0x95 : B256), (0xc9c65396 : B256)] fm1
      (((G0 - 225 - 3920 - 34184) + create2ChargeH sevm fm12 0xa0 0x2d74) + 3920) by
    rw [hc2, show G0 - 225 - 3920 - 34184 + 34184 + 3920 = G0 - 225 by omega]]
  refine createPair_prefix hfork hcode hshifts hv1 ?_
  show SFunc.RunExact _ _ _ (.next (.exec .create2) (SFunc.lineDrop 81 t_0531_c10)) _
  refine .next (pairCreate2_runCompiled hfork hstatic htarget hdepth hnonce hfresh hgasY
    (Nat.le_of_ble_eq_true rfl)) ?_
  change SFunc.RunExact _ _ (frameP sevm b G0) _ _
  rw [St.self hPst hPmem]
  rw [show (frameP sevm b G0).gasLeft = (frameX sevm b G0 + 2) + 883 from by
    unfold frameX; omega]
  refine createPair_window hfork hsizeP ?_
  show SFunc.RunExact _ _ _ (.next (.reg .gas) (.next (.exec .call) (SFunc.lineDrop 4 t_065e_c10))) _
  refine rx_gas (Nat.le_of_ble_eq_true rfl) ?_
  refine .next (pairInitCall_runCompiled hfork hstatic htarget hdepth hcodeP hstorP hX h700 hgasQ
    (Nat.le_of_ble_eq_true rfl)) ?_
  change SFunc.RunExact _ _ (frameQ sevm b G0) _ _
  have hGf : 2300 ≤ frameGf sevm b G0 := by unfold frameGf; omega
  have hgasQ' : (frameQ sevm b G0).gasLeft = frameGf sevm b G0 + 2904 +
      sfxCost4 sevm (frameQ sevm b G0) + 848 + sfxCost3 sevm (frameQ sevm b G0) + 818 +
      sfxCost2 sevm (frameQ sevm b G0) + 938 + sfxCost1 sevm (frameQ sevm b G0) + 1032 := by
    unfold frameGf sfxCost at *; omega
  have e : frameQ sevm b G0 = St (frameQ sevm b G0) ((1 : B256) :: belowCall) fm15
      (frameGf sevm b G0 + 2904 +
      sfxCost4 sevm (frameQ sevm b G0) + 848 + sfxCost3 sevm (frameQ sevm b G0) + 818 +
      sfxCost2 sevm (frameQ sevm b G0) + 938 + sfxCost1 sevm (frameQ sevm b G0) + 1032) := by
    rw [← hgasQ']
    exact St.self hQst hQmem
  have hsfx := createPair_suffix (b := frameQ sevm b G0) (G := frameGf sevm b G0) hfork hstatic
    hv2Q hGf
  rw [← e] at hsfx
  exact hsfx

/-! ## The frame -/

theorem getStorVal_afterSstoreH_ite (sevm : Sevm) (base : Devm) (key value k : B256) :
    (afterSstoreH sevm base key value).getStorVal sevm.currentTarget k =
      if key = k then value else base.getStorVal sevm.currentTarget k := by
  show (Devm.getStor _ _).get _ = _
  rw [afterSstoreH_getStor_self, Stor.get_set_ite]
  rfl

theorem sfxMerge_ne_zero (x : B256) : sfxMerge x ≠ 0 := by
  obtain ⟨⟨hh, hl⟩, ⟨lh, ll⟩⟩ := x
  intro h
  have h' := congrArg (fun z : B256 => z.2.2) h
  change ((0x85b44281ec28c9dc : UInt64) ||| ((0 : UInt64) &&& ll)) = 0 at h'
  rw [UInt64.zero_and, UInt64.or_zero] at h'
  exact absurd h' (by decide)

/-- The factory's storage words a store reads either were zero at the transaction's start or are
non-zero now, at each of the suffix's four stores, when the factory's storage at the frame's start
is the transaction-start snapshot and `getPair[USDC][WETH]` is unset there. -/
theorem sfx_refund_conditions {sevm : Sevm} {b q : Devm}
    (horig : ∀ k, getOrigStorVal sevm sevm.currentTarget k = b.getStorVal sevm.currentTarget k)
    (hq : ∀ k, q.getStorVal sevm.currentTarget k = b.getStorVal sevm.currentTarget k)
    (hv1 : b.getStorVal sevm.currentTarget fk2 = 0) :
    ((sfxB1 sevm q).getOrigStorVal sevm sevm.currentTarget fk2 = 0 ∨
      (sfxB1 sevm q).getStorVal sevm.currentTarget fk2 ≠ 0) ∧
    ((sfxB3 sevm q).getOrigStorVal sevm sevm.currentTarget fk5 = 0 ∨
      (sfxB3 sevm q).getStorVal sevm.currentTarget fk5 ≠ 0) ∧
    ((sfxB5 sevm q).getOrigStorVal sevm sevm.currentTarget 3 = 0 ∨
      (sfxB5 sevm q).getStorVal sevm.currentTarget 3 ≠ 0) ∧
    ((sfxB7 sevm q).getOrigStorVal sevm sevm.currentTarget (sfxSlot sevm q) = 0 ∨
      (sfxB7 sevm q).getStorVal sevm.currentTarget (sfxSlot sevm q) ≠ 0) := by
  -- an original word is zero when the frame-start word is
  have orig0 : ∀ (d : Devm) (k : B256), b.getStorVal sevm.currentTarget k = 0 →
      d.getOrigStorVal sevm sevm.currentTarget k = 0 := fun d k hk => by
    unfold Devm.getOrigStorVal
    split
    · rfl
    · rw [horig, hk]
  -- the current word at the frame's other keys, through the two mapping stores
  have cur4 : ∀ k, (sfxB4 sevm q).getStorVal sevm.currentTarget k =
      if fk5 = k then sfxMerge (sfxW10 sevm q)
      else if fk2 = k then (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) else b.getStorVal sevm.currentTarget k := fun k => by
    rw [show sfxB4 sevm q = afterSstoreH sevm (sfxB3 sevm q) fk5 (sfxMerge (sfxW10 sevm q)) from rfl,
      getStorVal_afterSstoreH_ite]
    split
    · rfl
    · rw [show sfxB3 sevm q = afterSloadH sevm (sfxB2 sevm q) fk5 from rfl, getStorVal_afterSloadH,
        show sfxB2 sevm q = afterSstoreH sevm (sfxB1 sevm q) fk2 (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) from rfl,
        getStorVal_afterSstoreH_ite]
      split
      · rfl
      · rw [show sfxB1 sevm q = afterSloadH sevm q fk2 from rfl, getStorVal_afterSloadH, hq]
  -- the clean-or-nonzero case split for one key whose current word is `cur`
  have split4 : ∀ (d : Devm) (k : B256), d.getStorVal sevm.currentTarget k =
      (sfxB4 sevm q).getStorVal sevm.currentTarget k →
      d.getOrigStorVal sevm sevm.currentTarget k = 0 ∨ d.getStorVal sevm.currentTarget k ≠ 0 :=
    fun d k hd => by
      rw [hd, cur4]
      split
      · exact Or.inr (sfxMerge_ne_zero _)
      · split
        · exact Or.inr (by decide)
        · by_cases hz : b.getStorVal sevm.currentTarget k = 0
          · exact Or.inl (orig0 d k hz)
          · exact Or.inr hz
  refine ⟨Or.inl (orig0 _ _ hv1), ?_, ?_, ?_⟩
  · by_cases hz : b.getStorVal sevm.currentTarget fk5 = 0
    · exact Or.inl (orig0 _ _ hz)
    · right
      rw [show sfxB3 sevm q = afterSloadH sevm (sfxB2 sevm q) fk5 from rfl,
        getStorVal_afterSloadH,
        show sfxB2 sevm q = afterSstoreH sevm (sfxB1 sevm q) fk2
          (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256) from rfl,
        getStorVal_afterSstoreH_ite]
      split
      · decide
      · rw [show sfxB1 sevm q = afterSloadH sevm q fk2 from rfl,
          getStorVal_afterSloadH, hq]
        exact hz
  · exact split4 _ 3 (by
      rw [show sfxB5 sevm q = afterSloadH sevm (sfxB4 sevm q) 3 from rfl, getStorVal_afterSloadH])
  · have h7 : (sfxB7 sevm q).getStorVal sevm.currentTarget (sfxSlot sevm q) =
        if (3 : B256) = sfxSlot sevm q then sfxN sevm q + 1
        else (sfxB4 sevm q).getStorVal sevm.currentTarget (sfxSlot sevm q) := by
      rw [show sfxB7 sevm q = afterSloadH sevm (sfxB6 sevm q) (sfxSlot sevm q) from rfl,
        getStorVal_afterSloadH,
        show sfxB6 sevm q = afterSstoreH sevm (sfxB5 sevm q) 3 (sfxN sevm q + 1) from rfl,
        getStorVal_afterSstoreH_ite]
      split
      · rfl
      · rw [show sfxB5 sevm q = afterSloadH sevm (sfxB4 sevm q) 3 from rfl,
          getStorVal_afterSloadH]
    by_cases h3 : (3 : B256) = sfxSlot sevm q
    · right
      rw [h7, ite_eq_left_iff.mpr (fun h => absurd h3 h)]
      intro hz
      have e1 := congrArg B256.toNat hz
      have e2 := congrArg B256.toNat h3
      unfold sfxSlot at e2
      rw [B256.toNat_add] at e1 e2
      unfold Nat.lo at e1 e2
      have hn := (sfxN sevm q).toNat_lt
      revert e1 e2 hn
      generalize (sfxN sevm q).toNat = n
      intro e1 e2 hn
      simp only [show (1 : B256).toNat = 1 from rfl, show (0 : B256).toNat = 0 from rfl,
        show (3 : B256).toNat = 3 from rfl,
        show (0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b : B256).toNat =
          0xc2575a0e9e593c00f959f8c92f12db2869c3395a3b0502d05e2516446f71f85b from rfl] at e1 e2
      omega
    · exact split4 _ _ (by rw [h7, ite_eq_right_iff.mpr (fun h => absurd h h3)])

theorem create2Prepared_state (sevm : Sevm) (b : Devm) (S : List B256) (M : Mem) (G : Nat)
    (i sz : B256) (addr : Adr) :
    (create2Prepared sevm b S M G i sz addr).state = b.state.incrNonce sevm.currentTarget := rfl

theorem returnPost_meta (d : Devm) (i sz : B256) (S : List B256) :
    (returnPost d i sz S).accountsToDelete = d.accountsToDelete ∧
    (returnPost d i sz S).refundCounter = d.refundCounter ∧
    (returnPost d i sz S).state = d.state := ⟨rfl, rfl, returnPost_state d i sz S⟩

/-- **The `createPair(WETH, USDC)` frame at Muir Glacier.**  A frame running the certified factory
runtime at the factory address with the recorded calldata, no value, positive depth and at least
2,600,000 gas (below `2^64`), from a world `b` holding the factory code there with a nonce below the
maximum, a Pair `CREATE2` address with nonce zero and no code, `getPair[USDC][WETH]` unset, and the factory's
storage equal to the transaction-start snapshot, runs to a machine with the frame's error, the
certified Pair runtime at the Pair address, storage at the initialized checkpoint over the factory,
the domain separator of the frame's chain id and the Pair address, and the sorted tokens; the Pair
address is not added to the accounts to delete, and the refund counter stays non-negative.
No new account deletion is scheduled, and every account other than the factory and Pair is unchanged. -/
theorem createPair_frame_effects {sevm : Sevm} {b : Devm} {G0 : Nat}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hcode : sevm.code = code)
    (htarget : sevm.currentTarget = UniswapV2Pair.Creation.factory)
    (hvalue : sevm.value = 0) (hdata : sevm.data = createPairData)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hinstalled : b.state.getCode sevm.currentTarget = code)
    (hempty : Create2TargetNoCollision b UniswapV2Pair.Creation.pairAddress)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hv1 : b.getStorVal sevm.currentTarget fk2 = 0)
    (horig : ∀ k, getOrigStorVal sevm sevm.currentTarget k = b.getStorVal sevm.currentTarget k)
    (hG : 2600000 ≤ G0) (hG64 : G0 < 2 ^ 64) :
    ∃ post, SProg.RunExact cert.prog sevm (St b [] Mem.empty G0) post ∧
      post.error = b.error ∧
      (post.getCode UniswapV2Pair.Creation.pairAddress).toList = UniswapV2Pair.code.toList ∧
      UniswapV2Pair.InitializedCheckpoint (post.getStor UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.factory
        (UniswapV2Pair.Creation.domainSeparator sevm.benvStat.chainId.toB256
          UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1 ∧
      (∀ a, a ∉ b.accountsToDelete → a ∉ post.accountsToDelete) ∧
      (0 ≤ b.refundCounter → 0 ≤ post.refundCounter) ∧
      (∀ a, a ≠ sevm.currentTarget → a ≠ UniswapV2Pair.Creation.pairAddress →
        post.state.get a = b.state.get a) := by
  have rules := muirRules hfork
  have hflat5 : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 5000 := fun g h => by
    rw [rules, show (Fork.ruleSet .muirGlacier).access = .flat istanbulAccessGas from rfl] at h
    cases h
    decide
  have hflat : ∀ g, sevm.benvStat.rules.access = .flat g → g.sload ≤ 2100 := fun g h => by
    rw [rules, show (Fork.ruleSet .muirGlacier).access = .flat istanbulAccessGas from rfl] at h
    cases h
    decide
  have htne : sevm.currentTarget ≠ UniswapV2Pair.Creation.pairAddress := by
    rw [htarget]; decide
  have hsrd : sevm.benvStat.rules.settle.selfdestructRefund ≠ 0 := by rw [rules]; decide
  -- the worlds
  set B1 := afterSloadH sevm b fk2 with hB1
  set Y := G0 - 225 - 3920 - 34184 with hY
  set P := frameP sevm b G0 with hP
  have hPdef : P = pairCreate2Post sevm B1 belowCreate2 Y := rfl
  obtain ⟨-, -, hPgas, hPerr, hPstate, hPatd, hPrc, hPca⟩ :=
    pairCreate2Post_facts sevm B1 belowCreate2 Y
  obtain ⟨hCcode, hCstor, hCkeep, hCatd, hCrc, hCcreated⟩ :=
    pairChild_facts (b := B1) (S := belowCreate2) (Y := Y) hflat5
  obtain ⟨-, -, -, -, -, -, hCDatd, -⟩ := pairCtor_facts sevm B1 belowCreate2 Y
  have hcost := pairCtorCost_le hfork B1 belowCreate2 Y
  have hB1state : B1.state = b.state := afterSloadH_state _ _ _
  -- the factory's account in `P`
  have hfacP : ∀ k, P.getStorVal sevm.currentTarget k = b.getStorVal sevm.currentTarget k := by
    intro k
    show ((P.state.get sevm.currentTarget).stor).get k = ((b.state.get sevm.currentTarget).stor).get k
    rw [hPdef, hPstate, hCkeep _ htne, hB1state, State.incrNonce_get_stor]
    split_ifs with hcond
    · exfalso
      obtain ⟨-, hE⟩ := hcond
      have hsz : (b.state.get sevm.currentTarget).code.size = 0 := hE.1
      rw [show (b.state.get sevm.currentTarget).code = b.state.getCode sevm.currentTarget from rfl,
        hinstalled, ByteArray.size_eq_length_toList, code_toList_length] at hsz
      exact absurd hsz (by decide)
    · rfl
  -- gas through `CREATE2`
  have hPgas' : P.gasLeft = (Y - except64th Y) +
      (except64th Y - pairCtorCost sevm B1 belowCreate2 Y - 2258600) := by
    rw [hPdef, hPgas]; rfl
  have he64Y : 2510454 - 2510454 / 64 ≤ except64th Y := by unfold except64th; omega
  set X := frameX sevm b G0 with hX
  have hXdef : X = P.gasLeft - 883 - 2 := rfl
  have hXb : 170969 ≤ X := by rw [hXdef, hPgas']; unfold except64th at *; omega
  have hX64 : X < 2 ^ 256 := by rw [hXdef, hPgas']; unfold except64th at *; omega
  -- the `initialize` call
  set Q := frameQ sevm b G0 with hQ
  have hQdef : Q = initCallPost sevm P belowCall X := rfl
  obtain ⟨-, -, hQgas, hQerr, hQstate, hQatd, hQrc⟩ := initCallPost_facts sevm P belowCall X
  have hcreatedP : UniswapV2Pair.Creation.pairAddress ∈ P.createdAccounts := by
    rw [hPdef, hPca]; exact hCcreated
  obtain ⟨hIcode, hIkeep, hIatd, hIrc⟩ := initChild_facts (b := P) (S := belowCall) (X := X)
    hflat5 hcreatedP
  have hcharge : initCallCharge sevm P belowCall X ≤ 72600 :=
    UniswapV2Pair.initializeStorageChargeH_le _ hflat
  have hgasQ : initCallCharge sevm P belowCall X + 377 + 2400 ≤ except64th (X - 700) := by
    unfold except64th; omega
  have hcodeP : P.state.getCode UniswapV2Pair.Creation.pairAddress = UniswapV2Pair.code := by
    rw [hPdef, hPstate]; exact hCcode
  have hstorP : P.getStor UniswapV2Pair.Creation.pairAddress =
      UniswapV2Pair.Creation.ctorStor sevm.benvStat.chainId.toB256
        UniswapV2Pair.Creation.pairAddress UniswapV2Pair.Creation.factory Stor.empty := by
    rw [← htarget]
    show (P.state.get _).stor = _
    rw [hPdef, hPstate]; exact hCstor
  -- the factory's storage in `Q`
  have hq : ∀ k, Q.getStorVal sevm.currentTarget k = b.getStorVal sevm.currentTarget k := by
    intro k
    show ((Q.state.get sevm.currentTarget).stor).get k = _
    rw [hQdef, hQstate, hIkeep _ htne]
    exact hfacP k
  -- the suffix
  have hc1 := sstoreCostH_le (sevm := sevm) (devm := sfxB1 sevm Q) (key := fk2)
    (value := (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256)) hflat
  have hc2 := sstoreCostH_le (sevm := sevm) (devm := sfxB3 sevm Q) (key := fk5)
    (value := sfxMerge (sfxW10 sevm Q)) hflat
  have hc3 := sstoreCostH_le (sevm := sevm) (devm := sfxB5 sevm Q) (key := 3)
    (value := sfxN sevm Q + 1) hflat
  have hc4 := sstoreCostH_le (sevm := sevm) (devm := sfxB7 sevm Q) (key := sfxSlot sevm Q)
    (value := sfxMerge (sfxWAll sevm Q)) hflat
  have hsfx : sfxCost sevm Q ≤ 6540 + 4 * 22100 := by
    unfold sfxCost sfxCost1 sfxCost2 sfxCost3 sfxCost4; omega
  have hQgasL : Q.gasLeft = X - (except64th (X - 700) + 700 + 0) +
      (except64th (X - 700) - initCallCharge sevm P belowCall X - 377) := by
    rw [hQdef]; exact hQgas
  have hQgas' : sfxCost sevm Q + 2300 + 52 ≤ Q.gasLeft := by
    rw [hQgasL]; unfold except64th at *; omega
  obtain ⟨h1, h2, h3, h4⟩ := sfx_refund_conditions horig hq hv1
  -- the run
  have hnonceB1 : ((afterSloadH sevm b fk2).state.get sevm.currentTarget).nonce ≠ UInt64.max := by
    rw [afterSloadH_state]; exact hnonce
  have hfresh : Create2TargetNoCollision (create2Prepared sevm (afterSloadH sevm b fk2) belowCreate2 fm12
      (G0 - 225 - 3920 - 34184) 0xa0 0x2d74 UniswapV2Pair.Creation.pairAddress) UniswapV2Pair.Creation.pairAddress := by
    have hget : (create2Prepared sevm (afterSloadH sevm b fk2) belowCreate2 fm12
        (G0 - 225 - 3920 - 34184) 0xa0 0x2d74 UniswapV2Pair.Creation.pairAddress).state.get UniswapV2Pair.Creation.pairAddress = b.state.get UniswapV2Pair.Creation.pairAddress := by
      rw [create2Prepared_state]
      unfold State.incrNonce
      rw [State.setAccount_get_ne _ htne, afterSloadH_state]
    unfold Create2TargetNoCollision
    rw [hget]
    exact hempty
  have hsizeP : ((P.getCode (0xb4e16d0168e52d35cacd2c6185b44281ec28c9dc : B256).toAdr).size.toB256 =
      0x2c1d) := by
    rw [pairAddress_word_toAdr]
    show (P.state.getCode UniswapV2Pair.Creation.pairAddress).size.toB256 = _
    rw [hcodeP, ByteArray.size_eq_length_toList, ← UniswapV2Pair.Creation.runtimeWindow_eq,
      UniswapV2Pair.Creation.runtimeWindow_length]
    rfl
  have hrun := createPair_frame_run (b := b) (G0 := G0) (chainWord := sevm.benvStat.chainId.toB256)
    hfork hcode htarget hvalue hdata hstatic hdepth hv1 hnonceB1 hfresh (by omega)
    (by unfold except64th; omega) hcodeP hstorP hsizeP
    (by show 885 ≤ P.gasLeft; rw [hPgas']; unfold except64th at *; omega) hX64 (by omega) hgasQ
    ((hq fk2).trans hv1) hQgas'
  -- the final machine's account at the Pair address is the `initialize` child's
  have hpost : ∀ a, a ≠ sevm.currentTarget →
      (framePost sevm b G0).state.get a = (initChild sevm P belowCall X).state.get a := by
    intro a ha
    rw [framePost, returnPost_state]
    show (sfxB10 sevm Q).state.get a = _
    rw [sfxB10_state_ne sevm Q ha, hQdef, hQstate]
  refine ⟨framePost sevm b G0, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [framePost, (returnPost_facts _ _ _ _).2.1, St_error]
    show (sfxB10 sevm Q).error = _
    rw [sfxB10_error, hQdef, hQerr, hPdef, hPerr, hB1]
    exact afterSloadH_error _ _ _
  · show (((framePost sevm b G0).state.get UniswapV2Pair.Creation.pairAddress).code).toList = _
    rw [hpost _ (Ne.symm htne)]
    show ((initChild sevm P belowCall X).getCode UniswapV2Pair.Creation.pairAddress).toList = _
    rw [hIcode]
    show (P.state.getCode UniswapV2Pair.Creation.pairAddress).toList = _
    rw [hcodeP]
  · have hstor : Devm.getStor (framePost sevm b G0) UniswapV2Pair.Creation.pairAddress =
        Devm.getStor (initChild sevm P belowCall X) UniswapV2Pair.Creation.pairAddress := by
      show ((framePost sevm b G0).state.get UniswapV2Pair.Creation.pairAddress).stor = _
      rw [hpost _ (Ne.symm htne)]
      rfl
    rw [hstor]
    obtain ⟨run⟩ := initChild_exec (b := P) (S := belowCall) (X := X) hfork hstatic htarget hcodeP
      hstorP hgasQ
    have hib := St.self (d := initDevm (initCallMsg sevm P belowCall X)) (S := []) (M := Mem.empty)
      rfl rfl
    rw [hib] at run
    have hdata := initCallMsg_data sevm P belowCall X
    have hck := (UniswapV2Pair.Creation.pair_initializedH
      (chainWord := sevm.benvStat.chainId.toB256) (factory := UniswapV2Pair.Creation.factory)
      (sevm := initSevm (initCallMsg sevm P belowCall X))
      (b := initDevm (initCallMsg sevm P belowCall X))
      (by show Devm.getStor P UniswapV2Pair.Creation.pairAddress = _; exact hstorP)
      (by show (initCallMsg sevm P belowCall X).data.length < _; rw [hdata]; decide) rfl
      (by show P.state.getCode UniswapV2Pair.Creation.pairAddress = _; exact hcodeP)
      (by show sevm.benvStat.rules.stateGas = none; rw [rules]; rfl)
      (by
        show Bytes.toB256 ((initCallMsg sevm P belowCall X).data.sliceD (0 : B256).toNat 32 0) >>>
          224 = _
        rw [hdata]; decide) run).2
    have ht0 : UniswapV2Pair.initializeToken0 (initSevm (initCallMsg sevm P belowCall X)) =
        UniswapV2Pair.Creation.token0 := by
      show (Bytes.toB256 ((initCallMsg sevm P belowCall X).data.sliceD (4 : B256).toNat 32 0)).toAdr = _
      rw [hdata]; decide
    have ht1 : UniswapV2Pair.initializeToken1 (initSevm (initCallMsg sevm P belowCall X)) =
        UniswapV2Pair.Creation.token1 := by
      show (Bytes.toB256 ((initCallMsg sevm P belowCall X).data.sliceD (36 : B256).toNat 32 0)).toAdr = _
      rw [hdata]; decide
    rw [ht0, ht1] at hck
    exact hck
  · intro a hb hmem
    have hatd : (framePost sevm b G0).accountsToDelete = Q.accountsToDelete := by
      rw [framePost, (returnPost_meta _ _ _ _).1]
      exact sfxB10_accountsToDelete sevm Q
    rw [hatd, hQdef, hQatd, hIatd, ite_eq_right hsrd] at hmem
    have hP : a ∉ P.accountsToDelete := by
      rw [hPdef, hPatd, hCatd, hCDatd, ite_eq_right hsrd]
      intro h
      rcases Std.HashSet.mem_union_iff.mp h with h | h <;>
        (rw [hB1, afterSloadH_accountsToDelete] at h; exact hb h)
    rcases Std.HashSet.mem_union_iff.mp hmem with h | h <;> exact hP h
  · intro hb
    have hrc : Q.refundCounter ≤ (framePost sevm b G0).refundCounter := by
      rw [framePost, (returnPost_meta _ _ _ _).2.1]
      exact sfxB10_refundCounter_ge sevm Q hflat5 h1 h2 h3 h4
    have hQr : Q.refundCounter = P.refundCounter + (initChild sevm P belowCall X).refundCounter := by
      rw [hQdef]; exact hQrc
    have hPr : P.refundCounter = B1.refundCounter + (pairChild sevm B1 belowCreate2 Y).refundCounter := by
      rw [hPdef]; exact hPrc
    have hB1r : B1.refundCounter = b.refundCounter := afterSloadH_refundCounter _ _ _
    omega

  · intro a otherFactory otherPair
    rw [hpost a otherFactory, hIkeep a otherPair, hPdef, hPstate,
      hCkeep a otherPair, hB1state]
    unfold State.incrNonce
    exact State.setAccount_get_ne _ (Ne.symm otherFactory) _

/-- Compatibility projection of the full creation-frame effects. -/
theorem createPair_frame {sevm : Sevm} {b : Devm} {G0 : Nat}
    (hfork : sevm.benvStat.fork = .muirGlacier) (hcode : sevm.code = code)
    (htarget : sevm.currentTarget = UniswapV2Pair.Creation.factory)
    (hvalue : sevm.value = 0) (hdata : sevm.data = createPairData)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hinstalled : b.state.getCode sevm.currentTarget = code)
    (hempty : Create2TargetNoCollision b UniswapV2Pair.Creation.pairAddress)
    (hnonce : (b.state.get sevm.currentTarget).nonce ≠ UInt64.max)
    (hv1 : b.getStorVal sevm.currentTarget fk2 = 0)
    (horig : ∀ k, getOrigStorVal sevm sevm.currentTarget k = b.getStorVal sevm.currentTarget k)
    (hG : 2600000 ≤ G0) (hG64 : G0 < 2 ^ 64) :
    ∃ post, SProg.RunExact cert.prog sevm (St b [] Mem.empty G0) post ∧
      post.error = b.error ∧
      (post.getCode UniswapV2Pair.Creation.pairAddress).toList = UniswapV2Pair.code.toList ∧
      UniswapV2Pair.InitializedCheckpoint (post.getStor UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.factory
        (UniswapV2Pair.Creation.domainSeparator sevm.benvStat.chainId.toB256
          UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1 ∧
      (UniswapV2Pair.Creation.pairAddress ∉ b.accountsToDelete →
        UniswapV2Pair.Creation.pairAddress ∉ post.accountsToDelete) ∧
      (0 ≤ b.refundCounter → 0 ≤ post.refundCounter) := by
  obtain ⟨post, run, err, installed, initialized, notDeleted, refund, _⟩ :=
    createPair_frame_effects hfork hcode htarget hvalue hdata hstatic hdepth hinstalled
      hempty hnonce hv1 horig hG hG64
  exact ⟨post, run, err, installed, initialized,
    notDeleted UniswapV2Pair.Creation.pairAddress, refund⟩

end Blanc.Lift.UniswapV2Factory
