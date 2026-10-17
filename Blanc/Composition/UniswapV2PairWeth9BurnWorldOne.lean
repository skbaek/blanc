import Blanc.Composition.UniswapV2PairWeth9BurnEnvOne
import Blanc.Composition.UniswapV2PairWeth9BurnWorld
import Blanc.Composition.UniswapV2PairWeth9XLegStatic

/-!
# C4(b): Burn's worlds for the WETH9 = token1 legs (U8h)

With WETH9 as token1, Burn pays X = token0 first, at the suffix's entry world `burnBodyWorld`, and
WETH9's transfer after it is discharged by the X-leg quiescence (`burnWethLeg1_spec_afterX`), which
reads at the entry world: WETH9's code, footprint and the ether-supply bound, and the Pair's storage
representing a **locked** model state.  This module supplies them:

* `WethFootAt` — WETH9's code, footprint over `U` and the supply bound at one world, carried across
  the Pair's own steps (`BalKeeps`: they move no ether) and across the `STATICCALL`s Burn makes before
  the transfer (X's initial query, the factory `feeTo` query) under HASH-T over those children's
  WETH9 keys (`static_foot`);
* `burnPriced_lockedRep` — the Pair's storage at the entry world represents the model state after the
  fee mint and the LP burn, from the locked representation at the second initial query's result (the
  prefix of `burnFeePricing_exact`, keeping the representation instead of the run).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Joint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair
open Blanc.Composition.UniswapV2PairWeth9XLeg (StaticChildFresh wethRunKeys static_foot)

/-! ## Ether across the Pair's own steps -/

/-- `post` has `pre`'s ether balances and every account's code: a step of the Pair's own that moves
no ether and installs no code. -/
def BalKeeps (pre post : Devm) : Prop :=
  post.state.bal = pre.state.bal ∧ ∀ a, post.state.getCode a = pre.state.getCode a

namespace BalKeeps

theorem refl (d : Devm) : BalKeeps d d := ⟨rfl, fun _ => rfl⟩

theorem trans {a b c : Devm} (h : BalKeeps a b) (h' : BalKeeps b c) : BalKeeps a c :=
  ⟨h'.1.trans h.1, fun x => (h'.2 x).trans (h.2 x)⟩

theorem ofState {a b : Devm} (h : b.state = a.state) : BalKeeps a b := by
  unfold BalKeeps
  rw [h]
  exact ⟨rfl, fun _ => rfl⟩

theorem afterSload (sevm : Sevm) (b : Devm) (k : B256) : BalKeeps b (Blanc.afterSload sevm b k) :=
  ofState (by unfold Blanc.afterSload; split <;> rfl)

theorem afterSstore (sevm : Sevm) (b : Devm) (k v : B256) :
    BalKeeps b (Blanc.afterSstore sevm b k v) :=
  ⟨funext fun a => afterSstore_getBal a, fun a => afterSstore_getCode sevm b k v a⟩

theorem addLog (b : Devm) (l : Log) : BalKeeps b (b.addLog l) := refl b

theorem ofSt (b : Devm) (S : List B256) (M : Mem) (g : Nat) : BalKeeps b (St b S M g) := refl b

theorem access (b : Devm) (a : Adr) : BalKeeps b (temporalAccountAccessBase b a) :=
  ofState (temporalAccountAccessBase_state b a)

theorem lpMintPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (toWord value : B256)
    (G : Nat) : BalKeeps b (UniswapV2Pair.lpMintPost sevm b R M toWord value G) := by
  unfold UniswapV2Pair.lpMintPost lpMintSupplyPost lpMintCreditPost lpMintCreditBase
    lpMintSupplyBase
  exact ((((afterSload sevm b 0).trans (afterSstore sevm _ 0 _)).trans
    (afterSload sevm _ _)).trans (afterSstore sevm _ _ _)).trans (addLog _ _) |>.trans
    (ofSt _ _ _ _)

theorem feeBranchPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (K x r0 r1 : B256)
    (G : Nat) : BalKeeps b (UniswapV2Pair.feeBranchPost sevm b R M K x r0 r1 G) := by
  unfold UniswapV2Pair.feeBranchPost
  split
  · refine BalKeeps.trans ?_ (ofSt _ _ _ _)
    unfold feeOffWorld
    split
    · exact refl b
    · exact afterSstore sevm b 11 0
  · unfold feeOnPost
    split
    · exact ofSt b _ _ _
    · split
      · unfold feeGrowthPost feeLiquidityPost
        refine (afterSload sevm b 0).trans ?_
        split
        · exact ofSt _ _ _ _
        · exact lpMintPost sevm _ _ _ _ _ _
      · exact ofSt b _ _ _

theorem lpBurnPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (fromWord value : B256)
    (G : Nat) : BalKeeps b (UniswapV2Pair.lpBurnPost sevm b R M fromWord value G) := by
  unfold UniswapV2Pair.lpBurnPost lpBurnBalancePost lpBurnSupplyPost lpBurnSupplyBase
    lpBurnBalanceBase
  exact ((((afterSload sevm b _).trans (afterSstore sevm _ _ _)).trans
    (afterSload sevm _ 0)).trans (afterSstore sevm _ 0 _)).trans (addLog _ _) |>.trans
    (ofSt _ _ _ _)

end BalKeeps

/-- Burn's prefix up to the first initial query moves no ether and keeps every code. -/
theorem burnCall0World_bal (sevm : Sevm) (b : Devm) : BalKeeps b (burnCall0World sevm b) := by
  unfold burnCall0World burnTokensWorld burnReservedWorld burnLockedWorld
  exact (((((BalKeeps.afterSload sevm b 12).trans (BalKeeps.afterSstore sevm _ 12 0)).trans
    (BalKeeps.afterSload sevm _ 8)).trans (BalKeeps.afterSload sevm _ 6)).trans
    (BalKeeps.afterSload sevm _ 7)).trans (BalKeeps.access _ _)

/-- From the second initial query's result to the factory `STATICCALL`'s staged world. -/
theorem feeFactoryCallWorld_keeps {w : Adr} (sevm : Sevm) (d1 : Devm) :
    WethKeeps w d1 (feeFactoryCallWorld sevm (feeBurnWorld sevm d1)) ∧
      BalKeeps d1 (feeFactoryCallWorld sevm (feeBurnWorld sevm d1)) :=
  ⟨((WethKeeps.afterSload sevm d1 _).trans (WethKeeps.afterSload sevm _ 5)).trans
      (WethKeeps.access _ _),
    ((BalKeeps.afterSload sevm d1 _).trans (BalKeeps.afterSload sevm _ 5)).trans
      (BalKeeps.access _ _)⟩

/-- From the factory query's result to the suffix's entry world. -/
theorem burnBodyWorld_fromF {w : Adr} (sevm : Sevm) (b d0 d1 dF : Devm)
    (ne : sevm.currentTarget ≠ w) :
    WethKeeps w dF (burnBodyWorld sevm b d0 d1 dF) ∧ BalKeeps dF (burnBodyWorld sevm b d0 d1 dF) := by
  rw [burnBodyWorld_def]
  unfold burnPricedWorld burnFeeWorld
  exact ⟨(((WethKeeps.afterSload sevm dF 11).trans
      (WethKeeps.feeBranchPost ne _ _ _ _ _ _ _ _)).trans (WethKeeps.afterSload sevm _ 0)).trans
      (WethKeeps.lpBurnPost ne _ _ _ _ _ _),
    (((BalKeeps.afterSload sevm dF 11).trans (BalKeeps.feeBranchPost sevm _ _ _ _ _ _ _ _)).trans
      (BalKeeps.afterSload sevm _ 0)).trans (BalKeeps.lpBurnPost sevm _ _ _ _ _ _)⟩

/-! ## WETH9's footprint at a world -/

/-- WETH9's code, its footprint over `U` and the ether-supply bound at `d`. -/
structure WethFootAt (weth : Adr) (U : Weth9.Key → Prop) (d : Devm) : Prop where
  code : d.state.getCode weth = Weth9.code
  foot : Weth9.FootInv U (d.state.getStor weth) (d.state.bal weth)
  bound : sum d.state.bal < 2 ^ 256

namespace WethFootAt

variable {weth : Adr} {U : Weth9.Key → Prop}

theorem keeps {a b : Devm} (h : WethFootAt weth U a) (keeps : WethKeeps weth a b)
    (bal : BalKeeps a b) : WethFootAt weth U b := by
  have stor : b.state.getStor weth = a.state.getStor weth := keeps.2
  have code : b.state.getCode weth = a.state.getCode weth := keeps.1
  have bal' : b.state.bal = a.state.bal := bal.1
  exact ⟨code.trans h.code, by rw [stor, bal']; exact h.foot, by rw [bal']; exact h.bound⟩

theorem static {sevm : Sevm} {devm d : Devm} (h : WethFootAt weth U devm)
    (run : Ninst.RunCompiled sevm devm (.exec .staticcall) d)
    (fork : CoveredFork sevm.benvStat.fork) (targetNe : sevm.currentTarget ≠ weth)
    (callee : ∀ g c rest, devm.stack = g :: c :: rest → c.toAdr ≠ weth)
    (fresh : StaticChildFresh sevm devm fun D => Weth9.KeysFresh U (wethRunKeys weth D)) :
    WethFootAt weth U d := by
  obtain ⟨code, foot, bound⟩ := static_foot run fork targetNe callee h.code h.foot h.bound fresh
  exact ⟨code, foot, bound⟩

end WethFootAt

/-! ## The locked representation at the suffix's entry world -/

theorem feeBranchSourceFee_factory (st : UniswapV2Pair.State) (sevm : Sevm) (b : Devm) (w r0 r1 : B256) :
    (feeBranchSourceFee st sevm b w r0 r1).state.factory = st.factory := by
  unfold feeBranchSourceFee
  split
  · rfl
  · split
    · rfl
    · split
      · unfold feeGrowthSourceFee
        split <;> rfl
      · rfl

/-- **The Pair's storage after the fee mint and the LP burn.**  From the representation of `st` at
the second initial query's result `d1`, the factory record, and the model's fee acceptance at the
factory's actual answer: at Burn's priced world the Pair's storage represents a state with `st`'s
lock and factory, over rows inside any universe holding `K`, the fee recipient's LP row and the
Pair's own LP row; and the priced `amount1` word is at most the second answer. -/
theorem burnPriced_lockedRep {K : WriterKey → Prop} {st post : UniswapV2Pair.State}
    {fee : FeeResult} {events : List Event} {amount0 amount1 : Nat} {sevm : Sevm} {d1 dF : Devm} {M : Mem} {b0 t1 t0 r1 r0 toWord extρ : B256} {R : List B256}
    {Gp : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M) (room : R.length ≤ 990)
    (rep : WriterRep K (d1.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget)) (nonstatic : sevm.isStatic = false)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (c : BurnFeeCallee sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp)
    (accepted : mintFee st (Bytes.toB256 (dF.returnData.take 32)).toAdr r0.toNat r1.toNat = .ok fee)
    (fresh : FeeMintFresh K st sevm (feeKLastWorld sevm dF) (Bytes.toB256 (dF.returnData.take 32))
      r0 r1)
    (priced : burnAmounts (st.balanceOf sevm.currentTarget) b0 (feeBurnBalance1 M)
      fee.state.totalSupply = .ok (amount0, amount1))
    (burned : fee.state.burnLP sevm.currentTarget (st.balanceOf sevm.currentTarget) =
      .ok (post, events)) :
    (burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).amount1 ≤ feeBurnBalance1 M ∧
    ∃ (Kb : WriterKey → Prop) (stb : UniswapV2Pair.State),
      WriterRep Kb ((burnPricedWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R).getStor
        sevm.currentTarget) stb ∧
      stb.unlocked = st.unlocked ∧ stb.factory = st.factory ∧
      ∀ U : WriterKey → Prop, (∀ k, K k → U k) →
        U (.balance (Bytes.toB256 (dF.returnData.take 32)).toAdr) →
        U (.balance sevm.currentTarget) → ∀ k, Kb k → U k := by
  let FL := burnFeeLocalsAt sevm d1 M b0 t1 t0 r1 r0 toWord extρ R
  let w := Bytes.toB256 (dF.returnData.take 32)
  let GF := burnFeeResidual sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R Gp
  have rep' : WriterRep K ((feeBurnWorld sevm d1).getStor sevm.currentTarget) st := by
    simpa only [feeBurnWorld, afterSload_getStor] using rep
  have postCall := feeFactoryCompiled_post fork c.call c.success
  have postRep := rep'.fee_factory_post postCall
  have last : feeKLastWord sevm dF = st.kLast := by
    rcases postRep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, lastWord, _⟩
    change (dF.getStor sevm.currentTarget).get 11 = st.kLast
    simpa only [feeKLastWorld, afterSload_getStor] using lastWord
  have sentries := c.sentries
  have returnedGas := c.returnedGas
  rw [last] at sentries returnedGas
  have input : FeeMintForwardInput K st sevm (feeBurnWorld sevm d1) dF FL
      (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 GF c.factoryGas fee :=
    ⟨fork, feeBurnMemory_ptr mem sevm.currentTarget, rep', bound0, bound1,
      by simp only [FL, burnFeeLocalsAt, burnFeeLocals, List.length_cons]; omega,
      c.code, c.call, c.success, c.width, accepted, fresh,
      ⟨⟨fun _ _ => nonstatic, fun _ _ _ _ => nonstatic⟩, sentries.clearSentry,
        sentries.supplySentry, sentries.creditSentry⟩,
      by rw [returnedGas]; rfl⟩
  obtain ⟨_, source, feeEq⟩ := input.exact
  let bF0 := burnFeeWorld sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ R
  have repF : WriterRep (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF) w r0 r1)
      (bF0.getStor sevm.currentTarget) fee.state := by
    have h := source.2.1
    rw [feeEq, ← last, feeBranchPost_St, St_getStor] at h
    exact h
  have repS : WriterRep (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF) w r0 r1)
      ((afterSload sevm bF0 0).getStor sevm.currentTarget) fee.state := by
    simpa only [afterSload_getStor] using repF
  have cached := input.rep.selected (.balance sevm.currentTarget) tracked
  simp only [feeBurnWorld, afterSload_getStor] at cached
  change feeBurnLiquidity sevm d1 = st.balanceOf sevm.currentTarget at cached
  have supplyEq : bF0.getStorVal sevm.currentTarget 0 = fee.state.totalSupply := repF.fixed.1
  have priced' : burnAmounts (feeBurnLiquidity sevm d1) b0 (feeBurnBalance1 M)
      (bF0.getStorVal sevm.currentTarget 0) = .ok (amount0, amount1) := by
    rw [cached, supplyEq]
    exact priced
  have lp : feeBurnLiquidity sevm d1 ≤ bF0.getStorVal sevm.currentTarget 0 := by
    rw [cached, supplyEq, B256.le_iff_toNat_le_toNat]
    exact (State.burnLP_supply burned).1
  refine ⟨(burnAmount_le_balance priced' lp).2.2.2, ?_⟩
  have trackedAfter : ∀ key, K key → (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF) w r0 r1)
      key := fun _ h => feeBranchSourceKeys_contains h
  have freshF : WriterFreshKeys (feeBranchSourceKeys K st sevm (feeKLastWorld sevm dF) w r0 r1)
      (lpMintTouched sevm.currentTarget.toB256.toAdr) := by
    rw [toAdr_toB256]
    apply Blanc.SlotFootprint.FreshKeys.of_universe repF.inj repF.apart (fun _ h => h)
    intro k member
    rw [List.mem_singleton.mp (show k ∈ [WriterKey.balance sevm.currentTarget] from member)]
    exact trackedAfter _ tracked
  have repB := repS.lpBurn_post (R := (burnPricedWords sevm d1 dF M b0 t1 t0 r1 r0 toWord extρ
    R).locals (feeBurnBalance1 M) b0 R) (M := bF0.memory) (value := feeBurnLiquidity sevm d1)
    (G := 0) freshF
  refine ⟨_, _, repB, ?_, ?_, ?_⟩
  · show fee.state.unlocked = st.unlocked
    rw [← feeEq]
    exact feeBranchSourceFee_unlocked _ _ _ _ _ _
  · show fee.state.factory = st.factory
    rw [← feeEq]
    exact feeBranchSourceFee_factory _ _ _ _ _ _
  · intro U sub rowF rowP k hk
    rcases hk with old | new
    · exact pairFeeSourceKeys_sub sub rowF _ _ _ _ _ k old
    · rw [toAdr_toB256] at new
      exact lpMintTouched_rows rowP k new

/-! ## Small facts -/

/-- **HASH-T against a separated universe gives HASH-T against any tracked subset of it.** -/
theorem freshKeys_of_wider {K U : WriterKey → Prop} {ks : List WriterKey}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (h : WriterFreshKeys U ks) : WriterFreshKeys K ks := by
  refine ⟨fun k hk => ?_, h.2⟩
  by_cases hK : K k
  · exact Or.inl hK
  · right
    rcases h.1 k hk with hU | ⟨notFixed, distinct⟩
    · exact ⟨apart k hU, fun k' hk' heq => hK ((inj k' k (sub k' hk') hU heq) ▸ hk')⟩
    · exact ⟨notFixed, fun k' hk' => distinct k' (sub k' hk')⟩

/-- WETH9's runtime and the factory's runtime are not one account's. -/
theorem weth_ne_factory {d : Devm} {weth factory : Adr}
    (wethCode : d.getCode weth = Weth9.code)
    (factoryCode : d.getCode factory = UniswapV2Factory.code) : weth ≠ factory := by
  intro same
  have codes : Weth9.code = UniswapV2Factory.code := by
    rw [← wethCode, ← factoryCode, same]
  have lengths := Weth9.code_toList_length
  rw [codes, UniswapV2Factory.code_toList_length] at lengths
  exact absurd lengths (by decide)

end Blanc.Composition.UniswapV2PairWeth9Joint
