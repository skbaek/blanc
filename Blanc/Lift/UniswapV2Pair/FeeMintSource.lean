import Blanc.Lift.UniswapV2Pair.FeeMintWalk
import Blanc.Lift.UniswapV2Pair.LPMintSource

/-! Finite source accounting for actual fee68 and its literal mint/burn consumers. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def feeClearState (st : State) : State := { st with kLast := 0 }

theorem feeClearState_value (st : State) (k : WriterKey) :
    k.value (feeClearState st) = k.value st := by
  cases k <;> rfl

/-- Clearing the actual fixed slot11 preserves all finite tagged rows and other whole words. -/
theorem WriterRep.fee_clear_store {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : WriterRep K (s.set 11 0) (feeClearState st) := by
  have unchanged (n : B256) (off : (11 : B256) ≠ n) :
      (s.set 11 0).get n = s.get n := Stor.get_set_ne s off 0
  rcases rep.fixed with ⟨h0,h3,h5,h6,h7,h80,h81,h8t,h9,h10,h11,h12⟩
  refine ⟨rep.finite, ?_, ?_, rep.inj, rep.apart, ?_, ?_⟩
  · dsimp only [WriterFixedMatches, feeClearState]
    rw [unchanged 0 (by decide), unchanged 3 (by decide), unchanged 5 (by decide),
      unchanged 6 (by decide), unchanged 7 (by decide), unchanged 8 (by decide),
      unchanged 9 (by decide), unchanged 10 (by decide), Stor.get_set_self,
      unchanged 12 (by decide)]
    exact ⟨h0,h3,h5,h6,h7,h80,h81,h8t,h9,h10,rfl,h12⟩
  · intro n nonzero
    by_cases eleven : n = 11
    · exact .inl (eleven.symm ▸ (by decide : (11 : B256) ∈ writerFixedSlots))
    · rw [unchanged n (Ne.symm eleven)] at nonzero
      exact rep.support n nonzero
  · intro k tracked
    have off : (11 : B256) ≠ k.slot :=
      fun eq => rep.apart k tracked (eq ▸ (by decide : (11 : B256) ∈ writerFixedSlots))
    rw [unchanged k.slot off, feeClearState_value]
    exact rep.selected k tracked
  · intro k outside
    rw [feeClearState_value]
    exact rep.logicalZero k outside

/-- The actual factory prefix and static primitive transport incoming finite storage unchanged. -/
theorem WriterRep.fee_factory_post {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b d : Devm} {S : List B256} {M : Mem} {out : Bytes}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (post : StaticCallPost (feeFactoryCallWorld sevm b) d S M 128 4 128 32 1 out) :
    WriterRep K ((feeKLastWorld sevm d).getStor sevm.currentTarget) st := by
  rw [feeKLastWorld, afterSload_getStor, post.stor, feeFactoryCallWorld]
  unfold temporalAccountAccessBase
  split
  · rw [feeFactoryLoadWorld, afterSload_getStor]
    exact rep
  · change WriterRep K ((feeFactoryLoadWorld sevm b).getStor sevm.currentTarget) st
    rw [feeFactoryLoadWorld, afterSload_getStor]
    exact rep

/-- The two separately floored raw fee roots have their precise source Nat values. -/
theorem feeRoots_source {r0 r1 K : B256}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) :
    (feeReserveRoot r0 r1).toNat = Nat.sqrt (r0.toNat * r1.toNat) ∧
      (feeLastRoot K).toNat = Nat.sqrt K.toNat := by
  have product := feeReserveProduct_noWrap bound0 bound1
  have productBound : r0.toNat * r1.toNat < 2 ^ 256 := product
  have rootBound : Nat.sqrt (r0.toNat * r1.toNat) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sqrt_le_self _) productBound
  have lastBound : Nat.sqrt K.toNat < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sqrt_le_self _) (B256.toNat_lt K)
  constructor
  · rw [feeReserveRoot, B256.toNat_mul_eq_of_nofm product, B256.toNat_toB256_of_lt rootBound]
  · rw [feeLastRoot, B256.toNat_toB256_of_lt lastBound]

/-- Successful checked growth derives the source numerator/factor/denominator guards
and the exact floor-liquidity Nat, independently of reserve-size bounds. -/
theorem feeGrowth_arithmetic_source {sevm : Sevm} {b : Devm} {w z a : B256}
    (cover : z ≤ a) (accepts : feeGrowthAccepts sevm b w z a) :
    (b.getStorVal sevm.currentTarget 0).toNat * (a.toNat - z.toNat) < 2 ^ 256 ∧
      a.toNat * 5 < 2 ^ 256 ∧ a.toNat * 5 + z.toNat < 2 ^ 256 ∧
      (feeGrowthLiquidity sevm b z a).toNat =
        (b.getStorVal sevm.currentTarget 0).toNat * (a.toNat - z.toNat) /
          (a.toNat * 5 + z.toNat) := by
  have numerator : (b.getStorVal sevm.currentTarget 0).toNat * (a.toNat - z.toNat) < 2 ^ 256 := by
    have h := accepts.1
    change (b.getStorVal sevm.currentTarget 0).toNat * (a - z).toNat < 2 ^ 256 at h
    rw [B256.toNat_sub_eq_of_le a z cover] at h
    exact h
  have factor : a.toNat * 5 < 2 ^ 256 := by
    have h := accepts.2.1
    change a.toNat * (5 : B256).toNat < 2 ^ 256 at h
    exact h
  have factorWord : (a * 5).toNat = a.toNat * 5 :=
    B256.toNat_mul_eq_of_nofm accepts.2.1
  have denominator : a.toNat * 5 + z.toNat < 2 ^ 256 := by
    have h := accepts.2.2.1
    rw [factorWord] at h
    exact h
  refine ⟨numerator, factor, denominator, ?_⟩
  rw [feeGrowthLiquidity, B256.toNat_div accepts.2.2.2.1,
    feeNumeratorWord, B256.toNat_mul_eq_of_nofm accepts.1,
    B256.toNat_sub_eq_of_le a z cover, feeDenominatorWord,
    B256.toNat_add_eq_of_nof (a * 5) z accepts.2.2.1, factorWord]

/-- A positive raw liquidity word names the exact source LP update; zero performs none. -/
def feeGrowthSourceFee (st : State) (w L : B256) : FeeResult :=
  if L = 0 then { state := st, feeOn := true, minted := 0, events := [] }
  else
    { state := lpMintSourceState st w.toAdr L
      feeOn := true, minted := L.toNat, events := [.transfer 0 w.toAdr L] }

/-- Checked raw growth and finite recipient reads derive the actual source acceptance. -/
theorem feeGrowth_source_accept {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {w r0 r1 : B256}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (recipient : w.toAdr ≠ 0) (last : st.kLast ≠ 0)
    (growth : feeLastRoot st.kLast < feeReserveRoot r0 r1)
    (accepts : feeGrowthAccepts sevm b w (feeLastRoot st.kLast) (feeReserveRoot r0 r1))
    (fresh : feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 →
      WriterFreshKeys K (lpMintTouched w.toAdr)) :
    mintFee st w.toAdr r0.toNat r1.toNat = .ok
      (feeGrowthSourceFee st w
        (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1))) := by
  have roots := feeRoots_source (K := st.kLast) bound0 bound1
  have sourceGrowth : Nat.sqrt st.kLast.toNat < Nat.sqrt (r0.toNat * r1.toNat) := by
    rw [B256.lt_iff_toNat_lt_toNat, roots.1, roots.2] at growth
    exact growth
  have arithmetic := feeGrowth_arithmetic_source (le_of_lt growth) accepts
  have supply : b.getStorVal sevm.currentTarget 0 = st.totalSupply := rep.fixed.1
  rw [supply, roots.1, roots.2] at arithmetic
  rw [mintFee, ite_eq_right recipient, ite_eq_right last, ite_eq_left sourceGrowth,
    ite_eq_left arithmetic.1, ite_eq_left arithmetic.2.1, ite_eq_left arithmetic.2.2.1,
    ← arithmetic.2.2.2]
  by_cases zero : feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0
  · have noMint : ¬ (feeGrowthLiquidity sevm b (feeLastRoot st.kLast)
        (feeReserveRoot r0 r1)).toNat > 0 := by rw [zero]; decide
    rw [ite_eq_right noMint, feeGrowthSourceFee, ite_eq_left zero]
  · have positive : (feeGrowthLiquidity sevm b (feeLastRoot st.kLast)
        (feeReserveRoot r0 r1)).toNat > 0 := by
      have notZero : (feeGrowthLiquidity sevm b (feeLastRoot st.kLast)
          (feeReserveRoot r0 r1)).toNat ≠ 0 :=
        fun h => zero (B256.toNat_inj _ 0 h)
      omega
    have warmRep : WriterRep K ((afterSload sevm b 0).getStor sevm.currentTarget) st := by
      rw [afterSload_getStor]
      exact rep
    have lp := lpMint_source_result (R := []) (M := Mem.empty) (G := 0)
      warmRep (fresh zero) (accepts.2.2.2.2 zero)
    have lpAccept : st.mintLP w.toAdr
        (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)) =
        .ok (lpMintSourceState st w.toAdr
          (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)),
          [.transfer 0 w.toAdr
            (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1))]) := lp.1
    rw [ite_eq_left positive, toB256_toNat, lpAccept, feeGrowthSourceFee, ite_eq_right zero]
    rfl

/-- The finite result follows the same address, kLast, growth and liquidity tests. -/
def feeBranchSourceFee (st : State) (sevm : Sevm) (b : Devm) (w r0 r1 : B256) : FeeResult :=
  if w.toAdr = 0 then { state := feeClearState st, feeOn := false, minted := 0, events := [] }
  else if st.kLast = 0 then { state := st, feeOn := true, minted := 0, events := [] }
  else if feeLastRoot st.kLast < feeReserveRoot r0 r1 then
    feeGrowthSourceFee st w
      (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1))
  else { state := st, feeOn := true, minted := 0, events := [] }

/-- Freshness is requested only on the branch that actually writes the fee recipient. -/
def FeeMintFresh (K : WriterKey → Prop) (st : State) (sevm : Sevm) (b : Devm)
    (w r0 r1 : B256) : Prop :=
  w.toAdr ≠ 0 → st.kLast ≠ 0 → feeLastRoot st.kLast < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 →
      WriterFreshKeys K (lpMintTouched w.toAdr)

/-- Source acceptance is a consequence of actual fee branch guards, not an inverse premise. -/
theorem feeBranch_source_accept {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {w r0 r1 : B256}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (guards : feeBranchAccepts sevm b st.kLast w r0 r1)
    (fresh : FeeMintFresh K st sevm b w r0 r1) :
    mintFee st w.toAdr r0.toNat r1.toNat = .ok (feeBranchSourceFee st sevm b w r0 r1) := by
  by_cases recipient : w.toAdr = 0
  · rw [mintFee, ite_eq_left recipient, feeBranchSourceFee, ite_eq_left recipient]
    rfl
  · have word : w.toAdr.toB256 ≠ 0 := fun h => recipient (Adr.toB256_inj h)
    by_cases last : st.kLast = 0
    · rw [mintFee, ite_eq_right recipient, ite_eq_left last,
        feeBranchSourceFee, ite_eq_right recipient, ite_eq_left last]
    · by_cases growth : feeLastRoot st.kLast < feeReserveRoot r0 r1
      · rw [feeBranchSourceFee, ite_eq_right recipient, ite_eq_right last, ite_eq_left growth]
        have accepts := (show feeOnAccepts sevm b st.kLast w r0 r1 from
          by simpa only [feeBranchAccepts, ite_eq_right word] using guards) last growth
        exact feeGrowth_source_accept rep bound0 bound1 recipient last growth accepts
          (fresh recipient last growth)
      · have roots := feeRoots_source (K := st.kLast) bound0 bound1
        have noGrowth : ¬ Nat.sqrt st.kLast.toNat < Nat.sqrt (r0.toNat * r1.toNat) := by
          rw [B256.lt_iff_toNat_lt_toNat, roots.1, roots.2] at growth
          exact growth
        rw [mintFee, ite_eq_right recipient, ite_eq_right last, ite_eq_right noGrowth,
          feeBranchSourceFee, ite_eq_right recipient, ite_eq_right last, ite_eq_right growth]

/-- Only an actual positive fee mint extends the finite tracked recipient universe. -/
def feeBranchSourceKeys (K : WriterKey → Prop) (st : State) (sevm : Sevm) (b : Devm)
    (w r0 r1 : B256) : WriterKey → Prop :=
  if w.toAdr = 0 then K
  else if st.kLast = 0 then K
  else if feeLastRoot st.kLast < feeReserveRoot r0 r1 then
    if feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0 then K
    else WriterExtend K (lpMintTouched w.toAdr)
  else K

/-- The full raw branch post realizes the finite source state, including no-write branches. -/
theorem WriterRep.feeBranch_post {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {w r0 r1 : B256} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : FeeMintFresh K st sevm b w r0 r1) :
    WriterRep (feeBranchSourceKeys K st sevm b w r0 r1)
      ((feeBranchPost sevm b R M st.kLast w r0 r1 G).getStor sevm.currentTarget)
      (feeBranchSourceFee st sevm b w r0 r1).state := by
  by_cases recipient : w.toAdr = 0
  · have word : w.toAdr.toB256 = 0 := by rw [recipient]; rfl
    simp only [feeBranchSourceKeys, feeBranchSourceFee, ite_eq_left recipient,
      feeBranchPost, ite_eq_left word, St_getStor]
    by_cases last : st.kLast = 0
    · rw [feeOffWorld, ite_eq_left last]
      have clear : feeClearState st = st := by unfold feeClearState; rw [← last]
      rw [clear]
      exact rep
    · rw [feeOffWorld, ite_eq_right last, afterSstore_getStor_self]
      exact rep.fee_clear_store
  · have word : w.toAdr.toB256 ≠ 0 := fun h => recipient (Adr.toB256_inj h)
    simp only [feeBranchSourceKeys, feeBranchSourceFee, ite_eq_right recipient,
      feeBranchPost, ite_eq_right word]
    by_cases last : st.kLast = 0
    · simp only [feeOnPost, ite_eq_left last, St_getStor]
      exact rep
    · simp only [feeOnPost, ite_eq_right last]
      by_cases growth : feeLastRoot st.kLast < feeReserveRoot r0 r1
      · simp only [ite_eq_left growth]
        by_cases zero : feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0
        · simp only [ite_eq_left zero, feeGrowthSourceFee, feeGrowthPost, feeLiquidityPost]
          change WriterRep K
            ((if feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0 then
                St (afterSload sevm b 0) (feeOnWord w :: R) M G
              else lpMintPost sevm (afterSload sevm b 0) (feeOnWord w :: R) M w
                (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)) G).getStor
              sevm.currentTarget) st
          rw [ite_eq_left zero, St_getStor, afterSload_getStor]
          exact rep
        · simp only [ite_eq_right zero, feeGrowthSourceFee, feeGrowthPost, feeLiquidityPost]
          change WriterRep (WriterExtend K (lpMintTouched w.toAdr))
            ((if feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0 then
                St (afterSload sevm b 0) (feeOnWord w :: R) M G
              else lpMintPost sevm (afterSload sevm b 0) (feeOnWord w :: R) M w
                (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)) G).getStor
              sevm.currentTarget)
            (lpMintSourceState st w.toAdr
              (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)))
          rw [ite_eq_right zero]
          have warmRep : WriterRep K ((afterSload sevm b 0).getStor sevm.currentTarget) st := by
            rw [afterSload_getStor]
            exact rep
          exact warmRep.lpMint_post (fresh recipient last growth zero)
      · simp only [ite_eq_right growth, St_getStor]
        exact rep

/-- Raw logs coincide with the source fee event list, and foreign storage and gas are retained. -/
theorem feeBranchPost_facts {st : State} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {w r0 r1 : B256} {G : Nat} :
    (∀ a, a ≠ sevm.currentTarget →
      (feeBranchPost sevm b R M st.kLast w r0 r1 G).getStor a = b.getStor a) ∧
    (feeBranchPost sevm b R M st.kLast w r0 r1 G).gasLeft = G ∧
    (((feeBranchSourceFee st sevm b w r0 r1).events = [] ∧
      (feeBranchPost sevm b R M st.kLast w r0 r1 G).logs = b.logs) ∨
    ∃ L : B256, L ≠ 0 ∧
      (feeBranchSourceFee st sevm b w r0 r1).events = [.transfer 0 w.toAdr L] ∧
      (feeBranchPost sevm b R M st.kLast w r0 r1 G).logs =
        b.logs ++ [lpMintRawLog sevm.currentTarget w.toAdr L]) := by
  by_cases recipient : w.toAdr = 0
  · have word : w.toAdr.toB256 = 0 := by rw [recipient]; rfl
    simp only [feeBranchSourceFee, ite_eq_left recipient, feeBranchPost, ite_eq_left word]
    by_cases last : st.kLast = 0
    · simp only [feeOffWorld, ite_eq_left last]
      exact ⟨fun _ _ => St_getStor _ _ _ _ _, rfl, .inl ⟨True.intro, rfl⟩⟩
    · simp only [feeOffWorld, ite_eq_right last]
      refine ⟨?_, rfl, .inl ⟨True.intro, ?_⟩⟩
      · intro a different
        rw [St_getStor, afterSstore_getStor_ne _ _ _ _ _ different.symm]
      · change (afterSstore sevm b 11 0).logs = b.logs
        exact afterSstore_logs sevm b 11 0
  · have word : w.toAdr.toB256 ≠ 0 := fun h => recipient (Adr.toB256_inj h)
    simp only [feeBranchSourceFee, ite_eq_right recipient, feeBranchPost, ite_eq_right word]
    by_cases last : st.kLast = 0
    · simp only [feeOnPost, ite_eq_left last]
      exact ⟨fun _ _ => St_getStor _ _ _ _ _, rfl, .inl ⟨True.intro, rfl⟩⟩
    · simp only [feeOnPost, ite_eq_right last]
      by_cases growth : feeLastRoot st.kLast < feeReserveRoot r0 r1
      · simp only [ite_eq_left growth]
        by_cases zero : feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0
        · simp only [feeGrowthSourceFee, ite_eq_left zero]
          have eq : feeGrowthPost sevm b R M w (feeOnWord w)
              (feeLastRoot st.kLast) (feeReserveRoot r0 r1) G =
              St (afterSload sevm b 0) (feeOnWord w :: R) M G := by
            change (if feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0 then _ else _) = _
            rw [ite_eq_left zero]
          rw [eq]
          refine ⟨?_, rfl, .inl ⟨True.intro, ?_⟩⟩
          · intro a _
            rw [St_getStor, afterSload_getStor]
          · change (afterSload sevm b 0).logs = b.logs
            exact afterSload_logs sevm b 0
        · simp only [feeGrowthSourceFee, ite_eq_right zero]
          have eq : feeGrowthPost sevm b R M w (feeOnWord w)
              (feeLastRoot st.kLast) (feeReserveRoot r0 r1) G =
              lpMintPost sevm (afterSload sevm b 0) (feeOnWord w :: R) M w
                (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)) G := by
            change (if feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) = 0 then _ else _) = _
            rw [ite_eq_right zero]
            rfl
          rw [eq]
          have lp := lpMintPost_facts (sevm := sevm) (b := afterSload sevm b 0)
            (R := feeOnWord w :: R) (M := M) (toWord := w)
            (value := feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)) (G := G)
          refine ⟨?_, lp.2.2.2, .inr ⟨_, zero, rfl, ?_⟩⟩
          · intro a different
            rw [lp.2.1 a different, afterSload_getStor]
          · rw [lp.2.2.1, afterSload_logs]
      · simp only [ite_eq_right growth]
        exact ⟨fun _ _ => St_getStor _ _ _ _ _, rfl, .inl ⟨True.intro, rfl⟩⟩

/-- Finite acceptance, exact selected post-storage, event correspondence and residual gas. -/
def FeeMintSourceResult (K : WriterKey → Prop) (st : State) (sevm : Sevm) (b : Devm)
    (R : List B256) (M : Mem) (w r0 r1 : B256) (G : Nat) : Prop :=
  mintFee st w.toAdr r0.toNat r1.toNat = .ok (feeBranchSourceFee st sevm b w r0 r1) ∧
  WriterRep (feeBranchSourceKeys K st sevm b w r0 r1)
    ((feeBranchPost sevm b R M st.kLast w r0 r1 G).getStor sevm.currentTarget)
    (feeBranchSourceFee st sevm b w r0 r1).state ∧
  (∀ a, a ≠ sevm.currentTarget →
    (feeBranchPost sevm b R M st.kLast w r0 r1 G).getStor a = b.getStor a) ∧
  (feeBranchPost sevm b R M st.kLast w r0 r1 G).gasLeft = G ∧
  (((feeBranchSourceFee st sevm b w r0 r1).events = [] ∧
    (feeBranchPost sevm b R M st.kLast w r0 r1 G).logs = b.logs) ∨
  ∃ L : B256, L ≠ 0 ∧
    (feeBranchSourceFee st sevm b w r0 r1).events = [.transfer 0 w.toAdr L] ∧
    (feeBranchPost sevm b R M st.kLast w r0 r1 G).logs =
      b.logs ++ [lpMintRawLog sevm.currentTarget w.toAdr L])

theorem feeBranch_source_result {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {w r0 r1 : B256} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (guards : feeBranchAccepts sevm b st.kLast w r0 r1)
    (fresh : FeeMintFresh K st sevm b w r0 r1) :
    FeeMintSourceResult K st sevm b R M w r0 r1 G := by
  have facts := feeBranchPost_facts (st := st) (sevm := sevm) (b := b) (R := R)
    (M := M) (w := w) (r0 := r0) (r1 := r1) (G := G)
  exact ⟨feeBranch_source_accept rep bound0 bound1 guards fresh, rep.feeBranch_post fresh, facts⟩

/-- The actual same-D factory observation and both continuations survive the source adapter. -/
structure FeeMintSourceObservation (K : WriterKey → Prop) (st : State) (D : Exec.Deriv)
    (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (r1 r0 ρ : B256) (o : Outcome) where
  code : ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0
  gw : B256
  callGas : Nat
  d : Devm
  out : Bytes
  decodeGas : Nat
  branchGas : Nat
  residual : Nat
  step : StepIn D sevm
    (St (feeFactoryCallWorld sevm b)
      (gw :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
        132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) callGas) (.exec .staticcall) d
  post : StaticCallPost (feeFactoryCallWorld sevm b) d
    (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeRequestMemory M) 128 4 128 32 1 out
  width : 32 ≤ out.length
  bound : out.length < 2 ^ 256
  answer : StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
    (ExternalOperation.encode .feeTo) out
  decoder : SFunc.RunCutP (StepIn D) cert.prog sevm []
    (St d (out.length.toB256 :: 128 :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeReplyMemory M out) decodeGas) t_2781_c68 (.done o)
  branch : SFunc.RunCutP (StepIn D) cert.prog sevm []
    (St (feeKLastWorld sevm d)
      (feeKLastWord sevm d :: Bytes.toB256 (out.take 32) ::
        feeOnWord (Bytes.toB256 (out.take 32)) :: r1 :: r0 :: ρ :: R)
      (feeReplyMemory M out) branchGas)
    (feeDecodedTree (Bytes.toB256 (out.take 32))) (.done o)
  guards : feeBranchAccepts sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
    (Bytes.toB256 (out.take 32)) r0 r1
  last : feeKLastWord sevm d = st.kLast
  returned : o = .returned (feeBranchPost sevm (feeKLastWorld sevm d) R (feeReplyMemory M out)
    (feeKLastWord sevm d) (Bytes.toB256 (out.take 32)) r0 r1 residual)
  sourceResult : FeeMintSourceResult K st sevm (feeKLastWorld sevm d) R (feeReplyMemory M out)
    (Bytes.toB256 (out.take 32)) r0 r1 residual

/-- Only actual same-D factory steps request touched recipient freshness; hypothetical replies do not. -/
def FeeMintSourceFresh (K : WriterKey → Prop) (st : State) (D : Exec.Deriv) (sevm : Sevm) (b : Devm)
    (R : List B256) (M : Mem) (r1 r0 ρ : B256) : Prop :=
  ∀ gw callGas d out, StepIn D sevm
    (St (feeFactoryCallWorld sevm b)
      (gw :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
        132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) callGas) (.exec .staticcall) d →
    StaticCallPost (feeFactoryCallWorld sevm b) d
    (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
    (feeRequestMemory M) 128 4 128 32 1 out →
      FeeMintFresh K st sevm (feeKLastWorld sevm d) (Bytes.toB256 (out.take 32)) r0 r1

/-- Real fee68 success derives source acceptance and the complete finite post through the same D. -/
theorem fee68_source_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv} {sevm : Sevm}
    {b : Devm} {R : List B256} {M : Mem} {G : Nat} {r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (fresh : FeeMintSourceFresh K st D sevm b R M r1 r0 ρ)
    (run : SFunc.RunP (StepIn D) cert.prog sevm
      (St b (r1 :: r0 :: ρ :: R) M G) t_26ec_c68 o) :
    Nonempty (FeeMintSourceObservation K st D sevm b R M r1 r0 ρ o) := by
  obtain ⟨code, gw, callGas, d, out, decodeGas, branchGas, gas,
    step, post, width, bound, answer, decoder, branch, guards, result⟩ :=
    fee68_inv fork mem bound0 bound1 run
  have postRep := rep.fee_factory_post post
  have last : feeKLastWord sevm d = st.kLast := by
    rcases postRep.fixed with ⟨_,_,_,_,_,_,_,_,_,_,last,_⟩
    change (d.getStor sevm.currentTarget).get 11 = st.kLast
    simpa only [feeKLastWorld, afterSload_getStor] using last
  have sourceGuards : feeBranchAccepts sevm (feeKLastWorld sevm d) st.kLast
      (Bytes.toB256 (out.take 32)) r0 r1 := by rw [← last]; exact guards
  exact ⟨⟨code, gw, callGas, d, out, decodeGas, branchGas, gas,
    step, post, width, bound, answer, decoder, branch, guards, last, result,
    feeBranch_source_result postRep bound0 bound1 sourceGuards (fresh gw callGas d out step post)⟩⟩

def feeSourceNumerator (st : State) (r0 r1 : B256) : Nat :=
  st.totalSupply.toNat * (Nat.sqrt (r0.toNat * r1.toNat) - Nat.sqrt st.kLast.toNat)

def feeSourceDenominator (st : State) (r0 r1 : B256) : Nat :=
  Nat.sqrt (r0.toNat * r1.toNat) * 5 + Nat.sqrt st.kLast.toNat

/-- The checked source growth requirements, extracted from actual mintFee acceptance. -/
def FeeGrowthSourceAccepts (st : State) (recipient : Adr) (r0 r1 : B256) : Prop :=
  feeSourceNumerator st r0 r1 < 2 ^ 256 ∧
  Nat.sqrt (r0.toNat * r1.toNat) * 5 < 2 ^ 256 ∧
  feeSourceDenominator st r0 r1 < 2 ^ 256 ∧
  (feeSourceNumerator st r0 r1 / feeSourceDenominator st r0 r1 > 0 →
    ∃ post events, st.mintLP recipient
      (feeSourceNumerator st r0 r1 / feeSourceDenominator st r0 r1).toB256 = .ok (post, events))

/-- Positive growth success cannot bypass any source checked product or LP addition. -/
theorem feeGrowth_source_inv {st : State} {recipient : Adr} {r0 r1 : B256} {fee : FeeResult}
    (on : recipient ≠ 0) (last : st.kLast ≠ 0)
    (growth : Nat.sqrt st.kLast.toNat < Nat.sqrt (r0.toNat * r1.toNat))
    (accepted : mintFee st recipient r0.toNat r1.toNat = .ok fee) :
    FeeGrowthSourceAccepts st recipient r0 r1 := by
  rw [mintFee, ite_eq_right on, ite_eq_right last, ite_eq_left growth] at accepted
  by_cases numerator : feeSourceNumerator st r0 r1 < 2 ^ 256
  · change (if feeSourceNumerator st r0 r1 < 2 ^ 256 then _ else _) = _ at accepted
    rw [ite_eq_left numerator] at accepted
    by_cases factor : Nat.sqrt (r0.toNat * r1.toNat) * 5 < 2 ^ 256
    · rw [ite_eq_left factor] at accepted
      by_cases denominator : feeSourceDenominator st r0 r1 < 2 ^ 256
      · change (if feeSourceDenominator st r0 r1 < 2 ^ 256 then _ else _) = _ at accepted
        rw [ite_eq_left denominator] at accepted
        refine ⟨numerator, factor, denominator, ?_⟩
        intro positive
        change (if feeSourceNumerator st r0 r1 / feeSourceDenominator st r0 r1 > 0 then _ else _) = _ at accepted
        rw [ite_eq_left positive] at accepted
        cases lp : st.mintLP recipient
            (feeSourceNumerator st r0 r1 / feeSourceDenominator st r0 r1).toB256 with
        | error failure =>
          dsimp only [feeSourceNumerator, feeSourceDenominator] at lp
          rw [lp] at accepted
          cases accepted
        | ok pair => exact ⟨pair.1, pair.2, rfl⟩
      · change (if feeSourceDenominator st r0 r1 < 2 ^ 256 then _ else _) = _ at accepted
        rw [ite_eq_right denominator] at accepted
        cases accepted
    · rw [ite_eq_right factor] at accepted
      cases accepted
  · change (if feeSourceNumerator st r0 r1 < 2 ^ 256 then _ else _) = _ at accepted
    rw [ite_eq_right numerator] at accepted
    cases accepted

/-- Accepted source checks become actual word guards using the finite sequential LP reads. -/
theorem feeGrowth_raw_guards {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {w r0 r1 : B256}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (growth : feeLastRoot st.kLast < feeReserveRoot r0 r1)
    (source : FeeGrowthSourceAccepts st w.toAdr r0 r1)
    (fresh : feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 →
      WriterFreshKeys K (lpMintTouched w.toAdr))
    (nonstatic : feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 →
      sevm.isStatic = false) :
    feeGrowthAccepts sevm b w (feeLastRoot st.kLast) (feeReserveRoot r0 r1) := by
  have roots := feeRoots_source (K := st.kLast) bound0 bound1
  have sourceGrowth : Nat.sqrt st.kLast.toNat < Nat.sqrt (r0.toNat * r1.toNat) := by
    rw [B256.lt_iff_toNat_lt_toNat, roots.1, roots.2] at growth
    exact growth
  have supply : b.getStorVal sevm.currentTarget 0 = st.totalSupply := rep.fixed.1
  have numerator : B256.Nofm (b.getStorVal sevm.currentTarget 0)
      (feeReserveRoot r0 r1 - feeLastRoot st.kLast) := by
    change (b.getStorVal sevm.currentTarget 0).toNat *
      (feeReserveRoot r0 r1 - feeLastRoot st.kLast).toNat < 2 ^ 256
    rw [supply, B256.toNat_sub_eq_of_le _ _ (le_of_lt growth), roots.1, roots.2]
    exact source.1
  have factor : B256.Nofm (feeReserveRoot r0 r1) 5 := by
    change (feeReserveRoot r0 r1).toNat * 5 < 2 ^ 256
    rw [roots.1]
    exact source.2.1
  have factorWord : (feeReserveRoot r0 r1 * 5).toNat =
      Nat.sqrt (r0.toNat * r1.toNat) * 5 := by
    rw [B256.toNat_mul_eq_of_nofm factor, roots.1]
    rfl
  have denominator : (feeReserveRoot r0 r1 * 5).toNat + (feeLastRoot st.kLast).toNat < 2 ^ 256 := by
    rw [factorWord, roots.2]
    exact source.2.2.1
  have denominatorWord : (feeDenominatorWord (feeLastRoot st.kLast) (feeReserveRoot r0 r1)).toNat =
      feeSourceDenominator st r0 r1 := by
    rw [feeDenominatorWord, B256.toNat_add_eq_of_nof _ _ denominator, factorWord, roots.2]
    rfl
  have denominatorNonzero : feeDenominatorWord (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 := by
    intro zero
    rw [zero] at denominatorWord
    change 0 = Nat.sqrt (r0.toNat * r1.toNat) * 5 + Nat.sqrt st.kLast.toNat at denominatorWord
    omega
  have liquidity : (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)).toNat =
      feeSourceNumerator st r0 r1 / feeSourceDenominator st r0 r1 := by
    rw [feeGrowthLiquidity, B256.toNat_div denominatorNonzero, denominatorWord,
      feeNumeratorWord, B256.toNat_mul_eq_of_nofm numerator, supply,
      B256.toNat_sub_eq_of_le _ _ (le_of_lt growth), roots.1, roots.2]
    rfl
  refine ⟨numerator, factor, denominator, denominatorNonzero, ?_⟩
  intro positive
  have wordPositive : feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 := positive
  have natPositive : feeSourceNumerator st r0 r1 / feeSourceDenominator st r0 r1 > 0 := by
    rw [← liquidity]
    have notZero : (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)).toNat ≠ 0 :=
      fun h => wordPositive (B256.toNat_inj _ 0 h)
    omega
  obtain ⟨post, events, accepted⟩ := source.2.2.2 natPositive
  rw [← liquidity, toB256_toNat] at accepted
  have lp := lpMintLP_inv accepted
  have warmRep : WriterRep K ((afterSload sevm b 0).getStor sevm.currentTarget) st := by
    rw [afterSload_getStor]
    exact rep
  have reads := lpMint_source_reads
    (value := feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1))
    warmRep (fresh wordPositive)
  change lpMintAccepts sevm (afterSload sevm b 0) w
    (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1))
  refine ⟨?_, nonstatic wordPositive, ?_⟩
  · rw [reads.1]
    exact lp.1
  · rw [reads.2]
    exact lp.2.1

/-- Static execution is excluded only when the selected fee branch actually stores. -/
def FeeMintWrites (st : State) (sevm : Sevm) (b : Devm) (w r0 r1 : B256) : Prop :=
  (w.toAdr.toB256 = 0 → st.kLast ≠ 0 → sevm.isStatic = false) ∧
  (w.toAdr.toB256 ≠ 0 → st.kLast ≠ 0 → feeLastRoot st.kLast < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 →
      sevm.isStatic = false)

theorem feeBranch_raw_guards {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {w r0 r1 : B256} {fee : FeeResult}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (accepted : mintFee st w.toAdr r0.toNat r1.toNat = .ok fee)
    (fresh : FeeMintFresh K st sevm b w r0 r1)
    (writes : FeeMintWrites st sevm b w r0 r1) :
    feeBranchAccepts sevm b st.kLast w r0 r1 := by
  by_cases word : w.toAdr.toB256 = 0
  · rw [feeBranchAccepts, ite_eq_left word]
    exact writes.1 word
  · rw [feeBranchAccepts, ite_eq_right word]
    intro last growth
    have on : w.toAdr ≠ 0 := fun h => word (by rw [h]; rfl)
    have roots := feeRoots_source (K := st.kLast) bound0 bound1
    have sourceGrowth : Nat.sqrt st.kLast.toNat < Nat.sqrt (r0.toNat * r1.toNat) := by
      have g := growth
      rw [B256.lt_iff_toNat_lt_toNat, roots.1, roots.2] at g
      exact g
    exact feeGrowth_raw_guards rep bound0 bound1 growth
      (feeGrowth_source_inv on last sourceGrowth accepted) (fresh on last growth)
      (writes.2 word last growth)

/-- Forward store conditions carry genuine incoming sentries and only conditional static checks. -/
structure FeeMintStoreConditions (st : State) (sevm : Sevm) (b : Devm)
    (w r0 r1 : B256) (G : Nat) : Prop where
  writes : FeeMintWrites st sevm b w r0 r1
  clearSentry : w.toAdr.toB256 = 0 → st.kLast ≠ 0 →
    gCallStipend < G + sstoreCost sevm b 11 0 + 23
  supplySentry : w.toAdr.toB256 ≠ 0 → st.kLast ≠ 0 → feeLastRoot st.kLast < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 →
      lpMintSupplySentry sevm (afterSload sevm b 0) w
        (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)) (G + 47)
  creditSentry : w.toAdr.toB256 ≠ 0 → st.kLast ≠ 0 → feeLastRoot st.kLast < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1) ≠ 0 →
      lpMintCreditSentry sevm (afterSload sevm b 0) w
        (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)) (G + 47)

/-- Exact raw fee obligations are constructed from source success and canonical LP selected costs. -/
theorem feeBranch_source_forward {K : WriterKey → Prop} {st : State} {sevm : Sevm}
    {b : Devm} {w r0 r1 : B256} {fee : FeeResult} {G : Nat}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (accepted : mintFee st w.toAdr r0.toNat r1.toNat = .ok fee)
    (fresh : FeeMintFresh K st sevm b w r0 r1)
    (stores : FeeMintStoreConditions st sevm b w r0 r1 G) :
    FeeBranchForward sevm b st.kLast w r0 r1 G
      (lpMintSourceCharge sevm (afterSload sevm b 0))
      (lpMintSupplyCharge sevm (afterSload sevm b 0)
        (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)))
      (lpMintRecipientLoadCharge sevm (afterSload sevm b 0) w
        (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)))
      (lpMintCreditCharge sevm (afterSload sevm b 0) w
        (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1))) := by
  refine ⟨feeBranch_raw_guards rep bound0 bound1 accepted fresh stores.writes,
    stores.clearSentry, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro on last growth positive
    have h := stores.supplySentry on last growth positive
    dsimp only [lpMintSupplySentry] at h
    omega
  · intro on last growth positive
    have h := stores.creditSentry on last growth positive
    dsimp only [lpMintCreditSentry] at h
    omega

/-- The genuine compiled factory primitive produces the post used by finite source transport. -/
theorem feeFactoryCompiled_post {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {callGas : Nat} {r1 r0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork)
    (call : Ninst.RunCompiled sevm
      (St (feeFactoryCallWorld sevm b)
        (callGas.toB256 :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm b ::
      0 :: 0 :: r1 :: r0 :: ρ :: R) :
    StaticCallPost (feeFactoryCallWorld sevm b) d
      (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) 128 4 128 32 1 d.returnData := by
  obtain ⟨flag, out, post, _, _⟩ := ri_staticcall_bounded fork (by
    rcases call with ⟨xl, compiled, run⟩
    exact ⟨xl, compiled, 0, run 0⟩)
  have flagEq : flag = 1 := (List.cons.inj (post.stack.symm.trans success)).1
  subst flag
  rw [post.returnData]
  exact post

/-- Canonical fee gas uses the real post-call world, the second supply read and sequential LP costs. -/
def feeMintBranchGas (st : State) (sevm : Sevm) (b : Devm) (w r0 r1 : B256) (G : Nat) : Nat :=
  G + feeBranchCharge sevm b st.kLast w r0 r1
    (lpMintSourceCharge sevm (afterSload sevm b 0))
    (lpMintSupplyCharge sevm (afterSload sevm b 0)
      (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)))
    (lpMintRecipientLoadCharge sevm (afterSload sevm b 0) w
      (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)))
    (lpMintCreditCharge sevm (afterSload sevm b 0) w
      (feeGrowthLiquidity sevm b (feeLastRoot st.kLast) (feeReserveRoot r0 r1)))

/-- Actual source acceptance and a genuine factory step construct the full fee68 exact run. -/
theorem fee68_source_exact {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b d : Devm}
    {R : List B256} {M : Mem} {G callGas : Nat} {r1 r0 ρ : B256} {fee : FeeResult}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) (room : R.length ≤ 1003)
    (code : ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0)
    (call : Ninst.RunCompiled sevm
      (St (feeFactoryCallWorld sevm b)
        (callGas.toB256 :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm b ::
      0 :: 0 :: r1 :: r0 :: ρ :: R)
    (width : 32 ≤ d.returnData.length)
    (accepted : mintFee st (Bytes.toB256 (d.returnData.take 32)).toAdr r0.toNat r1.toNat = .ok fee)
    (fresh : FeeMintFresh K st sevm (feeKLastWorld sevm d)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1)
    (stores : FeeMintStoreConditions st sevm (feeKLastWorld sevm d)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 G)
    (returnedGas : d.gasLeft = feeMintBranchGas st sevm (feeKLastWorld sevm d)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 G + sloadCost sevm d 11 + 120) :
    SFunc.RunExact cert.prog sevm
      (St b (r1 :: r0 :: ρ :: R) M (callGas + sloadCost sevm b 5 +
        temporalAccountAccessCost (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr + 142))
      t_26ec_c68 (.returned (feeBranchPost sevm (feeKLastWorld sevm d) R
        (feeReplyMemory M d.returnData) st.kLast (Bytes.toB256 (d.returnData.take 32)) r0 r1 G)) ∧
    FeeMintSourceResult K st sevm (feeKLastWorld sevm d) R (feeReplyMemory M d.returnData)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 G ∧
    feeBranchSourceFee st sevm (feeKLastWorld sevm d) (Bytes.toB256 (d.returnData.take 32)) r0 r1 = fee := by
  have post := feeFactoryCompiled_post fork call success
  have postRep := rep.fee_factory_post post
  have last : feeKLastWord sevm d = st.kLast := by
    rcases postRep.fixed with ⟨_,_,_,_,_,_,_,_,_,_,last,_⟩
    change (d.getStor sevm.currentTarget).get 11 = st.kLast
    simpa only [feeKLastWorld, afterSload_getStor] using last
  have forward := feeBranch_source_forward postRep bound0 bound1 accepted fresh stores
  have sourceResult := feeBranch_source_result (R := R) (M := feeReplyMemory M d.returnData)
    (G := G) postRep bound0 bound1 forward.accepts fresh
  refine ⟨?_, sourceResult, ?_⟩
  · have exactRun := fee68_exact fork mem bound0 bound1 room code call success width
      (by rw [last]; exact returnedGas) (by rw [last]; exact forward)
    rw [last] at exactRun
    exact exactRun
  · exact Except.ok.inj (sourceResult.1.symm.trans accepted)

/-- Mint's cached amounts/balances/reserves and outer return remain beneath fee68. -/
def mintFeeLocals (amount1 amount0 b1 b0 r1 r0 toWord extρ : B256) (R : List B256) : List B256 :=
  0 :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R

def feeBurnMemory (M : Mem) (pair : Adr) : Mem := transferScratch M pair.toB256

def feeBurnBalance1 (M : Mem) : B256 := Bytes.toB256 (M.read 128 32).1

def feeBurnLiquidity (sevm : Sevm) (b : Devm) : B256 :=
  b.getStorVal sevm.currentTarget (transferBalanceSlot sevm.currentTarget)

def feeBurnWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm b (transferBalanceSlot sevm.currentTarget)

def burnFeeLocals (L b1 b0 token1 token0 r1 r0 toWord extρ : B256) (R : List B256) : List B256 :=
  0 :: L :: b1 :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R

theorem feeBurnMemory_ptr {M : Mem} (mem : PtrMem 128 192 M) (pair : Adr) :
    PtrMem 128 192 (feeBurnMemory M pair) := by
  have h := lpMintScratch_ptr mem pair.toB256
  simpa only [feeBurnMemory, transferScratch, toAdr_toB256] using h

theorem feeBurnMemory_hash (M : Mem) (pair : Adr) :
    ((feeBurnMemory M pair).read 0 64).1.keccak = transferBalanceSlot pair := by
  unfold feeBurnMemory transferScratch transferBalanceSlot
  rw [Mem.read_two_word_writes_at_raw M 0 pair.toB256 1]
  rfl

/-- Burn15c3 physically samples the pair LP balance before invoking fee68.
That cached word survives even when the fee recipient is the pair itself. -/
theorem feeBurn_source_caller_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {len discarded b0 token1 token0 r1 r0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (fresh : FeeMintSourceFresh K st D sevm (feeBurnWorld sevm b)
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
      (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (len :: 128 :: discarded :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
      t_15c3_c37 r) :
    feeBurnLiquidity sevm b = st.balanceOf sevm.currentTarget ∧ ∃ feeGas feePost,
      SFunc.RunP (StepIn D) cert.prog sevm
        (St (feeBurnWorld sevm b)
          (r1 :: r0 :: 0x15e2 :: burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M)
            b0 token1 token0 r1 r0 toWord extρ R) (feeBurnMemory M sevm.currentTarget) feeGas)
        t_26ec_c68 (.returned feePost) ∧
      Nonempty (FeeMintSourceObservation K st D sevm (feeBurnWorld sevm b)
        (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
        (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 (.returned feePost)) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_15e2_c37 r := by
  have cached : feeBurnLiquidity sevm b = st.balanceOf sevm.currentTarget :=
    rep.selected (.balance sevm.currentTarget) tracked
  refine ⟨cached, ?_⟩
  have postRep : WriterRep K ((feeBurnWorld sevm b).getStor sevm.currentTarget) st := by
    rw [feeBurnWorld, afterSload_getStor]
    exact rep
  have scratch := feeBurnMemory_ptr mem sevm.currentTarget
  unfold t_15c3_c37 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mload (StepIn.toRun hs)
  rw [show (128 : B256).toNat = 128 from rfl, mem.read_self (by decide : 128 + 32 ≤ 192)] at eq
  subst d
  obtain ⟨d, hs, run⟩ := ric_nextP run
  have address := of_run_address (StepIn.toRun hs)
  have stack : d.stack = sevm.currentTarget.toB256 :: feeBurnBalance1 M :: discarded ::
      b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R := by
    have h := address.stack
    change d.stack = sevm.currentTarget.toB256 :: feeBurnBalance1 M :: discarded ::
      b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R at h
    exact h
  have eq := St.of_stackRel address
  rw [stack] at eq
  rw [eq] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mstore (StepIn.toRun hs)
  rw [show (0 : B256).toNat = 0 from rfl] at eq
  subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rw [show Bytes.toB256 [1] = (1 : B256) from rfl] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at run
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mstore (StepIn.toRun hs)
  rw [show (32 : B256).toNat = 32 from rfl] at eq
  subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x40] = (64 : B256) from rfl] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_keccak (StepIn.toRun hs)
  change d = St b
    (((feeBurnMemory M sevm.currentTarget).read 0 64).1.keccak :: 0 :: feeBurnBalance1 M :: discarded ::
      b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
    ((feeBurnMemory M sevm.currentTarget).read 0 64).2 _ at eq
  rw [feeBurnMemory_hash, scratch.read_self (by decide : 0 + 64 ≤ 192)] at eq
  subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_sload fork (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_swap rfl (StepIn.toRun hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x15, 0xe2] = (0x15e2 : B256) from by decide] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rw [show Bytes.toB256 [0x26, 0xec] = (0x26ec : B256) from by decide] at run
  cases run with
  | callRet d lookup pop callee continuation =>
    change some t_26ec_c68 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    exact ⟨_, _, callee, fee68_source_inv fork scratch postRep bound0 bound1 fresh callee, continuation⟩
  | callHalt d lookup pop callee =>
    change some t_26ec_c68 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨observed⟩ := fee68_source_inv fork scratch postRep bound0 bound1 fresh callee
    cases observed.returned

def feeMintEntryGas (sevm : Sevm) (b : Devm) (callGas : Nat) : Nat :=
  callGas + sloadCost sevm b 5 +
    temporalAccountAccessCost (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr + 142

def feeMintSourcePost (st : State) (sevm : Sevm) (d : Devm) (R : List B256) (M : Mem)
    (r0 r1 : B256) (G : Nat) : Devm :=
  feeBranchPost sevm (feeKLastWorld sevm d) R (feeReplyMemory M d.returnData)
    st.kLast (Bytes.toB256 (d.returnData.take 32)) r0 r1 G

/-- Shared literal forward inputs retain genuine ENV/source/gas facts and no assumed fee outcome. -/
structure FeeMintForwardInput (K : WriterKey → Prop) (st : State) (sevm : Sevm) (b d : Devm)
    (R : List B256) (M : Mem) (r1 r0 ρ : B256) (G callGas : Nat) (fee : FeeResult) : Prop where
  fork : CoveredFork sevm.benvStat.fork
  mem : PtrMem 128 192 M
  rep : WriterRep K (b.getStor sevm.currentTarget) st
  bound0 : r0.toNat < 2 ^ 112
  bound1 : r1.toNat < 2 ^ 112
  room : R.length ≤ 1003
  code : ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0
  call : Ninst.RunCompiled sevm
    (St (feeFactoryCallWorld sevm b)
      (callGas.toB256 :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
        132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
      (feeRequestMemory M) callGas) (.exec .staticcall) d
  success : d.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm b ::
    0 :: 0 :: r1 :: r0 :: ρ :: R
  width : 32 ≤ d.returnData.length
  accepted : mintFee st (Bytes.toB256 (d.returnData.take 32)).toAdr r0.toNat r1.toNat = .ok fee
  fresh : FeeMintFresh K st sevm (feeKLastWorld sevm d) (Bytes.toB256 (d.returnData.take 32)) r0 r1
  stores : FeeMintStoreConditions st sevm (feeKLastWorld sevm d) (Bytes.toB256 (d.returnData.take 32)) r0 r1 G
  returnedGas : d.gasLeft = feeMintBranchGas st sevm (feeKLastWorld sevm d)
    (Bytes.toB256 (d.returnData.take 32)) r0 r1 G + sloadCost sevm d 11 + 120

theorem FeeMintForwardInput.exact {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b d : Devm}
    {R : List B256} {M : Mem} {r1 r0 ρ : B256} {G callGas : Nat} {fee : FeeResult}
    (input : FeeMintForwardInput K st sevm b d R M r1 r0 ρ G callGas fee) :
    SFunc.RunExact cert.prog sevm (St b (r1 :: r0 :: ρ :: R) M (feeMintEntryGas sevm b callGas))
      t_26ec_c68 (.returned (feeMintSourcePost st sevm d R M r0 r1 G)) ∧
    FeeMintSourceResult K st sevm (feeKLastWorld sevm d) R (feeReplyMemory M d.returnData)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 G ∧
    feeBranchSourceFee st sevm (feeKLastWorld sevm d) (Bytes.toB256 (d.returnData.take 32)) r0 r1 = fee := by
  exact fee68_source_exact input.fork input.mem input.rep input.bound0 input.bound1 input.room
    input.code input.call input.success input.width input.accepted input.fresh input.stores input.returnedGas

/-- Burn's105gas prefix and actual pair SLOAD construct fee68 without refreshing cached liquidity. -/
theorem feeBurn_source_caller_exact {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b d : Devm}
    {R : List B256} {M : Mem} {G callGas : Nat} {fee : FeeResult} {o : Outcome}
    {len discarded b0 token1 token0 r1 r0 toWord extρ : B256}
    (mem : PtrMem 128 192 M) (tracked : K (.balance sevm.currentTarget))
    (input : FeeMintForwardInput K st sevm (feeBurnWorld sevm b) d
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
      (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 G callGas fee)
    (continuation : SFunc.RunExact cert.prog sevm
      (feeMintSourcePost st sevm d
        (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
        (feeBurnMemory M sevm.currentTarget) r0 r1 G) t_15e2_c37 o) :
    feeBurnLiquidity sevm b = st.balanceOf sevm.currentTarget ∧
    SFunc.RunExact cert.prog sevm
      (St b (len :: 128 :: discarded :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        M (feeMintEntryGas sevm (feeBurnWorld sevm b) callGas +
          sloadCost sevm b (transferBalanceSlot sevm.currentTarget) + 105)) t_15c3_c37 o ∧
    FeeMintSourceResult K st sevm (feeKLastWorld sevm d)
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
      (feeReplyMemory (feeBurnMemory M sevm.currentTarget) d.returnData)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 G ∧
    feeBranchSourceFee st sevm (feeKLastWorld sevm d) (Bytes.toB256 (d.returnData.take 32)) r0 r1 = fee := by
  obtain ⟨callee, source, feeEq⟩ := input.exact
  have cached := input.rep.selected (.balance sevm.currentTarget) tracked
  simp only [feeBurnWorld, afterSload_getStor] at cached
  have room := input.room
  simp only [burnFeeLocals, List.length_cons] at room
  have m0 := mem.write 0 sevm.currentTarget.toB256 (Or.inl (by decide))
  rw [show memExtSize 192 0 32 = 192 from by decide] at m0
  have m1 := feeBurnMemory_ptr mem sevm.currentTarget
  refine ⟨cached, ?_, source, feeEq⟩
  unfold t_15c3_c37
  apply rx_dest
  apply rx_pop
  refine rx_mload (v := feeBurnBalance1 M) (c := 3) ?_ rfl
    (mem.read_self (by decide : 128 + 32 ≤ 192)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  refine .next (Ninst.runCompiled_pushItem
    (G := feeMintEntryGas sevm (feeBurnWorld sevm b) callGas +
      sloadCost sevm b (transferBalanceSlot sevm.currentTarget) + 97) (cost := gBase)
    (by rintro ⟨⟩) rfl rfl (by simp only [St.stack, List.length_cons]; omega)) ?_
  change SFunc.RunExact cert.prog sevm
    (St b (sevm.currentTarget.toB256 :: feeBurnBalance1 M :: discarded :: b0 :: token1 :: token0 ::
      r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M
      (feeMintEntryGas sevm (feeBurnWorld sevm b) callGas +
        sloadCost sevm b (transferBalanceSlot sevm.currentTarget) + 97)) _ o
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap rfl
  dsimp only [List.set]
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := 3) ?_ rfl ?_
  · change gVerylow + (St b _ (M.write 0 sevm.currentTarget.toB256.toBytes) _).extCost [(32, 32)] = 3
    rw [St.extCost_eq m0.size]; decide
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  refine rx_keccak (v := transferBalanceSlot sevm.currentTarget) (c := 42) ?_
    (feeBurnMemory_hash M sevm.currentTarget) (m1.read_self (by decide : 0 + 64 ≤ 192))
    (by simp only [List.length_cons]; omega) ?_
  · change gKeccak256 + gasKeccak256Word * ceilDiv 64 32 +
      (St b _ (feeBurnMemory M sevm.currentTarget) _).extCost [(0, 64)] = 42
    rw [St.extCost_eq m1.size]; decide
  rw [show feeMintEntryGas sevm (feeBurnWorld sevm b) callGas +
      sloadCost sevm b (transferBalanceSlot sevm.currentTarget) + 28 =
      (feeMintEntryGas sevm (feeBurnWorld sevm b) callGas + 28) +
        sloadCost sevm b (transferBalanceSlot sevm.currentTarget) from by omega]
  apply rx_sload_selC input.fork rfl (by simp only [List.length_cons]; omega)
  apply rx_swap rfl
  dsimp only [List.set]
  apply rx_swap rfl
  dsimp only [List.set]
  apply rx_pop
  apply rx_push (w := 0x15e2) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x26ec) rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_26ec_c68) rfl callee continuation


/-- The typed factory result retains the complete observed reply.  Success and code
existence are justified by the actual factory guard in the observation below. -/
def feeObservedResult (out : Bytes) : ExternalResult :=
  { success := true, returndata := out, codeExists := true, recoveryOutput := 0 }

theorem feeObservedResult_decode (site : CallSite) (target : Adr) {out : Bytes}
    (width : 32 ≤ out.length) :
    decodeExternal (requestFor site target .feeTo) (feeObservedResult out) =
      .ok (.address (Bytes.toB256 (out.take 32)).toAdr) := by
  simp only [decodeExternal, requestFor, feeObservedResult, Bool.not_true,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, width]

/-- The original typed mint handler consumes the source acceptance derived from
the same actual factory observation; cached reserves are caller obligations. -/
theorem FeeMintSourceObservation.resume_mint {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {r1 r0 ρ : B256} {o : Outcome}
    (observation : FeeMintSourceObservation K st D sevm b R M r1 r0 ρ o)
    (prior : Frame) (observed : MintObserved)
    (state : prior.current.state = st)
    (reserve0 : observed.reserves.reserve0.val = r0.toNat)
    (reserve1 : observed.reserves.reserve1.val = r1.toNat) :
    StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
      (requestFor .mintFeeTo (feeFactoryWord sevm b).toAdr .feeTo).calldata observation.out ∧
    resumeSegment prior (requestFor .mintFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
      (.mintFee observed) (feeObservedResult observation.out) =
      (prior.beginResume (requestFor .mintFeeTo (feeFactoryWord sevm b).toAdr .feeTo)).mintAfterFee
        observed (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
          (Bytes.toB256 (observation.out.take 32)) r0 r1) := by
  refine ⟨observation.answer, ?_⟩
  rw [resumeSegment, feeObservedResult_decode _ _ observation.width]
  simp only [Frame.beginResume, state, reserve0, reserve1, observation.sourceResult.1]

/-- Burn uses the same cached observation after fee minting, including when the
fee recipient is the Pair.  The handler reads supply from the actual fee state. -/
theorem FeeMintSourceObservation.resume_burn {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {r1 r0 ρ : B256} {o : Outcome}
    (observation : FeeMintSourceObservation K st D sevm b R M r1 r0 ρ o)
    (prior : Frame) (observed : BurnObserved)
    (state : prior.current.state = st)
    (reserve0 : observed.locals.reserves.reserve0.val = r0.toNat)
    (reserve1 : observed.locals.reserves.reserve1.val = r1.toNat) :
    StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
      (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo).calldata observation.out ∧
    resumeSegment prior (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)
      (.burnFee observed) (feeObservedResult observation.out) =
      (prior.beginResume (requestFor .burnFeeTo (feeFactoryWord sevm b).toAdr .feeTo)).burnAfterFee
        observed (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
          (Bytes.toB256 (observation.out.take 32)) r0 r1) := by
  refine ⟨observation.answer, ?_⟩
  rw [resumeSegment, feeObservedResult_decode _ _ observation.width]
  simp only [Frame.beginResume, state, reserve0, reserve1, observation.sourceResult.1]


theorem WriterRep.feeFactory_target {K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st) :
    (feeFactoryWord sevm b).toAdr = st.factory := by
  simpa only [feeFactoryWord, Devm.getStorVal, Devm.getStor, toAdr_toB256] using rep.fixed.2.2.1

def feeMintObserved (toWord amount1 amount0 b1 b0 r1 r0 : B256)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) : MintObserved :=
  { recipient := toWord.toAdr, reserves := ⟨⟨r0.toNat, bound0⟩, ⟨r1.toNat, bound1⟩⟩,
    balance0 := b0, balance1 := b1, amount0 := amount0, amount1 := amount1 }

def feeBurnObserved (toWord token1 token0 L b1 b0 r1 r0 : B256)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) : BurnObserved :=
  { locals := ⟨toWord.toAdr, ⟨⟨r0.toNat, bound0⟩, ⟨r1.toNat, bound1⟩⟩,
      token0.toAdr, token1.toAdr⟩,
    balance0 := b0, balance1 := b1, liquidity := L }

/-- Burn's typed observation is built from the actual MLOAD and selected LP
SLOAD.  The later fee recipient can equal the Pair without changing this cache. -/
theorem feeBurn_typed_caller_inv {K : WriterKey → Prop} {st : State} {D : Exec.Deriv}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {len discarded b0 token1 token0 r1 r0 toWord extρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (tracked : K (.balance sevm.currentTarget))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (fresh : FeeMintSourceFresh K st D sevm (feeBurnWorld sevm b)
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
      (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2)
    (prior : Frame) (state : prior.current.state = st)
    (pair : prior.context.pair = sevm.currentTarget)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (len :: 128 :: discarded :: b0 :: token1 :: token0 :: r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R) M G)
      t_15c3_c37 r) :
    feeBurnLiquidity sevm b = st.balanceOf prior.context.pair ∧
    ∃ feeGas feePost, ∃ observation : FeeMintSourceObservation K st D sevm (feeBurnWorld sevm b)
      (burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M) b0 token1 token0 r1 r0 toWord extρ R)
      (feeBurnMemory M sevm.currentTarget) r1 r0 0x15e2 (.returned feePost),
      SFunc.RunP (StepIn D) cert.prog sevm
        (St (feeBurnWorld sevm b)
          (r1 :: r0 :: 0x15e2 :: burnFeeLocals (feeBurnLiquidity sevm b) (feeBurnBalance1 M)
            b0 token1 token0 r1 r0 toWord extρ R) (feeBurnMemory M sevm.currentTarget) feeGas)
        t_26ec_c68 (.returned feePost) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C feePost t_15e2_c37 r ∧
      StaticAnswered sevm (feeFactoryCallWorld sevm (feeBurnWorld sevm b)) st.factory
        (requestFor .burnFeeTo st.factory .feeTo).calldata observation.out ∧
      resumeSegment prior (requestFor .burnFeeTo st.factory .feeTo)
        (.burnFee (feeBurnObserved toWord token1 token0 (feeBurnLiquidity sevm b)
          (feeBurnBalance1 M) b0 r1 r0 bound0 bound1)) (feeObservedResult observation.out) =
        (prior.beginResume (requestFor .burnFeeTo st.factory .feeTo)).burnAfterFee
          (feeBurnObserved toWord token1 token0 (feeBurnLiquidity sevm b)
            (feeBurnBalance1 M) b0 r1 r0 bound0 bound1)
          (feeBranchSourceFee st sevm (feeKLastWorld sevm observation.d)
            (Bytes.toB256 (observation.out.take 32)) r0 r1) := by
  obtain ⟨cached, feeGas, feePost, callee, ⟨observation⟩, continuation⟩ :=
    feeBurn_source_caller_inv fork mem rep tracked bound0 bound1 fresh run
  have postRep : WriterRep K ((feeBurnWorld sevm b).getStor sevm.currentTarget) st := by
    rw [feeBurnWorld, afterSload_getStor]
    exact rep
  have typed := observation.resume_burn prior
    (feeBurnObserved toWord token1 token0 (feeBurnLiquidity sevm b)
      (feeBurnBalance1 M) b0 r1 r0 bound0 bound1) state rfl rfl
  rw [postRep.feeFactory_target] at typed
  rw [pair]
  exact ⟨cached, feeGas, feePost, observation, callee, continuation, typed⟩

end Blanc.Lift.UniswapV2Pair
