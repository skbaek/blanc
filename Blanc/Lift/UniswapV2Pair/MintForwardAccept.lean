import Blanc.Lift.UniswapV2Pair.MintSource
import Blanc.Lift.UniswapV2Pair.FeeMintSource
import Blanc.Lift.UniswapV2Pair.PairFeeSourceKeys
import Blanc.Lift.UniswapV2Pair.MintPrefixWalk
import Blanc.Lift.UniswapV2Pair.PropertiesMintBurn

/-!
# The mint forward environment, from the callees and the model's acceptance

`MintPrefixForwardEnv` (`MintPrefixWalk.lean`) bundles the mint frame's callees with the facts the
bytes check: the lock word, the `uint112` bounds and cover of the two token answers, the fee branch's
checked arithmetic, and the pricing arm's checked products, floors and LP credits.  Those facts are the
model's acceptance at the actual answers.  This module splits them off:

* `MintModelConditions` — the guards of the model's mint (`resumeSegment`'s `mintBalance1` and
  `mintFee` arms and `Frame.mintAfterFee`), at given token answers and factory answer;
* `MintPrefixCallee` (with `MintFeePricingCallee`, `FeeBranchCallee`, `MintAfterFeeCallee`,
  `MintInitialCallee`, `MintLaterCallee`) — the callee-only environment: the three `STATICCALL`s with
  their replies and returned gas, and the charge equations and residual sentries;
* `MintPrefixCallee.accepted` — the forward environment, from the callee environment, the model's
  acceptance at the actual answers, and HASH-T freshness of the three LP rows a mint may credit.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- **The model's mint guards** at the token answers `balance0`, `balance1` and the factory answer
`feeTo`, from the state `st` the frame enters: the call is non-payable and non-static, the lock is
open, both answers cover the reserves, the protocol fee mints, the pricing accepts, the minimum and
recipient LP credits fit, liquidity is positive and the reserve update accepts the answers. -/
def MintModelConditions (st : State) (ctx : Context) (recipient : Adr) (balance0 balance1 : B256)
    (feeTo : Adr) : Prop :=
  ctx.value = 0 ∧ ctx.isStatic = false ∧ st.unlocked = 1 ∧
  st.reserve0.val ≤ balance0.toNat ∧ st.reserve1.val ≤ balance1.toNat ∧
  ∃ (fee : FeeResult) (liquidity : Nat) (minimum recipientState post : State)
    (minimumEvents recipientEvents : List Event) (event : Event) (oracle : OracleUpdate),
    mintFee { st with unlocked := 0 } feeTo st.reserve0.val st.reserve1.val = .ok fee ∧
    mintAmount (balance0 - Nat.toB256 st.reserve0.val) (balance1 - Nat.toB256 st.reserve1.val)
      fee.state.totalSupply st.reserve0.val st.reserve1.val = .ok liquidity ∧
    (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000 else .ok (fee.state, [])) =
      .ok (minimum, minimumEvents) ∧
    0 < liquidity ∧
    minimum.mintLP recipient (Nat.toB256 liquidity) = .ok (recipientState, recipientEvents) ∧
    recipientState.update ctx balance0 balance1 st.reserve0.val st.reserve1.val =
      .ok (post, event, oracle)

/-- The model's reserve update accepts only balances that fit `uint112`. -/
theorem State.update_bounds {st : State} {ctx : Context} {balance0 balance1 : B256}
    {reserve0 reserve1 : Nat} {result : State × Event × OracleUpdate}
    (accepted : st.update ctx balance0 balance1 reserve0 reserve1 = .ok result) :
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 := by
  rw [State.update] at accepted
  by_cases bound0 : balance0.toNat < 2 ^ 112
  · rw [dite_eq_left bound0] at accepted
    by_cases bound1 : balance1.toNat < 2 ^ 112
    · exact ⟨bound0, bound1⟩
    · rw [dite_eq_right bound1] at accepted
      cases accepted
  · rw [dite_eq_right bound0] at accepted
    cases accepted

/-- The stored lock word is the model's lock. -/
theorem WriterRep.unlocked_word {K : WriterKey → Prop} {s : Stor} {st : State}
    (rep : WriterRep K s st) : s.get 12 = st.unlocked :=
  rep.fixed.2.2.2.2.2.2.2.2.2.2.2

/-! ## Converses of the pricing and LP acceptance -/

/-- Accepted first-mint pricing gives the raw checked product and cover. -/
theorem mintInitialAmount_raw {amount0 amount1 : B256} {r0 r1 liquidity : Nat}
    (accepted : mintAmount amount0 amount1 0 r0 r1 = .ok liquidity) :
    B256.Nofm amount0 amount1 ∧ (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256 ∧
      liquidity = (mintInitialLiquidity amount0 amount1).toNat := by
  rw [mintAmount, ite_eq_left rfl] at accepted
  by_cases product : amount0.toNat * amount1.toNat < 2 ^ 256
  swap
  · rw [ite_eq_right product] at accepted; cases accepted
  rw [ite_eq_left product] at accepted
  by_cases coverNat : 1000 ≤ Nat.sqrt (amount0.toNat * amount1.toNat)
  swap
  · rw [ite_eq_right coverNat] at accepted; cases accepted
  have rootBound : Nat.sqrt (amount0.toNat * amount1.toNat) < 2 ^ 256 :=
    lt_of_le_of_lt (Nat.sqrt_le_self _) product
  have rootRead : (Nat.sqrt (amount0 * amount1).toNat).toB256.toNat =
      Nat.sqrt (amount0.toNat * amount1.toNat) := by
    rw [B256.toNat_mul_eq_of_nofm product, B256.toNat_toB256_of_lt rootBound]
  have cover : (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256 := by
    rw [B256.le_iff_toNat_le_toNat, rootRead]
    exact coverNat
  refine ⟨product, cover, ?_⟩
  have same := (mintInitialAmount_source (r0 := r0) (r1 := r1) product cover)
  rw [mintAmount, ite_eq_left rfl, ite_eq_left product, ite_eq_left coverNat] at same
  rw [ite_eq_left coverNat] at accepted
  exact (Except.ok.inj accepted).symm.trans (Except.ok.inj same)

/-- Accepted later-mint pricing gives the raw checked products and nonzero divisors. -/
theorem mintLaterAmount_raw {amount0 amount1 supply r0 r1 : B256} {liquidity : Nat}
    (supplyNonzero : supply ≠ 0)
    (accepted : mintAmount amount0 amount1 supply r0.toNat r1.toNat = .ok liquidity) :
    B256.Nofm amount0 supply ∧ r0 ≠ 0 ∧ B256.Nofm amount1 supply ∧ r1 ≠ 0 ∧
      liquidity = (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)).toNat := by
  rw [mintAmount, ite_eq_right supplyNonzero] at accepted
  by_cases product0 : amount0.toNat * supply.toNat < 2 ^ 256
  swap
  · rw [ite_eq_right product0] at accepted; cases accepted
  rw [ite_eq_left product0] at accepted
  by_cases divisor0 : r0.toNat = 0
  · rw [ite_eq_left divisor0] at accepted; cases accepted
  rw [ite_eq_right divisor0] at accepted
  by_cases product1 : amount1.toNat * supply.toNat < 2 ^ 256
  swap
  · rw [ite_eq_right product1] at accepted; cases accepted
  rw [ite_eq_left product1] at accepted
  by_cases divisor1 : r1.toNat = 0
  · rw [ite_eq_left divisor1] at accepted; cases accepted
  rw [ite_eq_right divisor1] at accepted
  have nonzero0 : r0 ≠ 0 := fun h => divisor0 (by rw [h]; rfl)
  have nonzero1 : r1 ≠ 0 := fun h => divisor1 (by rw [h]; rfl)
  refine ⟨product0, nonzero0, product1, nonzero1, ?_⟩
  have same := mintLaterAmount_source supplyNonzero product0 nonzero0 product1 nonzero1
  rw [mintAmount, ite_eq_right supplyNonzero, ite_eq_left product0, ite_eq_right divisor0,
    ite_eq_left product1, ite_eq_right divisor1] at same
  exact (Except.ok.inj accepted).symm.trans (Except.ok.inj same)

/-- An accepted model LP credit, with the recipient row fresh, gives the raw LP guards. -/
theorem lpMintAccepts_of_model {K : WriterKey → Prop} {st post : State} {events : List Event}
    {sevm : Sevm} {b : Devm} {toWord value : B256}
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (fresh : WriterFreshKeys K (lpMintTouched toWord.toAdr))
    (nonstatic : sevm.isStatic = false)
    (accepted : st.mintLP toWord.toAdr value = .ok (post, events)) :
    lpMintAccepts sevm b toWord value := by
  have lp := lpMintLP_inv accepted
  have reads := lpMint_source_reads (value := value) rep fresh
  refine ⟨?_, nonstatic, ?_⟩
  · rw [reads.1]
    exact lp.1
  · rw [reads.2]
    exact lp.2.1

/-! ## The pricing arms -/

/-- The first-mint arm's callee-only data: the update and unlock charges and the store sentries. -/
structure MintInitialCallee (sevm : Sevm) (b : Devm) (f toWord amount0 amount1 b0 b1 r0 r1 : B256)
    (G : Nat) where
  finish : MintAfterUpdateEnv sevm
    (updateWorld sevm (mintLPWorld sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1))
      r0 r1 b0 b1) f amount0 amount1 G
  charges : MintUpdateEnv sevm
    (mintLPWorld sevm (mintLPWorld sevm b 0 1000) toWord (mintInitialLiquidity amount0 amount1)) r0 r1 b0 b1 finish.gas
  supplySentry : lpMintSupplySentry sevm (mintLPWorld sevm b 0 1000) toWord
    (mintInitialLiquidity amount0 amount1) (charges.gas + 27)
  creditSentry : lpMintCreditSentry sevm (mintLPWorld sevm b 0 1000) toWord
    (mintInitialLiquidity amount0 amount1) (charges.gas + 27)
  minimumSupplySentry : lpMintSupplySentry sevm b 0 1000
    (mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27))
  minimumCreditSentry : lpMintCreditSentry sevm b 0 1000
    (mintInitialMinimumResidual sevm b toWord amount0 amount1 (charges.gas + 27))

/-- The later-mint arm's callee-only data. -/
structure MintLaterCallee (sevm : Sevm) (b : Devm) (supply f toWord amount0 amount1 b0 b1 r0 r1 : B256)
    (G : Nat) where
  finish : MintAfterUpdateEnv sevm
    (updateWorld sevm (mintLPWorld sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)))
      r0 r1 b0 b1) f amount0 amount1 G
  charges : MintUpdateEnv sevm
    (mintLPWorld sevm b toWord (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0))) r0 r1 b0 b1 finish.gas
  supplySentry : lpMintSupplySentry sevm b toWord
    (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27)
  creditSentry : lpMintCreditSentry sevm b toWord
    (mintMinWord ((amount1 * supply) / r1) ((amount0 * supply) / r0)) (charges.gas + 27)

/-- The pricing arms' callee-only data, conditional on the actual supply word. -/
structure MintAfterFeeCallee (sevm : Sevm) (b : Devm) (f toWord amount0 amount1 b0 b1 r0 r1 : B256)
    (G : Nat) where
  initial : lpMintSupplyWord sevm b = 0 →
    MintInitialCallee sevm (afterSload sevm b 0) f toWord amount0 amount1 b0 b1 r0 r1 G
  later : lpMintSupplyWord sevm b ≠ 0 →
    MintLaterCallee sevm (afterSload sevm b 0) (lpMintSupplyWord sevm b) f toWord amount0 amount1 b0 b1 r0 r1 G

def MintAfterFeeCallee.armGas {sevm : Sevm} {b : Devm} {f toWord amount0 amount1 b0 b1 r0 r1 : B256}
    {G : Nat} (c : MintAfterFeeCallee sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) : Nat :=
  if zero : lpMintSupplyWord sevm b = 0 then
    lpMintGas sevm (afterSload sevm b 0) 0 1000 (mintInitialMinimumResidual sevm (afterSload sevm b 0)
        toWord amount0 amount1 ((c.initial zero).charges.gas + 27)) +
      26 + 122 + sqrtCharge (amount0 * amount1).toNat + mul58Charge amount1
  else
    lpMintGas sevm (afterSload sevm b 0) toWord
        (mintMinWord ((amount1 * lpMintSupplyWord sevm b) / r1) ((amount0 * lpMintSupplyWord sevm b) / r0))
        ((c.later zero).charges.gas + 27) +
      44 + 137 + mul58Charge (lpMintSupplyWord sevm b) + mul58Charge (lpMintSupplyWord sevm b) +
      mintMin70Gas ((amount1 * lpMintSupplyWord sevm b) / r1) ((amount0 * lpMintSupplyWord sevm b) / r0)

def MintAfterFeeCallee.post {sevm : Sevm} {b : Devm} {f toWord amount0 amount1 b0 b1 r0 r1 : B256}
    {G : Nat} (c : MintAfterFeeCallee sevm b f toWord amount0 amount1 b0 b1 r0 r1 G) (M : Mem)
    (R : List B256) (ρ : B256) : Devm :=
  if zero : lpMintSupplyWord sevm b = 0 then
    mintPricedPost sevm (mintLPWorld sevm (afterSload sevm b 0) 0 1000) R (mintLPBuffer M 0 1000)
      (lpMintSupplyWord sevm b) f amount1 amount0 b1 b0 r1 r0 (mintInitialLiquidity amount0 amount1) toWord ρ
      ((c.initial zero).charges.gas + 27) G
  else
    mintPricedPost sevm (afterSload sevm b 0) R M (lpMintSupplyWord sevm b) f amount1 amount0 b1 b0 r1 r0
      (mintMinWord ((amount1 * lpMintSupplyWord sevm b) / r1) ((amount0 * lpMintSupplyWord sevm b) / r0)) toWord ρ
      ((c.later zero).charges.gas + 27) G

/-- **The pricing environment from the model.**  At a world whose storage represents `st` over rows
inside a separated universe holding the address-zero and recipient LP rows, the model's accepted
pricing, minimum credit, positive liquidity and recipient credit give the pricing environment, with
the callee-only data's gas and post. -/
theorem MintAfterFeeCallee.accepted {U K : WriterKey → Prop} {st minimum recipientState : State}
    {minimumEvents recipientEvents : List Event} {liquidity : Nat}
    {sevm : Sevm} {b : Devm} {f toWord amount0 amount1 b0 b1 r0 r1 : B256} {G : Nat}
    (c : MintAfterFeeCallee sevm b f toWord amount0 amount1 b0 b1 r0 r1 G)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (row0 : U (.balance (0 : B256).toAdr)) (rowTo : U (.balance toWord.toAdr))
    (nonstatic : sevm.isStatic = false)
    (pricing : mintAmount amount0 amount1 st.totalSupply r0.toNat r1.toNat = .ok liquidity)
    (initialOk : (if st.totalSupply = 0 then st.mintLP (0 : B256).toAdr 1000 else .ok (st, [])) =
      .ok (minimum, minimumEvents))
    (positive : 0 < liquidity)
    (minted : minimum.mintLP toWord.toAdr (Nat.toB256 liquidity) = .ok (recipientState, recipientEvents)) :
    ∃ env : MintAfterFeeEnv sevm b f toWord amount0 amount1 b0 b1 r0 r1 G,
      env.armGas = c.armGas ∧ ∀ M R ρ, env.post M R ρ = c.post M R ρ := by
  have supplyWord : lpMintSupplyWord sevm b = st.totalSupply := rep.fixed.1
  have loaded : WriterRep K ((afterSload sevm b 0).getStor sevm.currentTarget) st := by
    rw [afterSload_getStor]
    exact rep
  have row0Fresh : WriterFreshKeys K (lpMintTouched (0 : B256).toAdr) :=
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub
      (fun k member => by rw [List.mem_singleton.mp member]; exact row0)
  have rowToFresh : ∀ {K' : WriterKey → Prop}, (∀ k, K' k → U k) →
      WriterFreshKeys K' (lpMintTouched toWord.toAdr) := fun sub' =>
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub'
      (fun k member => by rw [List.mem_singleton.mp member]; exact rowTo)
  have initialArm : ∀ zero : lpMintSupplyWord sevm b = 0,
      B256.Nofm amount0 amount1 ∧ (1000 : B256) ≤ (Nat.sqrt (amount0 * amount1).toNat).toB256 ∧
      0 < (mintInitialLiquidity amount0 amount1).toNat ∧
      lpMintAccepts sevm (afterSload sevm b 0) 0 1000 ∧
      lpMintAccepts sevm (mintLPWorld sevm (afterSload sevm b 0) 0 1000) toWord
        (mintInitialLiquidity amount0 amount1) := by
    intro zero
    have zeroSupply : st.totalSupply = 0 := supplyWord.symm.trans zero
    rw [zeroSupply] at pricing
    rw [ite_eq_left zeroSupply] at initialOk
    obtain ⟨product, cover, liquidityEq⟩ := mintInitialAmount_raw pricing
    have minimumAccepts := lpMintAccepts_of_model loaded row0Fresh nonstatic initialOk
    have minimumResult := lpMint_source_result (R := []) (M := Mem.empty) (G := 0)
      loaded row0Fresh minimumAccepts
    have minimumState := (lpMintLP_inv initialOk).2.2.1
    have minimumRep : WriterRep (WriterExtend K (lpMintTouched (0 : B256).toAdr))
        ((mintLPWorld sevm (afterSload sevm b 0) 0 1000).getStor sevm.currentTarget) minimum := by
      have h := minimumResult.2.1
      rw [mintLPPost_image, St_getStor, ← minimumState] at h
      exact h
    have extSub : ∀ k, WriterExtend K (lpMintTouched (0 : B256).toAdr) k → U k := by
      intro k member
      rcases member with old | row
      · exact sub k old
      · rw [List.mem_singleton.mp row]; exact row0
    rw [liquidityEq, toB256_toNat] at minted
    have recipientAccepts := lpMintAccepts_of_model minimumRep (rowToFresh extSub) nonstatic minted
    have positiveWord : 0 < (mintInitialLiquidity amount0 amount1).toNat := by
      rw [← liquidityEq]; exact positive
    exact ⟨product, cover, positiveWord, minimumAccepts, recipientAccepts⟩
  have laterArm : ∀ zero : lpMintSupplyWord sevm b ≠ 0,
      B256.Nofm amount0 (lpMintSupplyWord sevm b) ∧ B256.Nofm amount1 (lpMintSupplyWord sevm b) ∧
      r0 ≠ 0 ∧ r1 ≠ 0 ∧
      0 < (mintMinWord ((amount1 * lpMintSupplyWord sevm b) / r1)
        ((amount0 * lpMintSupplyWord sevm b) / r0)).toNat ∧
      lpMintAccepts sevm (afterSload sevm b 0) toWord
        (mintMinWord ((amount1 * lpMintSupplyWord sevm b) / r1)
          ((amount0 * lpMintSupplyWord sevm b) / r0)) := by
    intro zero
    have nonzeroSupply : st.totalSupply ≠ 0 := fun h => zero (supplyWord.trans h)
    rw [← supplyWord] at pricing
    rw [ite_eq_right nonzeroSupply] at initialOk
    cases initialOk
    obtain ⟨product0, nonzero0, product1, nonzero1, liquidityEq⟩ := mintLaterAmount_raw zero pricing
    rw [liquidityEq, toB256_toNat, supplyWord] at minted
    have recipientAccepts := lpMintAccepts_of_model loaded (rowToFresh sub) nonstatic minted
    rw [← supplyWord] at recipientAccepts
    have positiveWord : 0 < (mintMinWord ((amount1 * lpMintSupplyWord sevm b) / r1)
        ((amount0 * lpMintSupplyWord sevm b) / r0)).toNat := by
      rw [← liquidityEq]; exact positive
    exact ⟨product0, product1, nonzero0, nonzero1, positiveWord, recipientAccepts⟩
  refine ⟨⟨fun zero => ⟨(initialArm zero).1, (initialArm zero).2.1, (initialArm zero).2.2.1,
      (initialArm zero).2.2.2.1, (initialArm zero).2.2.2.2, (c.initial zero).finish,
      (c.initial zero).charges, (c.initial zero).supplySentry, (c.initial zero).creditSentry,
      (c.initial zero).minimumSupplySentry, (c.initial zero).minimumCreditSentry⟩,
    fun zero => ⟨(laterArm zero).1, (laterArm zero).2.1, (laterArm zero).2.2.1,
      (laterArm zero).2.2.2.1, (laterArm zero).2.2.2.2.1, (laterArm zero).2.2.2.2.2,
      (c.later zero).finish, (c.later zero).charges, (c.later zero).supplySentry,
      (c.later zero).creditSentry⟩⟩, ?_, ?_⟩
  · unfold MintAfterFeeEnv.armGas MintAfterFeeCallee.armGas
    by_cases zero : lpMintSupplyWord sevm b = 0
    · rw [dite_eq_left zero, dite_eq_left zero]
      rfl
    · rw [dite_eq_right zero, dite_eq_right zero]
      rfl
  · intro M R ρ
    unfold MintAfterFeeEnv.post MintAfterFeeCallee.post
    by_cases zero : lpMintSupplyWord sevm b = 0
    · rw [dite_eq_left zero]
    · rw [dite_eq_right zero]

/-! ## The fee call and fee branch -/

/-- The fee branch's callee-only data: the charge equations and the residual sentries
(`FeeBranchForward` without its acceptance guard). -/
structure FeeBranchCallee (sevm : Sevm) (b : Devm) (K w r0 r1 : B256)
    (G sourceCost supplyCost loadCost creditCost : Nat) : Prop where
  clearSentry : w.toAdr.toB256 = 0 → K ≠ 0 →
    gCallStipend < G + sstoreCost sevm b 11 0 + 23
  sourceEq : sourceCost = sloadCost sevm (afterSload sevm b 0) 0
  supplyEq : supplyCost = sstoreCost sevm (afterSload sevm (afterSload sevm b 0) 0) 0
    (lpMintSupplyWord sevm (afterSload sevm b 0) +
      feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1))
  loadEq : loadCost = sloadCost sevm
    (lpMintSupplyBase sevm (afterSload sevm (afterSload sevm b 0) 0)
      (lpMintSupplyWord sevm (afterSload sevm b 0) +
        feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)))
    (transferBalanceSlot w.toAdr)
  creditEq : creditCost = sstoreCost sevm
    (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm (afterSload sevm b 0) 0)
      (lpMintSupplyWord sevm (afterSload sevm b 0) +
        feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)))
      (transferBalanceSlot w.toAdr)) (transferBalanceSlot w.toAdr)
    (lpMintRecipientWord sevm (afterSload sevm (afterSload sevm b 0) 0) w
      (lpMintSupplyWord sevm (afterSload sevm b 0) +
        feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)) +
      feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1))
  supplySentry : w.toAdr.toB256 ≠ 0 → K ≠ 0 → feeLastRoot K < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1) ≠ 0 →
    gCallStipend < G + supplyCost + loadCost + creditCost + 2124
  creditSentry : w.toAdr.toB256 ≠ 0 → K ≠ 0 → feeLastRoot K < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1) ≠ 0 →
    gCallStipend < G + creditCost + 1875

/-- The factory call and pricing arms' callee-only data (`MintFeePricingForward` without the answers'
bounds and cover, the fee branch's guard and the pricing arms' acceptance). -/
structure MintFeePricingCallee (sevm : Sevm) (b d : Devm) (R : List B256) (M : Mem)
    (feeResidual finalGas callGas sourceCost supplyCost loadCost creditCost : Nat)
    (b1 b0 r1 r0 toWord ρ : B256) where
  code : ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0
  call : Ninst.RunCompiled sevm
      (St (feeFactoryCallWorld sevm b)
        (callGas.toB256 :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: 0x1233 ::
          mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d
  success : d.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm b ::
      0 :: 0 :: r1 :: r0 :: 0x1233 :: mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R
  width : 32 ≤ d.returnData.length
  returnedGas : d.gasLeft = feeResidual +
      feeBranchCharge sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 sourceCost supplyCost loadCost creditCost +
      sloadCost sevm d 11 + 120
  forward : FeeBranchCallee sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual sourceCost supplyCost loadCost creditCost
  pricing : MintAfterFeeCallee sevm
      (feeBranchPost sevm (feeKLastWorld sevm d)
        (mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
        (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual)
      (feeOnWord (Bytes.toB256 (d.returnData.take 32))) toWord (b0-r0) (b1-r1) b0 b1 r0 r1 finalGas
  residualCharge : feeResidual = pricing.armGas + sloadCost sevm
      (feeBranchPost sevm (feeKLastWorld sevm d)
        (mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
        (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual) 0 + 28

/-- The fee branch's tracked rows stay inside a universe holding the fee recipient's row. -/
theorem feeBranchSourceKeys_sub {U K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    {w r0 r1 : B256} (sub : ∀ k, K k → U k) (row : U (.balance w.toAdr)) :
    ∀ k, feeBranchSourceKeys K st sevm b w r0 r1 k → U k :=
  pairFeeSourceKeys_sub sub row st sevm b r0 r1

def MintFeePricingCallee.post {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {feeResidual finalGas callGas sourceCost supplyCost loadCost creditCost : Nat}
    {b1 b0 r1 r0 toWord ρ : B256}
    (c : MintFeePricingCallee sevm b d R M feeResidual finalGas callGas
      sourceCost supplyCost loadCost creditCost b1 b0 r1 r0 toWord ρ) : Devm :=
  c.pricing.post (feeBranchPost sevm (feeKLastWorld sevm d)
    (mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
    (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
    (Bytes.toB256 (d.returnData.take 32)) r0 r1 feeResidual).memory R ρ

/-- **The fee call and pricing environment from the model.**  At the world after the token calls,
whose storage represents the locked state `st`, the model's accepted fee mint at the factory's actual
answer, its accepted pricing and LP credits, the answers' bounds and cover, and HASH-T rows for the fee
recipient, address zero and the recipient give `MintFeePricingForward`, with the callee data's gas and
post. -/
theorem MintFeePricingCallee.accepted {U K : WriterKey → Prop} {st minimum recipientState : State}
    {fee : FeeResult} {minimumEvents recipientEvents : List Event} {liquidity : Nat}
    {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {feeResidual finalGas callGas sourceCost supplyCost loadCost creditCost : Nat}
    {b1 b0 r1 r0 toWord ρ : B256}
    (c : MintFeePricingCallee sevm b d R M feeResidual finalGas callGas
      sourceCost supplyCost loadCost creditCost b1 b0 r1 r0 toWord ρ)
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (rowFee : U (.balance (Bytes.toB256 (d.returnData.take 32)).toAdr))
    (row0 : U (.balance (0 : B256).toAdr)) (rowTo : U (.balance toWord.toAdr))
    (nonstatic : sevm.isStatic = false)
    (reserveBound0 : r0.toNat < 2 ^ 112) (reserveBound1 : r1.toNat < 2 ^ 112)
    (balanceBound0 : b0.toNat < 2 ^ 112) (balanceBound1 : b1.toNat < 2 ^ 112)
    (cover0 : r0 ≤ b0) (cover1 : r1 ≤ b1)
    (accepted : mintFee st (Bytes.toB256 (d.returnData.take 32)).toAdr r0.toNat r1.toNat = .ok fee)
    (pricing : mintAmount (b0 - r0) (b1 - r1) fee.state.totalSupply r0.toNat r1.toNat = .ok liquidity)
    (initialOk : (if fee.state.totalSupply = 0 then fee.state.mintLP (0 : B256).toAdr 1000
      else .ok (fee.state, [])) = .ok (minimum, minimumEvents))
    (positive : 0 < liquidity)
    (minted : minimum.mintLP toWord.toAdr (Nat.toB256 liquidity) = .ok (recipientState, recipientEvents)) :
    ∃ env : MintFeePricingForward sevm b d R M feeResidual finalGas callGas
        sourceCost supplyCost loadCost creditCost b1 b0 r1 r0 toWord ρ,
      env.post = c.post := by
  let w := Bytes.toB256 (d.returnData.take 32)
  have post := feeFactoryCompiled_post fork c.call c.success
  have postRep := rep.fee_factory_post post
  have last : feeKLastWord sevm d = st.kLast := by
    rcases postRep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, lastWord, _⟩
    change (d.getStor sevm.currentTarget).get 11 = st.kLast
    simpa only [feeKLastWorld, afterSload_getStor] using lastWord
  have fresh : FeeMintFresh K st sevm (feeKLastWorld sevm d) w r0 r1 := fun _ _ _ _ =>
    Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub
      (fun k member => by rw [List.mem_singleton.mp member]; exact rowFee)
  have writes : FeeMintWrites st sevm (feeKLastWorld sevm d) w r0 r1 :=
    ⟨fun _ _ => nonstatic, fun _ _ _ _ => nonstatic⟩
  have guards := feeBranch_raw_guards postRep reserveBound0 reserveBound1 accepted fresh writes
  have source := feeBranch_source_result
    (R := mintFeeLocals (b1-r1) (b0-r0) b1 b0 r1 r0 toWord ρ R)
    (M := feeReplyMemory M d.returnData) (G := feeResidual) postRep reserveBound0 reserveBound1
    guards fresh
  have feeEq : feeBranchSourceFee st sevm (feeKLastWorld sevm d) w r0 r1 = fee :=
    Except.ok.inj (source.1.symm.trans accepted)
  have pricedRep := source.2.1
  rw [feeEq, ← last] at pricedRep
  obtain ⟨penv, penvGas, penvPost⟩ := c.pricing.accepted pricedRep inj apart
    (feeBranchSourceKeys_sub sub rowFee) row0 rowTo nonstatic pricing initialOk positive minted
  rw [← last] at guards
  refine ⟨⟨balanceBound0, balanceBound1, cover0, cover1, c.code, c.call, c.success, c.width,
    c.returnedGas, ⟨guards, c.forward.clearSentry, c.forward.sourceEq, c.forward.supplyEq,
      c.forward.loadEq, c.forward.creditEq, c.forward.supplySentry, c.forward.creditSentry⟩,
    penv, by rw [penvGas]; exact c.residualCharge⟩, ?_⟩
  unfold MintFeePricingForward.post MintFeePricingCallee.post
  exact penvPost _ _ _

/-! ## The whole forward environment -/

/-- The callee-only mint environment: the two token `balanceOf` `STATICCALL`s and the factory `feeTo`
`STATICCALL` with their replies and returned gas, the lock and reserve charges, the pricing arms'
charges and every residual sentry (`MintPrefixForwardEnv` without the lock word, the frame's
non-static flag, and the answers' acceptance facts). -/
structure MintPrefixCallee (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (toWord ρ : B256) (finalGas : Nat) where
  d0 : Devm
  d1 : Devm
  factoryPost : Devm
  callGas0 : Nat
  callGas1 : Nat
  factoryGas : Nat
  feeResidual : Nat
  sourceCost : Nat
  supplyCost : Nat
  recipientLoad : Nat
  creditCost : Nat
  lockLoad : Nat
  lockStore : Nat
  reserveLoad : Nat
  loadEq : lockLoad = sloadCost sevm b 12
  storeEq : lockStore = sstoreCost sevm (afterSload sevm b 12) 12 0
  reserveEq : reserveLoad = sloadCost sevm (mintLockedWorld sevm b) 8
  fee : MintFeePricingCallee sevm d1 factoryPost R
    (balanceReplyMemory (balanceReplyMemory M sevm.currentTarget d0.returnData)
      sevm.currentTarget d1.returnData)
    feeResidual finalGas factoryGas sourceCost supplyCost recipientLoad creditCost
    (Bytes.toB256 (d1.returnData.take 32)) (Bytes.toB256 (d0.returnData.take 32))
    (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)) toWord ρ
  tokens : MintBalanceForward sevm (afterSload sevm (mintLockedWorld sevm b) 8) d0 d1 R M
    callGas0 callGas1
    (factoryGas + sloadCost sevm d1 5 +
      temporalAccountAccessCost (feeFactoryLoadWorld sevm d1) (feeFactoryWord sevm d1).toAdr + 360)
    (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)) toWord ρ
  sentry : gCallStipend < callGas0 + 5 +
    sloadCost sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6 +
    temporalAccountAccessCost (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6)
      ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr +
    166 + reserveLoad + 87 + lockStore

/-- The mint frame's entry gas, from the callee environment (`MintPrefixForwardEnv.gas`). -/
def MintPrefixCallee.gas {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord ρ : B256} {finalGas : Nat} (c : MintPrefixCallee sevm b R M toWord ρ finalGas) : Nat :=
  c.callGas0 + 5 + sloadCost sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6 +
    temporalAccountAccessCost (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6)
      ((afterSload sevm (mintLockedWorld sevm b) 8).getStorVal sevm.currentTarget 6).toAdr + 166 +
    c.reserveLoad + 100 + c.lockStore + c.lockLoad + 26

/-- The token answers and the factory answer of the callee environment. -/
def MintPrefixCallee.balance0 {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord ρ : B256} {finalGas : Nat} (c : MintPrefixCallee sevm b R M toWord ρ finalGas) : B256 :=
  Bytes.toB256 (c.d0.returnData.take 32)

def MintPrefixCallee.balance1 {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord ρ : B256} {finalGas : Nat} (c : MintPrefixCallee sevm b R M toWord ρ finalGas) : B256 :=
  Bytes.toB256 (c.d1.returnData.take 32)

def MintPrefixCallee.feeTo {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {toWord ρ : B256} {finalGas : Nat} (c : MintPrefixCallee sevm b R M toWord ρ finalGas) : Adr :=
  (Bytes.toB256 (c.factoryPost.returnData.take 32)).toAdr

/-- A compiled successful `STATICCALL` keeps every account's storage of its staged world. -/
theorem compiled_staticcall_stor {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem}
    {G : Nat} {g t ii is oi os : B256} (fork : CoveredFork sevm.benvStat.fork)
    (call : Ninst.RunCompiled sevm (St b (g :: t :: ii :: is :: oi :: os :: S) M G)
      (.exec .staticcall) d) :
    ∀ a, Devm.getStor d a = Devm.getStor b a := by
  obtain ⟨_, _, post, _, _⟩ := ri_staticcall_bounded fork (by
    rcases call with ⟨xl, compiled, run⟩
    exact ⟨xl, compiled, 0, run 0⟩)
  exact post.stor

/-- **The mint forward environment from the callees and the model.**  At a frame whose storage
represents `st` over rows inside a separated universe holding the LP rows of address zero, the
recipient and the factory's actual `feeTo` answer, the model's mint guards at the callees' actual
answers (`MintModelConditions`) give `MintPrefixForwardEnv`, with the callee environment's gas and
post. -/
theorem MintPrefixCallee.accepted {U K : WriterKey → Prop} {st : State} {sevm : Sevm} {b : Devm}
    {G : Nat}
    (c : MintPrefixCallee sevm b [0x6a627842] getterInitMemory
      (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43))
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (rowFee : U (.balance c.feeTo)) (row0 : U (.balance (0 : B256).toAdr))
    (rowTo : U (.balance (Sevm.dataWord sevm 4).toAdr))
    (conditions : MintModelConditions st (writerContext sevm []) (Sevm.dataWord sevm 4).toAdr
      c.balance0 c.balance1 c.feeTo) :
    ∃ env : MintPrefixForwardEnv sevm b [0x6a627842] getterInitMemory
        (Sevm.dataWord sevm 4).toAdr.toB256 0x039b (G + 43),
      env.gas = c.gas ∧ env.fee.post = c.fee.post := by
  obtain ⟨_, nonstatic, unlocked, cover0, cover1, fee, liquidity, minimum, recipientState, post,
    minimumEvents, recipientEvents, event, oracle, feeAccepted, pricing, initialOk, positive, minted,
    updated⟩ := conditions
  have nonstatic' : sevm.isStatic = false := nonstatic
  have unlockedRaw : b.getStorVal sevm.currentTarget 12 = 1 :=
    rep.fixed.2.2.2.2.2.2.2.2.2.2.2.trans unlocked
  have lockedRep := rep.mint_locked_world (sevm := sevm) (b := b)
  rcases lockedRep.fixed with ⟨_, _, _, _, _, cache0, cache1, _, _, _, _, _⟩
  change reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) =
    Nat.toB256 st.reserve0.val at cache0
  change reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) =
    Nat.toB256 st.reserve1.val at cache1
  have natCache0 : (Nat.toB256 st.reserve0.val).toNat = st.reserve0.val :=
    B256.toNat_toB256_of_lt (lt_trans st.reserve0.isLt (by decide : 2 ^ 112 < 2 ^ 256))
  have natCache1 : (Nat.toB256 st.reserve1.val).toNat = st.reserve1.val :=
    B256.toNat_toB256_of_lt (lt_trans st.reserve1.isLt (by decide : 2 ^ 112 < 2 ^ 256))
  -- storage after the two token calls is the locked storage
  have stor0 := compiled_staticcall_stor fork c.tokens.call0
  have stor1 := compiled_staticcall_stor fork c.tokens.call1
  have d1Rep : WriterRep K (c.d1.getStor sevm.currentTarget) { st with unlocked := 0 } := by
    have same : c.d1.getStor sevm.currentTarget =
        (mintLockedWorld sevm b).getStor sevm.currentTarget := by
      rw [stor1]
      simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
      change (afterSload sevm c.d0 7).getStor sevm.currentTarget = _
      rw [afterSload_getStor, stor0]
      simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
      change (afterSload sevm (afterSload sevm (mintLockedWorld sevm b) 8) 6).getStor
        sevm.currentTarget = _
      rw [afterSload_getStor, afterSload_getStor]
      rfl
    rw [same]
    exact lockedRep
  obtain ⟨bound0, bound1⟩ := State.update_bounds updated
  have rBound0 : (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat <
      2 ^ 112 := by rw [cache0, natCache0]; exact st.reserve0.isLt
  have rBound1 : (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat <
      2 ^ 112 := by rw [cache1, natCache1]; exact st.reserve1.isLt
  have wordCover0 : reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ≤
      c.balance0 := by
    rw [B256.le_iff_toNat_le_toNat, cache0, natCache0]; exact cover0
  have wordCover1 : reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ≤
      c.balance1 := by
    rw [B256.le_iff_toNat_le_toNat, cache1, natCache1]; exact cover1
  have feeAccepted' : mintFee { st with unlocked := 0 } c.feeTo
      (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat = .ok fee := by
    rw [cache0, cache1, natCache0, natCache1]; exact feeAccepted
  have pricing' : mintAmount
      (c.balance0 - reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
      (c.balance1 - reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8))
      fee.state.totalSupply
      (reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat
      (reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8)).toNat =
        .ok liquidity := by
    rw [cache0, cache1, natCache0, natCache1]; exact pricing
  have minted' : minimum.mintLP ((Sevm.dataWord sevm 4).toAdr.toB256).toAdr (Nat.toB256 liquidity) =
      .ok (recipientState, recipientEvents) := by
    rw [toAdr_toB256]; exact minted
  obtain ⟨fenv, fenvPost⟩ := c.fee.accepted fork d1Rep inj apart sub rowFee row0
    (by rw [toAdr_toB256]; exact rowTo) nonstatic' rBound0 rBound1 bound0 bound1 wordCover0
    wordCover1 feeAccepted' pricing' initialOk positive minted'
  exact ⟨⟨c.d0, c.d1, c.factoryPost, c.callGas0, c.callGas1, c.factoryGas, c.feeResidual,
    c.sourceCost, c.supplyCost, c.recipientLoad, c.creditCost, c.lockLoad, c.lockStore, c.reserveLoad,
    unlockedRaw, nonstatic', c.loadEq, c.storeEq, c.reserveEq, fenv, c.tokens, c.sentry⟩, rfl,
    fenvPost⟩

/-! ## Model acceptance gives the mint guards -/

/-- The guards of the model's post-fee mint continuation (`Frame.mintAfterFee`). -/
def MintAfterFeeGuards (ctx : Context) (observed : MintObserved) (fee : FeeResult) : Prop :=
  ∃ (liquidity : Nat) (minimum recipientState post : State)
    (minimumEvents recipientEvents : List Event) (event : Event) (oracle : OracleUpdate),
    mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok liquidity ∧
    (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000 else .ok (fee.state, [])) =
      .ok (minimum, minimumEvents) ∧
    0 < liquidity ∧
    minimum.mintLP observed.recipient (Nat.toB256 liquidity) = .ok (recipientState, recipientEvents) ∧
    recipientState.update ctx observed.balance0 observed.balance1
      observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok (post, event, oracle)

/-- A successful post-fee mint continuation passes all of its guards. -/
theorem Frame.mintAfterFee_guards {fuel : Nat} {frame : Frame} {observed : MintObserved}
    {fee : FeeResult} {tail : Transcript} {returndata : Bytes}
    (successful : (drive fuel (frame.mintAfterFee observed fee) tail).status = .success returndata) :
    MintAfterFeeGuards frame.context observed fee := by
  unfold Frame.mintAfterFee at successful
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure =>
    simp only [priced, Frame.fail] at successful
    exact absurd successful (drive_failed_not_success fuel _ _ tail returndata)
  | ok liquidity =>
    simp only [priced] at successful
    cases initial : (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000
        else .ok (fee.state, [])) with
    | error failure =>
      simp only [initial, Frame.fail] at successful
      exact absurd successful (drive_failed_not_success fuel _ _ tail returndata)
    | ok pair =>
      rcases pair with ⟨minimum, minimumEvents⟩
      simp only [initial] at successful
      by_cases positive : liquidity > 0
      swap
      · simp only [ite_eq_right positive, Frame.fail] at successful
        exact absurd successful (drive_failed_not_success fuel _ _ tail returndata)
      simp only [ite_eq_left positive] at successful
      cases minted : minimum.mintLP observed.recipient (Nat.toB256 liquidity) with
      | error failure =>
        simp only [minted, Frame.fail] at successful
        exact absurd successful (drive_failed_not_success fuel _ _ tail returndata)
      | ok result =>
        rcases result with ⟨recipientState, recipientEvents⟩
        simp only [minted] at successful
        unfold Frame.finishUpdated at successful
        cases updated : recipientState.update frame.context observed.balance0 observed.balance1
            observed.reserves.reserve0.val observed.reserves.reserve1.val with
        | error failure =>
          simp only [Frame.withEvents, updated, Frame.fail] at successful
          exact absurd successful (drive_failed_not_success fuel _ _ tail returndata)
        | ok result =>
          rcases result with ⟨post, event, oracle⟩
          exact ⟨liquidity, minimum, recipientState, post, minimumEvents, recipientEvents, event,
            oracle, priced, initial, positive, minted, updated⟩

/-- A successful mint fee query passes the fee mint at its decoded recipient and every later guard. -/
theorem drive_mintFee_guards {fuel : Nat} {frame : Frame} {request : Request}
    {observed : MintObserved} {transcript : Transcript} {returndata : Bytes}
    (operation : request.operation = .feeTo) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintFee observed))
      transcript).status = .success returndata) :
    ∃ fee, mintFee frame.current.state transcript.firstWord.toAdr
        observed.reserves.reserve0.val observed.reserves.reserve1.val = .ok fee ∧
      MintAfterFeeGuards frame.context observed fee := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
      drive_suspended_success successful
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | word value =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | address feeTo =>
        have recipientEq := decodeExternal_feeTo_address operation decoded
        cases charged : mintFee (frame.beginResume request).current.state feeTo
            observed.reserves.reserve0.val observed.reserves.reserve1.val with
        | error failure =>
          simp only [resumeSegment, decoded, charged, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _ failure tail returndata resumedSuccess)
        | ok fee =>
          simp only [resumeSegment, decoded, charged] at resumedSuccess
          refine ⟨fee, ?_, Frame.mintAfterFee_guards (frame := frame.beginResume request) resumedSuccess⟩
          rw [shape, Transcript.firstWord, ← recipientEq]
          exact charged

/-- A successful second mint balance query passes both covers, the fee mint and every later guard. -/
theorem drive_mintBalance1_guards {fuel : Nat} {frame : Frame} {request : Request}
    {recipient owner : Adr} {reserves : CachedReserves} {balance0 : B256}
    {transcript : Transcript} {returndata : Bytes}
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance1 recipient reserves balance0))
      transcript).status = .success returndata) :
    reserves.reserve0.val ≤ balance0.toNat ∧ reserves.reserve1.val ≤ transcript.firstWord.toNat ∧
      ∃ fee, mintFee frame.current.state transcript.ownTail.firstWord.toAdr
          reserves.reserve0.val reserves.reserve1.val = .ok fee ∧
        MintAfterFeeGuards frame.context
          (mintObservation recipient reserves balance0 transcript.firstWord) fee := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
      drive_suspended_success successful
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance1 =>
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded] at resumedSuccess
        by_cases backing : reserves.reserve0.val ≤ balance0.toNat ∧
            reserves.reserve1.val ≤ balance1.toNat
        · rw [ite_eq_left backing] at resumedSuccess
          simp only [Frame.suspend] at resumedSuccess
          obtain ⟨fee, charged, guards⟩ := drive_mintFee_guards rfl rfl resumedSuccess
          have firstEq : transcript.firstWord = balance1 := by
            rw [shape, Transcript.firstWord, ← observedWord]
          refine ⟨backing.1, firstEq ▸ backing.2, fee, ?_, ?_⟩
          · rw [shape, Transcript.ownTail]
            exact charged
          · rw [firstEq]
            exact guards
        · simp only [ite_eq_right backing, Frame.fail] at resumedSuccess
          exact False.elim (drive_failed_not_success fuel _
            (.sourceGuard "ds-math-sub-underflow") tail returndata resumedSuccess)

/-- A successful first mint balance query passes both covers at the decoded answers, the fee mint and
every later guard. -/
theorem drive_mintBalance0_guards {fuel : Nat} {frame : Frame} {request : Request}
    {recipient owner : Adr} {reserves : CachedReserves}
    {transcript : Transcript} {returndata : Bytes}
    (operation : request.operation = .balanceOf owner) (kind : request.kind = .staticCall)
    (successful : (drive fuel (.suspended frame request (.mintBalance0 recipient reserves))
      transcript).status = .success returndata) :
    reserves.reserve0.val ≤ transcript.firstWord.toNat ∧
      reserves.reserve1.val ≤ transcript.ownTail.firstWord.toNat ∧
      ∃ fee, mintFee frame.current.state transcript.ownTail.ownTail.firstWord.toAdr
          reserves.reserve0.val reserves.reserve1.val = .ok fee ∧
        MintAfterFeeGuards frame.context
          (mintObservation recipient reserves transcript.firstWord transcript.ownTail.firstWord) fee := by
  cases fuel with
  | zero => cases successful
  | succ fuel =>
    obtain ⟨result, turns, tail, shape, _complete, resumedSuccess, _⟩ :=
      drive_suspended_success successful
    have staticExternal : externalStatic frame request = true := by
      rw [externalStatic, kind]
      cases frame.context.isStatic <;> rfl
    have settled := Frame.settleExternal_static_frame frame fuel request result turns staticExternal
    rw [settled] at resumedSuccess
    cases decoded : decodeExternal request result with
    | error failure =>
      exact False.elim (resumeSegment_error_not_success decoded fuel tail returndata resumedSuccess)
    | ok decodedResult =>
      cases decodedResult with
      | address address =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | unit =>
        simp only [resumeSegment, decoded, Frame.fail] at resumedSuccess
        exact False.elim
          (drive_failed_not_success fuel _ .incompleteTranscript tail returndata resumedSuccess)
      | word balance0 =>
        have observedWord := decodeExternal_balance_word operation decoded
        simp only [resumeSegment, decoded, Frame.suspend] at resumedSuccess
        obtain ⟨cover0, cover1, fee, charged, guards⟩ := drive_mintBalance1_guards rfl rfl resumedSuccess
        have firstEq : transcript.firstWord = balance0 := by
          rw [shape, Transcript.firstWord, ← observedWord]
        have tailEq : transcript.ownTail = tail := by rw [shape, Transcript.ownTail]
        rw [firstEq, tailEq]
        exact ⟨cover0, cover1, fee, charged, guards⟩

/-- **The model's acceptance gives the mint guards.**  Every mint the model accepts — whatever the
transcript — passes `MintModelConditions` at the transcript's three answers: the two token balances
(its first two words) and the factory's `feeTo` answer (its third word). -/
theorem runTyped_mint_conditions {st : State} {ctx : Context} {recipient : Adr}
    {transcript : Transcript} {returndata : Bytes}
    (successful : (runTyped st ctx (.mint recipient) transcript).status = .success returndata) :
    MintModelConditions st ctx recipient transcript.firstWord transcript.ownTail.firstWord
      transcript.ownTail.ownTail.firstWord.toAdr := by
  let current : Checkpoint := { state := st, logs := [], updates := [] }
  change (drive (transcript.work + 2) (startTyped current ctx (.mint recipient)) transcript).status =
    .success returndata at successful
  by_cases paid : ctx.value ≠ 0
  · simp only [startTyped, startImmediate, ite_eq_left paid, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .emptyRevert transcript returndata successful)
  by_cases unlocked : st.unlocked = 1
  swap
  · have enteredLocked : ¬(Frame.enter current ctx (.mint recipient)).current.state.unlocked = 1 :=
      unlocked
    have closed : (Frame.enter current ctx (.mint recipient)).lock =
        .error (.sourceGuard "UniswapV2: LOCKED") := by
      rw [Frame.lock, ite_eq_right enteredLocked]
    simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, closed,
      Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _
      (.sourceGuard "UniswapV2: LOCKED") transcript returndata successful)
  have unlockedCurrent : current.state.unlocked = 1 := unlocked
  by_cases staticContext : ctx.isStatic = true
  · simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, Frame.lock,
      Frame.enter, ite_eq_left unlockedCurrent, staticContext, ite_true, Frame.fail] at successful
    exact False.elim (drive_failed_not_success _ _ .staticWrite transcript returndata successful)
  let lockedFrame : Frame :=
    { Frame.enter current ctx (.mint recipient) with
      current := { current with state := { st with unlocked := 0 } } }
  have enteredUnlocked : (Frame.enter current ctx (.mint recipient)).current.state.unlocked = 1 :=
    unlocked
  have enteredStatic : ¬(Frame.enter current ctx (.mint recipient)).context.isStatic = true :=
    staticContext
  have opened : (Frame.enter current ctx (.mint recipient)).lock = .ok lockedFrame := by
    rw [Frame.lock, ite_eq_left enteredUnlocked, ite_eq_right enteredStatic]
    rfl
  have stage : startTyped current ctx (.mint recipient) =
      lockedFrame.suspend .mintBalance0 st.token0 (.balanceOf ctx.pair)
        (.mintBalance0 recipient st.cachedReserves) := by
    simp only [startTyped, startImmediate, ite_eq_right paid, getterResult, opened]
    rfl
  rw [stage] at successful
  simp only [Frame.suspend] at successful
  obtain ⟨cover0, cover1, fee, charged, guards⟩ := drive_mintBalance0_guards rfl rfl successful
  obtain ⟨liquidity, minimum, recipientState, post, minimumEvents, recipientEvents, event, oracle,
    priced, initial, positive, minted, updated⟩ := guards
  have value : ctx.value = 0 := by
    by_contra h
    exact paid h
  have nonstatic : ctx.isStatic = false := by
    cases h : ctx.isStatic
    · rfl
    · exact absurd h staticContext
  exact ⟨value, nonstatic, unlocked, cover0, cover1, fee, liquidity, minimum, recipientState, post,
    minimumEvents, recipientEvents, event, oracle, charged, priced, initial, positive, minted,
    updated⟩

end Blanc.Lift.UniswapV2Pair
