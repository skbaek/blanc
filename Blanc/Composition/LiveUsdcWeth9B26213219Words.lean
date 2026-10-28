import Blanc.Composition.LiveUsdcWeth9B26213219Data.Data
import Blanc.Composition.UniswapV2PairUsdcWeth9HybridCheckpoint

/-!
# Finite word facts for the frozen B26213219 observation

These kernel proofs decode the supplied fixed words without evaluating a concrete
storage map. `PairWordsAt` is the finite observation boundary on an arbitrary
storage. The model's empty maps are only placeholders for the finite checker;
historical representation supplies the actual maps through model transport.
The fetched data remains unadmitted; this module does not authenticate its state
root, establish historical representation, or prove the supplied code identities.
-/

namespace Blanc.Composition.LiveUsdcWeth9B26213219

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair
  Blanc.Composition.UniswapV2PairUsdcWeth9

open LiveUsdcWeth9B26213219Data

def pair : Adr := pairCodeAccount.toAdr
def usdc : Adr := usdcProxyCodeAccount.toAdr
def weth : Adr := weth9CodeAccount.toAdr

/-- Only fixed fields are modeled here; the maps carry no historical claim. -/
def finiteModel : UniswapV2Pair.State :=
  { totalSupply := pairSlot0Word
    balanceOf := fun _ => 0
    allowance := fun _ _ => 0
    domainSeparator := pairSlot3Word
    nonces := fun _ => 0
    factory := pairSlot5Word.toAdr
    token0 := pairSlot6Word.toAdr
    token1 := pairSlot7Word.toAdr
    reserve0 := ⟨(reserve0Read pairSlot8Word).toNat, by decide +kernel⟩
    reserve1 := ⟨(reserve1Read pairSlot8Word).toNat, by decide +kernel⟩
    blockTimestampLast := UInt32.ofNat (reserveTimestampRead pairSlot8Word).toNat
    price0CumulativeLast := pairSlot9Word
    price1CumulativeLast := pairSlot10Word
    kLast := pairSlot11Word
    unlocked := pairSlot12Word }

/-- Exactly the ten supplied fixed-slot observations, on arbitrary storage. -/
structure PairWordsAt (s : Stor) : Prop where
  supply : s.get pairSlot0WordSlot = pairSlot0Word
  domain : s.get pairSlot3WordSlot = pairSlot3Word
  factory : s.get pairSlot5WordSlot = pairSlot5Word
  token0 : s.get pairSlot6WordSlot = pairSlot6Word
  token1 : s.get pairSlot7WordSlot = pairSlot7Word
  reserves : s.get pairSlot8WordSlot = pairSlot8Word
  cumulative0 : s.get pairSlot9WordSlot = pairSlot9Word
  cumulative1 : s.get pairSlot10WordSlot = pairSlot10Word
  kLast : s.get pairSlot11WordSlot = pairSlot11Word
  unlocked : s.get pairSlot12WordSlot = pairSlot12Word

theorem reserve0_word :
    reserve0Read pairSlot8Word = Nat.toB256 finiteModel.reserve0.val := by
  decide +kernel

theorem reserve1_word :
    reserve1Read pairSlot8Word = Nat.toB256 finiteModel.reserve1.val := by
  decide +kernel

theorem reserveTimestamp_word :
    reserveTimestampRead pairSlot8Word = finiteModel.blockTimestampLast.toB256 := by
  decide +kernel

/-- The supplied words determine the finite model's fixed-field representation. -/
theorem PairWordsAt.fixedMatches {s : Stor} (reads : PairWordsAt s) :
    WriterFixedMatches s finiteModel := by
  refine ⟨reads.supply, reads.domain, congrArg B256.toAdr reads.factory,
    congrArg B256.toAdr reads.token0, congrArg B256.toAdr reads.token1,
    ?_, ?_, ?_, reads.cumulative0, reads.cumulative1, reads.kLast, reads.unlocked⟩
  · rw [show s.get 8 = pairSlot8Word from reads.reserves]
    exact reserve0_word
  · rw [show s.get 8 = pairSlot8Word from reads.reserves]
    exact reserve1_word
  · rw [show s.get 8 = pairSlot8Word from reads.reserves]
    exact reserveTimestamp_word

/-- Apply the existing model transport without identifying any historical LP map. -/
theorem PairWordsAt.check_model {s : Stor} {st : UniswapV2Pair.State}
    {rows : List (Usdc.Key × B256)} {w : Jaune.State}
    (reads : PairWordsAt s) (actual : WriterFixedMatches s st) :
    checkJointHybrid pair usdc weth rows st w =
      checkJointHybrid pair usdc weth rows finiteModel w :=
  checkJointHybrid_model_congr actual reads.fixedMatches

theorem token0_eq : finiteModel.token0 = usdc := by decide +kernel
theorem token1_eq : finiteModel.token1 = weth := by decide +kernel
theorem unlocked_eq : finiteModel.unlocked = 1 := by decide +kernel

theorem usdc_notFrozen : Usdc.frozenBit usdcPairBalanceWord = false := by
  decide +kernel

theorem usdc_reserve : finiteModel.reserve0.val ≤ Usdc.balanceBits usdcPairBalanceWord := by
  decide +kernel

theorem weth_reserve : finiteModel.reserve1.val ≤ wethPairBalanceWord.toNat := by
  decide +kernel

theorem usdc_initialized : Usdc.flag20 usdcInitializedWord = true := by decide +kernel
theorem usdc_version : usdcVersionWord.toNat % 256 = 3 := by decide +kernel
theorem usdc_implementation : usdcImplementationWord = Usdc.usdcImpl.toB256 := by
  decide +kernel

/-- The finite holder rows use the actual hashed storage coordinates. -/
theorem usdc_balance_slot : Usdc.balSlot pair = usdcPairBalanceWordSlot := by
  decide +kernel

theorem weth_balance_slot : Weth9.balSlot pair = wethPairBalanceWordSlot := by
  decide +kernel

theorem address_separation :
    pair ≠ weth ∧ pair ≠ usdc ∧ usdc ≠ weth ∧ pair ≠ systemAddress ∧ pair ≠ 0 ∧
      usdc ≠ Usdc.usdcImpl ∧ usdc ≠ Usdc.usdcLib := by
  decide +kernel

theorem addresses_not_precompiles :
    (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp pair) ∧
    (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp usdc) ∧
    (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp weth) := by
  decide +kernel

/-- One balance row suffices for the support-free USDC holder checkpoint.
Future touched allowance rows are discharged separately by L3. -/
def usdcRows : List (Usdc.Key × B256) := [(.bal pair, usdcPairBalanceWordSlot)]

theorem usdc_rows_checked :
    usdcRows.all (fun r => decide (Usdc.Key.slot r.1 = r.2)) = true ∧
    FiniteCheckpoint.ascending (usdcRows.map Prod.snd) = true ∧
    usdcRows.all (fun r => decide (r.2 ∉ Usdc.fixedSlots)) = true := by
  decide +kernel

theorem usdc_holder_checked {s : Stor}
    (read : s.get usdcPairBalanceWordSlot = usdcPairBalanceWord) :
    checkUsdcHolder usdcRows s pair finiteModel.reserve0.val = true := by
  change ((decide (Usdc.Key.bal pair = .bal pair) &&
    decide (Usdc.frozenBit (s.get usdcPairBalanceWordSlot) = false) &&
    decide (finiteModel.reserve0.val ≤ Usdc.balanceBits (s.get usdcPairBalanceWordSlot))) ||
    false) && (true && true) = true
  rw [read]
  decide +kernel

/-- Generated account coordinates agree with the addresses used by the proofs. -/
theorem code_coordinates :
    pairCodeAccount = pair.toB256 ∧ weth9CodeAccount = weth.toB256 ∧
    usdcProxyCodeAccount = usdc.toB256 ∧
    usdcImplementationCodeAccount = Usdc.usdcImpl.toB256 ∧
    usdcLibraryCodeAccount = Usdc.usdcLib.toB256 ∧
    factoryCodeAccount = finiteModel.factory.toB256 := by
  decide +kernel

theorem pair_word_accounts :
    [pairSlot0WordAccount, pairSlot3WordAccount, pairSlot5WordAccount,
      pairSlot6WordAccount, pairSlot7WordAccount, pairSlot8WordAccount,
      pairSlot9WordAccount, pairSlot10WordAccount, pairSlot11WordAccount,
      pairSlot12WordAccount].all (fun a => decide (a = pair.toB256)) = true := by
  decide +kernel

theorem token_word_coordinates :
    [usdcImplementationWordAccount, usdcInitializedWordAccount, usdcVersionWordAccount,
      usdcAdminWordAccount, usdcPairBalanceWordAccount].all
        (fun a => decide (a = usdc.toB256)) = true ∧
    wethPairBalanceWordAccount = weth.toB256 ∧
    usdcImplementationWordSlot = Usdc.implSlot ∧
    usdcInitializedWordSlot = 8 ∧ usdcVersionWordSlot = 18 := by
  decide +kernel

end Blanc.Composition.LiveUsdcWeth9B26213219
