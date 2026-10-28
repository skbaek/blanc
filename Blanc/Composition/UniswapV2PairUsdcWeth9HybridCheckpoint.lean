import Blanc.Composition.UniswapV2PairUsdcWeth9CheckJointF

/-!
# A bounded checkpoint check combined with historical representation

The finite check reads code, fixed model fields and holder words. WETH9's
support/backing and the Pair's storage representation come from separate
historical proofs over arbitrary key predicates `KW` and `KP`. No finite list
enumerates either predicate, and neither storage nor world accounts are walked.
The historical WETH9 holder tracking/allowance facts and world balance bound
remain explicit. USDC uses its existing support-free finite row checker.

This is the assembly theorem, not a concrete historical instance: it does not
authenticate fetched words or supply the historical premises or L3's future
touched-row allowance bridge.
-/

namespace Blanc.Composition.UniswapV2PairUsdcWeth9

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Lift.FiniteCheckpoint
  Blanc.Composition.UniswapV2PairWeth9Joint

/-- The bounded WETH9/Pair facts left after historical representation and backing. -/
def checkWeth9PairFinite (pair weth : Adr) (st : UniswapV2Pair.State)
    (w : Jaune.State) : Bool :=
  decide ((w.getCode pair).data.toList = UniswapV2Pair.code.data.toList) &&
    decide ((w.getCode weth).data.toList = Weth9.code.data.toList) &&
    decide (st.token1 = weth) && decide (st.unlocked = 1) &&
    decide (st.reserve1.val ≤ ((w.getStor weth).get (Weth9.balSlot pair)).toNat) &&
    decide (pair ≠ weth) && decide (st.token0 ≠ st.token1) &&
    decide (pair ≠ systemAddress) && decide (pair ≠ 0) &&
    decide (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp weth)

/-- Finite facts assemble with the historical facts on the very same world. -/
theorem checkWeth9PairFinite_sound {pair weth : Adr} {KW : Weth9.Key → Prop}
    {KP : WriterKey → Prop} {st : UniswapV2Pair.State} {w : Jaune.State}
    (pairRep : WriterRep KP (w.getStor pair) st)
    (wethFoot : Weth9.FootInv KW (w.getStor weth) (w.bal weth))
    (sumNof : SumNof w.bal) (tracked : KW (.bal pair))
    (noAllowance : ∀ g, KW (.allow pair g) →
      (w.getStor weth).get (Weth9.allowSlot pair g) = 0)
    (h : checkWeth9PairFinite pair weth st w = true) :
    JointCheckpoint pair weth KW KP st .one w := by
  simp only [checkWeth9PairFinite, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hpair, hweth⟩, htoken⟩, hunlocked⟩, hreserve⟩, hapart⟩,
    hdistinct⟩, hsystem⟩, hzero⟩, hprecomp⟩ := h
  refine
    { pairCode := ?_
      pairRep := pairRep
      token := htoken
      unlocked := hunlocked
      wethCode := ?_
      wethFoot := wethFoot
      sumNof := sumNof
      tracked := tracked
      noAllowance := noAllowance
      reserve := hreserve
      apart := hapart
      distinct := hdistinct
      notSystem := hsystem
      pairNonzero := hzero
      wethNotPrecompile := fun s hf => hprecomp s.fork hf }
  · change some (w.getCode pair).toList = some UniswapV2Pair.code.toList
    simp only [ByteArray.toList_eq_toList_data, hpair]
  · change some (w.getCode weth).toList = some Weth9.code.toList
    simp only [ByteArray.toList_eq_toList_data, hweth]

/-- USDC's finite rows and the bounded WETH9/Pair check, without support enumeration. -/
def checkJointHybrid (pair usdc weth : Adr) (urows : List (Usdc.Key × B256))
    (st : UniswapV2Pair.State) (w : Jaune.State) : Bool :=
  checkWeth9PairFinite pair weth st w && Usdc.checkUsdcF usdc urows w &&
    decide (st.token0 = usdc) &&
    checkUsdcHolder urows (w.getStor usdc) pair st.reserve0.val && decide (pair ≠ usdc) &&
    decide (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp usdc) &&
    decide (∀ f ∈ coveredForks, ¬ (Fork.ruleSet f).isPrecomp pair)

/-- The hybrid check constructs the existing support-free joint checkpoint.
The historical key predicates and model maps are preserved verbatim. -/
theorem checkJointHybrid_sound {pair usdc weth : Adr} {urows : List (Usdc.Key × B256)}
    {KW : Weth9.Key → Prop} {KP : WriterKey → Prop} {st : UniswapV2Pair.State}
    {w : Jaune.State} (pairRep : WriterRep KP (w.getStor pair) st)
    (wethFoot : Weth9.FootInv KW (w.getStor weth) (w.bal weth))
    (sumNof : SumNof w.bal) (tracked : KW (.bal pair))
    (noAllowance : ∀ g, KW (.allow pair g) →
      (w.getStor weth).get (Weth9.allowSlot pair g) = 0)
    (h : checkJointHybrid pair usdc weth urows st w = true) :
    JointCheckpoint2F pair usdc weth (rowKeys urows) KW KP st w := by
  simp only [checkJointHybrid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hjoint, husdc⟩, htoken⟩, hholder⟩, hapart⟩, hprecomp⟩, hpairPrecomp⟩ := h
  obtain ⟨installed, foot⟩ := Usdc.checkUsdcF_sound husdc
  obtain ⟨utracked, notFrozen, reserve, uallow⟩ :=
    checkUsdcHolder_soundW (Usdc.checkUsdcF_word husdc) hholder
  exact
    { weth9 := checkWeth9PairFinite_sound pairRep wethFoot sumNof tracked noAllowance hjoint
      usdcInstalled := installed
      usdcFoot := foot
      token0 := htoken
      tracked := utracked
      notFrozen := notFrozen
      noAllowance := uallow
      reserve := reserve
      apart := hapart
      usdcNotPrecompile := fun s hf => hprecomp s.fork hf
      pairNotPrecompile := fun s hf => hpairPrecomp s.fork hf }

/-- Equality of exactly the world reads used by the hybrid check. The USDC row
quantifier ranges only over the supplied finite list, not over all storage. -/
structure HybridReadsEq (pair usdc weth : Adr) (urows : List (Usdc.Key × B256))
    (w v : Jaune.State) : Prop where
  pairCode : w.getCode pair = v.getCode pair
  wethCode : w.getCode weth = v.getCode weth
  usdcCode : w.getCode usdc = v.getCode usdc
  implCode : w.getCode Usdc.usdcImpl = v.getCode Usdc.usdcImpl
  libCode : w.getCode Usdc.usdcLib = v.getCode Usdc.usdcLib
  implWord : (w.getStor usdc).get Usdc.implSlot = (v.getStor usdc).get Usdc.implSlot
  initialized : (w.getStor usdc).get 8 = (v.getStor usdc).get 8
  version : (w.getStor usdc).get 18 = (v.getStor usdc).get 18
  usdcRows : ∀ r ∈ urows, (w.getStor usdc).get r.2 = (v.getStor usdc).get r.2
  wethBalance : (w.getStor weth).get (Weth9.balSlot pair) =
    (v.getStor weth).get (Weth9.balSlot pair)

/-- The holder check depends only on the words in its finite row list. -/
theorem checkUsdcHolder_congr {rows : List (Usdc.Key × B256)} {s t : Stor}
    {a : Adr} {n : Nat} (reads : ∀ r ∈ rows, s.get r.2 = t.get r.2) :
    checkUsdcHolder rows s a n = checkUsdcHolder rows t a n := by
  apply Bool.eq_iff_iff.mpr
  simp only [checkUsdcHolder, Bool.and_eq_true, List.any_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨r, hr, hc⟩, ha⟩
    refine ⟨⟨r, hr, ?_⟩, ?_⟩
    · rw [← reads r hr]
      exact hc
    · intro r hr
      rw [← reads r hr]
      exact ha r hr
  · rintro ⟨⟨r, hr, hc⟩, ha⟩
    refine ⟨⟨r, hr, ?_⟩, ?_⟩
    · rw [reads r hr]
      exact hc
    · intro r hr
      rw [reads r hr]
      exact ha r hr

/-- A finite snapshot can supply the check without supplying the actual world's
unlisted storage or accounts. Historical premises still refer to the actual world. -/
theorem checkJointHybrid_congr {pair usdc weth : Adr} {urows : List (Usdc.Key × B256)}
    {st : UniswapV2Pair.State} {w v : Jaune.State}
    (reads : HybridReadsEq pair usdc weth urows w v) :
    checkJointHybrid pair usdc weth urows st w =
      checkJointHybrid pair usdc weth urows st v := by
  have holder := checkUsdcHolder_congr (a := pair) (n := st.reserve0.val) reads.usdcRows
  simp only [checkJointHybrid, checkWeth9PairFinite, Usdc.checkUsdcF,
    reads.pairCode, reads.wethCode, reads.usdcCode, reads.implCode, reads.libCode,
    reads.implWord, reads.initialized, reads.version, reads.wethBalance, holder]

/-- Transfer only the finite reads from a checked snapshot; retain all historical
facts on the actual world. No final checkpoint is an input. -/
theorem checkJointHybrid_sound_of_reads {pair usdc weth : Adr}
    {urows : List (Usdc.Key × B256)} {KW : Weth9.Key → Prop} {KP : WriterKey → Prop}
    {st : UniswapV2Pair.State} {w snapshot : Jaune.State}
    (reads : HybridReadsEq pair usdc weth urows w snapshot)
    (pairRep : WriterRep KP (w.getStor pair) st)
    (wethFoot : Weth9.FootInv KW (w.getStor weth) (w.bal weth))
    (sumNof : SumNof w.bal) (tracked : KW (.bal pair))
    (noAllowance : ∀ g, KW (.allow pair g) →
      (w.getStor weth).get (Weth9.allowSlot pair g) = 0)
    (checked : checkJointHybrid pair usdc weth urows st snapshot = true) :
    JointCheckpoint2F pair usdc weth (rowKeys urows) KW KP st w := by
  apply checkJointHybrid_sound pairRep wethFoot sumNof tracked noAllowance
  rw [checkJointHybrid_congr reads]
  exact checked

/-- Only the Pair's ten fixed storage words are compared. No LP mapping row
is included, and the reserved mapping roots at slots 1, 2 and 4 are not read. -/
structure PairFixedReadsEq (s t : Stor) : Prop where
  supply : s.get 0 = t.get 0
  domain : s.get 3 = t.get 3
  factory : s.get 5 = t.get 5
  token0 : s.get 6 = t.get 6
  token1 : s.get 7 = t.get 7
  reserves : s.get 8 = t.get 8
  cumulative0 : s.get 9 = t.get 9
  cumulative1 : s.get 10 = t.get 10
  kLast : s.get 11 = t.get 11
  unlocked : s.get 12 = t.get 12

/-- Fixed-field matching transports using only those ten reads. -/
theorem PairFixedReadsEq.fixedMatches {s t : Stor} {st : UniswapV2Pair.State}
    (reads : PairFixedReadsEq s t) (fixed : WriterFixedMatches t st) :
    WriterFixedMatches s st := by
  simp only [WriterFixedMatches, reads.supply, reads.domain, reads.factory,
    reads.token0, reads.token1, reads.reserves, reads.cumulative0,
    reads.cumulative1, reads.kLast, reads.unlocked]
  exact fixed

/-- The check is independent of the model's LP maps. Two represented models
with the same fixed words give the same answer, even if their maps differ. -/
theorem checkJointHybrid_model_congr {pair usdc weth : Adr}
    {urows : List (Usdc.Key × B256)} {st finiteSt : UniswapV2Pair.State}
    {w : Jaune.State} {s : Stor}
    (actual : WriterFixedMatches s st) (finite : WriterFixedMatches s finiteSt) :
    checkJointHybrid pair usdc weth urows st w =
      checkJointHybrid pair usdc weth urows finiteSt w := by
  obtain ⟨reserve0, reserve1⟩ := actual.reserves_eq finite
  obtain ⟨_, _, _, token0, token1, _, _, _, _, _, _, unlocked⟩ := actual
  obtain ⟨_, _, _, token0', token1', _, _, _, _, _, _, unlocked'⟩ := finite
  have ht0 := token0.symm.trans token0'
  have ht1 := token1.symm.trans token1'
  have hu := unlocked.symm.trans unlocked'
  simp only [checkJointHybrid, checkWeth9PairFinite, ht0, ht1, hu, reserve0, reserve1]

/-- A fully finite snapshot check: fixed Pair words and the hybrid finite facts.
The finite model's maps need not represent the actual Pair's mapping storage. -/
def checkJointHybridSnapshot (pair usdc weth : Adr) (urows : List (Usdc.Key × B256))
    (finiteSt : UniswapV2Pair.State) (snapshot : Jaune.State) : Bool :=
  decide (WriterFixedMatches (snapshot.getStor pair) finiteSt) &&
    checkJointHybrid pair usdc weth urows finiteSt snapshot

/-- Instantiate the historical model from a finite snapshot's fixed fields.
The conclusion preserves the original historical model and its full maps. -/
theorem checkJointHybridSnapshot_sound {pair usdc weth : Adr}
    {urows : List (Usdc.Key × B256)} {KW : Weth9.Key → Prop} {KP : WriterKey → Prop}
    {st finiteSt : UniswapV2Pair.State} {w snapshot : Jaune.State}
    (reads : HybridReadsEq pair usdc weth urows w snapshot)
    (pairReads : PairFixedReadsEq (w.getStor pair) (snapshot.getStor pair))
    (pairRep : WriterRep KP (w.getStor pair) st)
    (wethFoot : Weth9.FootInv KW (w.getStor weth) (w.bal weth))
    (sumNof : SumNof w.bal) (tracked : KW (.bal pair))
    (noAllowance : ∀ g, KW (.allow pair g) →
      (w.getStor weth).get (Weth9.allowSlot pair g) = 0)
    (checked : checkJointHybridSnapshot pair usdc weth urows finiteSt snapshot = true) :
    JointCheckpoint2F pair usdc weth (rowKeys urows) KW KP st w := by
  simp only [checkJointHybridSnapshot, Bool.and_eq_true, decide_eq_true_eq] at checked
  have fixed := pairReads.fixedMatches checked.1
  apply checkJointHybrid_sound pairRep wethFoot sumNof tracked noAllowance
  rw [checkJointHybrid_model_congr pairRep.fixed fixed, checkJointHybrid_congr reads]
  exact checked.2

end Blanc.Composition.UniswapV2PairUsdcWeth9
