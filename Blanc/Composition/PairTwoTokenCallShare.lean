import Blanc.Composition.PairTwoToken
import Blanc.Lift.UniswapV2Pair.PairOuterCalls

/-!
# Share value at every outer Pair call, over storage words

`pair_two_token_call_product`: over a Pair whose two tokens are writer-shadowed cores with holder
laws for the Pair (the hypotheses of `pair_two_token_joint`), every outer Pair call `f`
(`OuterPairCall`) with positive incoming supply keeps

  `r0 · r1 · T'² ≤ r0' · r1' · (T + F)²`

where `r0, r1, T` are the reserve and supply words of the Pair storage at `f`'s entry, the primed
words those at `f`'s committed exit, and `F` the protocol-fee mint over the entry words at the
call's `feeTo` answer (`entryFeeWords`).

The proof walks both token cores (`pair_token_walk`) over the Pair replay of the settled frames up
to and including `f`'s block (`pair_history_outer_call_at`), which yields the backing answer
condition `EntryNoShrink` at `f`'s own step; the model share-value law (`runTyped_product`) then
transfers to the words through the entry and exit representations.
-/

namespace Blanc.Composition.PairTwoToken

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Token Blanc.Lift.UniswapV2Pair
  Blanc.Composition.PairTokenJoint

/-- A frame's own block (the frame, then its committed descendants) is Pair-closed. -/
theorem block_pairClosed (pair : Adr) (F : Exec.Frame) :
    PairClosed pair (F :: Exec.descendantFrames F.run) := by
  intro b₁ G b₂ split _ _
  cases b₁ with
  | nil =>
    obtain ⟨rfl, rfl⟩ := List.cons.inj split
    exact Nat.le_refl _
  | cons x b₁ =>
    obtain ⟨-, inner⟩ := List.cons.inj split
    obtain ⟨r, rfl⟩ := Exec.descendantFrames_contig F.run inner
    rw [List.length_append]
    omega

/-- The per-side backing condition of a replay extended by one invocation holds at that invocation,
from the state the replay reaches. -/
theorem sourceReplayNoShrinkSide_last {side : TokenSide} {st finish : UniswapV2Pair.State}
    {invs : List SourceInvocation} {inv : SourceInvocation} (replay : SourceReplay st invs finish)
    (sides : sourceReplayNoShrinkSide side st (invs ++ [inv])) :
    EntryNoShrinkSide side finish inv.context inv.entry inv.transcript := by
  induction replay with
  | nil st => exact sides.1
  | @cons st finish inv' rest out bytes consumed successful tail ih =>
    have runEq : inv'.run st = out := (runTyped_of_exact consumed).1
    have later := sides.2
    rw [runEq] at later
    exact ih later

/-- **Share value at every outer Pair call, two token cores** (hypotheses of
`pair_two_token_joint`): positive incoming supply word gives
`r0 · r1 · T'² ≤ r0' · r1' · (T + F)²` over the stored words at the call's entry and exit, `F` the
fee mint at the call's `feeTo` answer. -/
theorem pair_two_token_call_product {pair T0 T1 : Adr} {B0 B1 : Book} (C0 : CoreW T0 B0)
    (C1 : CoreW T1 B1) (abi0 : Erc20Abi B0) (abi1 : Erc20Abi B1) (self0 : SelfCallerW C0)
    (self1 : SelfCallerW C1) {cfg : ChainConfig} {checkpoint future : BlockChain}
    {K₀ : WriterKey → Prop} {st₀ : UniswapV2Pair.State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (laws0 : HolderLaws T0 B0 trace pair) (laws1 : HolderLaws T1 B1 trace pair)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace))
    (hist0 : C0.Hist trace) (hist1 : C1.Hist trace)
    (token0 : st₀.token0 = T0) (token1 : st₀.token1 = T1) (unlocked : st₀.unlocked = 1)
    (apart0 : pair ≠ T0) (apart1 : pair ≠ T1)
    (answerable0 : C0.Answerable trace pair) (answerable1 : C1.Answerable trace pair)
    (distinct : st₀.token0 ≠ st₀.token1) (notSystem : pair ≠ systemAddress)
    (factoryQuiet : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → G.sevm.caller ≠ st₀.factory)
    (tokenEntered0 : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T0) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T0)
    (tokenEntered1 : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode T1) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp T1)
    (start0 : JointAtW C0 trace pair .zero st₀ checkpoint.state)
    (start1 : JointAtW C1 trace pair .one st₀ checkpoint.state) :
    ∀ f, OuterPairCall pair trace f →
      ∃ s : PairStep, s.frame = f ∧ s.AuthenticWith PairEntryAuth pair ∧
        (0 < (supplyWord (preS pair f)).toNat →
          (reserve0Word (preS pair f)).toNat * (reserve1Word (preS pair f)).toNat *
              (supplyWord (postS pair f)).toNat ^ 2 ≤
            (reserve0Word (postS pair f)).toNat * (reserve1Word (postS pair f)).toNat *
              ((supplyWord (preS pair f)).toNat +
                entryFeeWords (preS pair f) s.entry s.transcript) ^ 2) := by
  have walk0 := pair_token_walk C0 abi0 self0 .zero trace laws0 installed initial fresh hist0 token0
    unlocked apart0 answerable0 distinct notSystem factoryQuiet tokenEntered0
  have walk1 := pair_token_walk C1 abi1 self1 .one trace laws1 installed initial fresh hist1 token1
    unlocked apart1 answerable1 distinct notSystem factoryQuiet tokenEntered1
  intro f ⟨target, nonstatic, before, after, split, noOpaque⟩
  obtain ⟨steps, s, st, st', out, K, K', observed, auth, replay, frameEq, authS, consumed, success,
    outEq, replay', preRep, postRep⟩ :=
    pair_history_outer_call_at trace installed initial fresh before f after split target nonstatic
      noOpaque
  obtain ⟨r, afterEq⟩ := trace.settledFrames_contig split
  have split' : trace.settledFrames =
      [] ++ (before ++ f :: Exec.descendantFrames f.run) ++ r := by
    rw [split, afterEq, List.nil_append, List.append_assoc, List.cons_append]
  have closed : PairClosed pair ([] ++ (before ++ f :: Exec.descendantFrames f.run)) := by
    rw [List.nil_append]
    exact (before_pairClosed trace split noOpaque).append (block_pairClosed pair f)
  have auth' : ∀ s' ∈ steps ++ [s], s'.AuthenticWith PairEntryAuth pair := by
    intro s' member
    rcases List.mem_append.mp member with h | h
    · exact auth s' h
    · rw [List.mem_singleton.mp h]
      exact authS
  have observed' : (steps ++ [s]).flatMap (fun s => pairSubtreeFrames pair s.frame) =
      (before ++ f :: Exec.descendantFrames f.run).flatMap (pairFrameObs pair) := by
    rw [List.flatMap_append, List.flatMap_append, observed, List.flatMap_singleton, frameEq,
      pairSubtreeFrames, Exec.Frame.committedFrames_self]
  obtain ⟨-, -, -, -, -, -, side0⟩ := walk0 (steps ++ [s]) replay' auth' observed' split'
    (PairClosed.nil pair) closed ⟨rfl, rfl, rfl⟩ unlocked rfl start0.1 start0.2
  obtain ⟨-, -, -, -, -, -, side1⟩ := walk1 (steps ++ [s]) replay' auth' observed' split'
    (PairClosed.nil pair) closed ⟨rfl, rfl, rfl⟩ unlocked rfl start1.1 start1.2
  have source := replay.sourceReplay fun _ _ _ _ consumed => consumed.positional.forget
  rw [List.map_append, List.map_singleton] at side0 side1
  have noShrink : EntryNoShrink st s.source.context s.source.entry s.source.transcript :=
    entryNoShrink_iff_sides.mpr
      ⟨sourceReplayNoShrinkSide_last source side0, sourceReplayNoShrinkSide_last source side1⟩
  have runEq : runTyped st s.source.context s.source.entry s.source.transcript = out :=
    (runTyped_of_exact consumed.positional.forget).1
  refine ⟨s, frameEq, authS, fun positive => ?_⟩
  rw [preRep.supplyWord_eq] at positive
  have accepted : (runTyped st s.source.context s.source.entry s.source.transcript).status =
      .success f.post.output := by rw [runEq]; exact success
  have bound := runTyped_product positive noShrink accepted
  rw [runEq, outEq] at bound
  rw [preRep.reserve0Word_toNat, preRep.reserve1Word_toNat, postRep.reserve0Word_toNat,
    postRep.reserve1Word_toNat, preRep.supplyWord_eq, postRep.supplyWord_eq,
    preRep.entryFeeWords_eq]
  exact bound

end Blanc.Composition.PairTwoToken
