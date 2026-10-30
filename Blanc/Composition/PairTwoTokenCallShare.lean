import Blanc.Composition.PairTwoToken
import Blanc.Lift.UniswapV2Pair.PairOuterCalls
import Blanc.Lift.UniswapV2Pair.PairFeeAnswer
import Blanc.Composition.PairTokenStepOracle
import Blanc.Lift.UniswapV2Pair.PairHistoryShape

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
transfers to the words through the entry and exit representations.  The model's fee answer is the
transcript's third reply; `feeAnswer_eq_feeToAnswer` identifies it with the output of the frame the
call's third child call entered (`feeToAnswer`), the stored factory being undelegated code and no
precompile (`factoryEntered`).
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

/-- **The transcript's factory answer is the factory frame's output**: along an actual positional
consumption of a successful `mint`/`burn` from a checkpoint whose factory is undelegated and not a
precompile at the frame's nodes, the third reply of the transcript is the output of the frame the
call's third child call entered, so its first word is `feeToAnswer f`. -/
theorem feeAnswer_eq_feeToAnswer {f : Exec.Frame} {current : Checkpoint} {ctx : Context}
    {entry : UniswapV2Pair.Entry} {transcript : Transcript} {out : RunResult} {bytes : Bytes}
    (fee : (∃ recipient, entry = .mint recipient) ∨ ∃ recipient, entry = .burn recipient)
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      (startTyped current ctx entry) transcript out)
    (success : out.status = .success bytes)
    (entered : ∀ {node : Exec.Deriv},
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv f) node →
        getDelegatedCodeAddress (node.devm.getCode current.state.factory) = none ∧
          ¬ node.sevm.benvStat.rules.isPrecomp current.state.factory) :
    transcript.ownTail.ownTail.firstWord.toAdr = feeToAnswer f := by
  have lead0 := startTyped_feeLead current ctx (entry := entry) fee
  generalize startTyped current ctx entry = seg0 at lead0 consumed
  rcases seg0 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨F0, req0, c0⟩
  · exact lead0.elim
  · rw [consumed.failed_status] at success
    cases success
  obtain ⟨r0, t0, tail0, obs0, prior0, out0, C0, rfl, -, eq0, below0, static0, rest0, status0⟩ :=
    consumed.suspended_inv
  rw [static0 (by rw [externalStatic, lead0.2.1]; exact Bool.or_true _)] at rest0
  have lead1 := resumeSegment_feeLead_zero lead0 r0
  generalize resumeSegment F0 req0 c0 r0 = seg1 at lead1 rest0
  rcases seg1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨F1, req1, c1⟩
  · exact lead1.elim
  · rw [status0, rest0.failed_status] at success
    cases success
  obtain ⟨r1, t1, tail1, obs1, prior1, out1, C1, rfl, -, eq1, below1, static1, rest1, status1⟩ :=
    rest0.suspended_inv
  rw [static1 (by rw [externalStatic, lead1.2.1]; exact Bool.or_true _)] at rest1
  have lead2 := resumeSegment_feeLead_one lead1 r1
  generalize resumeSegment F1 req1 c1 r1 = seg2 at lead2 rest1
  rcases seg2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨F2, req2, c2⟩
  · exact lead2.elim
  · rw [status0, status1, rest1.failed_status] at success
    cases success
  obtain ⟨r2, t2, tail2, obs2, prior2, out2, -, rfl, gap2, -, -, -, rest2, status2⟩ :=
    rest1.suspended_inv
  have answered : r2.success = true := by
    cases answer : r2.success
    · obtain ⟨_, _, failedEq⟩ := resumeSegment_feeLead_two_failed (fr := prior2) lead2 answer
      rw [failedEq] at rest2
      rw [status0, status1, status2, rest2.failed_status] at success
      cases success
    · rfl
  obtain ⟨targetEq, -, -⟩ := lead2
  obtain ⟨undelegated, notPrecomp⟩ := entered obs2.call.sameFrame
  rw [← targetEq] at undelegated notPrecomp
  have isSome := sourceCallAt_entered obs2 undelegated notPrecomp
  have replyFacts := sourceCallAt_reply_facts obs2
  rcases obs2.queue with ⟨slotNone, -⟩ |
    ⟨childEvm, raw, callee, resume, pc', childRun, next, spawn, enter, resumed, slotSome, nodeExc,
      -⟩
  · rw [slotNone] at isSome
    cases isSome
  have same := spawn.symm.trans obs2.spawned
  simp only [Step.spawn.injEq] at same
  obtain ⟨rfl, -, -⟩ := same
  have response := obs2.response
  rw [slotSome] at response
  obtain ⟨-, settleEq⟩ := RunFrame.some_inv response
  have clean : obs2.child.error.isSome = false := by
    have h := replyFacts.1
    rw [answered] at h
    cases hc : obs2.child.error.isSome
    · rfl
    · rw [hc] at h
      cases h
  have settles := ProcessMessage.settlementCommits_of_some_ok_clean response clean
  have nodeList : Exec.descendantFramePaths [] 2 obs2.call.occurrence.node.exc =
      ⟨[] ++ [2], Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)⟩
        :: (Exec.descendantFramePaths ([] ++ [2]) 0 childRun ++
          Exec.descendantFramePaths [] 3 next) := by
    rw [nodeExc, Exec.descendantFramePaths, dite_eq_left_of_eq_true (eq_true settles),
      List.cons_append]
  have whole : Exec.descendantFramePaths [] 0 f.run = C0 ++ C1 ++
      (⟨[] ++ [2], Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)⟩
        :: (Exec.descendantFramePaths ([] ++ [2]) 0 childRun ++
          Exec.descendantFramePaths [] 3 next)) := by
    change Exec.descendantFramePaths [] 0 (Blanc.Exec.Frame.rootDeriv f).exc = _
    rw [eq0, eq1, gap2.descendantFramePaths_eq, nodeList, List.append_assoc]
  have missing (C : List Exec.LocatedFrame) (i : Nat) (off : i ≠ 2)
      (below : ∀ c ∈ C, [i] <+: c.path) :
      C.find? (fun c => c.path == [2]) = none := by
    rw [List.find?_eq_none]
    intro c member
    obtain ⟨rest, pathEq⟩ := below c member
    rw [← pathEq]
    simp only [List.singleton_append, beq_iff_eq, List.cons.injEq, off, false_and,
      not_false_eq_true]
  have childEq : obs2.child.output =
      (Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)).post.output := by
    have settled := settleEq.trans
      (ofCall_settle_committed (Jaune.Frame.raw_commits_of_settlementCommits settles))
    rw [Except.ok.inj settled, Devm.recordTouch_output]
    rfl
  unfold feeToAnswer childAt
  rw [whole, List.find?_append, List.find?_append, missing C0 0 (by decide) below0,
    missing C1 1 (by decide) below1]
  simp only [Option.none_or, List.find?_cons, List.nil_append, beq_self_eq_true, Option.map_some]
  change (Bytes.toB256 (r2.returndata.take 32)).toAdr = _
  rw [replyFacts.2, childEq]

/-- **Share value at every outer Pair call, two token cores** (hypotheses of
`pair_two_token_joint`): positive incoming supply word gives
`r0 · r1 · T'² ≤ r0' · r1' · (T + F)²` over the stored words at the call's entry and exit, `F` the
fee its `mint`/`burn` mints at the factory's actual `feeTo()` answer (`callFeeWords`). -/
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
    (start1 : JointAtW C1 trace pair .one st₀ checkpoint.state)
    (factoryEntered : ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair →
      G.sevm.isStatic = false → ∀ {node : Exec.Deriv},
        Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv G) node →
          getDelegatedCodeAddress (node.devm.getCode st₀.factory) = none ∧
            ¬ node.sevm.benvStat.rules.isPrecomp st₀.factory) :
    ∀ f, OuterPairCall pair trace f →
      ShareValueKept (preS pair f) (postS pair f) (callFeeWords pair f) := by
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
  have member : f ∈ trace.settledFrames := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  have inSettled := mem_of_pairSubtree observed (settled := trace.settledFrames) (fun F inBefore => by
    rw [split]
    exact List.mem_append_left _ inBefore)
  obtain ⟨tokens, opened, -⟩ := replay.fixed auth
    (fun s member => factoryQuiet_of_subtree (inSettled s member) factoryQuiet) ⟨rfl, rfl, rfl⟩
    unlocked
  have answer (fee : (∃ recipient, s.entry = .mint recipient) ∨
      ∃ recipient, s.entry = .burn recipient) :
      s.transcript.ownTail.ownTail.firstWord.toAdr = feeToAnswer f := by
    rw [← frameEq] at success ⊢
    refine feeAnswer_eq_feeToAnswer fee consumed.1 success fun chain => ?_
    rw [tokens.2.2]
    exact factoryEntered s.frame (frameEq ▸ member) (frameEq ▸ target)
      (frameEq ▸ nonstatic) chain
  have fees : entryFeeWords (preS pair f) s.entry s.transcript = callFeeWords pair f :=
    entryFeeWords_eq_callFeeWords (frameEq ▸ authS.2.2.2.2) answer
  intro positive
  rw [preRep.supplyWord_eq] at positive
  have accepted : (runTyped st s.source.context s.source.entry s.source.transcript).status =
      .success f.post.output := by rw [runEq]; exact success
  have bound := runTyped_product positive noShrink accepted
  rw [runEq, outEq] at bound
  rw [preRep.reserve0Word_toNat, preRep.reserve1Word_toNat, postRep.reserve0Word_toNat,
    postRep.reserve1Word_toNat, preRep.supplyWord_eq, postRep.supplyWord_eq, ← fees,
    preRep.entryFeeWords_eq]
  exact bound

end Blanc.Composition.PairTwoToken
