import Blanc.Lift.UniswapV2Pair.PairWriterAbsorb
import Blanc.Lift.UniswapV2Pair.SwapCanonical
import Blanc.Lift.UniswapV2Pair.MintCanonical
import Blanc.Lift.UniswapV2Pair.SyncGasCanonical
import Blanc.Lift.UniswapV2Pair.BurnFeeTransfers
import Blanc.SlotFootprintSubset

/-!
# The Pair-frame supply interfaces

This module provides the trace-local writer admission and generic frame outcome interfaces used by
`PairPositionalSupply.lean`. The configured history instantiates `pairSupplyWith` with the recursively
admitted consumption and actual-position entry authentication of that module.

* `pairFrameKeys` — the HASH-T rows selected by one actual Pair frame;
* `PairGood U D` — every raw Pair frame root of `D` has its rows in `U`;
* `PairStepOutcomeWith` — the consumed invocation with model success and footprint growth;
* `PairSupplyRules` — the eleven-family supply obligations;
* `pairSupplyWith` — the 27-way dispatcher for those supplied obligations.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-! ## Rows and admission -/

/-- The HASH-T rows one actual Pair frame selects. -/
noncomputable def pairFrameKeys (D : Exec.Deriv) : List WriterKey :=
  pairDecodedKeys D.sevm ++ staticViewDecodedKeys D.sevm ++
    (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord D.sevm 4).toAdr) ++
    ([.balance D.sevm.currentTarget] ++ mintFeeReplyKeys D)

/-- Trace-local admission of a Pair frame's derivation: the rows of every raw Pair frame it enters
(itself included) lie in the universe. -/
def PairGood (U : WriterKey → Prop) (D : Exec.Deriv) : Prop :=
  ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = D.sevm.currentTarget →
    ∀ k ∈ pairFrameKeys F, U k

/-- The rows of every raw Pair frame a derivation enters (itself included), as one finite list fixed by
the derivation alone. -/
noncomputable def pairDerivKeys (D : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots D.exc).flatMap fun F =>
    if F.sevm.currentTarget = D.sevm.currentTarget then pairFrameKeys F else []

theorem pairGood_of_keys {U : WriterKey → Prop} {D : Exec.Deriv}
    (keys : ∀ k ∈ pairDerivKeys D, U k) : PairGood U D := by
  intro F member target k row
  apply keys k
  apply List.mem_flatMap.mpr
  refine ⟨F, member, ?_⟩
  rw [ite_eq_left target]
  exact row

section Good

variable {U : WriterKey → Prop} {D : Exec.Deriv}

theorem PairGood.self (good : PairGood U D) : ∀ k ∈ pairFrameKeys D, U k :=
  good D (by cases D; exact Exec.mem_rawFrameRoots_self _) rfl

theorem PairGood.decodedOwn (good : PairGood U D) : ∀ k ∈ pairDecodedKeys D.sevm, U k :=
  fun k member => good.self k
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member)))

theorem PairGood.viewsOwn (good : PairGood U D) : ∀ k ∈ staticViewDecodedKeys D.sevm, U k :=
  fun k member => good.self k
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ member)))

theorem PairGood.transferOwn (good : PairGood U D)
    (selector : Blanc.Sevm.selector D.sevm = 0xa9059cbb) :
    ∀ k ∈ transferTouched D.sevm.caller (transferRecipient D.sevm), U k := by
  have decoded := good.decodedOwn
  rw [pairDecodedKeys, ite_eq_left selector] at decoded
  exact decoded

theorem PairGood.approveOwn (good : PairGood U D)
    (selector : Blanc.Sevm.selector D.sevm = 0x095ea7b3) :
    ∀ k ∈ approveTouched D.sevm.caller (approveSpender D.sevm), U k := by
  have decoded := good.decodedOwn
  rw [pairDecodedKeys, ite_eq_right (by rw [selector]; decide), ite_eq_left selector] at decoded
  exact decoded

theorem PairGood.transferFromOwn (good : PairGood U D)
    (selector : Blanc.Sevm.selector D.sevm = 0x23b872dd) :
    ∀ k ∈ transferFromTouched (transferFromOwner D.sevm) D.sevm.caller
      (transferFromRecipient D.sevm), U k := by
  have decoded := good.decodedOwn
  rw [pairDecodedKeys, ite_eq_right (by rw [selector]; decide),
    ite_eq_right (by rw [selector]; decide), ite_eq_left selector] at decoded
  exact decoded

theorem PairGood.permitOwn (good : PairGood U D)
    (selector : Blanc.Sevm.selector D.sevm = 0xd505accf) :
    ∀ k ∈ permitTouched (permitOwner D.sevm) (permitSpender D.sevm), U k := by
  have decoded := good.decodedOwn
  rw [pairDecodedKeys, ite_eq_right (by rw [selector]; decide),
    ite_eq_right (by rw [selector]; decide), ite_eq_right (by rw [selector]; decide),
    ite_eq_left selector] at decoded
  exact decoded

theorem PairGood.decoded (good : PairGood U D) {F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots D.exc) (target : F.sevm.currentTarget = D.sevm.currentTarget) :
    ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm, U k := by
  intro k touched
  apply good F member target k
  simp only [pairFrameKeys, List.mem_append]
  rcases List.mem_append.mp touched with h | h
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))

theorem PairGood.locked (good : PairGood U D) :
    ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = D.sevm.currentTarget →
      LockedGood U F := by
  intro _ member target F' inner same
  exact good.decoded (Exec.rawFrameRoots_trans member inner) (same.trans target)

theorem PairGood.views (good : PairGood U D) :
    ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = D.sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k :=
  fun _ member target k touched => good.decoded member target k (List.mem_append_right _ touched)

theorem PairGood.skim (good : PairGood U D) : ∀ k ∈ skimTraceKeys D, U k := by
  intro k member
  obtain ⟨F, inner, picked⟩ := List.mem_flatMap.mp member
  by_cases target : F.sevm.currentTarget = D.sevm.currentTarget
  · rw [ite_eq_left target] at picked
    exact good.decoded inner target k picked
  · rw [ite_eq_right target] at picked
    exact absurd picked List.not_mem_nil

theorem PairGood.sync (good : PairGood U D) : ∀ k ∈ syncTraceKeys D, U k := by
  intro k member
  obtain ⟨F, inner, picked⟩ := List.mem_flatMap.mp member
  by_cases target : F.sevm.currentTarget = D.sevm.currentTarget ∧ F.sevm.isStatic = true
  · rw [ite_eq_left target] at picked
    exact good.views F inner target.1 k picked
  · rw [ite_eq_right target] at picked
    exact absurd picked List.not_mem_nil

theorem PairGood.mint (good : PairGood U D) : ∀ k ∈ mintTraceKeys D, U k := by
  intro k member
  have own := good.self
  simp only [mintTraceKeys, List.mem_append] at member
  rcases member with (views | rows) | fee
  · obtain ⟨F, inner, picked⟩ := List.mem_flatMap.mp views
    by_cases target : F.sevm.currentTarget = D.sevm.currentTarget
    · rw [ite_eq_left target] at picked
      exact good.views F inner target k picked
    · rw [ite_eq_right target] at picked
      exact absurd picked List.not_mem_nil
  · apply own k
    simp only [pairFrameKeys, List.mem_append]
    exact Or.inl (Or.inr rows)
  · apply own k
    simp only [pairFrameKeys, List.mem_append]
    exact Or.inr (Or.inr fee)

theorem PairGood.pairRow (good : PairGood U D) : U (.balance D.sevm.currentTarget) := by
  apply good.self
  simp only [pairFrameKeys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, true_or,
    or_true]

end Good

/-! ## The step outcome -/

/-- One successful Pair frame `D` consumed as one source invocation at `current`: an authenticated entry
and transcript, exact consumption ending in model success, and the finite representation of the frame's
post storage growing from the incoming tracked rows `K` inside the universe `U`. -/
def PairStepOutcomeWith
    (Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop)
    (Auth : Exec.Deriv → Entry → Transcript → Prop) (U : WriterKey → Prop)
    (current : Checkpoint) (invocation : List Nat) (K : WriterKey → Prop) (D : Exec.Deriv)
    (post : Devm) : Prop :=
  ∃ (entry : Entry) (nested : Transcript) (child : RunResult) (bytes : Bytes)
    (K' : WriterKey → Prop),
    Auth D entry nested ∧
    Consumes D (startTyped current (writerContext D.sevm invocation) entry) nested child ∧
    child.status = .success bytes ∧ bytes = post.output ∧
    (∀ k, K k → K' k) ∧ (∀ k, K' k → U k) ∧
    WriterRep K' (post.getStor D.sevm.currentTarget) child.frame.current.state

/-- The exact-consumption compatibility instance of the shared outcome. -/
def PairStepOutcome (Auth : Exec.Deriv → Entry → Transcript → Prop) (U : WriterKey → Prop)
    (current : Checkpoint) (invocation : List Nat) (K : WriterKey → Prop) (D : Exec.Deriv)
    (post : Devm) : Prop :=
  PairStepOutcomeWith (fun _ => ExactConsumes) Auth U current invocation K D post

theorem PairStepOutcomeWith.mono
    {Consumes Consumes' : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth Auth' : Exec.Deriv → Entry → Transcript → Prop}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat} {K : WriterKey → Prop}
    {D : Exec.Deriv} {post : Devm}
    (consume : ∀ segment T child, Consumes D segment T child → Consumes' D segment T child)
    (authenticate : ∀ entry T, Auth D entry T → Auth' D entry T)
    (outcome : PairStepOutcomeWith Consumes Auth U current invocation K D post) :
    PairStepOutcomeWith Consumes' Auth' U current invocation K D post := by
  obtain ⟨entry, nested, child, bytes, K', auth, consumed, rest⟩ := outcome
  exact ⟨entry, nested, child, bytes, K', authenticate entry nested auth,
    consume _ nested child consumed, rest⟩

/-- The step outcome from a consumed successful invocation whose final rows lie in `K` extended by
universe rows. -/
theorem pairStepOutcome_with
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop} {U K K' : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {D : Exec.Deriv} {post : Devm}
    {entry : Entry} {nested : Transcript} {child : RunResult} {bytes : Bytes}
    {keys : List WriterKey}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    {s : Stor} (incoming : WriterRep K s current.state)
    (good : ∀ k ∈ keys, U k) (auth : Auth D entry nested)
    (consumed : Consumes D (startTyped current (writerContext D.sevm invocation) entry) nested child)
    (success : child.status = .success bytes) (outputEq : bytes = post.output)
    (grown : ∀ k, K' k → WriterExtend K keys k)
    (rep : WriterRep K' (post.getStor D.sevm.currentTarget) child.frame.current.state) :
    PairStepOutcomeWith Consumes Auth U current invocation K D post := by
  have sub' : ∀ k, K' k → U k := by
    intro k member
    rcases grown k member with old | row
    · exact sub k old
    · exact good k row
  obtain ⟨K'', grows, inside, rep'⟩ := writerRep_absorb inj apart sub incoming sub' rep
  exact ⟨entry, nested, child, bytes, K'', auth, consumed, success, outputEq, grows, inside, rep'⟩

/-! ## Lock-free entries, at any lock state -/

/-! ## The lock-guarded families -/

/-- Universe rows extended by universe rows stay in the universe; injectivity and apartness restrict. -/
theorem writerExtend_universe {U K : WriterKey → Prop} {keys : List WriterKey}
    (sub : ∀ k, K k → U k) (good : ∀ k ∈ keys, U k) : ∀ k, WriterExtend K keys k → U k := by
  exact Blanc.SlotFootprint.extendBy_subset sub good

theorem writerInj_restrict {U V : WriterKey → Prop} (inj : WriterInj U) (inside : ∀ k, V k → U k) :
    WriterInj V :=
  fun k k' hk hk' same => inj k k' (inside k hk) (inside k' hk') same

theorem writerApart_restrict {U V : WriterKey → Prop} (apart : WriterApart U)
    (inside : ∀ k, V k → U k) : WriterApart V :=
  fun k hk => apart k (inside k hk)

/-- **Mint provenance.** The entry is the decoded mint; the transcript is the three actual `STATICCALL`
replies of the frame (token0 and token1 `balanceOf`, factory `feeTo`), each with the retained static Pair
views of the actual child. -/
def MintAuth (D : Exec.Deriv) (entry : Entry) (T : Transcript) : Prop :=
  Blanc.Sevm.selector D.sevm = 0x6a627842 ∧ entry = .mint (Sevm.dataWord D.sevm 4).toAdr ∧
  ∃ (current : Checkpoint) (out0 out1 outF : Bytes) (views0 views1 viewsF : List StaticViewTurn),
    MintObservedSteps D current D.sevm out0 out1 outF ∧
    T = .next (feeObservedResult out0) (staticViewTranscript views0 .done)
      (.next (feeObservedResult out1) (staticViewTranscript views1 .done)
        (.next (feeObservedResult outF) (staticViewTranscript viewsF .done) .done)) ∧
    (∀ picked ∈ views0 ++ views1 ++ viewsF,
      Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
      picked.1.frame.sevm.currentTarget = D.sevm.currentTarget ∧
      picked.1.frame.sevm.isStatic = true) ∧
    MintViewProvenance D D.sevm.currentTarget current.state.token0 views0 ∧
    MintViewProvenance D D.sevm.currentTarget current.state.token1 views1 ∧
    MintViewProvenance D D.sevm.currentTarget current.state.factory viewsF

/-- **Sync provenance.** The entry is `sync`; the transcript is the two actual `balanceOf(pair)`
`STATICCALL` replies of the frame with their retained static Pair views (`SyncCanonicalResult`). -/
def SyncAuth (D : Exec.Deriv) (entry : Entry) (T : Transcript) : Prop :=
  Blanc.Sevm.selector D.sevm = 0xfff6cae9 ∧ entry = .sync ∧
  ∃ (K : WriterKey → Prop) (current : Checkpoint) (invocation : List Nat) (b post : Devm)
    (result : SyncCanonicalResult K current invocation D b post),
    T = .next (syncExternalReply result.out0) (staticViewTranscript result.views0 .done)
      (.next (syncExternalReply result.out1) (staticViewTranscript result.views1 .done) .done)

/-- **Skim provenance.** The entry is the decoded skim; the transcript is the frame's actual
`balanceOf(pair)` replies and transfer `CALL` replies, in order, with the retained static Pair views and
the retained mutable turns (foreign logs and re-entered Pair frames, each `LockedAuth`) of the actual
children. -/
def SkimAuth (D : Exec.Deriv) (entry : Entry) (T : Transcript) : Prop :=
  Blanc.Sevm.selector D.sevm = 0xbc25cf77 ∧ entry = .skim (skimRecipient D.sevm) ∧
  ∃ (b : Devm) (G : Nat), D.pc = 0 ∧ D.devm = St b [] Mem.empty G ∧
  ∃ (out0 : Bytes) (d : Devm), SkimFirstSteps D D.sevm b out0 d ∧
  ∃ (out1 : Bytes) (d2 : Devm) (views0 views1 : List StaticViewTurn)
    (turns1 turns3 : List MutableTurn),
    SkimSecondSteps D D.sevm d (skimToken1 D.sevm b) out1 d2 ∧
    T = .next (skimBalanceReply out0) (staticViewTranscript views0 .done)
      (.next (skimTransferReply d.returnData true) (mutableTranscript turns1 .done)
        (.next (skimBalanceReply out1) (staticViewTranscript views1 .done)
          (.next (skimTransferReply d2.returnData true) (mutableTranscript turns3 .done) .done))) ∧
    (∀ picked ∈ views0 ++ views1, Blanc.Sevm.selector picked.1.frame.sevm = picked.2.selector ∧
      picked.1.frame.sevm.currentTarget = D.sevm.currentTarget) ∧
    (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns1 ++ turns3 →
      LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
    (views0 = [] ∧ D.sevm.benvStat.rules.isPrecomp (skimToken0 D.sevm b).toAdr ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw),
        Execution.commits raw = true ∧
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        views0.map Prod.fst =
          (Exec.retainedTargetTurnsAt D.sevm.currentTarget [] childRun).filterMap Sum.getRight?) ∧
    (views1 = [] ∧ D.sevm.benvStat.rules.isPrecomp
        (skimToken1 D.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw),
        Execution.commits raw = true ∧
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        views1.map Prod.fst =
          (Exec.retainedTargetTurnsAt D.sevm.currentTarget [] childRun).filterMap Sum.getRight?) ∧
    ((turns1 = [] ∧ D.sevm.benvStat.rules.isPrecomp
        (skimToken0 D.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw)
        (committed : Execution.commits raw = true),
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        turns1.map MutableTurn.event =
          Exec.targetLogEventsFrom D.sevm.currentTarget [] 0 childRun committed) ∧
    ((turns3 = [] ∧ D.sevm.benvStat.rules.isPrecomp
        (skimToken1 D.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr) ∨
      ∃ (child : Evm) (raw : Execution) (childRun : Exec child.pc child.sta child.dyna raw)
        (committed : Execution.commits raw = true),
        (∀ r ∈ Exec.rawFrameRoots childRun, r ∈ Exec.rawFrameRoots D.exc) ∧
        turns3.map MutableTurn.event =
          Exec.targetLogEventsFrom D.sevm.currentTarget [] 0 childRun committed)

/-- **Swap provenance.** The entry is the decoded swap; the transcript is, in order, the frame's actual
optional transfer `CALL`s and optional callback `CALL` (each present iff its amount, respectively the
data, is nonzero, with the retained mutable turns of the actual child, re-entered Pair frames
`LockedAuth`), and the two actual post-callback `balanceOf(pair)` `STATICCALL` replies with the retained
static Pair views (`SwapCanonicalBody`). -/
def SwapAuth (D : Exec.Deriv) (entry : Entry) (T : Transcript) : Prop :=
  Blanc.Sevm.selector D.sevm = 0x022c0d9f ∧ entry = swapDecodedEntry D.sevm ∧
  ∃ (b : Devm) (G : Nat) (current : Checkpoint) (invocation : List Nat) (frame : Frame),
    D.pc = 0 ∧ D.devm = St b [] Mem.empty G ∧ frame.checkpoint = current ∧
    frame.context = writerContext D.sevm invocation ∧
  let sevm := D.sevm
  let locals := swapFrontLocals sevm current.state
  let w := swapCutWords sevm current.state
  let S := swapCutStack w 0x257 [0x022c0d9f]
  ∃ (T0 T1 TC : Transcript → Transcript) (turns0 turns1 turnsC : List MutableTurn)
    (b1 b2 d d0 d1 : Devm) (M1 M2 M : Mem) (p1 p : B256) (out0 out1 : Bytes)
    (views0 views1 : List StaticViewTurn),
    SwapTransferOpt D sevm (swapPrefixWorld sevm b) S getterInitMemory 128
      (swapAmount0Out sevm) (swapRecipientWord sevm) current.state.token0.toB256 0x8d0 b1 M1 p1 ∧
    SwapTransferOpt D sevm b1 S M1 p1
      (swapAmount1Out sevm) (swapRecipientWord sevm) current.state.token1.toB256 0x8e1 b2 M2 p ∧
    SwapCallbackOpt D sevm b2 S M2 p (swapRecipientWord sevm) (swapAmount0Out sevm)
      (swapAmount1Out sevm) (swapDataLength sevm) (swapDataStart sevm) d M ∧
    ((swapAmount0Out sevm = 0 ∧ T0 = id) ∨ (swapAmount0Out sevm ≠ 0 ∧
      T0 = (fun tail => .next (swapTransferReply b1.returnData) (mutableTranscript turns0 .done) tail) ∧
      SwapCallProvenance sevm.currentTarget D sevm (swapPrefixWorld sevm b) b1 turns0)) ∧
    ((swapAmount1Out sevm = 0 ∧ T1 = id) ∨ (swapAmount1Out sevm ≠ 0 ∧
      T1 = (fun tail => .next (swapTransferReply b2.returnData) (mutableTranscript turns1 .done) tail) ∧
      SwapCallProvenance sevm.currentTarget D sevm b1 b2 turns1)) ∧
    ((swapDataLength sevm = 0 ∧ TC = id) ∨ (swapDataLength sevm ≠ 0 ∧
      TC = (fun tail => .next (swapCallbackReply d.returnData) (mutableTranscript turnsC .done) tail) ∧
      SwapCallProvenance sevm.currentTarget D sevm b2 d turnsC)) ∧
    SwapBalanceCall D sevm d M p w.token0
      (w.token1 :: w.token0 :: 0 :: 0 :: w.reserve1 :: w.reserve0 :: w.dataLength ::
        w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 :: [0x022c0d9f]) d0 out0 ∧
    SwapBalanceCall D sevm d0 (swapBalanceReply M p sevm.currentTarget out0) p w.token1
      (w.token1 :: w.token0 :: 0 :: swapBalanceWord out0 :: w.reserve1 :: w.reserve0 ::
        w.dataLength :: w.dataOffset :: w.recipient :: w.amount1Out :: w.amount0Out :: 0x257 ::
        [0x022c0d9f]) d1 out1 ∧
    T = ((T0 ∘ T1) ∘ TC)
      (.next (feeObservedResult out0) (staticViewTranscript views0 .done)
        (.next (feeObservedResult out1) (staticViewTranscript views1 .done) .done)) ∧
    (∀ located entry nested, Sum.inr (located, entry, nested) ∈ turns0 ++ turns1 ++ turnsC →
      LockedAuth (Exec.Frame.rootDeriv located.frame) entry nested) ∧
    PairViewProvenance D sevm frame (swapTokenWord w.token0) views0 ∧
    PairViewProvenance D sevm (frame.beginResume (swapRequest0 frame locals))
      (swapTokenWord w.token1) views1

/-- **Burn provenance.** The entry is the decoded burn; the transcript is the one the frame's actual
call answers fix (`BurnFrameAuth`: the initial balances, `feeTo`, the two transfer `CALL`s with their
retained turns and the two final balances, `BurnCallProvenance`). -/
def BurnAuth (D : Exec.Deriv) (entry : Entry) (T : Transcript) : Prop :=
  Blanc.Sevm.selector D.sevm = 0x89afcb44 ∧
  entry = .burn ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& Sevm.dataWord D.sevm 4).toAdr ∧
  BurnFrameAuth D T

/-! ## The dispatcher -/

/-- The supply of one successful pc-zero Pair frame at the current checkpoint: from every incoming
finite representation inside the separated universe `U`, the frame is one authenticated source
invocation that succeeds in the model (`PairStepOutcome`). -/
def PairStepSupplyWith
    (Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop)
    (Auth : Exec.Deriv → Entry → Transcript → Prop) (U : WriterKey → Prop)
    (selected : Sevm → Prop) : Prop :=
  ∀ (current : Checkpoint) (invocation : List Nat) {sevm : Sevm} {b post : Devm} {G : Nat}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) {K : WriterKey → Prop},
    sevm.code = code → b.getCode sevm.currentTarget = code → CoveredFork sevm.benvStat.fork →
    b.output = [] → sevm.data.length < 2 ^ 256 → selected sevm →
    PairGood U ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ →
    (∀ k, K k → U k) → WriterRep K (b.getStor sevm.currentTarget) current.state →
    PairStepOutcomeWith Consumes Auth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post

/-- One operation producer per family, all selecting the same outcome relation.
The dispatcher below owns the selector inversion; this record supplies no alternative witness. -/
structure PairSupplyRules
    (Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop)
    (Auth : Exec.Deriv → Entry → Transcript → Prop) (U : WriterKey → Prop) : Prop where
  transfer : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0xa9059cbb)
  approve : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0x095ea7b3)
  transferFrom : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0x23b872dd)
  initializeEntry : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0x485cc955)
  permit : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0xd505accf)
  mint : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0x6a627842)
  sync : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0xfff6cae9)
  skim : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0xbc25cf77)
  swap : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0x022c0d9f)
  burn : PairStepSupplyWith Consumes Auth U (fun sevm => Blanc.Sevm.selector sevm = 0x89afcb44)
  views : ∀ view : StaticView, PairStepSupplyWith Consumes Auth U
    (fun sevm => Blanc.Sevm.selector sevm = view.selector)

/-- The single Pair selector dispatch, parameterized by the operation producers. -/
theorem pairSupplyWith
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {Auth : Exec.Deriv → Entry → Transcript → Prop} {U : WriterKey → Prop}
    (rules : PairSupplyRules Consumes Auth U) :
    PairStepSupplyWith Consumes Auth U (fun _ => True) := by
  intro current invocation sevm b post G run K codeEq installedCode fork freshOutput representable
    _ good sub wrep
  have member := pair_bytecode_selector_inv codeEq fork run
  simp only [pairSelectors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact rules.views (.scalar (.address .token1)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.permit current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.allowance) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.sync current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.scalar (.constant .minimumLiquidity)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.skim current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.scalar (.address .factory)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.views (.singleMapping .nonces) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.burn current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.string .symbol) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.transfer current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.mint current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.singleMapping .balanceOf) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.views (.scalar (.stored .kLast)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.views (.scalar (.stored .domainSeparator)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.initializeEntry current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.scalar (.stored .price0CumulativeLast)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.views (.scalar (.stored .price1CumulativeLast)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.transferFrom current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.scalar (.constant .permitTypehash)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.views (.scalar (.constant .decimals)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.approve current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.scalar (.address .token0)) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.views (.totalSupply) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.swap current invocation run codeEq installedCode fork freshOutput
      representable h good sub wrep
  · exact rules.views (.string .name) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep
  · exact rules.views (.getReserves) current invocation run codeEq installedCode fork freshOutput
      representable (h.trans (by decide)) good sub wrep

end Blanc.Lift.UniswapV2Pair
