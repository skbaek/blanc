import Blanc.Lift.UniswapV2Pair.PairWriterAbsorb
import Blanc.Lift.UniswapV2Pair.SwapCanonical
import Blanc.Lift.UniswapV2Pair.MintCanonical
import Blanc.Lift.UniswapV2Pair.SyncGasCanonical
import Blanc.Lift.UniswapV2Pair.BurnFeeTransfers
import Blanc.SlotFootprintSubset

/-!
# The unlocked Pair-frame supply

`LockedSupply.lean` consumes a committed Pair frame entered while the Pair is locked.  This module is
its unlocked analogue for the history: every successful pc-zero Pair frame, at any of the 27 selectors,
is one exact source invocation that *succeeds* in the model, from any incoming finite representation
inside a separated trace-local universe `U`, and its entry and transcript are authenticated against the
frame's own derivation (`PairFrameAuth`).

* `pairFrameKeys` — the HASH-T rows one actual Pair frame selects: its decoded mapping rows, its static
  view rows, the two LP rows a mint may write, the Pair's own LP row (burn) and every possible
  fee-recipient row (`mintFeeReplyKeys`);
* `PairGood U D` — every raw Pair frame root of `D` has its rows in `U`; it gives each family's own
  trace-key obligation (`swapTraceKeys`, `mintTraceKeys`, `syncTraceKeys`, `LockedGood`);
* `PairStepOutcome` — the consumed invocation with model success and footprint growth;
* `SwapAuth`, `MintAuth`, `SyncAuth`, `SkimAuth`, `BurnAuth` — the per-family provenance the frame
  theorems state, with the transcript named; the lock-free entries use `LockedAuth`;
* `pairSupply` — the 27-way dispatcher.
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

theorem PairStepOutcome.mono {Auth Auth' : Exec.Deriv → Entry → Transcript → Prop}
    {U : WriterKey → Prop} {current : Checkpoint} {invocation : List Nat} {K : WriterKey → Prop}
    {D : Exec.Deriv} {post : Devm} (weaken : ∀ e T, Auth D e T → Auth' D e T)
    (outcome : PairStepOutcome Auth U current invocation K D post) :
    PairStepOutcome Auth' U current invocation K D post := by
  obtain ⟨entry, nested, child, bytes, K', auth, rest⟩ := outcome
  exact ⟨entry, nested, child, bytes, K', weaken entry nested auth, rest⟩

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

theorem pairStepOutcome_of {Auth : Exec.Deriv → Entry → Transcript → Prop} {U K K' : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {D : Exec.Deriv} {post : Devm}
    {entry : Entry} {nested : Transcript} {child : RunResult} {bytes : Bytes}
    {keys : List WriterKey}
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    {s : Stor} (incoming : WriterRep K s current.state)
    (good : ∀ k ∈ keys, U k) (auth : Auth D entry nested)
    (consumed : ExactConsumes (startTyped current (writerContext D.sevm invocation) entry) nested child)
    (success : child.status = .success bytes) (outputEq : bytes = post.output)
    (grown : ∀ k, K' k → WriterExtend K keys k)
    (rep : WriterRep K' (post.getStor D.sevm.currentTarget) child.frame.current.state) :
    PairStepOutcome Auth U current invocation K D post :=
  pairStepOutcome_with inj apart sub incoming good auth consumed success outputEq grown rep

/-! ## Lock-free entries, at any lock state -/

section Free

variable {U : WriterKey → Prop} (inj : WriterInj U) (apart : WriterApart U)
  {current : Checkpoint} {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
  {K : WriterKey → Prop}
  (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
  (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
  (representable : sevm.data.length < 2 ^ 256) (sub : ∀ k, K k → U k)
  (wrep : WriterRep K (b.getStor sevm.currentTarget) current.state)
include inj apart run codeEq fork representable sub wrep

theorem free_transfer_outcome (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (good : ∀ k ∈ transferTouched sevm.caller (transferRecipient sevm), U k) :
    PairStepOutcome LockedAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  obtain ⟨_, _, _, _, result, consumed⟩ := transfer_bytecode_exact_consumes
    (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine pairStepOutcome_of inj apart sub wrep good (Or.inl ⟨selector, rfl, rfl⟩) consumed rfl rfl
    (fun _ h => h) ?_
  rw [result.sourceState]
  exact result.representation

theorem free_approve_outcome (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (good : ∀ k ∈ approveTouched sevm.caller (approveSpender sevm), U k) :
    PairStepOutcome LockedAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  obtain ⟨_, _, _, _, ⟨_, representation, _⟩, consumed⟩ := approve_bytecode_exact_consumes
    (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  exact pairStepOutcome_of inj apart sub wrep good (Or.inr (Or.inl ⟨selector, rfl, rfl⟩))
    consumed rfl rfl (fun _ h => h) representation

theorem free_transferFrom_outcome (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (good : ∀ k ∈ transferFromTouched (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm), U k) :
    PairStepOutcome LockedAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  obtain ⟨_, _, _, _, result, consumed⟩ := transferFrom_bytecode_exact_consumes
    (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine pairStepOutcome_of inj apart sub wrep good
    (Or.inr (Or.inr (Or.inl ⟨selector, rfl, rfl⟩))) consumed rfl rfl (fun _ h => h) ?_
  rw [result.sourceState]
  exact result.representation

omit inj apart in
theorem free_initialize_outcome (inj : WriterInj U) (apart : WriterApart U)
    (freshOutput : b.output = []) (selector : Blanc.Sevm.selector sevm = 0x485cc955) :
    PairStepOutcome LockedAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  obtain ⟨_, _, _, _, _, result, consumed⟩ := initialize_bytecode_exact_consumes
    (invocation := invocation) wrep representable freshOutput codeEq fork selector run
  refine pairStepOutcome_of (keys := []) inj apart sub wrep (fun _ h => absurd h List.not_mem_nil)
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨selector, rfl, rfl⟩)))) consumed rfl rfl
    (fun _ h => Or.inl h) ?_
  rw [result.sourceCurrent]
  exact result.representation

theorem free_permit_outcome (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : b.getCode sevm.currentTarget = code) (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (touched : ∀ k ∈ permitTouched (permitOwner sevm) (permitSpender sevm), U k)
    (good : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    PairStepOutcome LockedAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  obtain ⟨_, _, _, _, _, out, _, entered, views, auth, result, consumed, _⟩ :=
    permit_bytecode_exact_turns (invocation := invocation) inj apart sub sem image wrep touched
      (by rw [installed]; exact image.symm) representable codeEq fork selector freshOutput run good
  obtain ⟨_, representation, _, _, _, _, _, _, _, _, outputEq, _⟩ := result
  exact pairStepOutcome_of inj apart sub wrep touched
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨selector, rfl, out, entered, views, rfl, auth⟩)))))
    consumed rfl outputEq.symm (fun _ h => h) representation

theorem free_view_outcome (view : StaticView)
    (selector : Blanc.Sevm.selector sevm = view.selector)
    (good : ∀ k ∈ staticViewDecodedKeys sevm, U k) :
    PairStepOutcome LockedAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good
  obtain ⟨_, _, _, storage, _, _, _, consumed, frameCurrent, _, _⟩ :=
    staticView_source_handler_selected (ctx := writerContext sevm invocation) wrep fresh
      representable rfl codeEq fork view selector run
  refine pairStepOutcome_of inj apart sub wrep good
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨view, selector, rfl, rfl⟩))))) consumed rfl rfl
    (fun _ h => h) ?_
  rw [frameCurrent, storage sevm.currentTarget]
  exact wrep.extend fresh

end Free

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
children (`skim_bytecode_exact_consumes_legacy`). -/
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

section Guarded

variable {U : WriterKey → Prop} (inj : WriterInj U) (apart : WriterApart U)
  {current : Checkpoint} {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
  {K : WriterKey → Prop}
  (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
  (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
  (sub : ∀ k, K k → U k)
  (wrep : WriterRep K (b.getStor sevm.currentTarget) current.state)
  (sem : CodeSem) (image : sem.image = some code.toList)
  (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
  (good : PairGood U ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)
include inj apart run codeEq fork sub wrep sem image installed good

theorem pair_mint_outcome (selector : Blanc.Sevm.selector sevm = 0x6a627842) :
    PairStepOutcome MintAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  have inside := writerExtend_universe sub good.mint
  obtain ⟨_, _, out0, out1, outF, steps, views0, views1, viewsF, final, rets, K', liquidity, fee,
      feeLogs, added, consumed, _, _, _, grown, rep, _, _, _, _, _, outputEq, picked, prov0, prov1,
      provF⟩ :=
    mint_bytecode_exact_consumes invocation wrep sem image installed codeEq fork selector run
      (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_of inj apart sub wrep good.mint
    ⟨selector, rfl, current, out0, out1, outF, views0, views1, viewsF, steps, rfl, picked, prov0,
      prov1, provF⟩ consumed rfl outputEq.symm grown rep

theorem pair_sync_outcome (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9) :
    PairStepOutcome SyncAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  have inside := writerExtend_universe sub good.sync
  obtain ⟨_, _, result, consumed, rep, _, _, outputEq⟩ :=
    sync_bytecode_exact_consumes invocation wrep sem image installed freshOutput codeEq fork
      selector run (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_of (keys := []) inj apart sub wrep (fun _ h => absurd h List.not_mem_nil)
    ⟨selector, rfl, K, current, invocation, b, post, result, rfl⟩ consumed rfl outputEq.symm
    (fun _ h => Or.inl h) rep

theorem pair_skim_outcome (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77) :
    PairStepOutcome SkimAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  have inside := writerExtend_universe sub good.skim
  obtain ⟨_, _, out0, d, first, out1, d2, views0, views1, turns1, turns3, final, rets, K', added,
      second, consumed, _, _, grown, rep, _, _, _, _, picked, auth, prov0, prov1, prov2, prov3, outputEq⟩ :=
    skim_bytecode_exact_consumes_legacy invocation wrep sem image installed freshOutput codeEq fork
      selector run (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_of inj apart sub wrep good.skim
    ⟨selector, rfl, b, G, rfl, rfl, out0, d, first, out1, d2, views0, views1, turns1, turns3, second,
      rfl, picked, auth, prov0, prov1, prov2, prov3⟩ consumed rfl outputEq.symm grown rep

theorem pair_swap_outcome (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) :
    PairStepOutcome SwapAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  have inside := writerExtend_universe sub good.skim
  obtain ⟨_, _, frame, T0, T1, TC, turns0, turns1, turnsC, b1, b2, d, d0, d1, M1, M2, M, p1, p,
      out0, out1, views0, views1, final, rets, K', added, opt0, opt1, optC, shape0, shape1, shapeC,
      call0, call1, consumed, frameCheckpoint, frameContext, _, _, _, grown, rep, _, _, _, _, outputEq,
      auth, prov0, prov1, _⟩ :=
    swap_bytecode_exact_consumes invocation wrep sem image installed freshOutput codeEq fork
      selector run (writerInj_restrict inj inside) (writerApart_restrict apart inside)
  exact pairStepOutcome_of inj apart sub wrep good.skim
    ⟨selector, rfl, b, G, current, invocation, frame, rfl, rfl, frameCheckpoint, frameContext,
      T0, T1, TC, turns0, turns1, turnsC, b1, b2, d, d0, d1, M1, M2, M, p1, p, out0, out1, views0,
      views1, opt0, opt1, optC, shape0, shape1, shapeC, call0, call1, rfl, auth, prov0, prov1⟩
    consumed rfl outputEq.symm grown rep

theorem pair_burn_outcome (selector : Blanc.Sevm.selector sevm = 0x89afcb44) :
    PairStepOutcome BurnAuth U current invocation K
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ post := by
  have row : ∀ k ∈ [WriterKey.balance sevm.currentTarget], U k := by
    intro k member
    rw [List.mem_singleton] at member
    rw [member]
    exact good.pairRow
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub row
  have sub₁ := writerExtend_universe sub row
  obtain ⟨a, amount0, amount1, provenance, K', final, rets, _, _, _, inside, grows, consumed, halted,
      outputEq, rep, _⟩ :=
    burnRaw_source_authentic_legacy invocation codeEq fork selector (wrep.extend fresh)
      (Or.inr (List.mem_singleton_self _)) run inj apart sub₁ good.mint sem image installed
      good.locked good.views
  cases halted
  exact ⟨_, a.transcript, _, _, K', ⟨selector, rfl, burnRaw_frameAuth provenance⟩, consumed, rfl,
    outputEq.symm,
    fun k h => grows k (Or.inl h), inside, rep⟩

end Guarded

/-! ## The dispatcher -/

/-- **Authenticated entry and transcript of one Pair frame**, by family: the lock-free entries
(`LockedAuth`), swap, mint, sync, skim and burn. -/
def PairFrameAuth (D : Exec.Deriv) (entry : Entry) (T : Transcript) : Prop :=
  LockedAuth D entry T ∨ SwapAuth D entry T ∨ MintAuth D entry T ∨ SyncAuth D entry T ∨
    SkimAuth D entry T ∨ BurnAuth D entry T

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

/-- The legacy supply is the exact-consumption instance with unchanged premises. -/
def PairStepSupply (Auth : Exec.Deriv → Entry → Transcript → Prop) (U : WriterKey → Prop)
    (selected : Sevm → Prop) : Prop :=
  PairStepSupplyWith (fun _ => ExactConsumes) Auth U selected

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

/-- Compatibility producers for the original authentication and exact-consumption APIs. -/
theorem pairSupplyRules_legacy {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) (sem : CodeSem) (image : sem.image = some code.toList) :
    PairSupplyRules (fun _ => ExactConsumes) PairFrameAuth U where
  transfer := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have decoded := good.transferOwn selector
    exact (free_transfer_outcome inj apart run codeEq fork representable sub wrep
      selector decoded).mono (fun _ _ a => Or.inl a)
  approve := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have decoded := good.approveOwn selector
    exact (free_approve_outcome inj apart run codeEq fork representable sub wrep
      selector decoded).mono (fun _ _ a => Or.inl a)
  transferFrom := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have decoded := good.transferFromOwn selector
    exact (free_transferFrom_outcome inj apart run codeEq fork representable sub wrep
      selector decoded).mono (fun _ _ a => Or.inl a)
  initializeEntry := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    exact (free_initialize_outcome run codeEq fork representable sub wrep inj apart
      freshOutput selector).mono (fun _ _ a => Or.inl a)
  permit := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have decoded := good.permitOwn selector
    exact (free_permit_outcome inj apart run codeEq fork representable sub wrep sem image
      installedCode freshOutput selector decoded good.views).mono (fun _ _ a => Or.inl a)
  mint := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have installed : some (b.getCode sevm.currentTarget).toList = sem.image := by
      rw [installedCode]
      exact image.symm
    exact (pair_mint_outcome inj apart run codeEq fork sub wrep sem image installed good
      selector).mono (fun _ _ a => Or.inr (Or.inr (Or.inl a)))
  sync := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have installed : some (b.getCode sevm.currentTarget).toList = sem.image := by
      rw [installedCode]
      exact image.symm
    exact (pair_sync_outcome inj apart run codeEq fork sub wrep sem image installed good
      freshOutput selector).mono (fun _ _ a => Or.inr (Or.inr (Or.inr (Or.inl a))))
  skim := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have installed : some (b.getCode sevm.currentTarget).toList = sem.image := by
      rw [installedCode]
      exact image.symm
    exact (pair_skim_outcome inj apart run codeEq fork sub wrep sem image installed good
      freshOutput selector).mono (fun _ _ a => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl a)))))
  swap := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have installed : some (b.getCode sevm.currentTarget).toList = sem.image := by
      rw [installedCode]
      exact image.symm
    exact (pair_swap_outcome inj apart run codeEq fork sub wrep sem image installed good
      freshOutput selector).mono (fun _ _ a => Or.inr (Or.inl a))
  burn := by
    intro current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    have installed : some (b.getCode sevm.currentTarget).toList = sem.image := by
      rw [installedCode]
      exact image.symm
    exact (pair_burn_outcome inj apart run codeEq fork sub wrep sem image installed good
      selector).mono (fun _ _ a => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr a)))))
  views := by
    intro view current invocation sevm b post G run K codeEq installedCode fork freshOutput
      representable selector good sub wrep
    exact (free_view_outcome inj apart run codeEq fork representable sub wrep view
      selector good.viewsOwn).mono (fun _ _ a => Or.inl a)

/-- **The unlocked Pair-frame supply.**  Every successful pc-zero Pair frame, at any of its 27
selectors, is one authenticated source invocation that succeeds in the model. -/
theorem pairSupply {U : WriterKey → Prop} (inj : WriterInj U)
    (apart : WriterApart U) (sem : CodeSem) (image : sem.image = some code.toList) :
    PairStepSupply PairFrameAuth U (fun _ => True) :=
  pairSupplyWith (pairSupplyRules_legacy inj apart sem image)

end Blanc.Lift.UniswapV2Pair
