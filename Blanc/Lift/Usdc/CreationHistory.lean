import Blanc.ExecutionHistoryInAssociativity
import Blanc.Lift.Usdc.ProxyCompleteAvailable
import Blanc.Lift.Usdc.ImplV2Creation.Observation
import Blanc.Lift.Usdc.ImplV2_1Creation.Observation
import Blanc.Lift.Usdc.ImplV2_2Creation.Observation
import Blanc.Lift.Usdc.LibCreation.Observation
import Blanc.Lift.Usdc.ProxyRetainedNoDel

/-! Concrete original creations extend the available USDC runtime family only
at their actual selected transaction cuts. Original observation correspondence
stays explicit; no final runtime, origin or allowance invariant is assumed. -/
namespace Blanc.Lift.Usdc

open Jaune Blanc.ExecutionTrace

/-- The observed library constructor contributes no proxy-origin obligation,
preserves all older available runtimes, and installs the new library entry.
The entry's historical metadata is retained as supplied; this theorem asserts
only runtime availability at the actual after-cut state. -/
theorem LibCreation.OriginalObservation.origins_and_available_targets
    {checkpoint future pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : LibCreation.OriginalObservation block)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    {W available : List UsdcDeployedEntry} (entry : UsdcDeployedEntry)
    (address : entry.adr = usdcLib) (code : entry.code = Lib.code)
    (impls : ∀ e ∈ available, UsdcImplCode e.code)
    (ready : UsdcEntriesReady available observed.cut.benv.state) :
    UsdcTransactionOrigins usdcProxy W observed.cut.head ∧
      UsdcGuardedInstallations usdcProxy W observed.cut.head.settledRoots ∧
      UsdcEntriesReady (entry :: available) observed.cut.afterBenv.state := by
  have guarded := ConfiguredHistoryTraceIn.txSplit_origins_and_available_of_retainedTargets_ne
    (W := W) history BodyStageCapabilities.historical (fun hf => hf.bal_none)
    block observed.cut rootsIn impls ready observed.retainedNodes_target_ne_proxy
  refine ⟨guarded.1, guarded.2.1, guarded.2.2.cons ?_ ?_⟩
  · rw [address, code]
    exact (observed.installed observed.cut).1
  · intro _
    exact (observed.installed observed.cut).1

/-- The original ImplV2Creation cut preserves older entries and adds its checked
runtime. Original correspondence remains the observation's explicit boundary. -/
theorem ImplV2Creation.OriginalObservation.origins_and_available_targets
    {checkpoint future pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : ImplV2Creation.OriginalObservation block)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    {W available : List UsdcDeployedEntry} (entry : UsdcDeployedEntry)
    (address : entry.adr = F2prime.implementationV2) (code : entry.code = ImplV2.code)
    (impls : ∀ e ∈ available, UsdcImplCode e.code)
    (ready : UsdcEntriesReady available observed.cut.benv.state) :
    UsdcTransactionOrigins usdcProxy W observed.cut.head ∧
      UsdcGuardedInstallations usdcProxy W observed.cut.head.settledRoots ∧
      UsdcEntriesReady (entry :: available) observed.cut.afterBenv.state := by
  have guarded := ConfiguredHistoryTraceIn.txSplit_origins_and_available_of_retainedTargets_ne
    (W := W) history BodyStageCapabilities.historical (fun hf => hf.bal_none)
    block observed.cut rootsIn impls ready observed.retainedNodes_target_ne_proxy
  refine ⟨guarded.1, guarded.2.1, guarded.2.2.cons ?_ ?_⟩
  · rw [address, code]
    exact (observed.installed observed.cut).1
  · intro implementation
    have sizes := congrArg ByteArray.size (code.symm.trans implementation)
    exact ((by decide +kernel : ImplV2.code.size ≠ Impl.code.size) sizes).elim

/-- The original ImplV2_1Creation cut preserves older entries and adds its checked
runtime. Original correspondence remains the observation's explicit boundary. -/
theorem ImplV2_1Creation.OriginalObservation.origins_and_available_targets
    {checkpoint future pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : ImplV2_1Creation.OriginalObservation block)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    {W available : List UsdcDeployedEntry} (entry : UsdcDeployedEntry)
    (address : entry.adr = F2prime.implementationV2_1) (code : entry.code = ImplV2_1.code)
    (impls : ∀ e ∈ available, UsdcImplCode e.code)
    (ready : UsdcEntriesReady available observed.cut.benv.state) :
    UsdcTransactionOrigins usdcProxy W observed.cut.head ∧
      UsdcGuardedInstallations usdcProxy W observed.cut.head.settledRoots ∧
      UsdcEntriesReady (entry :: available) observed.cut.afterBenv.state := by
  have guarded := ConfiguredHistoryTraceIn.txSplit_origins_and_available_of_retainedTargets_ne
    (W := W) history BodyStageCapabilities.historical (fun hf => hf.bal_none)
    block observed.cut rootsIn impls ready observed.retainedNodes_target_ne_proxy
  refine ⟨guarded.1, guarded.2.1, guarded.2.2.cons ?_ ?_⟩
  · rw [address, code]
    exact (observed.installed observed.cut).1
  · intro implementation
    have sizes := congrArg ByteArray.size (code.symm.trans implementation)
    exact ((by decide +kernel : ImplV2_1.code.size ≠ Impl.code.size) sizes).elim

/-- The original ImplV2_2Creation cut preserves older entries and adds its checked
runtime. Original correspondence remains the observation's explicit boundary. -/
theorem ImplV2_2Creation.OriginalObservation.origins_and_available_targets
    {checkpoint future pre post : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint future)
    {block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post}
    (observed : ImplV2_2Creation.OriginalObservation block)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    {W available : List UsdcDeployedEntry} (entry : UsdcDeployedEntry)
    (address : entry.adr = F2prime.implementationV2_2) (code : entry.code = Impl.code)
    (impls : ∀ e ∈ available, UsdcImplCode e.code)
    (library : ∃ l ∈ available, l.adr = usdcLib ∧ l.code = Lib.code)
    (ready : UsdcEntriesReady available observed.cut.benv.state) :
    UsdcTransactionOrigins usdcProxy W observed.cut.head ∧
      UsdcGuardedInstallations usdcProxy W observed.cut.head.settledRoots ∧
      UsdcEntriesReady (entry :: available) observed.cut.afterBenv.state := by
  have guarded := ConfiguredHistoryTraceIn.txSplit_origins_and_available_of_retainedTargets_ne
    (W := W) history BodyStageCapabilities.historical (fun hf => hf.bal_none)
    block observed.cut rootsIn impls ready observed.retainedNodes_target_ne_proxy
  refine ⟨guarded.1, guarded.2.1, guarded.2.2.cons ?_ ?_⟩
  · rw [address, code]
    exact (observed.installed observed.cut).1
  · intro implementation
    obtain ⟨l, member, address, code⟩ := library
    have installed := (guarded.2.2 l member).1
    rw [address, code] at installed
    exact installed

/-- The original four creation blocks and the exact histories between them.
Only original block/slot/receipt correspondence is supplied; runtime, origins
and guarded installations are derived separately. -/
structure OriginalModernCreationChain (start finish : BlockChain) where
  v2Pre : BlockChain
  v2Post : BlockChain
  v21Pre : BlockChain
  v21Post : BlockChain
  libraryPre : BlockChain
  libraryPost : BlockChain
  v22Pre : BlockChain
  v22Post : BlockChain
  beforeV2 : ConfiguredHistoryTraceIn HistFork mainnetChainConfig start v2Pre
  v2Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v2Pre v2Post
  v2Observed : ImplV2Creation.OriginalObservation v2Block
  v2ToV21 : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v2Post v21Pre
  v21Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v21Pre v21Post
  v21Observed : ImplV2_1Creation.OriginalObservation v21Block
  v21ToLibrary : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v21Post libraryPre
  libraryBlock : ConfiguredBlockTraceIn HistFork mainnetChainConfig libraryPre libraryPost
  libraryObserved : LibCreation.OriginalObservation libraryBlock
  libraryToV22 : ConfiguredHistoryTraceIn HistFork mainnetChainConfig libraryPost v22Pre
  v22Block : ConfiguredBlockTraceIn HistFork mainnetChainConfig v22Pre v22Post
  v22Observed : ImplV2_2Creation.OriginalObservation v22Block
  afterV22 : ConfiguredHistoryTraceIn HistFork mainnetChainConfig v22Post finish

/-- Reassemble the supplied original blocks and intervening histories. -/
def OriginalModernCreationChain.trace {start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish) :
    ConfiguredHistoryTraceIn HistFork mainnetChainConfig start finish :=
  (((((((chain.beforeV2.step chain.v2Block).append chain.v2ToV21).step chain.v21Block).append
    chain.v21ToLibrary).step chain.libraryBlock).append chain.libraryToV22).step
    chain.v22Block).append chain.afterV22

/-- An entry records the actual state and complete raw prefix at a supplied
cut. This definition alone makes no installation or historical-boundary claim. -/
def usdcEntryAtOriginalCut {checkpoint pre post : BlockChain}
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (address : Adr) (code : ByteArray) :
    UsdcDeployedEntry where
  adr := address
  code := code
  base := cut.afterBenv.state
  pre := before.rawNodes ++ block.bodyTrace.beacon.rawNodes ++
    block.bodyTrace.history.rawNodes ++ cut.before.rawNodes ++ cut.head.rawNodes

noncomputable def OriginalModernCreationChain.v2Entry {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start) :
    UsdcDeployedEntry :=
  usdcEntryAtOriginalCut (before.append chain.beforeV2) chain.v2Block chain.v2Observed.cut
    F2prime.implementationV2 ImplV2.code

noncomputable def OriginalModernCreationChain.v21Entry {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start) :
    UsdcDeployedEntry :=
  usdcEntryAtOriginalCut
    (((before.append chain.beforeV2).step chain.v2Block).append chain.v2ToV21)
    chain.v21Block chain.v21Observed.cut F2prime.implementationV2_1 ImplV2_1.code

noncomputable def OriginalModernCreationChain.libraryEntry {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start) :
    UsdcDeployedEntry :=
  usdcEntryAtOriginalCut
    (((((before.append chain.beforeV2).step chain.v2Block).append chain.v2ToV21).step
      chain.v21Block).append chain.v21ToLibrary)
    chain.libraryBlock chain.libraryObserved.cut usdcLib Lib.code

noncomputable def OriginalModernCreationChain.v22Entry {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start) :
    UsdcDeployedEntry :=
  usdcEntryAtOriginalCut
    (((((((before.append chain.beforeV2).step chain.v2Block).append chain.v2ToV21).step
      chain.v21Block).append chain.v21ToLibrary).step chain.libraryBlock).append chain.libraryToV22)
    chain.v22Block chain.v22Observed.cut F2prime.implementationV2_2 Impl.code

/-- The final runtime family retains the earlier V1 entry and all four actual
creation cuts. Earlier intervals use only the already-created suffix of it. -/
noncomputable def OriginalModernCreationChain.entries {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start)
    (v1 : UsdcDeployedEntry) : List UsdcDeployedEntry :=
  [chain.v22Entry before, chain.libraryEntry before, chain.v21Entry before,
    chain.v2Entry before, v1]


/-- Every concrete creation entry belongs to the checked implementation family. -/
theorem OriginalModernCreationChain.entries_impls {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start)
    (v1 : UsdcDeployedEntry) (v1Code : v1.code = ImplV1.code) :
    ∀ e ∈ chain.entries before v1, UsdcImplCode e.code := by
  intro e member
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .inr (.inr (.inr (.inl rfl)))
  · exact .inr (.inr (.inr (.inr rfl)))
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inl rfl)
  · exact .inl v1Code

/-- The four original creations cover every allowed upgrade address. -/
theorem OriginalModernCreationChain.entries_complete {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start)
    (v1 : UsdcDeployedEntry) :
    ∀ a ∈ F2prime.upgradeTargets, ∃ e ∈ chain.entries before v1, a = e.adr := by
  intro a member
  simp only [F2prime.upgradeTargets, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨chain.v2Entry before, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)), rfl⟩
  · exact ⟨chain.v21Entry before,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩
  · exact ⟨chain.v22Entry before, List.mem_cons_self, rfl⟩

/-- After the final actual creation cut, the complete family suffices across
all remaining original blocks, including enabled system stages. -/
theorem OriginalModernCreationChain.afterV22_origins_and_available
    {checkpoint start finish : BlockChain}
    (chain : OriginalModernCreationChain start finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint start)
    (v1 : UsdcDeployedEntry) (v1Code : v1.code = ImplV1.code)
    {W : List UsdcDeployedEntry}
    (subset : ∀ e ∈ chain.entries before v1, e ∈ W)
    (ready : UsdcEntriesReady (chain.entries before v1) chain.v22Observed.cut.afterBenv.state) :
    UsdcMidHistoryOrigins usdcProxy W
        ((MidHistoryTraceIn.tail chain.v22Block chain.v22Observed.cut).append chain.afterV22) ∧
      UsdcGuardedInstallations usdcProxy W
        ((MidHistoryTraceIn.tail chain.v22Block chain.v22Observed.cut).append chain.afterV22).settledRoots ∧
      UsdcEntriesReady (chain.entries before v1) finish.state := by
  let priorV22 := (((((((before.append chain.beforeV2).step chain.v2Block).append
    chain.v2ToV21).step chain.v21Block).append chain.v21ToLibrary).step
    chain.libraryBlock).append chain.libraryToV22)
  have same : before.append chain.trace = (priorV22.step chain.v22Block).append chain.afterV22 := by
    simp only [trace, priorV22, ← ConfiguredHistoryTraceIn.append_assoc, ConfiguredHistoryTraceIn.append]
  apply ConfiguredHistoryTraceIn.mid_origins_of_complete_available_family
    (before.append chain.trace) BodyStageCapabilities.historical (fun hf => hf.bal_none)
    subset (chain.entries_impls before v1 v1Code) (chain.entries_complete before v1)
    ((MidHistoryTraceIn.tail chain.v22Block chain.v22Observed.cut).append chain.afterV22) ?_ ready
  intro R member
  rw [same]
  exact MidHistoryTraceIn.settledRoots_subset_full priorV22 chain.v22Block
    chain.v22Observed.cut chain.afterV22 member

/-- Original receipt correspondences for the four creation intervals. Each
range covers the actual original boundary blocks and allows only entries that
already existed at its starting cut. These fields remain explicit evidence. -/
structure OriginalModernCreationChain.Censuses
    {checkpoint pre post finish : BlockChain}
    (chain : OriginalModernCreationChain post finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post)
    (v1 : UsdcDeployedEntry) : Prop where
  toV2 : ((before.step block).append chain.trace).ReceiptCensus
    block.block.header.number chain.v2Block.block.header.number
    (UpgradedTargetSatisfies usdcProxy (fun target => ∃ e ∈ [v1], target = e.adr))
  toV21 : ((before.step block).append chain.trace).ReceiptCensus
    chain.v2Block.block.header.number chain.v21Block.block.header.number
    (UpgradedTargetSatisfies usdcProxy (fun target =>
      ∃ e ∈ [chain.v2Entry (before.step block), v1], target = e.adr))
  toLibrary : ((before.step block).append chain.trace).ReceiptCensus
    chain.v21Block.block.header.number chain.libraryBlock.block.header.number
    (UpgradedTargetSatisfies usdcProxy (fun target =>
      ∃ e ∈ [chain.v21Entry (before.step block), chain.v2Entry (before.step block), v1],
        target = e.adr))
  toV22 : ((before.step block).append chain.trace).ReceiptCensus
    chain.libraryBlock.block.header.number chain.v22Block.block.header.number
    (UpgradedTargetSatisfies usdcProxy (fun target =>
      ∃ e ∈ [chain.libraryEntry (before.step block), chain.v21Entry (before.step block),
        chain.v2Entry (before.step block), v1], target = e.adr))

/-- Original receipt censuses, checked constructors and the initial V1 runtime
produce the complete original post-cut chronology. No runtime, origin or
installation invariant at a later cut is supplied. -/
theorem OriginalModernCreationChain.origins_and_available_of_censuses
    {checkpoint pre post finish : BlockChain}
    (chain : OriginalModernCreationChain post finish)
    (before : ConfiguredHistoryTraceIn HistFork mainnetChainConfig checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork mainnetChainConfig pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (v1 : UsdcDeployedEntry) (v1Code : v1.code = ImplV1.code)
    {W : List UsdcDeployedEntry}
    (subset : ∀ e ∈ chain.entries (before.step block) v1, e ∈ W)
    (census : chain.Censuses before block v1)
    (ready : UsdcEntriesReady [v1] cut.afterBenv.state) :
    UsdcMidHistoryOrigins usdcProxy W ((MidHistoryTraceIn.tail block cut).append chain.trace) ∧
      UsdcGuardedInstallations usdcProxy W
        ((MidHistoryTraceIn.tail block cut).append chain.trace).settledRoots ∧
      UsdcEntriesReady (chain.entries (before.step block) v1) finish.state := by
  let beforeChain := before.step block
  let full := beforeChain.append chain.trace
  let e2 := chain.v2Entry beforeChain
  let e21 := chain.v21Entry beforeChain
  let el := chain.libraryEntry beforeChain
  let e22 := chain.v22Entry beforeChain
  let a0 := [v1]
  let a1 := [e2, v1]
  let a2 := [e21, e2, v1]
  let a3 := [el, e21, e2, v1]
  let p2 := beforeChain.append chain.beforeV2
  let p21 := (p2.step chain.v2Block).append chain.v2ToV21
  let pl := (p21.step chain.v21Block).append chain.v21ToLibrary
  let afterLibrary := (chain.libraryToV22.step chain.v22Block).append chain.afterV22
  let afterV21 := (chain.v21ToLibrary.step chain.libraryBlock).append afterLibrary
  let afterV2 := (chain.v2ToV21.step chain.v21Block).append afterV21
  have allImpls := chain.entries_impls beforeChain v1 v1Code
  have inAll0 : ∀ e ∈ a0, e ∈ chain.entries beforeChain v1 := by
    intro e member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)))
  have inAll1 : ∀ e ∈ a1, e ∈ chain.entries beforeChain v1 := by
    intro e member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have inAll2 : ∀ e ∈ a2, e ∈ chain.entries beforeChain v1 := by
    intro e member
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)
  have inAll3 : ∀ e ∈ a3, e ∈ chain.entries beforeChain v1 := by
    intro e member
    exact List.mem_cons_of_mem _ member
  have roots (R : Exec.Frame)
      (member : R ∈ chain.v2Block.settledRoots ∨ R ∈ chain.v21Block.settledRoots ∨
        R ∈ chain.libraryBlock.settledRoots ∨ R ∈ chain.v22Block.settledRoots) :
      R ∈ full.settledRoots := by
    simp only [full, trace, ConfiguredHistoryTraceIn.append_settledRoots,
      ConfiguredHistoryTraceIn.settledRoots, List.mem_append]
    tauto
  have interval0 := ConfiguredHistoryTraceIn.origins_between_txSplits_of_census
    before block cut chain.beforeV2 chain.v2Block chain.v2Observed.cut afterV2
    (by rw [chain.v2Observed.timestamp]; decide +kernel) (Nat.le_refl _) (Nat.le_refl _) a0
    (by simpa only [Censuses, trace, beforeChain, afterV2, afterV21, afterLibrary,
          ← ConfiguredHistoryTraceIn.append_assoc, ConfiguredHistoryTraceIn.append] using census.toV2)
    (fun e member => subset e (inAll0 e member))
    (fun e member => allImpls e (inAll0 e member)) ready
  have head0 := chain.v2Observed.origins_and_available_targets (W := W) full
    (fun R member => roots R (.inl member)) e2 rfl rfl
    (fun e member => allImpls e (inAll0 e member)) interval0.2.2.2
  have interval1 := ConfiguredHistoryTraceIn.origins_between_txSplits_of_census
    p2 chain.v2Block chain.v2Observed.cut chain.v2ToV21 chain.v21Block
    chain.v21Observed.cut afterV21
    (by rw [chain.v21Observed.timestamp]; decide +kernel) (Nat.le_refl _) (Nat.le_refl _) a1
    (by simpa only [trace, beforeChain, p2, afterV21, afterLibrary,
          ← ConfiguredHistoryTraceIn.append_assoc, ConfiguredHistoryTraceIn.append] using census.toV21)
    (fun e member => subset e (inAll1 e member))
    (fun e member => allImpls e (inAll1 e member)) head0.2.2
  have head1 := chain.v21Observed.origins_and_available_targets (W := W) full
    (fun R member => roots R (.inr (.inl member))) e21 rfl rfl
    (fun e member => allImpls e (inAll1 e member)) interval1.2.2.2
  have interval2 := ConfiguredHistoryTraceIn.origins_between_txSplits_of_census
    p21 chain.v21Block chain.v21Observed.cut chain.v21ToLibrary chain.libraryBlock
    chain.libraryObserved.cut afterLibrary
    (by rw [chain.libraryObserved.timestamp]; decide +kernel) (Nat.le_refl _) (Nat.le_refl _) a2
    (by simpa only [trace, beforeChain, p2, p21, afterLibrary,
          ← ConfiguredHistoryTraceIn.append_assoc, ConfiguredHistoryTraceIn.append] using census.toLibrary)
    (fun e member => subset e (inAll2 e member))
    (fun e member => allImpls e (inAll2 e member)) head1.2.2
  have head2 := chain.libraryObserved.origins_and_available_targets (W := W) full
    (fun R member => roots R (.inr (.inr (.inl member)))) el rfl rfl
    (fun e member => allImpls e (inAll2 e member)) interval2.2.2.2
  have interval3 := ConfiguredHistoryTraceIn.origins_between_txSplits_of_census
    pl chain.libraryBlock chain.libraryObserved.cut chain.libraryToV22 chain.v22Block
    chain.v22Observed.cut chain.afterV22
    (by rw [chain.v22Observed.timestamp]; decide +kernel) (Nat.le_refl _) (Nat.le_refl _) a3
    (by simpa only [trace, beforeChain, p2, p21, pl,
          ← ConfiguredHistoryTraceIn.append_assoc, ConfiguredHistoryTraceIn.append] using census.toV22)
    (fun e member => subset e (inAll3 e member))
    (fun e member => allImpls e (inAll3 e member)) head2.2.2
  have head3 := chain.v22Observed.origins_and_available_targets (W := W) full
    (fun R member => roots R (.inr (.inr (.inr member)))) e22 rfl rfl
    (fun e member => allImpls e (inAll3 e member))
    ⟨el, List.mem_cons_self, rfl, rfl⟩ interval3.2.2.2
  have finalInterval := chain.afterV22_origins_and_available beforeChain v1 v1Code subset head3.2.2
  have origins3 : UsdcMidHistoryOrigins usdcProxy W
      ((MidHistoryTraceIn.tail chain.libraryBlock chain.libraryObserved.cut).append afterLibrary) := by
    simpa only [afterLibrary, ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append] using
      UsdcMidHistoryOrigins.splice
        ((MidHistoryTraceIn.tail chain.libraryBlock chain.libraryObserved.cut).append chain.libraryToV22)
        chain.v22Block chain.v22Observed.cut chain.afterV22
        interval3.1 interval3.2.1 head3.1 finalInterval.1
  have installs3 : UsdcGuardedInstallations usdcProxy W
      ((MidHistoryTraceIn.tail chain.libraryBlock chain.libraryObserved.cut).append afterLibrary).settledRoots := by
    simpa only [afterLibrary, ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append] using
      UsdcGuardedInstallations.splice
        ((MidHistoryTraceIn.tail chain.libraryBlock chain.libraryObserved.cut).append chain.libraryToV22)
        chain.v22Block chain.v22Observed.cut chain.afterV22
        (fun R member => interval3.2.2.1 R (List.mem_append_left _ member))
        (fun R member => interval3.2.2.1 R (List.mem_append_right _ member)) head3.2.1 finalInterval.2.1
  have origins2 : UsdcMidHistoryOrigins usdcProxy W
      ((MidHistoryTraceIn.tail chain.v21Block chain.v21Observed.cut).append afterV21) := by
    simpa only [afterV21, ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append] using
      UsdcMidHistoryOrigins.splice
        ((MidHistoryTraceIn.tail chain.v21Block chain.v21Observed.cut).append chain.v21ToLibrary)
        chain.libraryBlock chain.libraryObserved.cut afterLibrary
        interval2.1 interval2.2.1 head2.1 origins3
  have installs2 : UsdcGuardedInstallations usdcProxy W
      ((MidHistoryTraceIn.tail chain.v21Block chain.v21Observed.cut).append afterV21).settledRoots := by
    simpa only [afterV21, ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append] using
      UsdcGuardedInstallations.splice
        ((MidHistoryTraceIn.tail chain.v21Block chain.v21Observed.cut).append chain.v21ToLibrary)
        chain.libraryBlock chain.libraryObserved.cut afterLibrary
        (fun R member => interval2.2.2.1 R (List.mem_append_left _ member))
        (fun R member => interval2.2.2.1 R (List.mem_append_right _ member)) head2.2.1 installs3
  have origins1 : UsdcMidHistoryOrigins usdcProxy W
      ((MidHistoryTraceIn.tail chain.v2Block chain.v2Observed.cut).append afterV2) := by
    simpa only [afterV2, ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append] using
      UsdcMidHistoryOrigins.splice
        ((MidHistoryTraceIn.tail chain.v2Block chain.v2Observed.cut).append chain.v2ToV21)
        chain.v21Block chain.v21Observed.cut afterV21
        interval1.1 interval1.2.1 head1.1 origins2
  have installs1 : UsdcGuardedInstallations usdcProxy W
      ((MidHistoryTraceIn.tail chain.v2Block chain.v2Observed.cut).append afterV2).settledRoots := by
    simpa only [afterV2, ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append] using
      UsdcGuardedInstallations.splice
        ((MidHistoryTraceIn.tail chain.v2Block chain.v2Observed.cut).append chain.v2ToV21)
        chain.v21Block chain.v21Observed.cut afterV21
        (fun R member => interval1.2.2.1 R (List.mem_append_left _ member))
        (fun R member => interval1.2.2.1 R (List.mem_append_right _ member)) head1.2.1 installs2
  refine ⟨?_, ?_, finalInterval.2.2⟩
  · simpa only [trace, afterV2, afterV21, afterLibrary,
        ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append,
        ← ConfiguredHistoryTraceIn.append_assoc, ConfiguredHistoryTraceIn.append] using
      UsdcMidHistoryOrigins.splice ((MidHistoryTraceIn.tail block cut).append chain.beforeV2)
        chain.v2Block chain.v2Observed.cut afterV2 interval0.1 interval0.2.1 head0.1 origins1
  · simpa only [trace, afterV2, afterV21, afterLibrary,
        ← MidHistoryTraceIn.append_assoc, MidHistoryTraceIn.append,
        ← ConfiguredHistoryTraceIn.append_assoc, ConfiguredHistoryTraceIn.append] using
      UsdcGuardedInstallations.splice ((MidHistoryTraceIn.tail block cut).append chain.beforeV2)
        chain.v2Block chain.v2Observed.cut afterV2
        (fun R member => interval0.2.2.1 R (List.mem_append_left _ member))
        (fun R member => interval0.2.2.1 R (List.mem_append_right _ member)) head0.2.1 installs1

end Blanc.Lift.Usdc
