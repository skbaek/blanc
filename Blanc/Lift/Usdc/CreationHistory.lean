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


end Blanc.Lift.Usdc
