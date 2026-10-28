import Blanc.Lift.Usdc.ProxyRetainedContextCodes
import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.Usdc.ProxyRawCallers
import Blanc.Lift.Usdc.AllowanceRawHistory
import Blanc.Lift.UniswapV2Pair.PairPositionalCallsIn
import Blanc.ExecutionInCodeImage
import Blanc.ExecutionMidHistoryInForest
import Blanc.StaticStorage

/-! Retained Pair callers through the actual USDC proxy ancestry. -/

namespace Blanc.Composition.UniswapV2PairUsdcCallers

open Jaune Blanc Blanc.Lift Blanc.Lift.Usdc Blanc.ExecutionTrace

private def CallerShape (pair P : Adr) (G : Exec.Frame) : Prop :=
  G.sevm.currentTarget = P → G.sevm.isStatic = false → G.sevm.caller = pair →
    G.sevm.code = Lib.code ∨ Sevm.selector G.sevm = 0xa9059cbb ∨
      Sevm.selector G.sevm = 0x10d1e85c

private theorem caller_shapes {pair P : Adr} {frames roots : List Exec.Frame}
    (parents : ∀ before G after, frames = before ++ G :: after →
      G ∈ roots ∨ ∃ A ∈ before, G ∈ Exec.childFrames A.run ∧ Exec.SpawnedBy A.sevm G)
    (rootCallers : ∀ R ∈ roots, R.sevm.caller ≠ pair)
    (edge : ∀ A ∈ frames, CallerShape pair P A →
      ∀ G ∈ Exec.childFrames A.run, Exec.SpawnedBy A.sevm G → CallerShape pair P G) :
    ∀ G ∈ frames, CallerShape pair P G := by
  refine List.forall_mem_of_positional fun before G after split earlier => ?_
  rcases parents before G after split with root | ⟨A, member, child, spawned⟩
  · intro _ _ caller
    exact (rootCallers G root caller).elim
  · have inFrames : A ∈ frames := by
      rw [split]
      exact List.mem_append_left _ member
    exact edge A inFrames (earlier A member) G child spawned

private theorem proxy_child_selector {A G : Exec.Frame}
    (pc : A.pc = 0) (code : A.sevm.code = Proxy.code)
    (hsg : A.sevm.benvStat.rules.stateGas = none) (bal : A.sevm.benvStat.rules.bal = none)
    (size : A.sevm.data.length < 2 ^ 256) (child : G ∈ Exec.childFrames A.run)
    {pair : Adr} (apart : pair ≠ A.sevm.currentTarget) (caller : G.sevm.caller = pair) :
    A.sevm.caller = pair ∧ Sevm.selector G.sevm = Sevm.selector A.sevm := by
  rcases A with ⟨pcA, sevm, pre, out, run, committed⟩
  dsimp only at pc
  subst pcA
  obtain ⟨N, frame, resume, nextPc, childEvm, chain, step, enter, childEq⟩ :=
    Exec.childFrames_spawnedAt run (.refl _) G child
  obtain ⟨x, decoded, spawn, -⟩ := Evm.step_spawn_inv step
  obtain ⟨parentCaller, -, -, selector⟩ := Proxy.proxy_rawChild_caller_selectorH run code
    hsg bal size chain decoded spawn enter apart (by rw [← childEq]; exact caller)
  exact ⟨parentCaller, by rw [childEq]; exact selector⟩

private theorem retained_caller_write_excluded_of_contexts
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {pair P : Adr} {frames roots : List Exec.Frame}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (apart : pair ≠ P)
    (contexts : ∀ A ∈ frames, A.sevm.currentTarget = P →
      UsdcContextCode A.sevm.code ∧ ∀ N : Exec.Deriv,
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv A) N →
        A.sevm.code = Impl.code → N.devm.getCode usdcLib = Lib.code)
    (parents : ∀ before G after, frames = before ++ G :: after →
      G ∈ roots ∨ ∃ b₁ A b₂, before = b₁ ++ A :: b₂ ∧
        G ∈ Exec.childFrames A.run ∧ Exec.SpawnedBy A.sevm G ∧
        b₂.length < (Exec.descendantFrames A.run).length)
    (rootCallers : ∀ R ∈ roots, R.sevm.caller ≠ pair)
    (frameSubset : frames ⊆ history.settledFrames)
    (pairChildren : ∀ A ∈ frames, A.sevm.currentTarget = pair → A.sevm.isStatic = false →
      ∀ G ∈ Exec.childFrames A.run, G.sevm.isStatic = false →
        Sevm.selector G.sevm = 0xa9059cbb ∨ Sevm.selector G.sevm = 0x10d1e85c) :
    ∀ (G : Exec.Frame), G ∈ frames → G.sevm.currentTarget = P →
      ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
        Exec.Deriv.successfulSstore? m = some w →
        Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair := by
  have cap := BodyStageCapabilities.historical
  have bal : ∀ {f}, HistFork f → f.ruleSet.bal = none := fun h => h.bal_none
  have shapes : ∀ G ∈ frames, CallerShape pair P G := by
    refine caller_shapes (roots := roots) ?_ rootCallers ?_
    · intro before G after split
      rcases parents before G after split with root | ⟨b₁, A, b₂, equal, child, spawned, -⟩
      · exact Or.inl root
      · exact Or.inr ⟨A, by rw [equal]; exact List.mem_append_right _ List.mem_cons_self,
          child, spawned⟩
    · intro A member previous G child spawned target mutable caller
      have parentMutable : A.sevm.isStatic = false := by
        cases hs : A.sevm.isStatic with
        | false => rfl
        | true => rw [spawned.2 hs] at mutable; cases mutable
      have parentTarget : A.sevm.currentTarget = pair ∨ A.sevm.currentTarget = P := by
        rcases spawned.1 with h | h
        · exact Or.inl (h.symm.trans caller)
        · exact Or.inr (h.symm.trans target)
      rcases parentTarget with parentPair | parentP
      · exact Or.inr (pairChildren A member parentPair parentMutable G child mutable)
      · have rawA := history.mem_rawFrames_of_mem_settledFrames A (frameSubset member)
        obtain ⟨pc, selected, hsg, entry, gas⟩ := history.rawFrame_entryFacts cap _ rawA
        have size := history.calldata_bound cap (fun _ hf => hf.dataNonZero_ge) _ rawA
        have family := (contexts A member parentP).1
        obtain ⟨N, frame, resume, nextPc, childEvm, chain, step, enter, childEq⟩ :=
          Exec.childFrames_spawnedAt A.run (.refl _) G child
        obtain ⟨x, decoded, spawn, -⟩ := Evm.step_spawn_inv step
        have env := Exec.Deriv.ParentPrefix.sevm_eq chain
        rcases usdc_exec_kind pc hsg (bal selected) chain family decoded with
          call | staticcall | ⟨rfl, proxy | implementation⟩
        · have childCaller : G.sevm.caller = A.sevm.currentTarget := by
            rw [childEq, Frame.enter_run_caller enter, Xinst.step_call_spawn_caller (call ▸ spawn), env]
          exact (apart (caller.symm.trans (childCaller.trans parentP))).elim
        · have childCaller : G.sevm.caller = A.sevm.currentTarget := by
            rw [childEq, Frame.enter_run_caller enter,
              Xinst.step_staticcall_spawn_caller (staticcall ▸ spawn), env]
          exact (apart (caller.symm.trans (childCaller.trans parentP))).elim
        · obtain ⟨proxyCode, -⟩ := proxy
          obtain ⟨parentCaller, selector⟩ := proxy_child_selector pc proxyCode hsg (bal selected)
            size child (by rw [parentP]; exact apart) caller
          rcases previous parentP parentMutable parentCaller with library | selectors
          · exact (lib_ne_proxy (library.symm.trans proxyCode)).elim
          · rw [selector]
            exact Or.inr selectors
        · obtain ⟨implCode, operand⟩ := implementation
          have libCode := (contexts A member parentP).2 N chain implCode
          obtain ⟨g, address, rest, stack⟩ := Xinst.step_delegatecall_spawn_stack spawn
          have addressEq : address = usdcLib.toB256 := operand g address rest stack
          have actualCode : N.devm.getCode address.toAdr = Lib.code := by
            rw [addressEq, toAdr_toB256]
            exact libCode
          exact Or.inl (by
            rw [childEq, Frame.enter_run_code enter,
              Xinst.step_delegatecall_spawn_code spawn stack
                (by rw [actualCode]; exact Lib.code_not_delegation), actualCode])
  intro G member target m w chain found selector caller
  have rawG := history.mem_rawFrames_of_mem_settledFrames G (frameSubset member)
  obtain ⟨pc, selected, hsg, entry, gas⟩ := history.rawFrame_entryFacts cap _ rawG
  have rawM : m ∈ Exec.rawNodes G.run :=
    (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix G.run m).mpr
      ⟨_, List.mem_cons_self, chain⟩
  have mutable : G.sevm.isStatic = false := by
    cases hs : G.sevm.isStatic with
    | false => rfl
    | true =>
      obtain ⟨write, -⟩ := Exec.Deriv.successfulSstore?_sound_raw (G := Exec.Frame.rootDeriv G) rawM found
      have static := Exec.rawNodes_isStatic_of_static G.run hs
        write.occurrence.node write.occurrence.reached
      have storeRun : Ninst.Run write.occurrence.node.sevm write.occurrence.node.devm
          (.reg .sstore) write.stepPost := by
        refine ⟨write.occurrence.slot, write.occurrence.filled, write.occurrence.node.pc, ?_⟩
        simpa only [write.instruction_eq, write.stepSuccess] using write.occurrence.stepRun
      rw [of_run_sstore_not_static storeRun] at static
      cases static
  rcases shapes G member target mutable caller with library | transfer | callback
  · exact lib_no_sstore_node pc hsg chain library found
  · rw [transfer] at selector
    exact (by decide : (0xa9059cbb : B256) ∉ [0x095ea7b3, 0x39509351, 0xa457c2d7]) selector
  · rw [callback] at selector
    exact (by decide : (0x10d1e85c : B256) ∉ [0x095ea7b3, 0x39509351, 0xa457c2d7]) selector

private theorem retained_caller_write_excluded_of_forest
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    {pair P : Adr} {W : List UsdcDeployedEntry} {frames roots : List Exec.Frame}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes)
    (apartSlot : ImplSlotApart P history.rawNodes) (apart : pair ≠ P)
    (parents : ∀ before G after, frames = before ++ G :: after →
      G ∈ roots ∨ ∃ b₁ A b₂, before = b₁ ++ A :: b₂ ∧
        G ∈ Exec.childFrames A.run ∧ Exec.SpawnedBy A.sevm G ∧
        b₂.length < (Exec.descendantFrames A.run).length)
    (rootCallers : ∀ R ∈ roots, R.sevm.caller ≠ pair)
    (frameSubset : frames ⊆ history.settledFrames)
    (pairChildren : ∀ A ∈ frames, A.sevm.currentTarget = pair → A.sevm.isStatic = false →
      ∀ G ∈ Exec.childFrames A.run, G.sevm.isStatic = false →
        Sevm.selector G.sevm = 0xa9059cbb ∨ Sevm.selector G.sevm = 0x10d1e85c) :
    ∀ (G : Exec.Frame), G ∈ frames → G.sevm.currentTarget = P →
      ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
        Exec.Deriv.successfulSstore? m = some w →
        Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair := by
  have cap := BodyStageCapabilities.historical
  have bal : ∀ {f}, HistFork f → f.ruleSet.bal = none := fun h => h.bal_none
  have contexts := Usdc.ConfiguredHistoryTraceIn.usdc_ctxAt history cap bal world upgrades apartSlot
  have families := Usdc.ConfiguredHistoryTraceIn.usdc_contextCodes history cap bal world upgrades apartSlot
  apply retained_caller_write_excluded_of_contexts history apart ?_
    parents rootCallers frameSubset pairChildren
  intro A member target
  have rawA := history.mem_rawFrames_of_mem_settledFrames A (frameSubset member)
  refine ⟨families _ rawA target, ?_⟩
  intro N chain code
  have rawN : N ∈ history.rawNodes :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix N).mpr ⟨_, rawA, chain⟩
  obtain ⟨before, after, split⟩ := List.append_of_mem rawN
  have earlier : ∀ b₁ n b₂, before = b₁ ++ n :: b₂ → CtxAt P W b₁ n := by
    intro b₁ n b₂ equal
    apply contexts b₁ n (b₂ ++ N :: after)
    rw [split, equal]
    simp only [List.append_assoc, List.cons_append]
  obtain ⟨-, held, -⟩ := world_at history cap world upgrades apartSlot split earlier
  have env : N.sevm = A.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
  have nodeTarget : N.sevm.currentTarget = P := by rw [env]; exact target
  have allowed := contexts before N after split P (Or.inl rfl) nodeTarget
  have nodeCode : N.sevm.code = Impl.code := by rw [env]; exact code
  obtain ⟨_, _, _, _, _, libCode⟩ := world.active_library_code allowed nodeCode held
  exact libCode

/-- Actual retained Pair callers cannot execute a successful store under a caller-keyed
allowance selector. The root exclusion and both histories' genuine state premises are explicit. -/
theorem retained_caller_write_excluded {cfg : ChainConfig} {checkpoint future : BlockChain}
    {pair P : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (world : UsdcDeployedWorld history.BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W history.rawNodes)
    (apartSlot : ImplSlotApart P history.rawNodes) (apart : pair ≠ P)
    (rootCallers : ∀ R ∈ history.settledRoots, R.sevm.caller ≠ pair)
    (installed : some (checkpoint.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (checkpoint.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairHistoryTouchedKeysIn pair history)) :
    ∀ (G : Exec.Frame), G ∈ history.settledFrames → G.sevm.currentTarget = P →
      ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
        Exec.Deriv.successfulSstore? m = some w →
        Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair := by
  apply retained_caller_write_excluded_of_forest history world upgrades apartSlot apart
    (fun _ _ _ split => history.settledFrames_parentIn split) rootCallers
    (fun _ member => member)
  intro A member target mutable G child childMutable
  exact (UniswapV2Pair.pair_history_children_shapeHist history installed initial fresh
    A member target mutable G child childMutable).2.2

/-- Caller-keyed allowance stores are excluded on the actual post-cut mid history.
USDC world facts retain the original full chronology; Pair replay starts at afterBenv. -/
theorem mid_retained_caller_write_excluded_of_mid_senderQueries
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {pair P : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart P ((prior.step block).append later).rawNodes) (apart : pair ≠ P)
    (excluded : ∀ query ∈ ((MidHistoryTraceIn.tail block cut).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later))) :
    ∀ (G : Exec.Frame), G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
        Exec.Deriv.successfulSstore? m = some w →
        Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair := by
  let full := (prior.step block).append later
  let mid := (MidHistoryTraceIn.tail block cut).append later
  have rootCallers : ∀ R ∈ mid.settledRoots, R.sevm.caller ≠ pair :=
    mid.settledRoots_caller_ne_of_senderQueries excluded notSystem
  apply retained_caller_write_excluded_of_forest full world upgrades apartSlot apart
    (fun _ _ _ split => mid.settledFrames_parentIn split) rootCallers
    (MidHistoryTraceIn.settledFrames_subset_full prior block cut later)
  intro A member target mutable G child childMutable
  exact (UniswapV2Pair.pair_mid_history_children_shapeHist mid installed initial fresh
    A member target mutable G child childMutable).2.2

/-- Full-history compatibility wrapper; only the original post-cut sender queries
are consumed by the caller proof. -/
theorem mid_retained_caller_write_excluded
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {pair P : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (world : UsdcDeployedWorld ((prior.step block).append later).BoundaryAt P W checkpoint.state)
    (upgrades : UpgradesWithinFrom P W ((prior.step block).append later).rawNodes)
    (apartSlot : ImplSlotApart P ((prior.step block).append later).rawNodes) (apart : pair ≠ P)
    (excluded : ∀ query ∈ ((prior.step block).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later))) :
    ∀ (G : Exec.Frame), G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
        Exec.Deriv.successfulSstore? m = some w →
        Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair := by
  exact mid_retained_caller_write_excluded_of_mid_senderQueries
    prior block cut later world upgrades apartSlot apart
    (fun query member => excluded query
      (MidHistoryTraceIn.senderQueries_subset_full prior block cut later member))
    notSystem installed initial fresh

/-- Caller-keyed allowance writes are excluded on the actual post-cut history
using retained USDC contexts. Governance ranges over the original settled
frames; selected runtime readiness and actual upgrade installations remain
producer inputs, with no raw-upgrade or raw-world premise. -/
theorem mid_retained_caller_write_excluded_from_installations
    {cfg : ChainConfig} {checkpoint pre completed future : BlockChain} {i : Nat}
    {pair P : Adr} {W : List UsdcDeployedEntry}
    {KP : UniswapV2Pair.WriterKey → Prop} {st : UniswapV2Pair.State}
    (prior : ConfiguredHistoryTraceIn HistFork cfg checkpoint pre)
    (block : ConfiguredBlockTraceIn HistFork cfg pre completed)
    (cut : block.bodyTrace.transactions.TxSplit i)
    (later : ConfiguredHistoryTraceIn HistFork cfg completed future)
    (impls : ∀ e ∈ W, UsdcImplCode e.code)
    (lib : ∀ e ∈ W, e.code = Impl.code →
      ∃ l ∈ W, l.adr = usdcLib ∧ l.code = Lib.code)
    (rootReady : ∀ R ∈ ((prior.step block).append later).settledRoots,
      R.pre.getCode P = Proxy.code ∧
        ∃ e ∈ W, ((R.pre.getStor P).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre)
    (governance : UsdcGovernanceF2primeOn P ((prior.step block).append later).settledFrames)
    (installations : ∀ R ∈ ((prior.step block).append later).settledRoots,
      ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → N.sevm.code = Proxy.code →
      N.sevm.codeAddress = some P → ∀ write : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? N = some write → write.key = implSlot →
      write.value.toAdr ∈ F2prime.upgradeTargets →
      (N.devm.getCode write.value.toAdr).toList ≠ [] →
      ∃ e ∈ W, write.value.toAdr = e.adr ∧ e.RuntimeReady N.devm)
    (apartSlot : ∀ R ∈ ((prior.step block).append later).settledRoots,
      KnownImplSlotApart P (Exec.retainedNodes R.run))
    (apart : pair ≠ P)
    (excluded : ∀ query ∈ ((MidHistoryTraceIn.tail block cut).append later).senderQueries,
      query.recover ≠ .ok pair)
    (notSystem : pair ≠ systemAddress)
    (installed : some (cut.afterBenv.state.getCode pair).toList = UniswapV2Pair.pairSem.image)
    (initial : UniswapV2Pair.WriterRep KP (cut.afterBenv.state.getStor pair) st)
    (fresh : UniswapV2Pair.WriterFreshKeys KP (UniswapV2Pair.pairMidTouchedKeysIn pair
      ((MidHistoryTraceIn.tail block cut).append later))) :
    ∀ (G : Exec.Frame), G ∈ ((MidHistoryTraceIn.tail block cut).append later).settledFrames →
      G.sevm.currentTarget = P → ∀ (m : Exec.Deriv) (w : Exec.StorageWrite),
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv G) m →
        Exec.Deriv.successfulSstore? m = some w →
        Sevm.selector G.sevm ∈ [0x095ea7b3, 0x39509351, 0xa457c2d7] → G.sevm.caller ≠ pair := by
  let full := (prior.step block).append later
  let mid := (MidHistoryTraceIn.tail block cut).append later
  have contexts : ∀ A ∈ full.settledFrames, A.sevm.currentTarget = P →
      UsdcContextCode A.sevm.code ∧ ∀ N : Exec.Deriv,
        Exec.Deriv.ParentPrefix (Exec.Frame.rootDeriv A) N →
        A.sevm.code = Impl.code → N.devm.getCode usdcLib = Lib.code := by
    intro A member target
    rw [full.settledFrames_eq] at member
    obtain ⟨R, root, inRoot⟩ := List.mem_flatMap.mp member
    have ready := rootReady R root
    have world := Usdc.ConfiguredHistoryTraceIn.settledRoot_retained_proxyWorld_from_installations
      full BodyStageCapabilities.historical (fun h => h.bal_none)
      root ready.1 impls lib ready.2 governance (installations R root) (apartSlot R root)
    have entryRetained : Exec.Frame.rootDeriv A ∈ Exec.retainedNodes R.run :=
      (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run _).mpr
        ⟨A, inRoot, .refl _⟩
    have family : UsdcContextCode A.sevm.code := by
      rcases (world _ entryRetained).2 target with ⟨code, _⟩ | ⟨e, he, code, _⟩
      · exact .inl code
      · change A.sevm.code = e.code at code
        rw [code]
        exact (impls e he).context
    refine ⟨family, ?_⟩
    intro N chain code
    have retained : N ∈ Exec.retainedNodes R.run :=
      (Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run N).mpr ⟨A, inRoot, chain⟩
    have env : N.sevm = A.sevm := Exec.Deriv.ParentPrefix.sevm_eq chain
    have nodeTarget : N.sevm.currentTarget = P := by rw [env]; exact target
    have nodeCode : N.sevm.code = Impl.code := by rw [env]; exact code
    rcases (world N retained).2 nodeTarget with ⟨proxy, _⟩ | ⟨e, he, image, library⟩
    · exact (proxy_ne_impl (proxy.symm.trans nodeCode)).elim
    · exact library (image.symm.trans nodeCode)
  have subset := MidHistoryTraceIn.settledFrames_subset_full prior block cut later
  apply retained_caller_write_excluded_of_contexts full apart
    (fun A member => contexts A (subset member))
    (fun _ _ _ split => mid.settledFrames_parentIn split)
    (mid.settledRoots_caller_ne_of_senderQueries excluded notSystem) subset
  intro A member target mutable G child childMutable
  exact (UniswapV2Pair.pair_mid_history_children_shapeHist mid installed initial fresh
    A member target mutable G child childMutable).2.2

end Blanc.Composition.UniswapV2PairUsdcCallers
