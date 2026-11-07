import Blanc.Lift.Usdc.EntryChainSettled
import Blanc.Lift.Usdc.ProxyRetainedContextCodes

/-!
# From the scan of `Upgraded` logs to the certification at settled frames

`certifiedSettled_of_scan`: `CertifiedSettled` follows from what a reader scans and reads over the retained
logs. The implementation word starts on a listed version and every retained `Upgraded` log names one, whose code
(and, for V2_2, the library) is in place at the entry of the root that logs it. Reverted upgrades are in no retained
log, and they are in no conclusion either.

Listed, not proved, here: that certified codes write apart from the implementation slot (`KnownImplSlotApart`, which
`knownImplSlotApart_of_actualKeys` obtains from the finite key populations). This module is one root, reading the named
version at its entry; `VersionStands.lean` carries that through the history, and the deletion exclusion with it.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {T : Adr}

/-- The library's entry, beside the listed versions. -/
def libEntry : UsdcDeployedEntry := ⟨usdcLib, Lib.code, default, []⟩

/-- The word names a listed version. -/
def NamedVersion (Vs : List UsdcDeployedEntry) (w : B256) : Prop := ∃ e ∈ Vs, w.toAdr = e.adr

/-- What a scan of one root's logs establishes: each `Upgraded` log at `T` in it names a listed version, whose code
(and the library's, under V2_2) stands at the root's entry. -/
def ScanRoot (T : Adr) (Vs : List UsdcDeployedEntry) (R : Exec.Frame) : Prop :=
  ∀ entry ∈ R.post.logs, UpgradedTargetSatisfies T
    (fun a => ∃ e ∈ Vs, a = e.adr ∧ e.RuntimeReady R.pre) entry

/-- The word names a listed version that stands, with the library under V2_2. -/
def NamedReady (T : Adr) (Vs : List UsdcDeployedEntry) (w : State) : Prop :=
  ∃ e ∈ Vs, ((w.getStor T).get implSlot).toAdr = e.adr ∧ w.getCode e.adr = e.code ∧
    (e.code = Impl.code → w.getCode usdcLib = Lib.code)

/-- The list of versions: their codes, apart from the library, and no precompile on any fork. -/
structure VersionList (Vs : List UsdcDeployedEntry) : Prop where
  codes : ∀ e ∈ Vs, CurveCoins.UsdcVersion e.code
  apart : ∀ e ∈ Vs, e.adr ≠ usdcLib
  notPrecompile : ∀ e ∈ Vs, ∀ f : Fork, ¬ (Fork.ruleSet f).isPrecomp e.adr

theorem version_implCode {C : ByteArray} (h : CurveCoins.UsdcVersion C) : UsdcImplCode C := by
  rcases h with rfl | rfl | rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr (.inl rfl)))

theorem scan_inW {Vs : List UsdcDeployedEntry} (list : VersionList Vs) :
    ∀ e ∈ libEntry :: Vs, UsdcImplCode e.code := fun e he => by
  rcases List.mem_cons.mp he with rfl | he
  · exact .inr (.inr (.inr (.inr rfl)))
  · exact version_implCode (list.codes e he)

section Root

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F) (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)

include capabilities bal

/-- A retained proxy write of the word names a listed version, ready at the root's entry and at the node. -/
theorem scan_upgrade {Vs : List UsdcDeployedEntry} (list : VersionList Vs) {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (scan : ScanRoot T Vs R)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) (target : N.sevm.currentTarget = T)
    (code : N.sevm.code = Proxy.code) {write : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? N = some write) (key : write.key = implSlot) :
    ∃ e ∈ Vs, write.value.toAdr = e.adr ∧ e.RuntimeReady R.pre ∧ e.RuntimeReady N.devm := by
  have owner : write.owner = T := (successfulSstore?_node_owner found).2.trans target
  obtain ⟨e, inVs, address, ready⟩ := ConfiguredHistoryTraceIn.retained_implSstore_target_of_logs
    history capabilities bal member _ scan retained found owner key code
  have family := (version_implCode (list.codes e inVs)).context
  have raw := (Exec.retainedNodes_sublist_rawNodes R.run).subset retained
  refine ⟨e, inVs, address, ready, Exec.rawNodes_getCode R.run ready.1 family.ne_nil N raw, fun impl => ?_⟩
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  exact Exec.rawNodes_getCode R.run (ready.2 impl) libFamily.ne_nil N raw

/-- The retained induction at a root, on the listed versions and the library. -/
theorem scan_world {Vs : List UsdcDeployedEntry} (list : VersionList Vs) {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (proxy : R.pre.getCode T = Proxy.code)
    (live : NamedReady T Vs R.pre.state)
    (scan : ScanRoot T Vs R) (apart : KnownImplSlotApart T (Exec.retainedNodes R.run)) :
    ∀ N ∈ Exec.retainedNodes R.run,
      (∃ e ∈ libEntry :: Vs, ((N.devm.getStor T).get implSlot).toAdr = e.adr ∧ e.RuntimeReady N.devm) ∧
      (N.sevm.currentTarget = T →
        (N.sevm.code = Proxy.code ∧ (RootOwnEntry (Exec.Frame.rootDeriv R) → N.sevm.codeAddress = some T)) ∨
          ∃ e ∈ libEntry :: Vs, N.sevm.code = e.code ∧
            (e.code = Impl.code → N.devm.getCode usdcLib = Lib.code)) := by
  obtain ⟨e₀, he₀, word₀, ready₀⟩ := live
  exact ConfiguredHistoryTraceIn.retained_proxyWorld_context_from_installations
    (W := libEntry :: Vs) history capabilities bal (R := Exec.Frame.rootDeriv R)
    (history.mem_rawFrames_of_mem_settledRoots R member) R.committed
    (ConfiguredHistoryTraceIn.settledRoots_rootOwnCode history R member) proxy (scan_inW list)
    (fun _ _ _ => ⟨libEntry, List.mem_cons_self, rfl, rfl⟩)
    ⟨e₀, List.mem_cons_of_mem _ he₀, word₀, ready₀⟩
    (fun N retained target code _ write found key => by
      obtain ⟨e, he, address, -, ready⟩ := scan_upgrade history capabilities bal list member scan
        retained target code found key
      exact ⟨e, List.mem_cons_of_mem _ he, address, ready⟩)
    (fun N retained target e he code write found =>
      apart N retained target (code ▸ scan_inW list e he) write found)

/-- A retained write of the word names a listed version, ready at the root's entry. -/
theorem scan_write {Vs : List UsdcDeployedEntry} (list : VersionList Vs) {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (proxy : R.pre.getCode T = Proxy.code)
    (live : NamedReady T Vs R.pre.state)
    (scan : ScanRoot T Vs R) (apart : KnownImplSlotApart T (Exec.retainedNodes R.run))
    {m : Exec.Deriv} (retained : m ∈ Exec.retainedNodes R.run) {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) (owner : w.owner = T) (key : w.key = implSlot) :
    ∃ e ∈ Vs, w.value.toAdr = e.adr ∧ e.RuntimeReady R.pre := by
  have target : m.sevm.currentTarget = T := (successfulSstore?_node_owner found).2.symm.trans owner
  rcases (scan_world history capabilities bal list member proxy live scan apart m retained).2 target with
    ⟨code, -⟩ | ⟨e, he, code, -⟩
  · obtain ⟨e, he, address, ready, -⟩ := scan_upgrade history capabilities bal list member scan
      retained target code found key
    exact ⟨e, he, address, ready⟩
  · exact (apart m retained target (code ▸ scan_inW list e he) w found key).elim

/-- **Inside a root**: from a listed word at its entry and the scan of its logs, the word names a ready version
at every retained node. -/
theorem scan_nodes {Vs : List UsdcDeployedEntry} (list : VersionList Vs) {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (proxy : R.pre.getCode T = Proxy.code)
    (live : NamedReady T Vs R.pre.state)
    (scan : ScanRoot T Vs R) (apart : KnownImplSlotApart T (Exec.retainedNodes R.run)) :
    ∀ N ∈ Exec.retainedNodes R.run,
      ∃ e ∈ Vs, ((N.devm.getStor T).get implSlot).toAdr = e.adr ∧ e.RuntimeReady N.devm := by
  have hsg := (history.rawFrame_entryFacts capabilities _
    (history.mem_rawFrames_of_mem_settledRoots R member)).2.2.1
  have nonempty : (R.pre.getCode T).toList ≠ [] := by rw [proxy]; exact proxy_toList_ne_nil
  intro N retained
  obtain ⟨before, after, split⟩ := List.append_of_mem retained
  have named' : NamedVersion Vs ((N.devm.getStor T).get implSlot) := by
    rcases Exec.retainedNodes_cellProv_noStateGas R.run R.committed implSlot hsg nonempty split with
      same | ⟨b₁, b₂, m, w, hb, found, owner, key, value⟩
    · rw [same]
      obtain ⟨e, he, word, -⟩ := live
      exact ⟨e, he, word⟩
    · have retainedM : m ∈ Exec.retainedNodes R.run := by
        rw [split, hb]
        simp only [List.mem_append, List.mem_cons, true_or, or_true]
      rw [← value]
      obtain ⟨e, he, word, -⟩ :=
        scan_write history capabilities bal list member proxy live scan apart retainedM found owner key
      exact ⟨e, he, word⟩
  obtain ⟨e', he', word'⟩ := named'
  obtain ⟨e, he, word, ready⟩ :=
    (scan_world history capabilities bal list member proxy live scan apart N retained).1
  rcases List.mem_cons.mp he with rfl | he
  · exact (list.apart e' he' (word'.symm.trans word)).elim
  · exact ⟨e, he, word, ready⟩

/-- **Inside a root**: the settled proxy frames are certified. -/
theorem scan_frames {Vs : List UsdcDeployedEntry} (list : VersionList Vs) {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (proxy : R.pre.getCode T = Proxy.code)
    (live : NamedReady T Vs R.pre.state)
    (scan : ScanRoot T Vs R) (apart : KnownImplSlotApart T (Exec.retainedNodes R.run)) :
    ∀ G ∈ Exec.committedFrames R.run, UsdcCertified G.pre T := by
  intro G frame
  obtain ⟨e, he, word, ready⟩ := scan_nodes history capabilities bal list member proxy live scan apart
    (Exec.Frame.rootDeriv G)
    ((Exec.mem_retainedNodes_iff_committedFrame_parentPrefix R.run _).mpr ⟨G, frame, .refl _⟩)
  have code : G.pre.getCode (G.pre.getStorVal T implSlot).toAdr = e.code := by
    change G.pre.getCode ((G.pre.getStor T).get implSlot).toAdr = _
    rw [show ((G.pre.getStor T).get implSlot).toAdr = e.adr from word]
    exact ready.1
  refine ⟨by unfold CurveCoins.UsdcImplAt; rw [code]; exact list.codes e he,
    fun impl => ready.2 (code.symm.trans impl), fun f => ?_⟩
  change ¬ (Fork.ruleSet f).isPrecomp ((G.pre.getStor T).get implSlot).toAdr
  rw [show ((G.pre.getStor T).get implSlot).toAdr = e.adr from word]
  exact list.notPrecompile e he f

/-- The word at a root's exit names a listed version that stood at its entry. -/
theorem scan_post {Vs : List UsdcDeployedEntry} (list : VersionList Vs) {R : Exec.Frame}
    (member : R ∈ history.settledRoots) (proxy : R.pre.getCode T = Proxy.code)
    (live : NamedReady T Vs R.pre.state)
    (scan : ScanRoot T Vs R) (apart : KnownImplSlotApart T (Exec.retainedNodes R.run)) :
    ∃ e ∈ Vs, ((R.post.getStor T).get implSlot).toAdr = e.adr ∧ e.RuntimeReady R.pre := by
  have hsg := (history.rawFrame_entryFacts capabilities _
    (history.mem_rawFrames_of_mem_settledRoots R member)).2.2.1
  have nonempty : (R.pre.getCode T).toList ≠ [] := by rw [proxy]; exact proxy_toList_ne_nil
  by_cases same : (R.pre.getStor T).get implSlot = (R.post.getStor T).get implSlot
  · rw [← same]
    exact live
  obtain ⟨write, retained, owner, key, value, last⟩ :=
    Exec.exists_lastRetainedSstore_of_getStor_ne_noStateGas R.run R.committed hsg nonempty same
  have found : Exec.Deriv.successfulSstore? write.occurrence.node = some write.storageWrite := by
    obtain ⟨before, after, split, _⟩ := last
    have present : write.storageWrite ∈ Exec.retainedStorageWrites R.run := by
      rw [split]
      simp only [List.mem_append, List.mem_cons, true_or, or_true]
    rw [Exec.retainedStorageWrites, List.mem_filterMap] at present
    obtain ⟨node, _, found⟩ := present
    have sameNode := (successfulSstore?_node_owner found).1
    change write.occurrence.node = node at sameNode
    rw [sameNode]
    exact found
  have result := scan_write history capabilities bal list member proxy live scan apart retained found owner key
  rw [show (R.post.getStor T).get implSlot = write.storageWrite.value from value.symm]
  exact result

end Root

end Blanc.Lift.Usdc
