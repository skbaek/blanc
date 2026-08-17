import Blanc.LidoCircuitBreakerAccess

/-!
Gate-owned controls for the Stage 5 access and temporal-authority family.

Each control below *uses* a landed public result — at concrete data where the
statement admits it, and otherwise by composing two of them into a consequence
neither states alone.  Nothing here restates a production header.

Two recorded precision limits are respected verbatim rather than papered over:

* the temporal views (`isPauserLive`, `heartbeatExpiry`, `heartbeatInterval`)
  each carry a warm accessed-storage-key premise, so every control that
  exercises one carries it too and claims nothing about a cold slot;
* the settled-error restoration results bind their deployment-identity
  hypotheses as unused placeholders, so the control that exercises them is
  worded as the contract-neutral message rollback it actually is.
-/

namespace Blanc.LidoCircuitBreaker.AccessControls

open Jaune

set_option maxHeartbeats 800000
set_option maxRecDepth 16384

/-! ## AT4 structural classifier controls

The three literal PC lists are the exact compiled effect domains of the runtime
under any deployment parameters. -/

def structuralSstorePcs : List Nat :=
  [413, 1333, 1745, 2287, 2374, 2474, 2517, 2555, 2650, 2827,
   2870, 2910, 2952, 2992, 3212, 3302, 3441, 3586, 3912, 4032]

def transientStorePcs : List Nat := [853, 3985, 4105]

def externalCallPcs : List Nat := [3679, 3707]

/-- The structural inventory with its third row moved one byte forward.  This is
the relabelling a reviewer must be able to reject. -/
def relabelledSstorePcs : List Nat :=
  [413, 1333, 1746, 2287, 2374, 2474, 2517, 2555, 2650, 2827,
   2870, 2910, 2952, 2992, 3212, 3302, 3441, 3586, 3912, 4032]

/-- Exactly twenty structural runtime SSTORE sites, at exactly these compiled
PCs, with no repetition, and the typed row list is the same finite domain rather
than a separate list of matching size.  The last conjunct is the consequence
that makes the cardinality match load-bearing: no row is dangling, every one of
the twenty resolves to an actual compiled site. -/
theorem twenty_site_inventory_control (dp : DeployParams) :
    RuntimePersistentWrite.all.length = 20 ∧
      (runtimePersistentSourceSites dp).length = 20 ∧
      (runtimePersistentSourceSites dp).map (fun site => site.pc) =
        structuralSstorePcs ∧
      (runtimePersistentSourceSites dp).Nodup ∧
      RuntimePersistentWrite.all.map
          (RuntimePersistentWrite.sourceSite? dp) =
        (runtimePersistentSourceSites dp).map some ∧
      ∀ row : RuntimePersistentWrite,
        ∃ site, row.sourceSite? dp = some site := by
  refine ⟨RuntimePersistentWrite.all_length,
    runtimePersistentSourceSites_length dp,
    runtimePersistentSourceSites_pcs dp,
    runtimePersistentSourceSites_nodup dp,
    RuntimePersistentWrite.sourceSites_exact dp, ?_⟩
  intro row
  have bound : row.index < (runtimePersistentSourceSites dp).length := by
    rw [runtimePersistentSourceSites_length]
    exact row.index_lt
  exact ⟨(runtimePersistentSourceSites dp)[row.index],
    List.getElem?_eq_getElem bound⟩

/-- A relabelled row does not survive: the compiled PC inventory is pinned
exactly, source ownership is unique at row identity rather than at the numeric
index, and classifying a row's own path and PC returns that row and no other.

The frozen semantic label order is pinned separately, and the two orders really
do differ, so aligning labels to the compiler's structural traversal is not a
no-op that a relabelling could hide behind. -/
theorem site_row_relabel_rejected (dp : DeployParams) :
    (runtimePersistentSourceSites dp).map (fun site => site.pc) ≠
        relabelledSstorePcs ∧
      (∀ (left right : RuntimePersistentWrite) (site : Prog.SourceSite),
        left.sourceSite? dp = some site →
          right.sourceSite? dp = some site → left = right) ∧
      (∀ (row : RuntimePersistentWrite) (site : Prog.SourceSite),
        row.sourceSite? dp = some site →
          classifyRuntimePersistentWrite dp site.path site.pc = some row) ∧
      RuntimePersistentWrite.inventoryOrder.map
          RuntimePersistentWrite.inventoryEntry = persistentWriteInventory ∧
      RuntimePersistentWrite.inventoryOrder ≠ RuntimePersistentWrite.all := by
  refine ⟨?_, fun _ _ _ hleft hright =>
      RuntimePersistentWrite.sourceSite?_injective hleft hright,
    fun _ _ found => classifyRuntimePersistentWrite_complete found,
    RuntimePersistentWrite.inventory_exact, by decide⟩
  rw [runtimePersistentSourceSites_pcs]
  decide

/-- The three structural effect domains are pinned by exact PC, are pairwise
disjoint as PC sets, and a persistent site is a member of neither of the other
two domains — both non-memberships, not just the transient one. -/
theorem three_domain_separation_control (dp : DeployParams) :
    (runtimePersistentSourceSites dp).map (fun site => site.pc) =
        structuralSstorePcs ∧
      (runtimeTransientSourceSites dp).map (fun site => site.pc) =
        transientStorePcs ∧
      (runtimeExternalCallSourceSites dp).map (fun site => site.pc) =
        externalCallPcs ∧
      (∀ pc ∈ structuralSstorePcs,
        pc ∉ transientStorePcs ∧ pc ∉ externalCallPcs) ∧
      (∀ pc ∈ transientStorePcs, pc ∉ externalCallPcs) ∧
      (∀ site ∈ runtimePersistentSourceSites dp,
        site ∉ runtimeTransientSourceSites dp ∧
          site ∉ runtimeExternalCallSourceSites dp) :=
  ⟨runtimePersistentSourceSites_pcs dp,
   runtimeTransientSourceSites_pcs dp,
   runtimeExternalCallSourceSites_pcs dp,
   by decide,
   by decide,
   fun _ member => runtimePersistent_effectDomains_separate member⟩

/-- The constructor owns a 2/0/0 effect domain that cannot be confused with the
runtime's 20/3/2 source map, and its typed inventories have the matching
cardinalities. -/
theorem constructor_domain_separate_control :
    constructorProgramSiteCounts = (2, 0, 0) ∧
      constructorPersistentWriteInventory.length = 2 ∧
      constructorTransientWriteInventory.length = 0 ∧
      constructorExternalCallInventory.length = 0 ∧
      constructorProgramSiteCounts ≠ (2, 1, 0) ∧
      constructorProgramSiteCounts ≠
        ((runtimePersistentSourceSites officialParams).length,
         (runtimeTransientSourceSites officialParams).length,
         (runtimeExternalCallSourceSites officialParams).length) := by
  have counts : constructorProgramSiteCounts = (2, 0, 0) :=
    constructor_program_site_counts_exact
  have cardinalities := constructor_inventory_cardinalities
  refine ⟨counts, cardinalities.1, cardinalities.2.1, cardinalities.2.2, ?_, ?_⟩
  · rw [counts]
    decide
  · rw [counts, runtimePersistentSourceSites_length,
      runtimeTransientSourceSites_length, runtimeExternalCallSourceSites_length]
    decide

/-! ## AT3 checked-extension controls -/

/-- Concrete witnesses for the checked heartbeat extension.  A positive interval
lands strictly past the current timestamp, so liveness holds; a zero interval
still satisfies the checked-addition specification but lands exactly on the
timestamp, where liveness is false.  The positivity premise of
`CheckedHeartbeatExtension.strict_of_interval_pos` is therefore load-bearing and
not removable. -/
theorem checked_extension_strict_control :
    CheckedHeartbeatExtension 1000 3600 4600 ∧
      IsPauserLiveAt 1000 4600 ∧
      CheckedHeartbeatExtension 1000 0 1000 ∧
      ¬ IsPauserLiveAt 1000 1000 ∧
      (1000 : B256) + 3600 = 4600 := by
  have extension : CheckedHeartbeatExtension 1000 3600 4600 :=
    ⟨by decide, by decide⟩
  exact ⟨extension,
    CheckedHeartbeatExtension.strict_of_interval_pos extension (by decide),
    ⟨by decide, by decide⟩,
    IsPauserLiveAt.irrefl 1000,
    CheckedHeartbeatExtension.add_eq extension⟩

/-- Both named settled-error restoration results are exercised here, and both
give the same conclusion.  Their deployment-identity hypotheses are unused
placeholders in the sources, so the honest reading is recorded alongside: the
restoration is the contract-neutral message rollback and holds at *every*
account, not only at the exact deployment. -/
theorem settled_error_restores_owner_control
    (dp : DeployParams) {msg : Msg} {slot : Xlot} {post : Devm}
    {ca : Adr} {newInterval : B256}
    (htarget : msg.target = some ca)
    (howner : msg.currentTarget = ca)
    (hcodeAddress : msg.codeAddress = some ca)
    (hcode : msg.code.toList = lidoCircuitBreakerCode dp)
    (hvalue : msg.value = 0)
    (hdata : msg.data = setHeartbeatIntervalCalldata newInterval ∨
      msg.data = heartbeatCalldata)
    (hprocess : ProcessMessage msg slot (.ok post))
    (herror : post.error.isSome) :
    (Devm.getStor post ca = msg.benv.state.getStor ca ∧
        post.transientStorage = msg.tenv.transientStorage) ∧
      (∀ other : Adr,
        Devm.getStor post other = msg.benv.state.getStor other) := by
  refine ⟨?_, fun other =>
    congrArg (fun state : State => state.getStor other)
      (ProcessMessage.rollback_of_error hprocess herror).1⟩
  rcases hdata with hset | hbeat
  · exact setHeartbeatInterval_settled_error_restores_owner dp htarget howner
      hcodeAddress hcode hvalue hset hprocess herror
  · exact heartbeat_settled_error_restores_owner dp htarget howner
      hcodeAddress hcode hvalue hbeat hprocess herror

/-! ## AT2 temporal-view boundary controls

Every control in this section carries the production view's warm
accessed-storage-key premise.  None of them says anything about a cold slot. -/

/-- A pauser whose expiry was just produced by a checked extension with a
positive interval reads live from the deployed dispatcher: the public
`isPauserLive(address)` run returns one, and the returned word decodes back to
one.  This composes the AT3 transition kernel with the AT2 public view; neither
source states it. -/
theorem expiry_boundary_strict_control
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser interval expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "isPauserLive" [.address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (extension : CheckedHeartbeatExtension sevm.benvStat.time interval expiry)
    (positive : 0 < interval.toNat) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + isPauserLiveDispatchGas + temporalLiveBodyGasWarm⟩)
        (runtime dp) post ∧
      Devm.output post = (1 : B256).toBytes ∧
      Bytes.toB256 (Devm.output post) = 1 ∧
      IsPauserLiveAt sevm.benvStat.time expiry ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  have live : IsPauserLiveAt sevm.benvStat.time expiry :=
    CheckedHeartbeatExtension.strict_of_interval_pos extension positive
  rcases isPauserLive_runCompiled_of_live dp sevm base pauser expiry G
      hdata hvalue hselector hcodeAddress hcode hword hpauser hexpiry hwarm
      live with ⟨post, hrun, houtput, hworld, hlogs, hcompile⟩
  refine ⟨post, hrun, houtput, ?_, live, hworld, hlogs, hcompile⟩
  rw [houtput, B256.toB256_toBytes]

/-- The inclusive reading of the boundary is refuted by the deployed program
itself.  At `storedExpiry = timestamp` the public `isPauserLive(address)` run
returns zero, which is not the word it returns when liveness holds, so a mutant
predicate admitting equality would disagree with the compiled dispatcher. -/
theorem expiry_boundary_inclusive_rejected
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "isPauserLive" [.address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = sevm.benvStat.time)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ¬ IsPauserLiveAt sevm.benvStat.time sevm.benvStat.time ∧
      pauserLiveWord sevm.benvStat.time sevm.benvStat.time = 0 ∧
      ∃ post,
        Prog.RunCompiled sevm
          (base.setMach ⟨[], Mem.empty,
            G + isPauserLiveDispatchGas + temporalLiveBodyGasWarm⟩)
          (runtime dp) post ∧
        Devm.output post = (0 : B256).toBytes ∧
        Devm.output post ≠ (1 : B256).toBytes ∧
        Devm.WorldEq base post ∧
        post.logs = base.logs ∧
        some sevm.code.toList = Prog.compile (runtime dp) := by
  have separated : (0 : B256).toBytes ≠ (1 : B256).toBytes := by
    intro collision
    have decoded := congrArg Bytes.toB256 collision
    rw [B256.toB256_toBytes, B256.toB256_toBytes] at decoded
    exact absurd decoded (by decide)
  rcases isPauserLive_runCompiled_at_expiry dp sevm base pauser G
      hdata hvalue hselector hcodeAddress hcode hword hpauser hexpiry hwarm with
    ⟨post, hrun, houtput, hworld, hlogs, hcompile⟩
  exact ⟨IsPauserLiveAt.irrefl sevm.benvStat.time,
    pauserLiveWord_eq_zero_at_expiry sevm.benvStat.time,
    post, hrun, houtput, houtput ▸ separated, hworld, hlogs, hcompile⟩

/-- The canonical `heartbeatExpiry(address)` view is a pure read of the exact
expiry key: its output decodes back to the stored word, the world is unchanged,
and no log is emitted.  The expiry key it reads is not the configuration key
read by the interval view. -/
theorem canonical_expiry_view_control
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (pauser expiry : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm =
      selector "heartbeatExpiry" [.address])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hword : Sevm.dataWord sevm 4 = pauser)
    (hpauser : canonicalAddress pauser)
    (hexpiry : Devm.getStorVal base sevm.currentTarget
      (expirySlot pauser) = expiry)
    (hwarm : (⟨sevm.currentTarget, expirySlot pauser⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatExpiryDispatchGas + heartbeatExpiryBodyGasWarm⟩)
        (runtime dp) post ∧
      Bytes.toB256 (Devm.output post) =
        Devm.getStorVal base sevm.currentTarget (expirySlot pauser) ∧
      expirySlot pauser ≠ heartbeatIntervalSlot ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeatExpiry_runCompiled dp sevm base pauser expiry G
      hdata hvalue hselector hcodeAddress hcode hword hpauser hexpiry hwarm with
    ⟨post, hrun, houtput, hworld, hlogs, hcompile⟩
  refine ⟨post, hrun, ?_,
    expirySlot_ne_heartbeatIntervalSlot pauser hpauser, hworld, hlogs, hcompile⟩
  rw [houtput, B256.toB256_toBytes, hexpiry]

/-- The canonical `heartbeatInterval()` view is a pure read of the single
configuration key: its output decodes back to the stored word, the world is
unchanged, and no log is emitted.  Its calldata is the bare four-byte selector,
which is why no address argument appears. -/
theorem heartbeat_interval_view_control
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (interval : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 = 4)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "heartbeatInterval" [])
    (hcodeAddress : sevm.codeAddress = some sevm.currentTarget)
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hinterval : Devm.getStorVal base sevm.currentTarget
      heartbeatIntervalSlot = interval)
    (hwarm : (⟨sevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys) :
    ∃ post,
      Prog.RunCompiled sevm
        (base.setMach ⟨[], Mem.empty,
          G + heartbeatIntervalDispatchGas + heartbeatIntervalBodyGasWarm⟩)
        (runtime dp) post ∧
      Bytes.toB256 (Devm.output post) =
        Devm.getStorVal base sevm.currentTarget heartbeatIntervalSlot ∧
      Devm.WorldEq base post ∧
      post.logs = base.logs ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  rcases heartbeatInterval_runCompiled dp sevm base interval G
      hdata hvalue hselector hcodeAddress hcode hinterval hwarm with
    ⟨post, hrun, houtput, hworld, hlogs, hcompile⟩
  refine ⟨post, hrun, ?_, hworld, hlogs, hcompile⟩
  rw [houtput, B256.toB256_toBytes, hinterval]

end Blanc.LidoCircuitBreaker.AccessControls
