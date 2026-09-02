import Blanc.LidoCircuitBreakerAccess
import Blanc.LidoCircuitBreakerRetainedAuthority
import Blanc.LidoCircuitBreakerAttainment
import Blanc.LidoCircuitBreakerPauseJoin
import Blanc.LidoCircuitBreakerPauseSettlement
import Blanc.LidoCircuitBreakerPreControl
import Blanc.LidoCircuitBreakerCallBoundary
import Blanc.LidoCircuitBreakerObservation
import Blanc.LidoCircuitBreakerSuccess

/-!
Gate-owned controls for the Stage 5 access and temporal-authority family.

Each control below *uses* a landed public result — at concrete data where the
statement admits it, and otherwise by composing two of them into a consequence
neither states alone.  Nothing here restates a production header.

Three recorded precision limits are respected verbatim rather than papered
over:

* the temporal views (`isPauserLive`, `heartbeatExpiry`, `heartbeatInterval`)
  each carry a warm accessed-storage-key premise, so every control that
  exercises one carries it too and claims nothing about a cold slot;
* the settled-error restoration results bind their deployment-identity
  hypotheses as unused placeholders, so the control that exercises them is
  worded as the contract-neutral message rollback it actually is;
* the authority payload's guard occurrence is existential over its
  instruction kind, so the guard-chronology control exhibits an actually
  executed guard without claiming it is the authorization comparison.
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

/-! ## AT5 raw-authority controls

The concrete world below is the production direct-`pause` control: an actual
reverting execution of the exact deployed runtime.  Its root does not commit,
which is precisely the region the arbitrary-outcome raw theorems exist for. -/

/-- The AT5 raw-authority altitude carries no success or commitment premise,
and that absence is load-bearing: the production direct-`pause` control is an
actual reverting execution — `Execution.commits` is false and the committed
frame list is empty — in which a runtime SSTORE nevertheless carries its exact
source row and one of that row's permitted authority roles.  Giving the
raw-occurrence theorem a commitment premise (the labelled AT5 header mutation)
would empty this instance. -/
theorem raw_occurrence_commitment_premise_rejected :
    ∃ (sevm : Sevm) (pre raw : Devm)
      (rootExec : Exec 0 sevm pre (.error (.revert, raw)))
      (write : Exec.SuccessfulSstoreOccurrence
        (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv))
      (row : RuntimePersistentWrite) (site : Prog.SourceSite)
      (role : InvocationRole),
      Execution.commits (.error (.revert, raw)) ≠ true ∧
      Exec.committedFrames rootExec = [] ∧
      Exec.rawFrameRoots rootExec =
        [(⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv)] ∧
      row ∈ RuntimePersistentWrite.all ∧
      row.sourceSite? officialParams = some site ∧
      site.pc = write.occurrence.node.pc ∧
      site.instruction = .reg .sstore ∧
      role ∈ RuntimePersistentWrite.permittedRoles row ∧
      RuntimeWriteAuthority officialParams
        (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv)
        write.occurrence.node role := by
  obtain ⟨sevm, pre, raw, rootExec, write, row, site, role, notCommitted,
      rawRoots, _owner, rowMem, sourceSite, sitePc, siteInstruction,
      rolePermitted, authority⟩ :=
    exists_runtimeWriteAuthority_of_directPauseControl
  exact ⟨sevm, pre, raw, rootExec, write, row, site, role, notCommitted,
    Exec.committedFrames_eq_nil_of_not_commits rootExec notCommitted,
    rawRoots, rowMem, sourceSite, sitePc, siteInstruction, rolePermitted,
    authority⟩

/-- The sub-derivation order on execution derivations is asymmetric because it
is well-founded. -/
private theorem deriv_lt_asymm {left right : Exec.Deriv}
    (forward : Exec.Deriv.lt left right) : ¬ Exec.Deriv.lt right left :=
  Exec.Deriv.lt.well_founded.asymmetric _ _ forward

/-- The guard payload's chronology is genuinely oriented: at the live
direct-`pause` authority instance, an actually executed guard occurrence sits
strictly before the classified write in the sub-derivation order, and the
reversed placement — the guard occurring after the store — is refuted by
asymmetry of that order.  Authority evidence re-anchored at the write (the
labelled guard mutation) is therefore not satisfiable by this payload.  Per
the recorded precision limit, the guard is existential over its instruction
kind; nothing here claims it is the authorization comparison itself. -/
theorem guard_after_write_rejected :
    ∃ (frameRoot writeNode : Exec.Deriv) (instruction : Ninst)
      (guard : RuntimeGuardOccurrence frameRoot writeNode instruction),
      Exec.Deriv.ParentPrefix frameRoot guard.guard ∧
      Exec.Deriv.ParentPrefix guard.guard writeNode ∧
      Ninst.At guard.guard.sevm.code guard.guard.pc instruction ∧
      Exec.Deriv.lt writeNode guard.guard ∧
      ¬ Exec.Deriv.lt guard.guard writeNode := by
  obtain ⟨sevm, pre, raw, rootExec, write, _row, _site, _role, _notCommitted,
      _rawRoots, _owner, _rowMem, _sourceSite, _sitePc, _siteInstruction,
      _rolePermitted, authority⟩ :=
    exists_runtimeWriteAuthority_of_directPauseControl
  have package : ∀ {instruction : Ninst}
      (guard : RuntimeGuardOccurrence
        (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv)
        write.occurrence.node instruction),
      ∃ (frameRoot writeNode : Exec.Deriv) (instr : Ninst)
        (g : RuntimeGuardOccurrence frameRoot writeNode instr),
        Exec.Deriv.ParentPrefix frameRoot g.guard ∧
        Exec.Deriv.ParentPrefix g.guard writeNode ∧
        Ninst.At g.guard.sevm.code g.guard.pc instr ∧
        Exec.Deriv.lt writeNode g.guard ∧
        ¬ Exec.Deriv.lt g.guard writeNode :=
    fun guard => ⟨_, _, _, guard, guard.frameToGuard, guard.guardToWrite,
      guard.decoded, guard.strictBefore, deriv_lt_asymm guard.strictBefore⟩
  cases authority with
  | setPauseDuration endpoint guard callerEq => exact package guard
  | setHeartbeatInterval endpoint guard callerEq => exact package guard
  | adminRegistry endpoint guard callerEq writeSite => exact package guard
  | adminExpiry endpoint guard callerEq writeSite => exact package guard
  | heartbeatExpiry endpoint registeredGuard liveGuard registered live =>
      exact package liveGuard
  | pauseRegistry endpoint assignedGuard liveGuard assigned live writeSite =>
      exact package liveGuard
  | pauseExpiry endpoint assignedGuard liveGuard assigned live writeSite =>
      exact package liveGuard

/-! ### Permitted-role tightness at the one asymmetric row

Every Registry-class row but one carries a symmetric role set, permitting both
`adminRegistry` and `pauseRegistry`; every remaining row's set is a singleton.
`afterOld.newCount` is the exception — Registry-class, yet register-only,
because reaching it requires a nonzero new pauser.  It is therefore the single
place where widening the permitted-role table has semantic content rather than
bookkeeping content. -/

/-- The role-widening mutant of the permitted-role table: `afterOld.newCount`
made symmetric with its Registry siblings.  Unlike the structural inventory
above, no expected string rejects this edit — `permittedRoles` is certified as
an upper bound only, so enlarging a row's list falsifies no theorem that reads
it. -/
def widenedPermittedRoles :
    RuntimePersistentWrite → List InvocationRole
  | .afterOldNewCount => [.adminRegistry, .pauseRegistry]
  | row => RuntimePersistentWrite.permittedRoles row

/-- A permitted-role widening at `afterOld.newCount` is rejected on semantic
grounds rather than by a pinned string.

The first four conjuncts are the membership facts that flip: the mutant differs
from the production table at exactly that row, and there exactly by adding
`pauseRegistry`.  On their own they would pin nothing beyond the table's own
text.  The fifth rules out a vacuous separation — among the rows permitting
`adminRegistry` at all, `pauseRegistry` is permitted by every one *except* this
row, so the exclusion is specific to it and not a blanket absence.  The last
two are what give the membership facts teeth: every role the widening adds is
provably unattainable at this row, so no exact runtime execution reaches
`afterOld.newCount`'s frozen source site carrying a pause-registry authority
payload.

Epistemic status, stated plainly because it is the honest core of this control:
what this control certifies is only the negative direction.
`RuntimePersistentWrite.permittedRoles` is an upper bound, and nothing *below*
may be read as claiming the role sets are exact.

That the positive direction — tightness — is unproved was true when this control
was written and is **no longer true in general**.  `Blanc/LidoCircuitBreakerAttainment.lean`
now carries attainment witnesses, and at a row whose `permittedRoles` is a
singleton a witness makes the set exact rather than merely sound.  Five rows are
exact today on that argument: `.afterOldNewCount` at `[.adminRegistry]`,
`.registerFreshExpiry` at `[.adminExpiry]`, `.setPauseDurationConfig`
and `.setHeartbeatIntervalConfig` at `[.adminConfiguration]`, and
`.heartbeatExpiry` at `[.heartbeatExpiry]` — the last three of which state the
exactness themselves, as the `*_role_tightness_control` family below.

Every other row remains an upper bound only.  For a two-role row a single
witness settles one side and says nothing about the other, so the ten registry
rows are not exact no matter how many `.adminRegistry` witnesses land. -/
theorem permitted_role_widening_rejected :
    (∀ row ∈ RuntimePersistentWrite.all, row ≠ .afterOldNewCount →
        widenedPermittedRoles row =
          RuntimePersistentWrite.permittedRoles row) ∧
      InvocationRole.adminRegistry ∈
        RuntimePersistentWrite.permittedRoles .afterOldNewCount ∧
      InvocationRole.pauseRegistry ∉
        RuntimePersistentWrite.permittedRoles .afterOldNewCount ∧
      InvocationRole.pauseRegistry ∈
        widenedPermittedRoles .afterOldNewCount ∧
      (∀ row ∈ RuntimePersistentWrite.all,
        InvocationRole.adminRegistry ∈
            RuntimePersistentWrite.permittedRoles row →
          (InvocationRole.pauseRegistry ∈
              RuntimePersistentWrite.permittedRoles row ↔
            row ≠ .afterOldNewCount)) ∧
      ¬ Attainable officialParams .afterOldNewCount .pauseRegistry ∧
      ∀ role ∈ widenedPermittedRoles .afterOldNewCount,
        role ∉ RuntimePersistentWrite.permittedRoles .afterOldNewCount →
          ¬ Attainable officialParams .afterOldNewCount role := by
  refine ⟨by decide, by decide, by decide, by decide, by decide,
    not_attainable_afterOldNewCount_pauseRegistry, ?_⟩
  intro role member fresh
  have roleEq : role = .pauseRegistry := by
    revert member fresh
    cases role <;> decide
  subst roleEq
  exact not_attainable_afterOldNewCount_pauseRegistry

/-- Within-role guard strength, which no header pin can reach.

`permitted_role_widening_rejected` above catches a role set widened so that it
accepts a role it should not.  It cannot catch the opposite failure: a role kept in place
while the guard *inside* it is weakened, because `RuntimeWriteAuthority`'s
constructor payloads are not part of any pinned theorem header.

This control closes that by *extracting* both pause guards from an arbitrary
actual pause authority.  Weaken the strict entry liveness to `≤`, or drop the
assignment conjunct, and the corresponding extraction below stops elaborating.
The final clause records why `≤` is a genuine weakening and not a restatement:
the inclusive reading admits an entry state — exactly `time = expiry` — that the
strict one rejects, which is the same boundary AT2 fixes for `isPauserLive`. -/
theorem pause_within_role_guard_strength_control :
    (∀ (dp : DeployParams) (frameRoot write : Exec.Deriv),
      RuntimeWriteAuthority dp frameRoot write .pauseRegistry →
        frameRoot.sevm.benvStat.time <
          frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
            (expirySlot frameRoot.sevm.caller.toB256)) ∧
    (∀ (dp : DeployParams) (frameRoot write : Exec.Deriv),
      RuntimeWriteAuthority dp frameRoot write .pauseRegistry →
        frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
          (assignmentSlot (Sevm.dataWord frameRoot.sevm 4)) =
            frameRoot.sevm.caller.toB256) ∧
    (∀ (dp : DeployParams) (frameRoot write : Exec.Deriv),
      RuntimeWriteAuthority dp frameRoot write .pauseExpiry →
        frameRoot.sevm.benvStat.time <
          frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
            (expirySlot frameRoot.sevm.caller.toB256)) ∧
    ∃ time expiry : B256, time ≤ expiry ∧ ¬ time < expiry := by
  refine ⟨?_, ?_, ?_, 0, 0, by decide, by decide⟩
  · intro _dp _frameRoot _write authority
    cases authority with
    | pauseRegistry _ _ _ _ live _ => exact live
  · intro _dp _frameRoot _write authority
    cases authority with
    | pauseRegistry _ _ _ assigned _ _ => exact assigned
  · intro _dp _frameRoot _write authority
    cases authority with
    | pauseExpiry _ _ _ _ live _ => exact live

/-- The shape of `Attainable`, which no header pin can reach either.

`Attainable` is a `def`, and the gate pins normalized *theorem* headers, so a
conjunct quietly dropped from it would leave every `attainable_*` header
byte-identical while making all of them cheaper to prove.  Nothing else catches
that: `permitted_role_widening_rejected` consumes `Attainable` only negatively,
where a weakening makes the refutation harder rather than easier.

This restates the definition deliberately -- that is the whole mechanism.  The
proof is the identity, so it elaborates exactly while `Attainable` still implies
all seven conjuncts, and stops the moment one is removed. -/
theorem attainable_shape_control :
    ∀ (dp : DeployParams) (row : RuntimePersistentWrite)
      (role : InvocationRole),
      Attainable dp row role →
        ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
          (occurrence : Exec.NinstOccurrence globalRoot)
          (site : Prog.SourceSite),
          occurrence.instruction = .reg .sstore ∧
          frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
          frameRoot.exactInvocation (runtime dp) ca ca ∧
          Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
          row.sourceSite? dp = some site ∧
          site.pc = occurrence.node.pc ∧
          RuntimeWriteAuthority dp frameRoot occurrence.node role :=
  fun _ _ _ attainable => attainable

/-- The same within-role extraction for the admin and heartbeat roles.

AT8 asks for *each* admin/heartbeat/pause guard weakening to be rejected.  The
pause control above covers one of the three; this covers the other two.  Both
`.adminConfiguration` arms and both admin Registry/expiry arms must yield the
exact-admin equality, and the heartbeat arm must yield **both** its entry facts —
a nonzero entry count and strict entry liveness — so dropping either, or
relaxing `<` to `≤`, stops this elaborating. -/
theorem admin_heartbeat_within_role_guard_strength_control :
    (∀ (dp : DeployParams) (frameRoot write : Exec.Deriv),
      RuntimeWriteAuthority dp frameRoot write .adminConfiguration →
        frameRoot.sevm.caller.toB256 = dp.admin) ∧
    (∀ (dp : DeployParams) (frameRoot write : Exec.Deriv),
      RuntimeWriteAuthority dp frameRoot write .adminRegistry →
        frameRoot.sevm.caller.toB256 = dp.admin) ∧
    (∀ (dp : DeployParams) (frameRoot write : Exec.Deriv),
      RuntimeWriteAuthority dp frameRoot write .adminExpiry →
        frameRoot.sevm.caller.toB256 = dp.admin) ∧
    (∀ (dp : DeployParams) (frameRoot write : Exec.Deriv),
      RuntimeWriteAuthority dp frameRoot write .heartbeatExpiry →
        frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
            (countSlot frameRoot.sevm.caller.toB256) ≠ 0 ∧
          frameRoot.sevm.benvStat.time <
            frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
              (expirySlot frameRoot.sevm.caller.toB256)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _dp _frameRoot _write authority
    cases authority with
    | setPauseDuration _ _ callerEq _ => exact callerEq
    | setHeartbeatInterval _ _ callerEq _ => exact callerEq
  · intro _dp _frameRoot _write authority
    cases authority with
    | adminRegistry _ _ callerEq _ => exact callerEq
  · intro _dp _frameRoot _write authority
    cases authority with
    | adminExpiry _ _ callerEq _ => exact callerEq
  · intro _dp _frameRoot _write authority
    cases authority with
    | heartbeatExpiry _ _ _ registered live _ => exact ⟨registered, live⟩

/-! ### AT8 executable controls at the `setPauseDuration.config` site

Review finding R9.  Inventory row `0` was classified by AT4 and role-pinned by
AT5 exactly like the other nineteen, yet no control and no witness reached it,
so AT3's demand for "exact admin/site/guard access classification **and
executable controls**" was open at precisely one site.  The two controls below
close it.

Both are compositions rather than restatements.  The first joins the reaching
execution, the frozen site's compiled coordinates and the within-role caller
equality into a single statement no header makes; the second turns the row's
`permittedRoles` entry from an upper bound into an exact one, which is the one
direction `permitted_role_widening_rejected` above deliberately does not
certify.  That exactness is claimed **for this row only**; nothing here says
anything about the Registry-class rows whose sets are not singletons. -/

set_option maxRecDepth 20000 in
/-- The compiled coordinates of inventory row `0`'s own frozen source site:
`PC 413`, source function `0`, and a sixty-four-step path.  The source function
is the AT4 fact that makes the site main-function-resident, which is why no
`.call` restarts its source position; the instruction kind is not repeated
here because `sourceSite?_sound` already supplies it. -/
private theorem setPauseDurationConfig_site_shape :
    ((RuntimePersistentWrite.setPauseDurationConfig).sourceSite?
        officialParams).map
      (fun site =>
        (site.pc, site.path.functionIndex, site.path.steps.length)) =
      some (413, 0, 64) := by
  decide +kernel

/-- One concrete production execution reaches inventory row `0`'s own frozen
source site, and the authority it carries there really did compare the caller
against the immutable admin.

Nothing in the landed headers says this.  `Attainable` supplies the reaching
execution and the raw authority payload but names no compiled coordinate;
`runtimePersistentSourceSites_pcs` pins the twenty PCs but reaches no
execution; and `admin_heartbeat_within_role_guard_strength_control` extracts
the caller equality from an *arbitrary* `.adminConfiguration` authority without
exhibiting one.  Composed, they say that an actual admin `setPauseDuration`
call reaches PC `413` in source function `0` inside an exact same-frame
invocation of the production runtime, carrying an authority whose guard is the
admin comparison. -/
theorem setPauseDurationConfig_admin_site_control :
    ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
      (occurrence : Exec.NinstOccurrence globalRoot) (site : Prog.SourceSite),
      (RuntimePersistentWrite.setPauseDurationConfig).sourceSite?
          officialParams = some site ∧
      site ∈ runtimePersistentSourceSites officialParams ∧
      (site.pc, site.path.functionIndex, site.path.steps.length) =
          (413, 0, 64) ∧
      site.instruction = .reg .sstore ∧
      site.pc = occurrence.node.pc ∧
      occurrence.instruction = .reg .sstore ∧
      frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
      frameRoot.exactInvocation (runtime officialParams) ca ca ∧
      Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
      RuntimeWriteAuthority officialParams frameRoot occurrence.node
        .adminConfiguration ∧
      frameRoot.sevm.caller.toB256 = officialParams.admin := by
  obtain ⟨ca, globalRoot, frameRoot, occurrence, site, instructionEq, rawRoots,
    invocation, sameFrame, found, sitePc, authority⟩ :=
    attainable_setPauseDurationConfig_adminConfiguration
  refine ⟨ca, globalRoot, frameRoot, occurrence, site, found,
    RuntimePersistentWrite.mem_runtimePersistentSourceSites found, ?_,
    (RuntimePersistentWrite.sourceSite?_sound found).2, sitePc,
    instructionEq, rawRoots, invocation, sameFrame, authority,
    admin_heartbeat_within_role_guard_strength_control.1 officialParams
      frameRoot occurrence.node authority⟩
  have shape := setPauseDurationConfig_site_shape
  rw [found] at shape
  exact Option.some.inj shape

/-- At inventory row `0` the permitted-role table is **exact**, not merely a
sound upper bound: its single entry is attained.

This is the positive direction `permitted_role_widening_rejected` above
explicitly leaves open, and it is available here only because the row's set is
a singleton *and* that one role now carries a witness.  Read it at exactly that
width — it is a statement about one row, and it does not upgrade
`RuntimePersistentWrite.permittedRoles` anywhere else. -/
theorem setPauseDurationConfig_role_tightness_control :
    RuntimePersistentWrite.permittedRoles .setPauseDurationConfig =
        [.adminConfiguration] ∧
      ∀ role ∈ RuntimePersistentWrite.permittedRoles .setPauseDurationConfig,
        Attainable officialParams .setPauseDurationConfig role := by
  refine ⟨rfl, ?_⟩
  intro role member
  have roleEq : role = .adminConfiguration := by
    revert member
    cases role <;> decide
  subst roleEq
  exact attainable_setPauseDurationConfig_adminConfiguration

/-! ### AT8 executable controls at the two remaining main-function sites

Inventory rows `1` and `2` — `setHeartbeatInterval`'s configuration `SSTORE`
and the expiry `SSTORE` on `heartbeat`'s success arm — are the other two sites
that live in the compiled main function, and they carry the same pair of
controls as row `0` for the same reason: a reaching execution composed with the
frozen compiled coordinates, and a per-row exactness statement.

Row `2` is the one place a control reaches the `.heartbeatExpiry` role at all.
Its site control extracts **both** entry facts the role carries — a nonzero
entry count and strict entry liveness — from an authority that an actual
execution produced, where
`admin_heartbeat_within_role_guard_strength_control` extracts them from an
arbitrary one.  Read the pair together: the fourth conjunct there says every
`.heartbeatExpiry` authority has those facts, and this says one exists. -/

set_option maxRecDepth 20000 in
/-- The compiled coordinates of inventory row `1`'s own frozen source site:
`PC 1333`, source function `0`, and a sixty-six-step path. -/
private theorem setHeartbeatIntervalConfig_site_shape :
    ((RuntimePersistentWrite.setHeartbeatIntervalConfig).sourceSite?
        officialParams).map
      (fun site =>
        (site.pc, site.path.functionIndex, site.path.steps.length)) =
      some (1333, 0, 66) := by
  decide +kernel

/-- One concrete production execution reaches inventory row `1`'s own frozen
source site, and the authority it carries there really did compare the caller
against the immutable admin. -/
theorem setHeartbeatIntervalConfig_admin_site_control :
    ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
      (occurrence : Exec.NinstOccurrence globalRoot) (site : Prog.SourceSite),
      (RuntimePersistentWrite.setHeartbeatIntervalConfig).sourceSite?
          officialParams = some site ∧
      site ∈ runtimePersistentSourceSites officialParams ∧
      (site.pc, site.path.functionIndex, site.path.steps.length) =
          (1333, 0, 66) ∧
      site.instruction = .reg .sstore ∧
      site.pc = occurrence.node.pc ∧
      occurrence.instruction = .reg .sstore ∧
      frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
      frameRoot.exactInvocation (runtime officialParams) ca ca ∧
      Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
      RuntimeWriteAuthority officialParams frameRoot occurrence.node
        .adminConfiguration ∧
      frameRoot.sevm.caller.toB256 = officialParams.admin := by
  obtain ⟨ca, globalRoot, frameRoot, occurrence, site, instructionEq, rawRoots,
    invocation, sameFrame, found, sitePc, authority⟩ :=
    attainable_setHeartbeatIntervalConfig_adminConfiguration
  refine ⟨ca, globalRoot, frameRoot, occurrence, site, found,
    RuntimePersistentWrite.mem_runtimePersistentSourceSites found, ?_,
    (RuntimePersistentWrite.sourceSite?_sound found).2, sitePc,
    instructionEq, rawRoots, invocation, sameFrame, authority,
    admin_heartbeat_within_role_guard_strength_control.1 officialParams
      frameRoot occurrence.node authority⟩
  have shape := setHeartbeatIntervalConfig_site_shape
  rw [found] at shape
  exact Option.some.inj shape

/-- At inventory row `1` the permitted-role table is **exact**, not merely a
sound upper bound: its single entry is attained.  Read it at exactly that
width — it is a statement about one row. -/
theorem setHeartbeatIntervalConfig_role_tightness_control :
    RuntimePersistentWrite.permittedRoles .setHeartbeatIntervalConfig =
        [.adminConfiguration] ∧
      ∀ role ∈
        RuntimePersistentWrite.permittedRoles .setHeartbeatIntervalConfig,
        Attainable officialParams .setHeartbeatIntervalConfig role := by
  refine ⟨rfl, ?_⟩
  intro role member
  have roleEq : role = .adminConfiguration := by
    revert member
    cases role <;> decide
  subst roleEq
  exact attainable_setHeartbeatIntervalConfig_adminConfiguration

set_option maxRecDepth 20000 in
/-- The compiled coordinates of inventory row `2`'s own frozen source site:
`PC 1745`, source function `0`, and a sixty-five-step path. -/
private theorem heartbeatExpiry_site_shape :
    ((RuntimePersistentWrite.heartbeatExpiry).sourceSite?
        officialParams).map
      (fun site =>
        (site.pc, site.path.functionIndex, site.path.steps.length)) =
      some (1745, 0, 65) := by
  decide +kernel

/-- One concrete production execution reaches inventory row `2`'s own frozen
source site, and the authority it carries there really was a registered caller
that was strictly live at frame entry.

This is the positive half of the heartbeat guard obligation.  The negative
half — that *every* `.heartbeatExpiry` authority carries those two facts — is
`admin_heartbeat_within_role_guard_strength_control`'s fourth conjunct, which
is vacuous on its own until something exhibits an authority of that role.  This
exhibits one. -/
theorem heartbeatExpiry_live_site_control :
    ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
      (occurrence : Exec.NinstOccurrence globalRoot) (site : Prog.SourceSite),
      (RuntimePersistentWrite.heartbeatExpiry).sourceSite?
          officialParams = some site ∧
      site ∈ runtimePersistentSourceSites officialParams ∧
      (site.pc, site.path.functionIndex, site.path.steps.length) =
          (1745, 0, 65) ∧
      site.instruction = .reg .sstore ∧
      site.pc = occurrence.node.pc ∧
      occurrence.instruction = .reg .sstore ∧
      frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
      frameRoot.exactInvocation (runtime officialParams) ca ca ∧
      Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
      RuntimeWriteAuthority officialParams frameRoot occurrence.node
        .heartbeatExpiry ∧
      frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
          (countSlot frameRoot.sevm.caller.toB256) ≠ 0 ∧
      frameRoot.sevm.benvStat.time <
        frameRoot.devm.getStorVal frameRoot.sevm.currentTarget
          (expirySlot frameRoot.sevm.caller.toB256) := by
  obtain ⟨ca, globalRoot, frameRoot, occurrence, site, instructionEq, rawRoots,
    invocation, sameFrame, found, sitePc, authority⟩ :=
    attainable_heartbeatExpiry_heartbeatExpiry
  obtain ⟨registered, live⟩ :=
    admin_heartbeat_within_role_guard_strength_control.2.2.2 officialParams
      frameRoot occurrence.node authority
  refine ⟨ca, globalRoot, frameRoot, occurrence, site, found,
    RuntimePersistentWrite.mem_runtimePersistentSourceSites found, ?_,
    (RuntimePersistentWrite.sourceSite?_sound found).2, sitePc,
    instructionEq, rawRoots, invocation, sameFrame, authority, registered,
    live⟩
  have shape := heartbeatExpiry_site_shape
  rw [found] at shape
  exact Option.some.inj shape

/-- At inventory row `2` the permitted-role table is **exact**, not merely a
sound upper bound: its single entry is attained.  Read it at exactly that
width — it is a statement about one row, and in particular it says nothing
separating `.heartbeatExpiry` from `.adminConfiguration`, the two roles whose
`writeSite` pins agree. -/
theorem heartbeatExpiry_role_tightness_control :
    RuntimePersistentWrite.permittedRoles .heartbeatExpiry =
        [.heartbeatExpiry] ∧
      ∀ role ∈ RuntimePersistentWrite.permittedRoles .heartbeatExpiry,
        Attainable officialParams .heartbeatExpiry role := by
  refine ⟨rfl, ?_⟩
  intro role member
  have roleEq : role = .heartbeatExpiry := by
    revert member
    cases role <;> decide
  subst roleEq
  exact attainable_heartbeatExpiry_heartbeatExpiry

/-! ## AT6 owner-closure and settlement controls -/

/-- The raw/retained separation at one concrete noncommitting execution: the
reverting direct-`pause` run still contains an actual successful owner SSTORE
occurrence in its raw chronology, yet it retains no owner write, has no
committed frame, and admits no retained owner-cell authority witness at any
key or value.  Together with the raw-authority control above, both sides of
the separation are exercised on the same world: raw authority survives
noncommitment, retained authority does not. -/
theorem noncommitting_root_has_no_authority_control :
    ∃ (sevm : Sevm) (pre raw : Devm)
      (rootExec : Exec 0 sevm pre (.error (.revert, raw))),
      Execution.commits (.error (.revert, raw)) ≠ true ∧
      (∃ write : Exec.SuccessfulSstoreOccurrence
          (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
        write.storageOwner = Nat.toAdr 100) ∧
      (¬ ∃ write : Exec.SuccessfulSstoreOccurrence
          (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ : Exec.Deriv),
        write.Retained ∧ write.storageOwner = Nat.toAdr 100) ∧
      ∀ key final : B256,
        ¬ Exec.RuntimeOwnerCellAuthority officialParams (Nat.toAdr 100)
          rootExec key final := by
  obtain ⟨sevm, pre, raw, rootExec, write, _row, _site, _role, notCommitted,
      _rawRoots, owner, _rowMem, _sourceSite, _sitePc, _siteInstruction,
      _rolePermitted, _authority⟩ :=
    exists_runtimeWriteAuthority_of_directPauseControl
  exact ⟨sevm, pre, raw, rootExec, notCommitted, ⟨write, owner⟩,
    Exec.no_retainedOwnerSstore_of_not_commits rootExec notCommitted,
    fun key final =>
      Exec.no_runtimeOwnerCellAuthority_of_not_commits rootExec notCommitted
        key final⟩

/-! ### A synthetic committed double-write world

No production flow writes one storage key twice in a committed run, so the
last-retained/first-writer distinction needs a hand-built execution: three
instructions (`SSTORE`, `SSTORE`, `STOP`) over a preloaded stack write the
values `1` and then `2` to the same key of the same account, and the run
commits.  The two `Rinst.run` step equations below are closed by steering the
accessed-storage-set decisions and the storage reads with named lemmas; the
machine states are explicit literals, so every later fact about them is a
small projection. -/

private def twoWriteCode : ByteArray := ByteArray.mk #[0x55, 0x55, 0x00]

private def twoWriteSevm : Sevm :=
  { (default : Sevm) with code := twoWriteCode }

private def twoWritePre : Devm :=
  ((default : Devm).withGasLeft 100000).withStack [0, 1, 0, 2]

private def twoWriteAcctMid : Acct :=
  { nonce := 0, bal := 0, stor := Stor.empty.set 0 1,
    code := ByteArray.mk #[] }

private def twoWriteAcctEnd : Acct :=
  { nonce := 0, bal := 0, stor := (Stor.empty.set 0 1).set 0 2,
    code := ByteArray.mk #[] }

private def twoWriteMid : Devm :=
  { mach :=
      { stack := [0, 2]
        memory := { data := #[], size := 0 }
        gasLeft := 77900 }
    «meta» :=
      { logs := []
        refundCounter := 0
        output := []
        accountsToDelete := Std.HashSet.emptyWithCapacity
        returnData := []
        error := none
        accessedAddresses := Std.HashSet.emptyWithCapacity
        accessedStorageKeys := Std.HashSet.emptyWithCapacity.insert (0, 0)
        createdAccounts := Std.HashSet.emptyWithCapacity }
    world :=
      { state := State.set Std.TreeMap.empty 0 twoWriteAcctMid
        transientStorage := ∅ } }

private def twoWriteEnd : Devm :=
  { mach :=
      { stack := []
        memory := { data := #[], size := 0 }
        gasLeft := 77800 }
    «meta» :=
      { logs := []
        refundCounter := 0
        output := []
        accountsToDelete := Std.HashSet.emptyWithCapacity
        returnData := []
        error := none
        accessedAddresses := Std.HashSet.emptyWithCapacity
        accessedStorageKeys := Std.HashSet.emptyWithCapacity.insert (0, 0)
        createdAccounts := Std.HashSet.emptyWithCapacity }
    world :=
      { state := State.set (State.set Std.TreeMap.empty 0 twoWriteAcctMid) 0
          twoWriteAcctEnd
        transientStorage := ∅ } }

private theorem state_get_empty {a : Adr} :
    State.get Std.TreeMap.empty a = Acct.nil := by
  simp [State.get]

private theorem acctNil_nonce : Acct.nil.nonce = 0 := rfl
private theorem acctNil_bal : Acct.nil.bal = 0 := rfl
private theorem acctNil_stor : Acct.nil.stor = Stor.empty := rfl
private theorem acctNil_code : Acct.nil.code = ByteArray.mk #[] := rfl

private theorem stor_get_empty {k : B256} : Stor.get Stor.empty k = 0 := by
  simp [Stor.get, Stor.empty]

private theorem b256_zero_eq_one_false : ((0 : B256) = 1) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

private theorem b256_one_eq_zero_false : ((1 : B256) = 0) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

private theorem b256_two_eq_zero_false : ((2 : B256) = 0) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

private theorem b256_zero_eq_two_false : ((0 : B256) = 2) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

private theorem b256_one_eq_two_false : ((1 : B256) = 2) = False := by
  simp only [eq_iff_iff, iff_false]
  decide

/-- One normalization pass for the double-write machine: unfold the `SSTORE`
step, steer the accessed-storage-set and storage-read decisions, and fold the
result back into the named literal states. -/
macro "tw_norm" : tactic => `(tactic|
  simp +decide only [twoWriteMid, twoWriteEnd, twoWriteAcctMid,
    twoWriteAcctEnd,
    Rinst.run, Rinst.runCore, Devm.pop_def, chargeGas_def,
    Bind.bind, Except.bind, Except.assert, assertDynamic,
    getOrigStorVal, getOrigAcct, Devm.getStorVal, Devm.getAcct,
    sstoreNewRefundCounter, safeSub,
    twoWriteSevm, twoWritePre, twoWriteCode, default,
    Devm.withGasLeft, Devm.withStack, Devm.setMach, Devm.setMeta,
    Devm.setWorld, Devm.stack, Devm.gasLeft, Devm.state,
    Devm.accessedStorageKeys, Devm.refundCounter,
    addAccessedStorageKey, liftMachMetaPure, Meta.addAccessedStorageKey,
    Devm.withRefundCounter, Devm.setStorVal, State.setStorVal,
    Devm.withState, Devm.mach, Devm.meta, Devm.world, Devm.error,
    state_get_empty, acctNil_nonce, acctNil_bal, acctNil_stor, acctNil_code,
    stor_get_empty, State.get_set_self, Stor.get_set_self,
    b256_zero_eq_one_false, b256_one_eq_zero_false, b256_two_eq_zero_false,
    b256_zero_eq_two_false, b256_one_eq_two_false,
    eq_self_iff_true, and_true, true_and, and_false, false_and,
    not_true, not_false_iff, not_false_eq_true, ne_eq,
    Std.HashSet.not_mem_emptyWithCapacity, Std.HashSet.mem_insert,
    ite_true, ite_false, if_true, if_false,
    Nat.reduceAdd, Nat.reduceSub,
    gCallStipend, gasColdSload, gasStorageSet, gasWarmAccess,
    gasStorageUpdate, rSClear])

private theorem twoWriteStep0 :
    Rinst.run ⟨0, twoWriteSevm, twoWritePre⟩ .sstore = .ok twoWriteMid := by
  tw_norm
  rfl

private theorem twoWriteStep1 :
    Rinst.run ⟨1, twoWriteSevm, twoWriteMid⟩ .sstore = .ok twoWriteEnd := by
  tw_norm

private theorem twoWriteEvmStep0 :
    Evm.step ⟨0, twoWriteSevm, twoWritePre⟩ = .cont 1 twoWriteMid := by
  rw [Evm.step_next (show Ninst.At twoWriteSevm.code 0 (.reg .sstore) by rfl)]
  simp only [Ninst.step, twoWriteStep0, Step.ofExecution, Ninst.size]

private theorem twoWriteEvmStep1 :
    Evm.step ⟨1, twoWriteSevm, twoWriteMid⟩ = .cont 2 twoWriteEnd := by
  rw [Evm.step_next (show Ninst.At twoWriteSevm.code 1 (.reg .sstore) by rfl)]
  simp only [Ninst.step, twoWriteStep1, Step.ofExecution, Ninst.size]

private theorem twoWriteEvmStep2 :
    Evm.step ⟨2, twoWriteSevm, twoWriteEnd⟩ = .halt (.ok twoWriteEnd) := by
  rw [Evm.step_last (show Linst.At twoWriteSevm.code 2 .stop by rfl)]
  rfl

private def twoWriteRun : Exec 0 twoWriteSevm twoWritePre (.ok twoWriteEnd) :=
  .cont twoWriteEvmStep0 (.cont twoWriteEvmStep1 (.halt twoWriteEvmStep2))

private def twoWriteRoot : Exec.Deriv :=
  ⟨0, twoWriteSevm, twoWritePre, .ok twoWriteEnd, twoWriteRun⟩

private def twoWriteNodeMid : Exec.Deriv :=
  ⟨1, twoWriteSevm, twoWriteMid, .ok twoWriteEnd,
    .cont twoWriteEvmStep1 (.halt twoWriteEvmStep2)⟩

private theorem twoWriteCommits :
    Execution.commits (.ok twoWriteEnd) = true := rfl

private theorem twoWritePre_cell :
    (Devm.getStor twoWritePre twoWriteSevm.currentTarget).get 0 = 0 := by
  simp only [Devm.getStor, Devm.getAcct, twoWritePre, twoWriteSevm, default,
    Devm.withGasLeft, Devm.withStack, Devm.setMach, Devm.state,
    state_get_empty, acctNil_stor, stor_get_empty]

private theorem twoWriteEnd_cell :
    (Devm.getStor twoWriteEnd twoWriteSevm.currentTarget).get 0 = 2 := by
  simp only [Devm.getStor, Devm.getAcct]
  tw_norm

private theorem twoWriteGetInst0 :
    Evm.getInst ⟨0, twoWriteSevm, twoWritePre⟩ =
      some (.next (.reg .sstore)) := rfl

private theorem twoWriteGetInst1 :
    Evm.getInst ⟨1, twoWriteSevm, twoWriteMid⟩ =
      some (.next (.reg .sstore)) := rfl

private theorem twoWritePre_stack : twoWritePre.stack = [0, 1, 0, 2] := rfl

private theorem twoWriteMid_stack : twoWriteMid.stack = [0, 2] := rfl

/-- The exact retained chronology of the double-write run: two successful
SSTORE events to the same owner and key, first value `1`, then value `2`. -/
private theorem twoWriteWrites :
    Exec.retainedStorageWrites twoWriteRun =
      [{ node := twoWriteRoot, owner := twoWriteSevm.currentTarget,
         key := 0, value := 1 },
       { node := twoWriteNodeMid, owner := twoWriteSevm.currentTarget,
         key := 0, value := 2 }] := by
  simp only [Exec.retainedStorageWrites, Exec.retainedNodes, twoWriteCommits,
    twoWriteRun, Exec.retainedNodesOfCommits, twoWriteRoot, twoWriteNodeMid,
    List.filterMap, Exec.Deriv.successfulSstore?, twoWriteGetInst0,
    twoWriteGetInst1, twoWritePre_stack, twoWriteMid_stack, dite_true]

/-- The public last-retained selector, instantiated at the double-write run:
the selected writer carries the second value `2`, the surviving word. -/
private theorem twoWrite_lastRetained_exists :
    ∃ write : Exec.SuccessfulSstoreOccurrence twoWriteRoot,
      write.Retained ∧ write.storageOwner = twoWriteSevm.currentTarget ∧
        write.key = 0 ∧ write.value = 2 ∧ write.IsLastRetained := by
  have changed :
      (Devm.getStor twoWritePre twoWriteSevm.currentTarget).get 0 ≠
        (Devm.getStor
          (Execution.committedPost (.ok twoWriteEnd) twoWriteCommits)
          twoWriteSevm.currentTarget).get 0 := by
    rw [show Execution.committedPost (.ok twoWriteEnd) twoWriteCommits =
        twoWriteEnd from rfl, twoWritePre_cell, twoWriteEnd_cell]
    decide
  obtain ⟨write, retained, owner, key, value, last⟩ :=
    Exec.exists_lastRetainedSstore_of_getStor_ne twoWriteRun twoWriteCommits
      changed
  refine ⟨write, retained, owner, key, ?_, last⟩
  rw [value, show Execution.committedPost (.ok twoWriteEnd) twoWriteCommits =
    twoWriteEnd from rfl, twoWriteEnd_cell]

/-- No last-retained owner/key attribution in the double-write run can carry
the first writer's value: the split demanded by `IsLastRetained` leaves the
first event with a later same-cell write after it. -/
private theorem twoWrite_lastRetained_value
    (write : Exec.SuccessfulSstoreOccurrence twoWriteRoot)
    (owner : write.storageOwner = twoWriteSevm.currentTarget)
    (key : write.key = 0)
    (last : write.IsLastRetained) : write.value = 2 := by
  obtain ⟨before, after, split, maximal⟩ := last
  rw [show Exec.retainedStorageWrites twoWriteRoot.exc =
      Exec.retainedStorageWrites twoWriteRun from rfl, twoWriteWrites] at split
  cases before with
  | nil =>
      rw [List.nil_append] at split
      simp only [List.cons.injEq] at split
      obtain ⟨-, hafter⟩ := split
      exfalso
      apply maximal
        { node := twoWriteNodeMid, owner := twoWriteSevm.currentTarget,
          key := 0, value := 2 }
      · rw [← hafter]
        exact List.mem_singleton_self _
      · exact ⟨owner.symm, key.symm⟩
  | cons b bs =>
      cases bs with
      | nil =>
          simp only [List.cons_append, List.nil_append,
            List.cons.injEq] at split
          obtain ⟨-, hsw, -⟩ := split
          have projected := congrArg Exec.StorageWrite.value hsw
          simpa [Exec.SuccessfulSstoreOccurrence.storageWrite] using
            projected.symm
      | cons b2 bs2 =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨-, -, h⟩ := split
          simp at h

/-- Attribution is to the last retained writer, never the first: a synthetic
committed run writes `1` and then `2` to one cell of one account.  The
retained chronology records both events in order, the surviving word is the
second value, the production last-retained selector picks a writer carrying
`2`, and every last-retained attribution for that cell must carry `2` — a
first-writer substitution (the labelled owner-closure mutation) would
attribute the surviving word to the superseded store carrying `1`. -/
theorem first_writer_substitution_rejected :
    ∃ (sevm : Sevm) (pre : Devm) (out : Execution)
      (run : Exec 0 sevm pre out)
      (committed : Execution.commits out = true),
      (Devm.getStor pre sevm.currentTarget).get 0 = 0 ∧
      (Devm.getStor (Execution.committedPost out committed)
          sevm.currentTarget).get 0 = 2 ∧
      (Exec.retainedStorageWrites run).map
          (fun event => (event.owner, event.key, event.value)) =
        [(sevm.currentTarget, 0, 1), (sevm.currentTarget, 0, 2)] ∧
      (∃ write : Exec.SuccessfulSstoreOccurrence
          (⟨0, sevm, pre, out, run⟩ : Exec.Deriv),
        write.Retained ∧ write.storageOwner = sevm.currentTarget ∧
          write.key = 0 ∧ write.value = 2 ∧ write.IsLastRetained) ∧
      ∀ write : Exec.SuccessfulSstoreOccurrence
          (⟨0, sevm, pre, out, run⟩ : Exec.Deriv),
        write.storageOwner = sevm.currentTarget → write.key = 0 →
          write.IsLastRetained → write.value = 2 := by
  refine ⟨twoWriteSevm, twoWritePre, .ok twoWriteEnd, twoWriteRun,
    twoWriteCommits, twoWritePre_cell, twoWriteEnd_cell, ?_,
    twoWrite_lastRetained_exists, twoWrite_lastRetained_value⟩
  rw [twoWriteWrites]
  rfl

/-- The concrete direct-`pause` world re-exported as an exact-invocation
witness: the actual reverting root execution of the production Registry
control satisfies `exactInvocation` at the deployed owner for both the
storage identity and the code-address identity, with the exact compiled
runtime bytes. -/
private theorem directPauseExactInvocation :
    ∃ (sevm : Sevm) (pre raw : Devm)
      (rootExec : Exec 0 sevm pre (.error (.revert, raw))),
      (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ :
          Exec.Deriv).exactInvocation
        (runtime officialParams) (Nat.toAdr 100) (Nat.toAdr 100) := by
  obtain ⟨msg, sevm, pre, raw, _htarget, hcurrent, hcodeAddress, hcodeBytes,
      _hvalue, _hdata, sevmEq, _hpre, _hframe, _hwitness, _hcaller,
      _hassignment, _hexpiry, _hlive, _htargetNe, _hcanonical, _hzeroCodeSize,
      _hrun, rootExec, _houtput, _hevidence, _hpost⟩ :=
    directPause_zeroCode_postWrite_error_control
  refine ⟨sevm, pre, raw, rootExec, rfl, ?_, ?_, ?_⟩
  · show sevm.currentTarget = Nat.toAdr 100
    rw [sevmEq]
    exact hcurrent
  · show sevm.codeAddress = some (Nat.toAdr 100)
    rw [sevmEq]
    exact hcodeAddress
  · show some sevm.code.toList = (runtime officialParams).compile
    rw [sevmEq]
    show some msg.code.toList = _
    rw [hcodeBytes, lidoCircuitBreakerCode_compile]

/-- Exact-instance identity requires the storage owner: the concrete
direct-`pause` root inhabits `exactInvocation` at the deployed owner, and the
same root — same entry PC, same code address, same compiled bytes — fails it
for every other nominated storage owner, by nothing more than the
storage-target projection.  This is the semantic content whose deletion the
labelled storage-owner header mutations relabel. -/
theorem storage_owner_identity_required_control :
    ∃ (sevm : Sevm) (pre raw : Devm)
      (rootExec : Exec 0 sevm pre (.error (.revert, raw))),
      (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ :
          Exec.Deriv).exactInvocation
        (runtime officialParams) (Nat.toAdr 100) (Nat.toAdr 100) ∧
      ∀ other : Adr, other ≠ Nat.toAdr 100 →
        ¬ (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ :
            Exec.Deriv).exactInvocation
          (runtime officialParams) other (Nat.toAdr 100) := by
  obtain ⟨sevm, pre, raw, rootExec, invocation⟩ := directPauseExactInvocation
  refine ⟨sevm, pre, raw, rootExec, invocation, ?_⟩
  intro other hne contra
  exact hne (contra.2.1.symm.trans invocation.2.1)

/-- Exact-instance identity requires the code address independently of the
storage owner: the same concrete root, with identical entry PC, storage
target, and compiled bytes, fails `exactInvocation` for every other nominated
code address, by the code-address projection alone.  Equal code bytes do not
substitute for code-address identity. -/
theorem code_address_identity_required_control :
    ∃ (sevm : Sevm) (pre raw : Devm)
      (rootExec : Exec 0 sevm pre (.error (.revert, raw))),
      (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ :
          Exec.Deriv).exactInvocation
        (runtime officialParams) (Nat.toAdr 100) (Nat.toAdr 100) ∧
      ∀ other : Adr, other ≠ Nat.toAdr 100 →
        ¬ (⟨0, sevm, pre, .error (.revert, raw), rootExec⟩ :
            Exec.Deriv).exactInvocation
          (runtime officialParams) (Nat.toAdr 100) other := by
  obtain ⟨sevm, pre, raw, rootExec, invocation⟩ := directPauseExactInvocation
  refine ⟨sevm, pre, raw, rootExec, invocation, ?_⟩
  intro other hne contra
  exact hne (Option.some.inj (contra.2.2.1.symm.trans invocation.2.2.1))

/-- Owner closure is derived, never assumed: from installation-grade evidence
alone — the installed exact runtime and the exact root invocation — the
production bridge produces the committed exact frame of a retained owner
write, and the same write is independently visible to the commitment-free raw
traversal.  Under the labelled owner-closure mutation the committed-frame
invocation would instead be a caller-supplied assumption, and this
composition — which supplies only installation facts — could not be stated.
Neither production result states the conjunction below alone. -/
theorem owner_closure_assumed_premise_rejected
    {dp : DeployParams} {ca : Adr}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true)
    (installed : Prog.At (runtime dp) ca pc sevm pre)
    (rootExact :
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv).exactInvocation
        (runtime dp) ca ca)
    (write : Exec.SuccessfulSstoreOccurrence
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
    (retained : write.Retained)
    (owner : write.storageOwner = ca) :
    ∃ frame ∈ Exec.committedFrames run,
      frame.exactInvocation (runtime dp) ca ca ∧
        Exec.Deriv.ParentPrefix frame.rootDeriv write.occurrence.node ∧
        ∃ rawRoot ∈ Exec.rawFrameRoots run,
          Exec.Deriv.ParentPrefix rawRoot write.occurrence.node := by
  rcases Exec.retainedSstore_runtimeOwnerClosure run committed installed
      rootExact write retained owner with
    ⟨frame, member, invocation, sameFrame⟩
  rcases (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run
      write.occurrence.node).mp write.occurrence.reached with
    ⟨rawRoot, rawMember, rawPrefix⟩
  exact ⟨frame, member, invocation, sameFrame, rawRoot, rawMember, rawPrefix⟩

/-! ### AT8 executable controls at the three replacement-arm expiry sites

Inventory rows `14`, `15` and `16` are `registerAfterSet`'s expiry writes
behind `previousPauser ≠ 0`: the retained arm's write, the retiring pauser's
expiry clear, and the new pauser's write after that clear.  All three are
attained at the two concrete replacement worlds of
`Blanc/LidoCircuitBreakerReplacementWorld.lean`.

They need a site control more than the earlier rows did, for a reason that is
about *names*.  `Func.sourceSites` visits `registerAfterSet`'s fall-through arm
first, so the frozen inventory's constructor labels at indices 14 and 17 are
transposed relative to the sites: `.registerRetainedOldNewExpiry` sits at the
`previousPauser ≠ 0` write and `.registerFreshExpiry` sits at the
fresh registration's.  A reader who takes either label for a description gets
the wrong site.  The control below is the machine-checked answer: each attained
row is identified by its **compiled PC and source function**, not by its label,
so a witness pointed at the wrong site could not typecheck.

Renaming a row is a user decision and the inventory is frozen; nothing here
proposes one.  What this does is make the mismatch harmless. -/

set_option maxRecDepth 20000 in
/-- The compiled coordinates of the three replacement-arm expiry sites: PCs
`3212`, `3302` and `3441`, all in source function `19`, with `31`, `16` and
`46` step paths.  Being behind a `.call` is why the source function is
`registerAfterSet`'s own and not the main function's. -/
private theorem registerReplacementArm_site_shapes :
    ((RuntimePersistentWrite.registerRetainedOldNewExpiry).sourceSite?
          officialParams).map
        (fun site =>
          (site.pc, site.path.functionIndex, site.path.steps.length)) =
        some (3212, 19, 31) ∧
      ((RuntimePersistentWrite.registerLastOldClear).sourceSite?
          officialParams).map
        (fun site =>
          (site.pc, site.path.functionIndex, site.path.steps.length)) =
        some (3302, 19, 16) ∧
      ((RuntimePersistentWrite.registerLastOldNewExpiry).sourceSite?
          officialParams).map
        (fun site =>
          (site.pc, site.path.functionIndex, site.path.steps.length)) =
        some (3441, 19, 46) := by
  decide +kernel

/-- The composition, once, for a row whose coordinates are known and whose
`.adminExpiry` attainment is in hand. -/
private theorem attained_at_shape {row : RuntimePersistentWrite}
    {pc steps : Nat}
    (shape : (row.sourceSite? officialParams).map
        (fun site =>
          (site.pc, site.path.functionIndex, site.path.steps.length)) =
        some (pc, 19, steps))
    (attained : Attainable officialParams row .adminExpiry) :
    ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
      (occurrence : Exec.NinstOccurrence globalRoot) (site : Prog.SourceSite),
      row.sourceSite? officialParams = some site ∧
      site ∈ runtimePersistentSourceSites officialParams ∧
      (site.pc, site.path.functionIndex, site.path.steps.length) =
        (pc, 19, steps) ∧
      site.instruction = .reg .sstore ∧
      site.pc = occurrence.node.pc ∧
      occurrence.instruction = .reg .sstore ∧
      frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
      frameRoot.exactInvocation (runtime officialParams) ca ca ∧
      Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
      RuntimeWriteAuthority officialParams frameRoot occurrence.node
        .adminExpiry := by
  obtain ⟨ca, globalRoot, frameRoot, occurrence, site, instructionEq, rawRoots,
    invocation, sameFrame, found, sitePc, authority⟩ := attained
  refine ⟨ca, globalRoot, frameRoot, occurrence, site, found,
    RuntimePersistentWrite.mem_runtimePersistentSourceSites found, ?_,
    (RuntimePersistentWrite.sourceSite?_sound found).2, sitePc,
    instructionEq, rawRoots, invocation, sameFrame, authority⟩
  rw [found] at shape
  exact Option.some.inj shape

/-- Each of the three replacement-arm expiry rows is reached by a real
production execution **at its own compiled PC**, inside an exact same-frame
invocation of the production runtime, carrying an `.adminExpiry` authority.

Nothing in the landed headers says this.  `Attainable` supplies the execution
and the authority payload but names no compiled coordinate;
`runtimePersistentSourceSites_pcs` pins the twenty PCs but reaches no
execution.  Composed, and quantified over the three (row, PC) pairs at once,
they say which site each witness actually reached. -/
theorem registerReplacementArm_admin_site_control :
    ∀ (row : RuntimePersistentWrite) (pc steps : Nat),
      (row, pc, steps) ∈
          [((RuntimePersistentWrite.registerRetainedOldNewExpiry), 3212, 31),
           ((RuntimePersistentWrite.registerLastOldClear), 3302, 16),
           ((RuntimePersistentWrite.registerLastOldNewExpiry), 3441, 46)] →
      ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
        (occurrence : Exec.NinstOccurrence globalRoot)
        (site : Prog.SourceSite),
        row.sourceSite? officialParams = some site ∧
        site ∈ runtimePersistentSourceSites officialParams ∧
        (site.pc, site.path.functionIndex, site.path.steps.length) =
          (pc, 19, steps) ∧
        site.instruction = .reg .sstore ∧
        site.pc = occurrence.node.pc ∧
        occurrence.instruction = .reg .sstore ∧
        frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
        frameRoot.exactInvocation (runtime officialParams) ca ca ∧
        Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
        RuntimeWriteAuthority officialParams frameRoot occurrence.node
          .adminExpiry := by
  intro row pc steps member
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact attained_at_shape registerReplacementArm_site_shapes.1
      attainable_registerRetainedOldNewExpiry_adminExpiry
  · exact attained_at_shape registerReplacementArm_site_shapes.2.1
      attainable_registerLastOldClear_adminExpiry
  · exact attained_at_shape registerReplacementArm_site_shapes.2.2
      attainable_registerLastOldNewExpiry_adminExpiry

/-- At all three rows the permitted-role table is **exact**, not merely a sound
upper bound: each row's single entry is attained.

Read it at exactly that width, as with the row-`0` control above: it is a
statement about these three rows, and it does not upgrade
`RuntimePersistentWrite.permittedRoles` anywhere else. -/
theorem registerReplacementArm_role_tightness_control :
    ∀ row ∈ [(RuntimePersistentWrite.registerRetainedOldNewExpiry),
             (RuntimePersistentWrite.registerLastOldClear),
             (RuntimePersistentWrite.registerLastOldNewExpiry)],
      RuntimePersistentWrite.permittedRoles row = [.adminExpiry] ∧
        ∀ role ∈ RuntimePersistentWrite.permittedRoles row,
          Attainable officialParams row role := by
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨rfl, fun role roleMember => ?_⟩
    have roleEq : role = .adminExpiry := by revert roleMember; cases role <;> decide
    subst roleEq
    exact attainable_registerRetainedOldNewExpiry_adminExpiry
  · refine ⟨rfl, fun role roleMember => ?_⟩
    have roleEq : role = .adminExpiry := by revert roleMember; cases role <;> decide
    subst roleEq
    exact attainable_registerLastOldClear_adminExpiry
  · refine ⟨rfl, fun role roleMember => ?_⟩
    have roleEq : role = .adminExpiry := by revert roleMember; cases role <;> decide
    subst roleEq
    exact attainable_registerLastOldNewExpiry_adminExpiry

/-! ## The pause joins' value law

`pauseLastWorld_join` and `pauseRetainedWorld_join` each conclude with a
`PauseExpiryValue` conjunct.  `PauseExpiryValue` is a `def`, so — exactly as
with `Attainable` above — a clause dropped from it would leave both join
headers byte-identical while making both *cheaper* to prove, and no header pin
in this gate would see anything. -/

/-- The pause joins' value law, extracted from an **arbitrary** join rather
than from the landed proof.

Each of the first two clauses takes a join's own existential body at one
witness world — the `pauseSuccess` boundary walk, the reached expiry `SSTORE`,
and the value law at that world's post-callback count — and reads the concrete
stored word back out *through* `PauseExpiryValue`'s own laws, never by
re-deriving it from the suffix walk: row 19's count-zero arm stores `0`
(`PauseExpiryValue.eq_zero_iff`, on the count-zero disjunct), and row 18's
checked arm stores `pauseWorldTime + pauseWorldInterval = 2592010`, which is
nonzero (`PauseExpiryValue.eq_zero_iff_count_eq_zero`, at this world, where
the block time is `10` and so the degenerate zero-sum case is excluded).
Weaken either clause of `PauseExpiryValue` and the corresponding extraction
stops elaborating — while both joins, whose conclusions name only the `def`,
stay provable against the weaker target and keep byte-identical headers.  That
asymmetry is the point: a header pin cannot see this, and this can.

NON-VACUITY.  First, structurally: the two closing existentials *are* the
landed joins, so neither implication is true-because-unsatisfiable, and the
two extracted words are different — `0` against `2592010` — so neither clause
restates the other and the `value ≠ 0` conjunct is not carried vacuously by
the zero arm.

Second, VERIFIED by mutation: six single-edit rewrites of this control were
each run through `lake env lean` on a throwaway copy and each was rejected —
(1) replacing row 19's value-law premise by `True`; (2) changing row 19's
extracted word to `1`; (3) changing row 18's extracted word to `0`;
(4) changing row 19's count argument from `0` to `1`; (5) changing row 18's
count argument from `1` to `0`, which `decide` refutes outright; and
(6) reading row 18's law at `pauseWorldDuration` instead of the configured
`pauseWorldInterval`.  So the world, the count and the extracted word are all
load-bearing here, and none of them is recoverable from the boundary walk or
the `PauseExpiryWrite` occurrence alone.

Recorded limit, and the reason this control is worth its cost:
`PauseExpiryValue.eq_zero_iff` is what ties the `def` down, and it is not a
pinned header of this gate, so the `def` and that law could in principle be
weakened *together* while `pauseSuccess_expiryWrite_stores_zero_iff` — whose
statement is about the concrete `if`, not about `PauseExpiryValue` — keeps its
pinned header and is re-proved directly.  Both join headers would survive that
byte-identical.  This control is what does not. -/
theorem pause_join_expiry_value_control :
    (∀ (mid : Devm) (out : Execution) (value : B256),
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseLastSevm mid pauseSuccess out →
      PauseExpiryWrite pauseLastSevm mid configWorldOwner value →
      PauseExpiryValue pauseLastSevm.benvStat.time pauseWorldInterval 0
        value →
        value = 0 ∧
          PauseExpiryWrite pauseLastSevm mid configWorldOwner 0) ∧
    (∀ (mid : Devm) (out : Execution) (value : B256),
      Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        pauseRetainedSevm mid pauseSuccess out →
      PauseExpiryWrite pauseRetainedSevm mid configWorldOwner value →
      PauseExpiryValue pauseRetainedSevm.benvStat.time pauseWorldInterval 1
        value →
        value = pauseWorldTime + pauseWorldInterval ∧ value ≠ 0 ∧
          PauseExpiryWrite pauseRetainedSevm mid configWorldOwner
            (pauseWorldTime + pauseWorldInterval)) ∧
    (pauseWorldTime + pauseWorldInterval : B256) = 2592010 ∧
    (2592010 : B256) ≠ 0 ∧
    (∃ (mid : Devm) (out : Execution) (value : B256),
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          pauseLastSevm mid pauseSuccess out ∧
        PauseExpiryWrite pauseLastSevm mid configWorldOwner value ∧
        PauseExpiryValue pauseLastSevm.benvStat.time pauseWorldInterval 0
          value) ∧
    (∃ (mid : Devm) (out : Execution) (value : B256),
      Func.RunCompiledTo
          ((runtime officialParams).main :: (runtime officialParams).aux)
          pauseRetainedSevm mid pauseSuccess out ∧
        PauseExpiryWrite pauseRetainedSevm mid configWorldOwner value ∧
        PauseExpiryValue pauseRetainedSevm.benvStat.time pauseWorldInterval 1
          value) := by
  refine ⟨?_, ?_, by decide, by decide, ?_, ?_⟩
  · intro _mid _out value _boundary write law
    have zero : value = 0 := law.eq_zero_iff.mpr (Or.inl rfl)
    exact ⟨zero, zero ▸ write⟩
  · intro _mid _out value _boundary write law
    have nondegenerate :
        ¬ (pauseRetainedSevm.benvStat.time = 0 ∧ pauseWorldInterval = 0) := by
      rintro ⟨time, -⟩
      exact absurd (time ▸ pauseWorld_time pauseRetainedWorldStor
        pauseRetainedWorldGas) (by decide)
    have nonzero : value ≠ 0 := fun hzero =>
      absurd ((law.eq_zero_iff_count_eq_zero nondegenerate).mp hzero)
        (by decide)
    have extension := law.2 (by decide)
    have sum : pauseRetainedSevm.benvStat.time + pauseWorldInterval = value :=
      extension.add_eq
    rw [show pauseRetainedSevm.benvStat.time = pauseWorldTime from
      pauseWorld_time _ _] at sum
    exact ⟨sum.symm, nonzero, sum ▸ write⟩
  · obtain ⟨mid, out, value, boundary, write, law, -⟩ := pauseLastWorld_join
    exact ⟨mid, out, value, boundary, write, law⟩
  · obtain ⟨mid, out, value, boundary, write, law, -⟩ :=
      pauseRetainedWorld_join
    exact ⟨mid, out, value, boundary, write, law⟩

/-! ## What the settled message leaves behind

`pauseLastWorld_settles` and `pauseRetainedWorld_settles` are the family's
first message-altitude statements, and their entire lift over the raw run is
the `ProcessMessage` conjunct.  `ProcessMessage` is a `def` unfolding to
`RunFrame (Frame.ofCall msg)`, and `RunFrame` is a `def` too, so gutting
either in `Blanc/Semantics.lean` -- `ProcessMessage _ _ _ := True` is the
one-line version -- would leave all five pinned headers of
`Blanc/LidoCircuitBreakerPauseSettlement.lean` byte-identical while making
both settlements trivially provable and empty. -/

/-- What a settled pause message leaves behind, read back out of the landed
settlements rather than out of the run.

The first clause is `RunFrame`'s whole content at the call frame, universally
quantified: once a message's frame is entered, its result is *the settle of
the raw execution* and not something the error path invented.  Gut `RunFrame`
or `ProcessMessage` to anything trivially true and this clause stops being
derivable at all, while both settlement headers -- which name only the `def`
-- stay byte-identical and stay provable against the gutted target.  That
asymmetry is the point, and it is the same blind spot
`pause_join_expiry_value_control` covers for `PauseExpiryValue`.

The last two clauses consume the two landed settlements at concrete data and
extract each world's own surviving expiry word *through* its `ProcessMessage`,
so neither survives that conjunct being dropped from a settlement: row 19
retires the pauser and leaves `0`, row 18 retains it and leaves
`pauseWorldInterval + pauseWorldTime = 2592010`, which is nonzero.  The two
words are different, so neither clause restates the other and the `≠ 0`
conjunct is not carried vacuously by the zero arm.

NON-VACUITY.  First, structurally: the two closing existentials *are* the
landed settlements, so the second and third clauses are witnessed rather than
true-because-unsatisfiable, and the first clause's premise is inhabited at
exactly those two worlds.

Second, VERIFIED by mutation: seven single-edit rewrites of this control were
each run through `lake env lean` on a throwaway copy carrying this control and
its import, and each was rejected --
(1) dropping the `ProcessMessage` premise from the first clause, which leaves
the result unconstrained (`introN` failure);
(2) taking that clause's settle at `Frame.ofCreate msg` instead of
`Frame.ofCall msg` (type mismatch);
(3) changing row 19's extracted expiry word from `0` to `1`;
(4) replacing row 19's message world `pauseWorldMsg pauseLastWorldStor
pauseLastWorldGas` by row 18's;
(5) changing row 18's extracted expiry word from `2592010` to `0`;
(6) replacing row 18's execution world `⟨0, pauseRetainedSevm,
pauseRetainedPre⟩` by row 19's;
(7) restating the closing arithmetic as `2592011`, which `decide` refutes
outright.
So the frame, the message world, the execution world and both extracted words
are all load-bearing here.

Recorded limit, and the reason this control is worth its cost: a gutted
`RunFrame` would also break `RunFrame.some_inv` and much of the library above
it, so `RunFrame` alone is not where a silent weakening could hide.
`ProcessMessage` is: it is the thin specialization the settlements name, it
has no other consumer in this family, and emptying *it* leaves every pinned
header in this gate byte-identical.  This control is what does not survive
that. -/
theorem pause_settlement_message_content_control :
    (∀ (msg : Msg) (evm : Evm) (raw : Execution)
        (result : Except (EvmError × State × AdrSet × Tra) Devm),
      (Frame.ofCall msg).enter = .run evm →
      ProcessMessage msg (.some ⟨evm, raw⟩) result →
        result = (Frame.ofCall msg).settle raw) ∧
    (∃ post : Devm,
      ProcessMessage (pauseWorldMsg pauseLastWorldStor pauseLastWorldGas)
          (.some ⟨⟨0, pauseLastSevm, pauseLastPre⟩, (.ok post : Execution)⟩)
          (.ok post) ∧
        post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) = 0) ∧
    (∃ post : Devm,
      ProcessMessage
          (pauseWorldMsg pauseRetainedWorldStor pauseRetainedWorldGas)
          (.some ⟨⟨0, pauseRetainedSevm, pauseRetainedPre⟩,
            (.ok post : Execution)⟩) (.ok post) ∧
        post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) =
          2592010 ∧
        post.getStorVal configWorldOwner (expirySlot pauseWorldPauser) ≠ 0) ∧
    (pauseWorldInterval + pauseWorldTime : B256) = 2592010 ∧
    (2592010 : B256) ≠ 0 := by
  refine ⟨?_, ?_, ?_, by decide, by decide⟩
  · intro _msg evm raw result henter hrun
    unfold ProcessMessage RunFrame at hrun
    rw [henter] at hrun
    obtain ⟨raw', hxl, hr⟩ := hrun
    cases hxl
    exact hr
  · obtain ⟨post, _hexec, hmsg, _herr, _hout, _hgas, _hlock, hexp, -⟩ :=
      pauseLastWorld_settles
    exact ⟨post, hmsg, hexp⟩
  · obtain ⟨post, _hexec, hmsg, _herr, _hout, _hgas, _hlock, hexp, -⟩ :=
      pauseRetainedWorld_settles
    have value : post.getStorVal configWorldOwner
        (expirySlot pauseWorldPauser) = 2592010 := hexp.trans (by decide)
    exact ⟨post, hmsg, value, by rw [value]; decide⟩

/-! ## Pre-control: what is settled before the target gets control

The pre-control family is the program's first claim quantified over arbitrary
target bytecode, so the control it needs is the one no callee-pinning
weakening could supply. -/

/-- The pre-control results at an ARBITRARY target bytecode, joined into the
consequence none of them states alone: at the instant the target receives
control the paused target's assignment cell is `0` and the reentrancy lock is
held, and a `pause` re-entered from that very state takes the lock guard's
refusal arm and reverts with `ReentrantCall`'s own payload.

`code` is universally quantified, and `hcode` is the only thing this control
says about the code at `target` — which the first conjunct then carries
across the span, so the arbitrary code is still the one installed when the
target receives control.  A weakening that pinned the callee — an
added hypothesis naming the target's bytecode, or one satisfiable only in a
world where the target answers the pausable interface — could not discharge
this control, because there is nothing here to discharge it with.

The re-entrant frame is taken at `callPre` itself, the state the target is
looking at the moment it receives control, rather than at a later
reconstruction of it. -/
theorem pre_control_arbitrary_target_code_control
    (dp : DeployParams) (sevm sevm' : Sevm)
    (entry guardPost branchPost callPre : Devm) (xs : List B256)
    (target reentrantTarget : B256) (code : ByteArray) (G : Nat)
    (hcode : CodeAt entry target.toAdr code)
    (hguard : Line.Run sevm entry pauseCodeGuard guardPost)
    (hbranch : Devm.PopBurn xs guardPost branchPost)
    (hstaging : Line.Run sevm branchPost pauseCallStaging callPre)
    (hassignment : entry.getStorVal sevm.currentTarget
      (assignmentSlot target) = 0)
    (hlock : entry.getTransVal sevm.currentTarget lockKey = 1)
    (hframe : sevm'.currentTarget = sevm.currentTarget)
    (hdataLength : sevm'.data.length = 36)
    (hmask : addressMask &&& reentrantTarget = 0)
    (hdataTarget : Sevm.dataWord sevm' 4 = reentrantTarget) :
    CodeAt callPre target.toAdr code ∧
      callPre.getStorVal sevm.currentTarget (assignmentSlot target) = 0 ∧
      callPre.getTransVal sevm.currentTarget lockKey = 1 ∧
      ∃ post,
        Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm'
          (callPre.setMach ⟨[], Mem.empty, G + pauseReentrantGas⟩)
          pause (.error (.revert, post)) ∧
        post.output = customErrorData "ReentrantCall" := by
  obtain ⟨hassign', hlock'⟩ :=
    pauseCallEntry_assignment_and_lock hguard hbranch hstaging hassignment
      hlock
  refine ⟨CodeAt.acrossLine pauseCallStaging_codeInv hstaging
      (CodeAt.ofState hbranch.state
        (CodeAt.acrossLine pauseCodeGuard_codeInv hguard hcode)),
    hassign', hlock', ?_⟩
  obtain ⟨post, hrun, hout, _, _, _⟩ :=
    pause_body_runCompiledTo_error_of_locked dp sevm' callPre reentrantTarget G
      hdataLength hmask hdataTarget (by rw [hframe, hlock']; decide)
  exact ⟨post, hrun, hout⟩

/-! ## Call-boundary control: what the two outgoing messages carry

Stage 6's second cut states what the CircuitBreaker *sends* at the pause's two
external edges, for arbitrary target bytecode.  All of that content lives
inside two `def` relations, `PauseCallBoundary` and `PauseStatBoundary`, where
a header pin cannot reach it: a weakened clause leaves every public header in
`callBoundary` byte-identical. -/

/-- The pause's external boundary at an ARBITRARY target bytecode, read out of
the two relations: at each edge, the argument window's bytes against the
spelled-out encoder, and the message itself as a bare `ProcessMessage` fact.
The CALL carries `pauseFor(uint256)`'s selector followed by the configured
duration, goes to `target`, is sent by the CircuitBreaker, carries no value, is
dynamic, and hands the callee the very transient storage that holds the
reentrancy lock; the staged target word is still the CircuitBreaker's when the
observation is staged, after arbitrary callee execution; and the STATICCALL
carries `isPaused()`'s bare selector, goes to the **same** target, and is
static.

`hcode` is the only thing this control says about the code at `target`, and
`code` is universally quantified.  It is bound and never used, deliberately:
it is the shape a callee pin would have to take, and there is nothing here to
satisfy one with.

Three weakenings this control is the only thing standing between and a green
gate.  None is reachable by a header pin, because each lives inside a
relation's clauses or a `def`'s body rather than in a statement's shape:

1. **Encoder substitution.**  `PauseCallBoundary` states its calldata twice —
   once as the argument window's content at `0x11c`, once as `msg.data` — and
   *either* could be restated against the window's own content,
   `(callPre.memory.read 0x11c 36).1 = (callPre.memory.read 0x11c 36).1`,
   which is what `callSpawnMsg` builds its calldata from anyway.  Both
   boundary headers would stay byte-identical.  This control therefore reads
   **both**: the window equation and the message's own `msg.data`.  It obtains
   each **only by destructuring the relation**; it never calls
   `pauseCallStaging_calldata` or any other staging lemma, which would
   re-establish the encoder behind the relation's back and leave the control
   green under exactly that substitution.  Both conclusions also spell the
   encoder out — `abiSelectorBytes pauseForSelector ++ B256.toBytes duration`,
   `abiSelectorBytes isPausedSelector` — rather than naming `pauseForCalldata`
   or `isPausedCalldata`, so mutating an encoder's *definition* cannot rescue
   it either.

2. **A callee pin.**  An added premise naming the target's bytecode — a
   `CodeAt callPre target calleeCode` on `pauseCall_boundary`, or any premise
   satisfiable only in a world where the target answers the pausable
   interface — would leave every header recognisable while silently restricting
   the claim to a cooperative callee.  See `hcode` above: this control has an
   arbitrary `code` and nothing else, so a pinned callee has nothing to
   discharge it with.

3. **A cooperative-callee premise on the observation.**  `PauseStatBoundary`
   is stated downstream of arbitrary callee execution, so a premise of the
   form "memory is unchanged across the callback" (`statPre.memory =
   callPost.memory`, say) would read as bookkeeping and would restrict the
   second edge to a target that left the CircuitBreaker's memory alone.  The
   middle conjunct here is `pauseCall_targetWord_survives`'s conclusion, taken
   from the joined boundary and nothing else, and the third is the STATICCALL
   relation reached across that same span; neither is supplied with such a
   premise.

NON-VACUITY.  Structurally: every conjunct below is extracted from a relation
`pause_externalBoundary` returns, so none is true-because-unsatisfiable.

VERIFIED by mutation: each of the three weakenings above was applied to
`Blanc/LidoCircuitBreakerCallBoundary.lean`, the **whole library rebuilt** so
that the mutation was live rather than self-defeating upstream, and this
control then rejected by `lake env lean`.  One measured limit is recorded with
it: the encoder substitution had to be paired with its construction site
(`h_window` -> `rfl` in `pauseCall_boundary`'s closing `refine`) to keep the
library compiling, and an **earlier draft of this control that read only
`msg.data` survived it** — the relation's two calldata clauses are independent,
and `msg.data` stays pinned while the window clause is gutted.  The window
equations in the conclusion are what close that hole; they were added in
response to the measurement, not before it.

What this control does **not** claim, matching the cut it guards: nothing about
what the target does with either message or returns, no claim that the pause
completes, and no claim that either edge is reached in any particular run —
`hCall` and `hStat` are derivations handed in, and `hDepth`/`hDynamic` are the
enclosing frame's honest premises.  `msg.isStatic = true` on the observation is
a property of the message the CircuitBreaker builds, not a theorem that the
child changed no state. -/
theorem call_boundary_arbitrary_target_code_control
    (sevm : Sevm) (target : Adr) (duration : B256) (code : ByteArray)
    (entry callPre callPost statPre statPost : Devm)
    (hcode : CodeAt entry target code)
    (hTarget : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (hDuration : MemWordAt entry (durationWord * 32).toNat duration)
    (hCallStaging : Line.Run sevm entry pauseCallStaging callPre)
    (hDepth : sevm.depth ≠ 0)
    (hDynamic : sevm.isStatic = false)
    (hCall : Ninst.RunCompiled sevm callPre (.exec .call) callPost)
    (hStatStaging : Line.Run sevm callPost pauseStatStaging statPre)
    (hStat : Ninst.RunCompiled sevm statPre (.exec .staticcall) statPost) :
    ((callPre.memory.read 0x11c 36).1 =
          abiSelectorBytes pauseForSelector ++ B256.toBytes duration ∧
        ∃ msg xl child, ProcessMessage msg xl (.ok child) ∧
          msg.data =
            abiSelectorBytes pauseForSelector ++ B256.toBytes duration ∧
          msg.currentTarget = target ∧ msg.caller = sevm.currentTarget ∧
          msg.value = 0 ∧ msg.isStatic = false ∧
          msg.tenv.transientStorage = callPre.transientStorage) ∧
      MemWordAt statPre (targetWord * 32).toNat target.toB256 ∧
      ((statPre.memory.read 0x11c 4).1 = abiSelectorBytes isPausedSelector ∧
        ∃ msg xl child, ProcessMessage msg xl (.ok child) ∧
          msg.data = abiSelectorBytes isPausedSelector ∧
          msg.currentTarget = target ∧ msg.isStatic = true) := by
  -- Everything below comes out of `pause_externalBoundary` and the two
  -- relations it returns.  No staging lemma is invoked here.
  obtain ⟨callB, word, statB⟩ :=
    pause_externalBoundary hTarget hDuration hCallStaging hDepth hDynamic
      hCall hStatStaging hStat
  obtain ⟨callParent, callChild, callMessage, callSlot, callDelegated,
    callCode, callGasWord, callChildGas,
    -, callWindow, -, -, -, -, -, -, -, -, -, callTarget, -, callCaller,
    callValue, callStatic, callData, callTrans, -, callProcess,
    -, -, -, -, -⟩ := callB
  obtain ⟨statParent, statChild, statMessage, statSlot, statDelegated,
    statCode, statGasWord, statChildGas,
    -, statWindow, -, -, -, -, -, -, -, -, -, statTarget, -, -, -, statStatic,
    statData, -, -, statProcess, -, -, -, -, -⟩ := statB
  exact ⟨⟨callWindow, callMessage, callSlot, callChild, callProcess, callData,
      callTarget, callCaller, callValue, callStatic, callTrans⟩,
    word,
    ⟨statWindow, statMessage, statSlot, statChild, statProcess, statData,
      statTarget, statStatic⟩⟩

/-- **The observation's answer-handling is a function of the answer.**

Four clauses, one per weakening this control exists to defeat, and all four are
read — the lesson the predecessor's control learned the hard way is that a
control which reads only one clause of a multi-clause relation survives a
mutation that guts the others.

* **(i)** defeats *decoder substitution*.  It spells `pausedAnswer`'s body out
  in full — `Bytes.toB256 (out.sliceD 0 32 0)`, a projection of the child's
  bytes — and quantifies over the CircuitBreaker's prior memory `μ`.  Restating
  the decode against the word memory happens to hold makes this underivable,
  because `μ` is unconstrained.
* **(ii)** defeats a *stale-memory assumption on the short-return arm*.  The
  two runs start from memories `μ₁` and `μ₂` that are arbitrary and unrelated,
  and below 32 bytes the observation's write leaves the rest of the window
  holding whatever each of them staged.  A proof that presumed those bytes zero
  proves one of the two and not the other.
* **(iii)** defeats *a length equality on the accepting path*.  `t ≠ []` forces
  an answer strictly longer than a word, so any premise `length = 32` upstream
  makes this underivable.  This is the Stage 6 trailing-bytes requirement,
  stated so it can fail.
* **(iv)** defeats *a cooperative-callee premise*.  It consumes the arms and
  the join with exactly the premises they state and nothing else, so any
  premise about how the callee behaves leaves it unprovable.  The target's
  bytecode is arbitrary here without a `CodeAt` binder, because
  `PauseStatBoundary` already binds the callee's code existentially and
  constrains it not at all; a decorative binder would defend nothing.

* **(v)** reads the **join** rather than the decode, and exists because an
  earlier draft of `pauseAfterSet_outcomes` was vacuous in outcomes 2 to 7
  while clauses (i) to (iv) noticed nothing: they exercise the decode
  theorems, and a control guards the clauses it reads and nothing else.  This
  one drives the join from a derivation of the whole routine and makes the code
  guard's own condition decide outcome 1, so a join whose outcome-1 branch
  stopped depending on the target's code size fails here.

None of the pinned headers states the conjunction, and none states (i), (ii) or
(iii) at an arbitrary prior memory at all. -/
theorem observation_arbitrary_answer_control
    (fs : List Func) (sevm : Sevm) (target : Adr) (duration : B256)
    (statPre statPost : Devm) (ex : Execution)
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex) :
    (∀ (μ : Mem) (s s' : Devm) (out : Bytes),
        s.memory = μ.write 0 (out.take 32) → 32 ≤ out.length →
        Line.Run sevm s (loadWord 0) s' →
        ∃ rest, s'.stack = Bytes.toB256 (out.sliceD 0 32 0) :: rest) ∧
      (∀ (μ₁ μ₂ : Mem) (p₁ p₂ : Devm) (e₁ e₂ : Execution) (out : Bytes),
        p₁.memory = μ₁.write 0 (out.take 32) →
        p₂.memory = μ₂.write 0 (out.take 32) →
        p₁.returnData = out → p₂.returnData = out → out.length < 32 →
        Func.RunCompiledTo fs sevm p₁ decodePausedResult e₁ →
        Func.RunCompiledTo fs sevm p₂ decodePausedResult e₂ →
        (∃ q, e₁ = .error (.revert, q) ∧ q.output = []) ∧
          (∃ q, e₂ = .error (.revert, q) ∧ q.output = [])) ∧
      (∀ (μ : Mem) (p : Devm) (e : Execution) (w t : Bytes),
        w.length = 32 → Bytes.toB256 w = 1 → t ≠ [] →
        p.memory = μ.write 0 ((w ++ t).take 32) → p.returnData = w ++ t →
        ¬ Nat.toB256 (w ++ t).length < (32 : B256) →
        Func.RunCompiledTo fs sevm p decodePausedResult e →
        ∃ successPre, Func.RunCompiledTo fs sevm successPre pauseSuccess e) ∧
      (∃ child : Devm,
        statPost.returnData = child.output ∧
        (child.error.isSome = false →
          ¬ Nat.toB256 child.output.length < (32 : B256) →
          (pausedAnswer child.output = 0 →
            ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
              (∃ post, ex = .error (.revert, post) ∧
                post.output = customErrorData "PauseFailed"))) ∧
          (pausedAnswer child.output = 1 →
            ∃ successPre : Devm,
              Func.RunCompiledTo fs sevm successPre pauseSuccess ex))) ∧
      (∀ (entry : Devm) (e : Execution),
        MemWordAt entry (targetWord * 32).toNat target.toB256 →
        (entry.getCode target).size.toB256 = 0 →
        Func.RunCompiledTo fs sevm entry pauseAfterSet e →
        ∃ post, e = .error (.revert, post) ∧ post.output = []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ s s' out hmem hlong hrun
    obtain ⟨hstk, -⟩ :=
      pauseDecode_loadWord_eq_answer hmem hlong nil_pref hrun
    obtain ⟨t, ht⟩ := hstk
    exact ⟨t, ht⟩
  · intro μ₁ μ₂ p₁ p₂ e₁ e₂ out hm₁ hm₂ hr₁ hr₂ hshort hrun₁ hrun₂
    exact ⟨pauseDecode_shortReturn_payload h_empty hm₁ hr₁ hshort hrun₁,
      pauseDecode_shortReturn_payload h_empty hm₂ hr₂ hshort hrun₂⟩
  · intro μ p e w t hw hone hne hmem hrd hflag hrun
    exact pauseDecode_accepts_one_withTail hw hone hmem hrd hflag hrun
  · obtain ⟨child, hrd, houtcomes⟩ :=
      pauseObservation_outcomes h_empty h_bubble h_failed boundary run
    refine ⟨child, hrd, fun herr hflag => ⟨?_, ?_⟩⟩
    · intro hzero
      rcases houtcomes with ⟨he, -⟩ | ⟨-, hs, -⟩ | ⟨-, -, -, -, hpay⟩ |
        ⟨-, -, -, hne0, -, -⟩ | ⟨-, -, -, hone, -⟩
      · rw [herr] at he; exact absurd he (by decide)
      · exact absurd hs hflag
      · exact hpay
      · exact absurd hzero hne0
      · exact absurd (hzero.symm.trans hone) (by decide)
    · intro hone
      rcases houtcomes with ⟨he, -⟩ | ⟨-, hs, -⟩ | ⟨-, -, -, hzero, -⟩ |
        ⟨-, -, -, -, hne1, -⟩ | ⟨-, -, -, -, hsucc⟩
      · rw [herr] at he; exact absurd he (by decide)
      · exact absurd hs hflag
      · exact absurd (hzero.symm.trans hone) (by decide)
      · exact absurd hone hne1
      · exact hsucc
  · intro entry e hword hzero hrun
    rcases pauseAfterSet_outcomes (duration := duration)
        h_empty h_bubble h_failed hword hrun with
      ⟨-, hpost⟩ | ⟨hne, -⟩
    · exact hpost
    · exact absurd hzero hne

/-- **The success result stays post-callback, transported, coupled, and exact.**

This one control reads every clause protected by the success cut's five fixed
anti-vacuity decisions.  It starts only with the two memory windows before the
observation, an arbitrary `PauseStatBoundary`, the two explicitly named
storage noninterference equalities, and the actual answer-handling run.

* The `PauseSuccessInputs` extracted below bind count and interval at the
  reached `successPre`; `PauseSuccessNoninterference` then binds those same
  values to `entry`.  Substituting entry-time reads inside the result therefore
  removes evidence this conclusion consumes.
* Target and duration are recovered at `successPre` from the two pre-observation
  windows.  There is no success-entry window premise and no concrete word.
* `value` is one binder shared by `PauseExpiryWrite`, `PauseExpiryValue`, and
  `heartbeatUpdatedLog`; splitting the log word from the write loses the
  displayed conjunction.
* The accepting hypothesis says only that the child's first decoded word is
  one.  No bytecode, exact returndata, or no-tail premise occurs; arbitrary
  trailing bytes remain admitted.
* The log equation is the entire walk's exact two-record delta in source order,
  so adding or permitting any other emitted record cannot satisfy it.

The panic disjunct remains because a canonical answer can still encounter the
post-callback checked-addition overflow.  Thus the control neither assumes
success nor hides an out-of-gas/revert route. -/
theorem success_commit_arbitrary_target_control
    (fs : List Func) (sevm : Sevm) (entry statPre statPost : Devm)
    (target : Adr) (duration : B256) (ex : Execution)
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (targetWindow : MemWordAt statPre
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt statPre
      (durationWord * 32).toNat duration)
    (noninterference : ∀ successPre,
      Func.RunCompiledTo fs sevm successPre pauseSuccess ex →
        PauseSuccessNoninterference sevm entry successPre)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex) :
    ∃ child : Devm,
      statPost.returnData = child.output ∧
      (child.error.isSome = false →
        ¬ Nat.toB256 child.output.length < (32 : B256) →
        pausedAnswer child.output = 1 →
        ∃ successPre : Devm,
          Func.RunCompiledTo fs sevm successPre pauseSuccess ex ∧
          PauseSuccessNoninterference sevm entry successPre ∧
          PauseSuccessInputs sevm successPre target.toB256 duration
            (entry.getStorVal sevm.currentTarget
              (countSlot sevm.caller.toB256))
            (entry.getStorVal sevm.currentTarget heartbeatIntervalSlot) ∧
          ((∃ post value,
              ex = .ok post ∧
              PauseSuccessCommitTrace fs sevm successPre post
                target.toB256 duration value ∧
              PauseExpiryWrite sevm successPre sevm.currentTarget value ∧
              PauseExpiryValue sevm.benvStat.time
                (entry.getStorVal sevm.currentTarget heartbeatIntervalSlot)
                (entry.getStorVal sevm.currentTarget
                  (countSlot sevm.caller.toB256)) value ∧
              post.logs = successPre.logs ++
                [pauseTriggeredLog sevm target.toB256 duration,
                  heartbeatUpdatedLog sevm value] ∧
              (∀ owner,
                Devm.getStor post owner =
                  if owner = sevm.currentTarget then
                    (Devm.getStor successPre owner).set
                      (expirySlot sevm.caller.toB256) value
                  else Devm.getStor successPre owner) ∧
              post.getTransVal sevm.currentTarget lockKey = 0 ∧
              (∀ owner key,
                (owner, key) ≠ (sevm.currentTarget, lockKey) →
                  post.getTransVal owner key =
                    successPre.getTransVal owner key) ∧
              post.output = successPre.output) ∨
            PauseSuccessPanic fs sevm successPre target.toB256 duration
              (entry.getStorVal sevm.currentTarget
                (countSlot sevm.caller.toB256))
              (entry.getStorVal sevm.currentTarget heartbeatIntervalSlot)
              ex)) := by
  obtain ⟨child, hreturn, outcomes⟩ :=
    pauseObservation_committed_outcomes h_empty h_bubble h_failed h_panic
      boundary targetWindow durationWindow noninterference run
  refine ⟨child, hreturn, ?_⟩
  intro hclean hlong hone
  rcases outcomes with
    ⟨herror, -⟩ |
      ⟨-, hshort, -⟩ |
      ⟨-, -, -, hzero, -⟩ |
      ⟨-, -, -, -, hnotone, -⟩ |
      ⟨-, -, -, -, successPre, hsuccess, hni, houtcome⟩
  · rw [hclean] at herror
    exact absurd herror (by decide)
  · exact absurd hshort hlong
  · rw [hone] at hzero
    exact absurd hzero (by decide)
  · exact absurd hone hnotone
  · rcases houtcome with ⟨post, value, hex, commit⟩ | panic
    · rcases commit with
        ⟨inputs, -, trace, write, expiryValue, logs, storage, lock, other,
          output⟩
      exact ⟨successPre, hsuccess, hni, inputs, Or.inl
        ⟨post, value, hex, trace, write, expiryValue, logs, storage, lock,
          other, output⟩⟩
    · exact ⟨successPre, hsuccess, hni, panic.1, Or.inr panic⟩

/-- Role determinacy within each deconflated pair, which is the property
`runtimeWriteAuthority_of_rawFrameRoot`'s "carries a permitted invocation role"
language rests on: if the role at a write were not determined, "the role" would
name nothing and a role-swap mutant would typecheck. That was a real defect --
the four constructors once had literally identical premises, so a witness for
either member of a pair repacked into the other -- and the two exclusivity
results are the artifact of its fix.

This composes them into a consequence neither states alone, and it is the
re-pin-proof half of their wiring. A header pin catches a narrowing only until
someone re-takes the digest in good faith; narrowing either exclusivity theorem,
by adding a premise or restricting it to particular deployment parameters, stops
the applications below elaborating, and a build failure is not a recorded string
a re-pin can reach.

Non-vacuous by the attainment family: `attainable_setPauserAssignment_adminRegistry`
and `attainable_setPauserAssignment_pauseRegistry` exhibit actual authorities at
both leading roles. -/
theorem deconflated_role_determinacy_control
    {dp : DeployParams} {frameRoot write : Exec.Deriv}
    {r r' : InvocationRole}
    (hr : RuntimeWriteAuthority dp frameRoot write r)
    (hr' : RuntimeWriteAuthority dp frameRoot write r') :
    ((r = .adminRegistry ∨ r = .adminExpiry) →
        (r' = .adminRegistry ∨ r' = .adminExpiry) → r = r') ∧
      ((r = .pauseRegistry ∨ r = .pauseExpiry) →
        (r' = .pauseRegistry ∨ r' = .pauseExpiry) → r = r') := by
  constructor
  · rintro (rfl | rfl) (rfl | rfl)
    · rfl
    · exact absurd hr' (RuntimeWriteAuthority.adminRegistry_not_adminExpiry hr)
    · exact absurd hr (RuntimeWriteAuthority.adminRegistry_not_adminExpiry hr')
    · rfl
  · rintro (rfl | rfl) (rfl | rfl)
    · rfl
    · exact absurd hr' (RuntimeWriteAuthority.pauseRegistry_not_pauseExpiry hr)
    · exact absurd hr (RuntimeWriteAuthority.pauseRegistry_not_pauseExpiry hr')
    · rfl

end Blanc.LidoCircuitBreaker.AccessControls
