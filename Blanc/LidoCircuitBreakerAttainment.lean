import Blanc.SourceAttainment
import Blanc.MemoryImage
import Blanc.LidoCircuitBreakerAuthority
import Blanc.LidoCircuitBreakerRegistrationWorld
import Blanc.LidoCircuitBreakerReplacementWorld

/-!
Forward attainment for exact Lido CircuitBreaker runtime persistent writes.

`Blanc/LidoCircuitBreakerAuthority.lean` states the *upper bound*: every
same-frame runtime `SSTORE` in an exact invocation carries one typed row and
one of that row's permitted invocation roles.  Nothing there says a given
(row, role) pair is ever actually reached, so `permittedRoles` is certified in
one direction only.

`Attainable` below is the matching lower-bound shape.  Its premise set is
exactly the hypothesis block of
`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot`, so a witness is
literally what that theorem consumes, and the row is pinned by the *row's own*
frozen source site rather than existentially hidden.

The rest of this module builds positive witnesses, unconditionally, at the one
concrete admin registration of
`Blanc/LidoCircuitBreakerRegistrationWorld.lean`.  That single walk performs
six persistent writes, and **all six** are attained here: five with the
`.adminRegistry` role — `.setPauserAssignment` (source function 14), the three
`appendTarget` rows `.appendArrayEntry`, `.appendReverseIndex` and
`.appendArrayLength` (function 15), and `.afterOldNewCount` (function 16) — and
one with `.adminExpiry`, the expiry write on `registerAfterSet`'s fresh arm
(function 19, inventory index 17).  One world, one derivation, six rows;
everything after the route is row-independent (`attainable_of_route`).

Three facts made the first route cheap, and all three generalize.  A
`REVERT`-only arm cannot produce an `.ok` outcome at all, so seven of the
seventeen branch crossings need no branch word and no cleanliness antecedent;
six more are the dispatcher's selector comparisons, decided on the concrete
calldata selector alone; and the same-frame premise comes back from the routed
bridge already proved, so no frame-entry-freedom certificate is involved — see
*Same-frame reachability, and why no certificate is needed* below.

The remaining four crossings are the priced ones, and they split by where their
word lives.  The `appendTarget` rows add `setPauserKernel`'s previous-pauser
test, whose word is *storage-valued*: the entry storage has to survive every
earlier crossing, which is why the route carries a `Devm.getStor` chain and the
shared kit gained its `routeTo_branch*_frame` family.  The last three are
*memory*-valued — `afterOldPauser`'s new-pauser test, `finishSetPauser`'s
continuation test and `registerAfterSet`'s previous-pauser test — and none of
them can be made key-anonymous the way the storage one is, so a memory image
travels from `registerPauser`'s staging line as three 32-byte windows.  See
*Carrying one memory word across a route* below.

A **seventh** row is attained at the end, and it needs a **second world**.
Inventory index `0`, `setPauseDuration`'s configuration write, sits in the main
function and is reached only by calldata selecting `setPauseDuration`, which
this walk's calldata does not; so `attainable_of_route` — tied as it is to that
one walk — cannot serve it, and the concrete admin configuration call of
*The `setPauseDuration.config` row, at its own world* is built instead.  It is
the module's cheapest route despite being its longest path: not one of its ten
branch crossings is priced.

Three rows are attained last, and they need a **third and fourth** world.
Inventory indices `14`, `15` and `16` are `registerAfterSet`'s expiry writes
behind `previousPauser ≠ 0`, which no fresh registration reaches, so they are
taken at the two concrete *replacement* worlds of
`Blanc/LidoCircuitBreakerReplacementWorld.lean` — one whose old pauser keeps
another assignment and one whose old pauser keeps none.  They are also the
first rows whose route has to follow a storage cell that the walk *itself*
writes; see *The three expiry rows on `registerAfterSet`'s replacement arms*
for what that costs, and for why the constructor names at 14 and 17 must not be
read as descriptions.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The attainment predicate -/

/-- A concrete exact runtime execution actually reaches this row's frozen
source site with this invocation role.

Every conjunct is load-bearing.  `row.sourceSite? dp = some site` together with
`site.pc = occurrence.node.pc` is what names the *row*; dropping either would
leave a statement about some runtime `SSTORE`, not about this one.  The frame
premises are the ones
`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` consumes, so an
`Attainable` witness and that theorem's hypotheses are the same data.

Deliberately no `Decidable` instance: attainment is an execution claim, not a
structural one. -/
def Attainable (dp : DeployParams) (row : RuntimePersistentWrite)
    (role : InvocationRole) : Prop :=
  ∃ (ca : Adr) (globalRoot frameRoot : Exec.Deriv)
    (occurrence : Exec.NinstOccurrence globalRoot) (site : Prog.SourceSite),
    occurrence.instruction = .reg .sstore ∧
    frameRoot ∈ Exec.rawFrameRoots globalRoot.exc ∧
    frameRoot.exactInvocation (runtime dp) ca ca ∧
    Exec.Deriv.ParentPrefix frameRoot occurrence.node ∧
    row.sourceSite? dp = some site ∧
    site.pc = occurrence.node.pc ∧
    RuntimeWriteAuthority dp frameRoot occurrence.node role

/-- Every row named by an attainment witness lies in the runtime's structural
persistent source inventory. -/
theorem RuntimePersistentWrite.mem_runtimePersistentSourceSites
    {dp : DeployParams} {row : RuntimePersistentWrite} {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    site ∈ runtimePersistentSourceSites dp := by
  have sound := RuntimePersistentWrite.sourceSite?_sound found
  unfold runtimePersistentSourceSites
  rw [List.mem_filter]
  exact ⟨sound.1, by simp [sound.2, isPersistentWriteInstruction]⟩

/-! ## Refuting a permitted-role widening

`RuntimePersistentWrite.permittedRoles` lists `.afterOldNewCount` as
admin-registry only.  The theorem below is the semantic content of that single
entry: a `.pauseRegistry` authority payload pins its write's own persistent
source site into source functions 14/15/17, and `.afterOldNewCount` sits in
function 16.  No execution is constructed, because none is needed — the two
role payloads are already incompatible at the source-site level.

Two further refutations follow the same shape at the roles whose site pin was
added later.  Every one of the six authority roles now constrains its write's
source function, so the mechanism applies uniformly: a widening is refutable
exactly when the role's pinned function set misses the row's frozen
`sourceFunctionIndex`.  What it cannot do is separate two roles sharing one
compiled function — `.adminConfiguration` and `.heartbeatExpiry` both live in
the main function — so no refutation between those two appears here. -/

/-- A pause-registry role can never be attained at the `afterOld.newCount`
row.  This is the mutant that a role-widening edit to `permittedRoles` would
have to make typecheck, and it does not. -/
theorem not_attainable_afterOldNewCount_pauseRegistry :
    ¬ Attainable officialParams .afterOldNewCount .pauseRegistry := by
  rintro ⟨ca, globalRoot, frameRoot, occurrence, site, _instructionEq,
    _selected, _invocation, _sameFrame, found, sitePc, authority⟩
  cases authority with
  | pauseRegistry _endpoint _assignedGuard _liveGuard _assigned _live
      writeSite =>
      rcases writeSite with ⟨other, otherMem, otherPc, otherIndex⟩
      have siteEq : other = site :=
        runtimePersistentSourceSite_eq_of_pc otherMem
          (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
          (otherPc.trans sitePc.symm)
      rw [siteEq, RuntimePersistentWrite.sourceSite?_functionIndex found]
        at otherIndex
      exact absurd otherIndex (by decide)

/-- An admin-configuration role can never be attained at the
`setPauser.assignment` row.  `setPauseDuration` and `setHeartbeatInterval` both
write in the main function; the registry row sits in source function 14. -/
theorem not_attainable_setPauserAssignment_adminConfiguration :
    ¬ Attainable officialParams .setPauserAssignment .adminConfiguration := by
  rintro ⟨ca, globalRoot, frameRoot, occurrence, site, _instructionEq,
    _selected, _invocation, _sameFrame, found, sitePc, authority⟩
  cases authority with
  | setPauseDuration _endpoint _guard _callerEq writeSite
  | setHeartbeatInterval _endpoint _guard _callerEq writeSite =>
      rcases writeSite with ⟨other, otherMem, otherPc, otherIndex⟩
      have siteEq : other = site :=
        runtimePersistentSourceSite_eq_of_pc otherMem
          (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
          (otherPc.trans sitePc.symm)
      rw [siteEq, RuntimePersistentWrite.sourceSite?_functionIndex found]
        at otherIndex
      exact absurd otherIndex (by decide)

/-- A heartbeat-expiry role can never be attained at the
`pause.lastTargetExpiry` row.  The heartbeat endpoint writes in the main
function; the row sits in `pauseAfterSet`, source function 20. -/
theorem not_attainable_pauseLastTargetExpiry_heartbeatExpiry :
    ¬ Attainable officialParams .pauseLastTargetExpiry .heartbeatExpiry := by
  rintro ⟨ca, globalRoot, frameRoot, occurrence, site, _instructionEq,
    _selected, _invocation, _sameFrame, found, sitePc, authority⟩
  cases authority with
  | heartbeatExpiry _endpoint _registered _live _countNe _liveLt writeSite =>
      rcases writeSite with ⟨other, otherMem, otherPc, otherIndex⟩
      have siteEq : other = site :=
        runtimePersistentSourceSite_eq_of_pc otherMem
          (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
          (otherPc.trans sitePc.symm)
      rw [siteEq, RuntimePersistentWrite.sourceSite?_functionIndex found]
        at otherIndex
      exact absurd otherIndex (by decide)

/-! ## The last leg of the `setPauser.assignment` route

`Blanc/SourceAttainment.lean`'s contract-neutral `routeTo_*` kit, exercised on
the exact production `Func`.  Read that module's *route-construction kit*
section before adding a leg: it records why `RouteTo`'s constructors cannot be
`apply`d, which is the one trap in front of every consumer.

This is the leg the
`.setPauserAssignment` row's attainment witness ends with: from the callee root
of `setPauserKernel` down to the assignment `SSTORE`: seventeen crossed source
nodes, one branch, and the designated head.  Nothing here reduces a program
counter.

The three legs in this section take **branch-word** hypotheses, which is what
the shared kit's branch lemmas ask for.  At a successful outcome none of those
words has to be computed — the shared kit's `routeTo_*RevertsOk` pair settles
a branch from a certified-reverting arm alone — so
`setPauserKernel_routeTo_assignment_ok`,
`runtimeMain_routeTo_setPauserAssignment` and
`call_setPauserSlot_routeTo_assignment_ok` supersede them for the witness.
These remain as the general-outcome forms. -/

/-- The kernel's zero-check prefix, spelled out: `loadWord targetWord`'s
expansion followed by `iszero`.  The combinator form unifies here too; this
`def` just names the line once for the three legs that cross it. -/
def setPauserKernelZeroCheck : Line :=
  [Ninst.pushB256 (targetWord * 32), Ninst.mload, Ninst.iszero]

/-- The kernel's assignment prefix, from the fall-through arm to the `SSTORE`;
`targetKey ++ [sload, dup 0] ++ mstoreAt previousPauserWord ++
loadWord newPauserWord ++ targetKey`, spelled out for the same reason. -/
def setPauserKernelAssignmentPrefix : Line :=
  [Ninst.pushB256 (targetWord * 32), Ninst.mload,
   Ninst.pushB256 (regionWord assignmentRegion), Ninst.or,
   Ninst.sload, Ninst.dup 0,
   Ninst.pushB256 (previousPauserWord * 32), Ninst.mstore,
   Ninst.pushB256 (newPauserWord * 32), Ninst.mload,
   Ninst.pushB256 (targetWord * 32), Ninst.mload,
   Ninst.pushB256 (regionWord assignmentRegion), Ninst.or]

/-- Structural source position of the `setPauser.assignment` `SSTORE`. -/
def setPauserAssignmentPath : Prog.SourcePath :=
  ⟨setPauserSlot,
    List.replicate 3 .rest ++ [.branchLeft] ++ List.replicate 14 .rest⟩

/-- Inside `setPauserKernel`, a walk whose zero-check falls through reaches the
assignment `SSTORE` at `setPauserAssignmentPath`.  The nonzero-target branch
word is the leg's only execution premise. -/
theorem setPauserKernel_routeTo_assignment
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm setPauserKernel out)
    (nonzeroTarget : ∀ devm' : Devm,
      Line.Run sevm devm setPauserKernelZeroCheck devm' →
      ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h
      setPauserAssignmentPath (.reg .sstore) := by
  refine routeTo_line setPauserKernelZeroCheck h
    (fun zeroCheck lineRun tail => ?_)
  refine routeTo_branchLeft tail (nonzeroTarget zeroCheck lineRun)
    (fun _armStart arm => ?_)
  refine routeTo_line setPauserKernelAssignmentPrefix arm
    (fun _writeState _writeRun write => ?_)
  have pathEq :
      ((([] ++ List.replicate setPauserKernelZeroCheck.length
              Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
          List.replicate setPauserKernelAssignmentPrefix.length
            Prog.SourceStep.rest) =
        setPauserAssignmentPath.steps := by
    simp [setPauserAssignmentPath, setPauserKernelZeroCheck,
      setPauserKernelAssignmentPrefix]
  exact pathEq ▸ routeTo_head write setPauserAssignmentPath

/-- The dispatcher's entry guard, spelled literally. -/
def runtimeMainEntryPrefix : Line :=
  [Ninst.callvalue, Ninst.pushB256 4, Ninst.calldatasize, Ninst.lt, Ninst.or]

/-- The dispatcher's opening crossing, on the exact production `runtimeMain`.

This is the named hazard zone: exposing `runtimeMain dp`'s head through
`prepend` is the unfolding that neighbouring stage lemmas pay for with
`unfold runtime runtimeMain hybridDispatchWith` plus a `simpa`.  Through
`routeTo_line` it costs nothing measurable — the route never needs the
compiled form, only the source constructor head. -/
theorem runtimeMain_routeTo_dispatch (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    {target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (runtimeMain dp) out)
    (accepted : ∀ entry : Devm,
      Line.Run sevm devm runtimeMainEntryPrefix entry →
      ∀ (w : B256) (rest : Stack), entry.stack = w :: rest → w = 0)
    (dispatchRoute : ∀ entry : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm entry
        (fsig +++ hybridDispatchWith fallbackSlot (funcs dp)) out,
        Func.RunCompiledTo.RouteTo
          ⟨0, List.replicate 5 .rest ++ [.branchLeft]⟩ tail target
          targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h target targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun entry lineRun tail => ?_)
  refine routeTo_branchLeft tail (accepted entry lineRun) (fun body arm => ?_)
  have pathEq :
      ([] ++ List.replicate runtimeMainEntryPrefix.length
            Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft] =
        List.replicate 5 Prog.SourceStep.rest ++
          [Prog.SourceStep.branchLeft] := by
    simp [runtimeMainEntryPrefix]
  exact pathEq ▸ dispatchRoute body arm

/-- The `.call setPauserSlot` crossing, on top of the leg above.

An internal `.call` restarts the source position at the callee's root, so the
target path is `setPauserAssignmentPath` regardless of where in the dispatcher
or in `registerPauser`'s body the call was reached: **no dispatcher path
arithmetic survives the call**.  Only the branch words do. -/
theorem call_setPauserSlot_routeTo_assignment
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    {current : Prog.SourcePath}
    (lookup : fs[setPauserSlot]? = some setPauserKernel)
    (h : Func.RunCompiledTo fs sevm devm (.call setPauserSlot) out)
    (nonzeroTarget : ∀ kernelStart zeroCheck : Devm,
      Line.Run sevm kernelStart setPauserKernelZeroCheck zeroCheck →
      ∀ (w : B256) (rest : Stack), zeroCheck.stack = w :: rest → w = 0) :
    Func.RunCompiledTo.RouteTo current h setPauserAssignmentPath
      (.reg .sstore) :=
  routeTo_call h lookup fun kernelStart _burn tail =>
    setPauserKernel_routeTo_assignment tail (nonzeroTarget kernelStart)

/-- A crossing that leaves the world state alone leaves storage alone.  Every
`Devm.PopBurnBy` and `Devm.BurnBy` the route kit hands back is `Devm.Rels.eq`
at the `state` field, so this is the whole content of "a branch and a call
write no storage". -/
theorem getStor_of_state {a b : Devm} (h : a.state = b.state) :
    Devm.getStor a = Devm.getStor b := by
  funext adr
  show (a.state.get adr).stor = (b.state.get adr).stor
  rw [h]

/-- Read a branch word off a known stack prefix. -/
theorem head_of_stack_prefix {devm : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ devm.stack) {w : B256} {rest : Stack}
    (hstack : devm.stack = w :: rest) : w = x := by
  rcases hp with ⟨t, ht⟩
  rw [hstack] at ht
  exact (List.cons.inj ht).1

/-- Carry a stack prefix across a branch's own pop. -/
theorem tail_of_stack_prefix {devm devm' : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ devm.stack)
    (hpop : ∃ w : B256, devm.stack = w :: devm'.stack) : xs <<+ devm'.stack := by
  rcases hpop with ⟨w, hw⟩
  rcases hp with ⟨t, ht⟩
  rw [hw] at ht
  exact ⟨t, (List.cons.inj ht).2⟩

/-! ## Carrying one memory word across a route

The `afterOldPauser` rows need a branch word that is **memory**-valued, and
unlike the kernel's storage-valued previous-pauser test it cannot be made
key-anonymous: the word *is* the staged new pauser, and there is nothing else
to read it off.  So a memory image has to travel from `registerPauser`'s
staging line down to `afterOldPauser`'s entry.

The image never becomes a byte list anyone `decide`s on.  Only one 32-byte
window is ever asked about, and three facts keep it symbolic all the way:

* a crossing that leaves memory alone keeps the window
  (`MemWordAt.acrossLine`, and the `.memory` field of every pop and burn);
* an `MLOAD`'s extension keeps it, because `Mem.extend` changes only the
  logical size and `Mem.Reads` reads the backing array
  (`MemWordAt.acrossLoadWord`); and
* a write at or past the end of the window keeps it
  (`MemWordAt.acrossMstoreAt`, on `Bytes.sliceD_writeAt_before`).

Every memory write this route crosses after the staging one lands at
`previousPauserWord`, `continuationWord` or `arrayLengthWord` — byte offsets
576, 608 and 672 — and the window is `[544, 576)`, so the third fact applies
every time and `Mem.Wf` is the only thing that has to be threaded beside the
image itself. The contract-independent carrier and transports now live in
`Blanc.MemoryImage`; only this route's zero-test combinator remains here. -/

/-- `loadWord k` followed by `iszero`: the shape of every memory-valued test
on this route.  Four branches read one, and the only thing that varies is
which word and what the image holds there. -/
def memoryZeroCheck (k : B256) : Line := loadWord k ++ [Ninst.iszero]

/-- Cross a memory-valued test. -/
theorem _root_.Blanc.MemWordAt.acrossMemoryZeroCheck
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w k : B256} (run : Line.Run e a (memoryZeroCheck k) b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold memoryZeroCheck at run
  rcases of_run_append (loadWord k) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

/-- A memory-valued test's branch word: `iszero` of the word the image holds
at the tested offset. -/
theorem memoryZeroCheck_word {e : Sevm} {s s' : Devm} {k w : B256}
    (window : MemWordAt s (k * 32).toNat w)
    (run : Line.Run e s (memoryZeroCheck k) s') :
    ∀ (v : B256) (rest : Stack), s'.stack = v :: rest → v = (w =? 0) := by
  unfold memoryZeroCheck at run
  rcases of_run_append (loadWord k) run with ⟨s1, r1, run⟩
  have p1 : w :: [] <<+ s1.stack := prefix_of_loadWord_window window nil_pref r1
  rcases Line.of_run_cons run with ⟨_s2, q2, hnil⟩
  cases hnil
  intro v rest hstack
  exact head_of_stack_prefix (prefix_of_iszero q2 p1) hstack

/-! ## The dispatcher route

`Blanc/SourceAttainment.lean`'s route-construction kit takes `routeTo_line`'s
prefix in whatever form reads best: `fsig` and `arg k ++ checkNonAddress` are
passed to it below as combinator applications and unify without complaint.
The `def`s here — `splitTest`, `linearTest`, and the guard-cascade lines
further down — name lines that have no combinator form, not workarounds. -/

/-- One `splitDispatch` pivot test, spelled as a list literal. -/
def splitTest (pivot : B256) : Line :=
  [Ninst.dup 0, Ninst.pushB256 pivot, Ninst.gt]

/-- One `linearDispatchWith` selector test, spelled as a list literal. -/
def linearTest (word : B256) : Line :=
  [Ninst.dup 0, Ninst.pushB256 word, Ninst.eq]

/-- The **final** entry of a `linearDispatchWith` chain, which is a different
line: with no further entry to compare against, the chain does not `DUP` the
selector, and the matched body is entered without the `POP` every earlier
entry's arm carries.  Two instructions, not three.

Both facts show up as path arithmetic — the chain's last entry contributes
`replicate 2 .rest` where the others contribute `replicate 3 .rest`, and the
body's first line starts at the body's own head. -/
def lastLinearTest (word : B256) : Line :=
  [Ninst.pushB256 word, Ninst.eq]

/-- A pivot test leaves `pivot > selector` above the retained selector. -/
theorem prefix_of_splitTest {sevm : Sevm} {s s' : Devm} {sel pivot : B256}
    {xs : Stack} (hp : sel :: xs <<+ s.stack)
    (run : Line.Run sevm s (splitTest pivot) s') :
    (pivot >? sel) :: sel :: xs <<+ s'.stack := by
  rcases Line.of_run_cons run with ⟨_s1, hdup, r1⟩
  rcases Line.of_run_cons r1 with ⟨_s2, hpush, r2⟩
  rcases Line.of_run_cons r2 with ⟨_s3, hop, r3⟩
  cases r3
  exact prefix_of_gt hop (prefix_of_push (of_run_pushB256 hpush)
    (prefix_of_dup_val hdup (by show_nth) hp))

/-- A selector test leaves `word = selector` above the retained selector. -/
theorem prefix_of_linearTest {sevm : Sevm} {s s' : Devm} {sel word : B256}
    {xs : Stack} (hp : sel :: xs <<+ s.stack)
    (run : Line.Run sevm s (linearTest word) s') :
    (word =? sel) :: sel :: xs <<+ s'.stack := by
  rcases Line.of_run_cons run with ⟨_s1, hdup, r1⟩
  rcases Line.of_run_cons r1 with ⟨_s2, hpush, r2⟩
  rcases Line.of_run_cons r2 with ⟨_s3, hop, r3⟩
  cases r3
  exact prefix_of_eq hop (prefix_of_push (of_run_pushB256 hpush)
    (prefix_of_dup_val hdup (by show_nth) hp))

/-- The last entry's test consumes the selector: what it leaves is the
comparison alone, on top of whatever sat *under* the selector. -/
theorem prefix_of_lastLinearTest {sevm : Sevm} {s s' : Devm} {sel word : B256}
    {xs : Stack} (hp : sel :: xs <<+ s.stack)
    (run : Line.Run sevm s (lastLinearTest word) s') :
    (word =? sel) :: xs <<+ s'.stack := by
  rcases Line.of_run_cons run with ⟨_s1, hpush, r1⟩
  rcases Line.of_run_cons r1 with ⟨_s2, hop, r2⟩
  cases r2
  exact prefix_of_eq hop (prefix_of_push (of_run_pushB256 hpush) hp)

set_option maxRecDepth 16384 in
/-- The six selector crossings of `hybridDispatchWith`, on a walk whose
calldata selects `registerPauser`: two `splitDispatch` pivots taken jumped,
then three `linearDispatchWith` misses and the match.

The continuation is quantified over the reached source path, because the
`.call setPauserSlot` further down restarts the position at the callee's root:
no dispatcher path arithmetic survives it, so none is done here.

Two frame observations are carried alongside, on the same chain and for the
same reason: nothing in the dispatcher writes storage or memory, and both
facts are needed further down — storage for `setPauserKernel`'s previous-pauser
test, memory for `afterOldPauser`'s. -/
theorem dispatch_routeTo_registerPauser (dp : DeployParams)
    {fs : List Func} {sevm : Sevm} {devm : Devm} {out : Execution}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm
      (fsig +++ hybridDispatchWith fallbackSlot (funcs dp)) out)
    (selectorEq :
      Sevm.selector sevm = selector "registerPauser" [.address, .address])
    (bodyRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      devm'.memory = devm.memory →
      ∀ tail : Func.RunCompiledTo fs sevm devm' (registerPauser dp) out,
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line fsig h (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack := prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  have g0 : Devm.getStor s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) run0).symm
  have m0 : s0.memory = devm.memory :=
    (Line.of_inv Devm.memory (by line_inv) run0).symm
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  have g1 := (Line.of_inv Devm.getStor (by line_inv) run1).symm.trans g0
  have m1 := (Line.of_inv Devm.memory (by line_inv) run1).symm.trans m0
  refine routeTo_branchRight_frame tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 _w2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 ⟨_, hpop2.stack⟩
  have g2 := (getStor_of_state hpop2.state).symm.trans g1
  have m2 := hpop2.memory.symm.trans m1
  refine routeTo_line (splitTest (selector "getPauser" [.address])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  have g3 := (Line.of_inv Devm.getStor (by line_inv) run3).symm.trans g2
  have m3 := (Line.of_inv Devm.memory (by line_inv) run3).symm.trans m2
  refine routeTo_branchRight_frame tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 _w4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 ⟨_, hpop4.stack⟩
  have g4 := (getStor_of_state hpop4.state).symm.trans g3
  have m4 := hpop4.memory.symm.trans m3
  refine routeTo_line (linearTest (selector "pauseDuration" [])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  have g5 := (Line.of_inv Devm.getStor (by line_inv) run5).symm.trans g4
  have m5 := (Line.of_inv Devm.memory (by line_inv) run5).symm.trans m4
  refine routeTo_branchLeft_frame tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 hpop6 tail6 => ?_)
  have p6 := tail_of_stack_prefix p5 ⟨_, hpop6.stack⟩
  have g6 := (getStor_of_state hpop6.state).symm.trans g5
  have m6 := hpop6.memory.symm.trans m5
  refine routeTo_line (linearTest (selector "MAX_PAUSE_DURATION" [])) tail6
    (fun _s7 run7 tail7 => ?_)
  have p7 := prefix_of_linearTest p6 run7
  have g7 := (Line.of_inv Devm.getStor (by line_inv) run7).symm.trans g6
  have m7 := (Line.of_inv Devm.memory (by line_inv) run7).symm.trans m6
  refine routeTo_branchLeft_frame tail7
    (fun _w _rest hs => by rw [head_of_stack_prefix p7 hs]; decide)
    (fun _s8 hpop8 tail8 => ?_)
  have p8 := tail_of_stack_prefix p7 ⟨_, hpop8.stack⟩
  have g8 := (getStor_of_state hpop8.state).symm.trans g7
  have m8 := hpop8.memory.symm.trans m7
  refine routeTo_line (linearTest (selector "ADMIN" [])) tail8
    (fun _s9 run9 tail9 => ?_)
  have p9 := prefix_of_linearTest p8 run9
  have g9 := (Line.of_inv Devm.getStor (by line_inv) run9).symm.trans g8
  have m9 := (Line.of_inv Devm.memory (by line_inv) run9).symm.trans m8
  refine routeTo_branchLeft_frame tail9
    (fun _w _rest hs => by rw [head_of_stack_prefix p9 hs]; decide)
    (fun _s10 hpop10 tail10 => ?_)
  have p10 := tail_of_stack_prefix p9 ⟨_, hpop10.stack⟩
  have g10 := (getStor_of_state hpop10.state).symm.trans g9
  have m10 := hpop10.memory.symm.trans m9
  refine routeTo_line
    (linearTest (selector "registerPauser" [.address, .address])) tail10
    (fun _s11 run11 tail11 => ?_)
  have p11 := prefix_of_linearTest p10 run11
  have g11 := (Line.of_inv Devm.getStor (by line_inv) run11).symm.trans g10
  have m11 := (Line.of_inv Devm.memory (by line_inv) run11).symm.trans m10
  refine routeTo_branchRight_frame tail11
    (fun _w _rest hs => by rw [head_of_stack_prefix p11 hs]; decide)
    (fun _s12 _w12 hpop12 tail12 => ?_)
  have g12 := (getStor_of_state hpop12.state).symm.trans g11
  have m12 := hpop12.memory.symm.trans m11
  refine routeTo_line [Ninst.pop] tail12 (fun _s13 run13 tail13 => ?_)
  exact bodyRoute _ _
    ((Line.of_inv Devm.getStor (by line_inv) run13).symm.trans g12)
    ((Line.of_inv Devm.memory (by line_inv) run13).symm.trans m12) tail13

/-! ## The `registerPauser` guard cascade

Four branches, and not one of them costs a branch word: every arm this walk
does *not* take is `Func.revert` or a `.call` to one, so the successful outcome
alone settles all four. -/

/-- `requireStaticArgs 2`'s guard line, spelled literally. -/
def registerStaticArgsTest : Line :=
  [Ninst.pushB256 (Nat.toB256 (4 + 32 * 2)), Ninst.calldatasize, Ninst.lt]

/-- `onlyAdmin`'s guard line, spelled literally. -/
def adminTest (dp : DeployParams) : Line :=
  [Ninst.caller, pushDeployWord dp.admin, Ninst.eq]

/-- `registerPauser`'s staging line, from the admin guard to the kernel call. -/
def registerStagingLine : Line :=
  [Ninst.pushB256 ((32 * (0 : B256)) + 4), Ninst.calldataload,
   Ninst.pushB256 (targetWord * 32), Ninst.mstore,
   Ninst.pushB256 ((32 * (1 : B256)) + 4), Ninst.calldataload,
   Ninst.pushB256 (newPauserWord * 32), Ninst.mstore,
   Ninst.pushB256 0, Ninst.pushB256 (previousPauserWord * 32), Ninst.mstore,
   Ninst.pushB256 0, Ninst.pushB256 (continuationWord * 32), Ninst.mstore]

/-- From `registerPauser`'s entry to its `.call setPauserSlot`: the static
argument-length guard, two canonical-address guards and the admin guard,
crossed on the strength of the successful outcome alone.

The staging line is the one crossing whose *effect* a caller needs rather than
its invariance -- it is where the two arguments enter memory -- so the
continuation receives the crossing itself: the state the line started from,
that state's memory, and the `Line.Run`.  Everything before the staging line is
memory-silent, which is the whole content of `stage.memory = devm.memory`. -/
theorem registerPauser_routeTo_setPauserCall (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (registerPauser dp) (.ok post))
    (callRoute : ∀ (current : Prog.SourcePath) (stage devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      stage.memory = devm.memory →
      Line.Run sevm stage registerStagingLine devm' →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm devm' (Func.call setPauserSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line registerStaticArgsTest h (fun _s0 r0 tail0 => ?_)
  have g0 : Devm.getStor _s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) r0).symm
  have n0 : _s0.memory = devm.memory :=
    (Line.of_inv Devm.memory (by line_inv) r0).symm
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail0 (fuel := 4) (by rfl)
    (fun _s1 hpop1 tail1 => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  have n1 := hpop1.memory.symm.trans n0
  refine routeTo_line (arg 0 ++ checkNonAddress) tail1 (fun _s2 r2 tail2 => ?_)
  have g2 := (Line.of_inv Devm.getStor (by line_inv) r2).symm.trans g1
  have n2 := (Line.of_inv Devm.memory (by line_inv) r2).symm.trans n1
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail2 (fuel := 4) (by rfl)
    (fun _s3 hpop3 tail3 => ?_)
  have g3 := (getStor_of_state hpop3.state).symm.trans g2
  have n3 := hpop3.memory.symm.trans n2
  refine routeTo_line (arg 1 ++ checkNonAddress) tail3 (fun _s4 r4 tail4 => ?_)
  have g4 := (Line.of_inv Devm.getStor (by line_inv) r4).symm.trans g3
  have n4 := (Line.of_inv Devm.memory (by line_inv) r4).symm.trans n3
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail4 (fuel := 4) (by rfl)
    (fun _s5 hpop5 tail5 => ?_)
  have g5 := (getStor_of_state hpop5.state).symm.trans g4
  have n5 := hpop5.memory.symm.trans n4
  refine routeTo_line (adminTest dp) tail5 (fun _s6 r6 tail6 => ?_)
  have g6 := (Line.of_inv Devm.getStor
    (by unfold adminTest pushDeployWord; line_inv) r6).symm.trans g5
  have n6 := (Line.of_inv Devm.memory
    (by unfold adminTest pushDeployWord; line_inv) r6).symm.trans n5
  refine routeTo_branchRight_of_leftRevertsOk_frame tail6 (fuel := 8) (by rfl)
    (fun _s7 _w7 hpop7 tail7 => ?_)
  have g7 := (getStor_of_state hpop7.state).symm.trans g6
  have n7 := hpop7.memory.symm.trans n6
  refine routeTo_line registerStagingLine tail7 (fun _s8 r8 tail8 => ?_)
  exact callRoute _ _ _
    ((Line.of_inv Devm.getStor (by line_inv) r8).symm.trans g7) n7 r8 tail8

/-! ## The kernel leg and the whole route -/

/-- The kernel's zero-check crossed without its branch word: the
target-is-zero arm is `.call pausableZeroErrorSlot`, which cannot end `.ok`. -/
theorem setPauserKernel_routeTo_assignment_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      setPauserKernel (.ok post)) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h
      setPauserAssignmentPath (.reg .sstore) := by
  refine routeTo_line setPauserKernelZeroCheck h (fun _zeroCheck _run tail => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail (fuel := 8) (by rfl)
    (fun _armStart arm => ?_)
  refine routeTo_line setPauserKernelAssignmentPrefix arm
    (fun _writeState _writeRun write => ?_)
  have pathEq :
      ((([] ++ List.replicate setPauserKernelZeroCheck.length
              Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
          List.replicate setPauserKernelAssignmentPrefix.length
            Prog.SourceStep.rest) =
        setPauserAssignmentPath.steps := by
    simp [setPauserAssignmentPath, setPauserKernelZeroCheck,
      setPauserKernelAssignmentPrefix]
  exact pathEq ▸ routeTo_head write setPauserAssignmentPath

theorem call_setPauserSlot_routeTo_assignment_ok (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm} {current : Prog.SourcePath}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (.call setPauserSlot) (.ok post)) :
    Func.RunCompiledTo.RouteTo current h setPauserAssignmentPath
      (.reg .sstore) :=
  routeTo_call h (by rfl) fun _kernelStart _burn tail =>
    setPauserKernel_routeTo_assignment_ok dp tail

/-- The complete route: program entry to the `setPauser.assignment` `SSTORE`,
across all twelve branches.  Only the calldata selector is an execution
premise; the successful outcome discharges the other six branch words. -/
theorem runtimeMain_routeTo_setPauserAssignment (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (runtime dp).main (.ok post))
    (selectorEq :
      Sevm.selector sevm = selector "registerPauser" [.address, .address]) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h setPauserAssignmentPath
      (.reg .sstore) := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry _run tail => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail (fuel := 4) (by rfl)
    (fun _body arm => ?_)
  exact dispatch_routeTo_registerPauser dp arm selectorEq
    (fun _current _devm' _stor _mem bodyTail =>
      registerPauser_routeTo_setPauserCall dp bodyTail
        (fun _c _stage _d _stor' _mem' _staging callTail =>
          call_setPauserSlot_routeTo_assignment_ok dp callTail))

/-! ## Pinning the row

`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` hands back *a*
row and the site it nominates.  The route names a *path*, so the two are
joined by the persistent inventory: PC identity settles which site was
reached, and index identity settles which row owns it. -/

theorem RuntimePersistentWrite.sourceSite?_official {dp : DeployParams}
    {row : RuntimePersistentWrite} {site : Prog.SourceSite}
    (found : row.sourceSite? dp = some site) :
    row.sourceSite? officialParams = some site := by
  unfold RuntimePersistentWrite.sourceSite? at found ⊢
  rwa [runtimePersistentSourceSites_eq_official dp] at found

/-- Only inventory index `3` — `.setPauserAssignment` — nominates a site whose
source path is `setPauserAssignmentPath`. -/
theorem setPauserAssignment_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some setPauserAssignmentPath) → index = 3 := by
  decide +kernel

/-- A row whose nominated site sits at `setPauserAssignmentPath` is exactly
`.setPauserAssignment`. -/
theorem RuntimePersistentWrite.eq_setPauserAssignment_of_path
    {dp : DeployParams} {row : RuntimePersistentWrite}
    {site : Prog.SourceSite} (found : row.sourceSite? dp = some site)
    (pathEq : site.path = setPauserAssignmentPath) :
    row = .setPauserAssignment := by
  have official := RuntimePersistentWrite.sourceSite?_official found
  unfold RuntimePersistentWrite.sourceSite? at official
  have mapped :
      (runtimePersistentSourceSites officialParams)[row.index]?.map
        (fun s => s.path) = some setPauserAssignmentPath := by
    rw [official]
    exact congrArg some pathEq
  have indexEq : row.index = 3 :=
    setPauserAssignment_index_pin row.index
      (List.mem_range.mpr (by
        have bound := row.index_lt
        omega)) mapped
  exact RuntimePersistentWrite.index_injective indexEq

/-! ## Same-frame reachability, and why no certificate is needed

`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` consumes
`Exec.Deriv.ParentPrefix frameRoot occurrence.node`, and the routed bridge
returns exactly that, built alongside the derivation it constructs.  Nothing
below has to certify that the registration walk enters no child frame.

That is worth recording, because the certificate route looks mandatory and is
not, and one of the two ways of stating it is not even true.  Reading the
obligation at the *code* level — no reached node decodes an `Xinst` — cannot
hold here at all: the frozen inherited inventory is 20 persistent, 3 transient
and **2 external-call** runtime sites, and both call sites are in
`pauseAfterSet`, so a claim about `node.sevm.code` is a claim about a runtime
that demonstrably contains `CALL` and `STATICCALL`.  The honest version is
about which nodes the walk *visits*, which is what the direct-pause control
establishes as data: `Blanc/LidoCircuitBreakerRegistry.lean`'s private
`DirectPausePath` carries a childless side condition at every `.next` node,
and `directPause_zeroCode_postWrite_error_control` exports the result.

Even that version cannot be replaced by a decidable source-level certificate
in the style of `Func.alwaysRevertsWithin`.  Such a certificate has to pass
*both* arms of every `.branch` it crosses, and this runtime's dispatcher has a
`pause` arm; more sharply, `setPauserKernel` is shared, and its own
continuation branch in `finishSetPauser` selects `.call pauseAfterSetSlot` on
the pause side.  So no static certificate rooted at `runtimeMain` — or even at
`registerPauser` — can be `true`, however call-free the registration walk is.

The route already crosses only same-frame steps, so the fact is free: see
`Blanc/SourceAttainment.lean`'s *Same-frame packaging*. -/

/-- The concrete registration world is an exact runtime invocation. -/
theorem freshWorld_exactInvocation {post : Devm}
    (exc : Exec 0 freshWorldSevm freshWorldPre (.ok post)) :
    (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
      Exec.Deriv).exactInvocation (runtime officialParams)
      freshWorldOwner freshWorldOwner := by
  refine ⟨rfl, freshWorld_currentTarget, ?_, ?_⟩
  · show freshWorldSevm.codeAddress = some freshWorldOwner
    rw [freshWorld_codeAddress, freshWorld_currentTarget]
  · show some freshWorldSevm.code.toList = Prog.compile (runtime officialParams)
    rw [freshWorld_codeBytes, lidoCircuitBreakerCode_compile]

/-! ## The positive witness -/

/-- The first positive attainment witness: the concrete admin registration of
`Blanc/LidoCircuitBreakerRegistrationWorld.lean` reaches the
`.setPauserAssignment` row's own frozen source site with the `.adminRegistry`
invocation role.

Unconditional, and nothing in `Attainable` is relaxed, existentially hidden or
hypothesised: the row is named, the role is named, and the frame premises are
the ones `Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot`
consumes. -/
theorem attainable_setPauserAssignment_adminRegistry :
    Attainable officialParams .setPauserAssignment .adminRegistry := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, hrun, _hexec, _hfilled,
    _hgas, _hexpiry, _hlogs, hcompile⟩ := freshRegistrationWorld_run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := runtimeMain_routeTo_setPauserAssignment officialParams hwalk
    freshWorld_dataFacts.2.1
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation := freshWorld_exactInvocation exc
  have instructionEq : occurrence.instruction = .reg .sstore :=
    hinstr.trans hinstrTarget
  obtain ⟨row, rowSite, _rowMem, found, _classified, rowSitePc, _rowInstr,
    _unique, role, rolePermitted, authority⟩ :=
    Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot occurrence
      instructionEq (Exec.mem_rawFrameRoots_self exc) invocation sameFrame
  have routedMember : site ∈ runtimePersistentSourceSites officialParams := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hinstrTarget, isPersistentWriteInstruction]⟩
  have siteEq : rowSite = site :=
    runtimePersistentSourceSite_eq_of_pc
      (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
      routedMember (rowSitePc.trans hpc)
  have rowEq : row = .setPauserAssignment :=
    RuntimePersistentWrite.eq_setPauserAssignment_of_path found
      (siteEq ▸ hpath)
  subst rowEq
  have roleEq : role = .adminRegistry := by
    have alternatives : role = .adminRegistry ∨ role = .pauseRegistry := by
      simpa [RuntimePersistentWrite.permittedRoles] using rolePermitted
    rcases alternatives with rfl | rfl
    · rfl
    · exfalso
      cases authority with
      | pauseRegistry _endpoint _assignedGuard _liveGuard assigned _live
          _writeSite =>
          have zero : freshWorldPre.getStorVal freshWorldOwner
              (assignmentSlot freshWorldTarget) = 0 := by
            have witness := freshWorld_preWitness.assignments freshWorldTarget
              freshWorld_targetValid.2
            rw [freshWorld_getStorVal, ← freshWorld_getStor]
            simpa [logicalStorageOfStor, assignmentAt] using witness
          rw [show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).sevm = freshWorldSevm from rfl,
            freshWorld_currentTarget, freshWorld_dataFacts.2.2.1,
            show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).devm = freshWorldPre from rfl,
            zero, freshWorld_admin] at assigned
          exact absurd assigned.symm (by decide)
  subst roleEq
  exact ⟨freshWorldOwner, ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩,
    ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩, occurrence, rowSite,
    instructionEq, Exec.mem_rawFrameRoots_self exc, invocation, sameFrame,
    found, rowSitePc, authority⟩


/-! ## The `appendTarget` rows

`freshRegistrationWorld_run` performs six persistent writes, and three of them
sit in source function 15, `appendTarget`.  Reaching them means crossing
`setPauserKernel`'s *second* branch — the `iszero` on the previous pauser the
kernel just `SLOAD`ed — and that arm's sibling is an ordinary old-pauser
update, not a `REVERT`, so the free crossing of
`routeTo_branchLeft_of_rightRevertsOk` is unavailable and the branch word has
to be computed.

The word is **storage-valued**, which is what the whole storage-carrying
apparatus below exists for: the crossed line's `SLOAD` reads a key the walk
built out of memory, so the `Devm.getStor` of the message-entry state has to
survive twelve earlier crossings to be read here.  It does, because a branch
and a call are `Devm.Rels.eq` in the `state` field
(`routeTo_branch*_frame`, `getStor_of_state`) and no line before the assignment
`SSTORE` contains one.

What *this* branch deliberately does not need is the memory image.  The key is
`slot assignmentRegion m` for **whatever** word `m` the kernel loaded, and this
world's storage is zero at *every* assignment slot — `heartbeatIntervalSlot` is
the only nonzero cell and it is in the config region.  Separating the two takes
no payload bound and no calldata fact, only one bit of the region tag, so this
crossing reads no memory.  The three later branches are not so lucky; the
windows they need are threaded past this point all the same. -/

/-- The config region's tag bit is set where the assignment region's is not, so
the fresh world's one nonzero cell is not an assignment slot — for any payload
whatsoever, canonical or not.  `slot_ne_of_region_ne` cannot be used here: it
needs both payloads below `2 ^ 252`, and a word loaded out of memory has no
such bound. -/
private theorem heartbeatIntervalSlot_ne_assignmentSlot (m : B256) :
    heartbeatIntervalSlot ≠ assignmentSlot m := by
  intro h
  have hl : heartbeatIntervalSlot.1.1 = (0x1000000000000000 : UInt64) := rfl
  have hr : (assignmentSlot m).1.1
      = (0x3000000000000000 : UInt64) ||| m.1.1 := rfl
  have h1 : (0x1000000000000000 : UInt64) = 0x3000000000000000 ||| m.1.1 := by
    rw [← hl, ← hr, h]
  have h2 := congrArg (fun u : UInt64 => u.toNat.testBit 61) h1
  rw [UInt64.toNat_or, Nat.testBit_or] at h2
  simp only [show (0x1000000000000000 : UInt64).toNat.testBit 61 = false from
      by decide,
    show (0x3000000000000000 : UInt64).toNat.testBit 61 = true from by decide,
    Bool.true_or] at h2
  exact Bool.noConfusion h2

/-- At the fresh registration world no target word is assigned a pauser. -/
theorem freshWorld_assignment_zero (m : B256) :
    freshWorldPre.getStorVal freshWorldOwner (assignmentSlot m) = 0 := by
  rw [freshWorld_getStorVal, freshWorldStor,
    Stor.get_set_ne _ (heartbeatIntervalSlot_ne_assignmentSlot m)]
  simp [Stor.get, Stor.empty]

/-- `setPauserKernelAssignmentPrefix` continued across the assignment `SSTORE`
and the previous-pauser zero test: the line whose last word decides the
kernel's second branch. -/
def setPauserKernelAppendPrefix : Line :=
  setPauserKernelAssignmentPrefix ++ [Ninst.sstore, Ninst.iszero]

/-- The kernel's second branch word, at the fresh registration world: the
previous pauser is zero, so the `iszero` above it is not — and the same zero is
what the kernel's own `mstoreAt previousPauserWord` stages, which is the second
conclusion.

The storage premise is that the walk has written no storage yet, which is
exactly what the `Devm.getStor` chain carries down from message entry.  The
loaded target word stays anonymous — see this section's note.  `window` is
needed only for its image: a fresh write's read-back is stated over the image
that was there before it, and any window carries one. -/
theorem freshWorld_previousPauserZero {devm devm' : Devm} {offset : Nat}
    {w : B256}
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (window : MemWordAt devm offset w)
    (run : Line.Run freshWorldSevm devm setPauserKernelAppendPrefix devm') :
    (∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0) ∧
      MemWordAt devm' (previousPauserWord * 32).toNat 0 := by
  unfold setPauserKernelAppendPrefix setPauserKernelAssignmentPrefix at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  have p1 : (targetWord * 32) :: [] <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) nil_pref
  obtain ⟨m, p2⟩ := prefix_of_mload q2 p1
  have p3 : regionWord assignmentRegion :: m :: [] <<+ s3.stack :=
    prefix_of_push (of_run_pushB256 q3) p2
  have p4 : assignmentSlot m :: [] <<+ s4.stack := prefix_of_or q4 p3
  have hstor4 : Devm.getStor s4 = Devm.getStor freshWorldPre := by
    rw [← hstor]
    exact (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 (Line.Run.cons q3
        (Line.Run.cons q4 Line.Run.nil))))).symm
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  obtain ⟨v, p5, hv⟩ := prefix_of_sload q5 p4
  have hzero : v = 0 := by
    rw [hv, freshWorld_currentTarget,
      show Devm.getStorVal s4 freshWorldOwner (assignmentSlot m)
          = freshWorldPre.getStorVal freshWorldOwner (assignmentSlot m) from
        congrArg (fun f : Adr → Stor =>
          (f freshWorldOwner).get (assignmentSlot m)) hstor4]
    exact freshWorld_assignment_zero m
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  have p6 : v :: v :: [] <<+ s6.stack :=
    prefix_of_dup_val q6 (by show_nth) p5
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have p7 := prefix_of_push (of_run_pushB256 q7) p6
  rcases Line.of_run_cons run with ⟨s8, q8, run⟩
  obtain ⟨p8, hmem8⟩ := prefix_of_mstore_val q8 p7
  obtain ⟨_img7, image7⟩ :=
    (((((((window.acrossNinst q1).acrossMload q2).acrossNinst q3).acrossNinst
      q4).acrossNinst q5).acrossNinst q6).acrossNinst q7).memImage
  have staged : MemWordAt s8 (previousPauserWord * 32).toNat 0 := by
    rw [← hzero]
    exact MemWordAt.of_write image7 hmem8
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have p9 := prefix_of_push (of_run_pushB256 q9) p8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  obtain ⟨n, p10⟩ := prefix_of_mload q10 p9
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have p11 := prefix_of_push (of_run_pushB256 q11) p10
  rcases Line.of_run_cons run with ⟨s12, q12, run⟩
  obtain ⟨m2, p12⟩ := prefix_of_mload q12 p11
  rcases Line.of_run_cons run with ⟨s13, q13, run⟩
  have p13 := prefix_of_push (of_run_pushB256 q13) p12
  rcases Line.of_run_cons run with ⟨s14, q14, run⟩
  have p14 := prefix_of_or q14 p13
  rcases Line.of_run_cons run with ⟨s15, q15, run⟩
  have p15 := prefix_of_sstore q15 p14
  rcases Line.of_run_cons run with ⟨s16, q16, hnil⟩
  cases hnil
  have p16 := prefix_of_iszero q16 p15
  refine ⟨?_, ?_⟩
  · intro w rest hstack
    rw [head_of_stack_prefix p16 hstack, hzero]
    decide
  · exact ((((((((staged.acrossNinst q9).acrossMload q10).acrossNinst
      q11).acrossMload q12).acrossNinst q13).acrossNinst q14).acrossNinst
      q15).acrossNinst q16)

/-! ### From the kernel to `appendTarget`'s three writes

`appendTarget` has no branch at all, so once the fresh arm is taken the three
rows are three different split points of one straight line. -/

/-- `appendTarget`'s prefix up to the array-entry `SSTORE`. -/
def appendArrayEntryPrefix : Line :=
  [Ninst.pushB256 arrayLengthSlot, Ninst.sload, Ninst.pushB256 1, Ninst.add,
    Ninst.dup 0] ++ mstoreAt arrayLengthWord ++ loadWord targetWord ++
    loadWord arrayLengthWord ++ tagTop arrayRegion

/-- From the array-entry `SSTORE` to the reverse-index `SSTORE`. -/
def appendReverseIndexPrefix : Line :=
  Ninst.sstore :: (loadWord arrayLengthWord ++ targetIndexKey)

/-- From the reverse-index `SSTORE` to the array-length `SSTORE`. -/
def appendArrayLengthPrefix : Line :=
  Ninst.sstore :: (loadWord arrayLengthWord ++ [Ninst.pushB256 arrayLengthSlot])

/-- Structural source position of the `append.arrayEntry` `SSTORE`. -/
def appendArrayEntryPath : Prog.SourcePath :=
  ⟨appendTargetSlot, List.replicate 13 .rest⟩

/-- Structural source position of the `append.reverseIndex` `SSTORE`. -/
def appendReverseIndexPath : Prog.SourcePath :=
  ⟨appendTargetSlot, List.replicate 20 .rest⟩

/-- Structural source position of the `append.arrayLength` `SSTORE`. -/
def appendArrayLengthPath : Prog.SourcePath :=
  ⟨appendTargetSlot, List.replicate 24 .rest⟩

/-! ### The staged words, and the lines they survive

`registerPauser`'s staging line is where the new pauser and the zero
continuation enter memory, and the crossings between there and
`registerAfterSet` are the lines below.  Each is split at its own memory
instructions and nowhere else: `line_inv` carries a window across every
memory-silent stretch, including the `SLOAD`s and `SSTORE`s, so only the
`MLOAD`s, the `MSTORE`s and the one `LOG` cost anything.

Three words are read as branch conditions on this route — the new pauser at
544, the previous pauser at 576 and the continuation at 608 — and they are
tracked as three independent windows rather than one image, because they are
created at three different points and each survives the others' writes by the
same one-line disjointness argument. -/

/-- The two words `registerPauser`'s staging line lays down that are later read
as branch conditions. -/
def EntryWindows (devm : Devm) : Prop :=
  MemWordAt devm (newPauserWord * 32).toNat freshWorldPauser ∧
    MemWordAt devm (continuationWord * 32).toNat 0

/-- Those two, plus the previous pauser that `setPauserKernel` stages out of
storage. -/
def KernelWindows (devm : Devm) : Prop :=
  EntryWindows devm ∧ MemWordAt devm (previousPauserWord * 32).toNat 0

/-- What the staging line stages: from empty memory, memory word
`newPauserWord` holds the call's second argument and memory word
`continuationWord` holds zero.

The image is built forward only as far as the new-pauser write and then read
back immediately (`MemWordAt.of_write`), so the target word laid down before it
never has to be described; the continuation window is read back the same way at
the line's last store.  Nothing here evaluates a byte. -/
theorem freshWorld_stagedEntry {stage post : Devm}
    (hmem : stage.memory = Mem.empty)
    (run : Line.Run freshWorldSevm stage registerStagingLine post) :
    EntryWindows post := by
  unfold registerStagingLine at run
  rcases of_run_append (arg 0) run with ⟨s1, r1, run⟩
  have p1 : Sevm.argWord freshWorldSevm 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref r1
  have i1 : MemImage s1 [] :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r1).symm
      ⟨by rw [hmem]; exact Mem.wf_empty, by rw [hmem]; exact Mem.reads_empty⟩
  rcases of_run_append (mstoreAt targetWord) run with ⟨_s2, r2, run⟩
  obtain ⟨p2, hm2⟩ := of_run_mstoreAt_val r2 p1
  rcases of_run_append (arg 1) run with ⟨_s3, r3, run⟩
  have p3 := prefix_of_arg p2 r3
  have i3 : MemImage _s3 _ :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r3).symm
      (i1.write hm2)
  rcases of_run_append (mstoreAt newPauserWord) run with ⟨_s4, r4, run⟩
  obtain ⟨_p4, hm4⟩ := of_run_mstoreAt_val r4 p3
  have window : MemWordAt _s4 (newPauserWord * 32).toNat freshWorldPauser := by
    rw [← freshWorld_dataFacts.2.2.2]
    exact MemWordAt.of_write i3 hm4
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s5, r5, run⟩
  have p5 : (0 : B256) :: [] <<+ _s5.stack := by
    rcases Line.of_run_cons r5 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) _p4
  rcases of_run_append (mstoreAt previousPauserWord) run with ⟨_s6, r6, run⟩
  obtain ⟨p6, _⟩ := of_run_mstoreAt_val r6 p5
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s7, r7, run⟩
  have p7 : (0 : B256) :: [] <<+ _s7.stack := by
    rcases Line.of_run_cons r7 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) p6
  have window7 : MemWordAt _s7 (newPauserWord * 32).toNat freshWorldPauser :=
    ((window.acrossLine (by line_inv) r5).acrossMstoreAt (by decide)
      r6).acrossLine (by line_inv) r7
  obtain ⟨_img7, image7⟩ := window7.memImage
  obtain ⟨_p8, hm8⟩ := of_run_mstoreAt_val run p7
  exact ⟨window7.acrossMstoreAt (by decide) run,
    MemWordAt.of_write image7 hm8⟩

/-- The kernel's zero-check reads memory and writes none. -/
theorem _root_.Blanc.MemWordAt.acrossZeroCheck
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a setPauserKernelZeroCheck b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold setPauserKernelZeroCheck at run
  rcases of_run_append (loadWord targetWord) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

/-- The kernel's assignment line plus its previous-pauser test.  Its one write
is `mstoreAt previousPauserWord`. -/
theorem _root_.Blanc.MemWordAt.acrossAppendPrefix
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256}
    (miss : offset + 32 ≤ (previousPauserWord * 32).toNat ∨
      (previousPauserWord * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a setPauserKernelAppendPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold setPauserKernelAppendPrefix setPauserKernelAssignmentPrefix at run
  rcases of_run_append (loadWord targetWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append
    [Ninst.pushB256 (regionWord assignmentRegion), Ninst.or, Ninst.sload,
      Ninst.dup 0] run with ⟨_s2, r2, run⟩
  rcases of_run_append (mstoreAt previousPauserWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s4, r4, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s5, r5, run⟩
  exact (((((window.acrossLoadWord r1).acrossLine (by line_inv)
    r2).acrossMstoreAt miss r3).acrossLoadWord r4).acrossLoadWord
    r5).acrossLine (by line_inv) run

/-- `appendTarget`'s first fragment.  Its one write is
`mstoreAt arrayLengthWord`. -/
theorem _root_.Blanc.MemWordAt.acrossArrayEntryPrefix
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256}
    (miss : offset + 32 ≤ (arrayLengthWord * 32).toNat ∨
      (arrayLengthWord * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a appendArrayEntryPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold appendArrayEntryPrefix at run
  rcases of_run_append
    [Ninst.pushB256 arrayLengthSlot, Ninst.sload, Ninst.pushB256 1, Ninst.add,
      Ninst.dup 0] run with ⟨_s1, r1, run⟩
  rcases of_run_append (mstoreAt arrayLengthWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append (loadWord arrayLengthWord) run with ⟨_s4, r4, run⟩
  exact ((((window.acrossLine (by line_inv) r1).acrossMstoreAt miss
    r2).acrossLoadWord r3).acrossLoadWord r4).acrossLine (by line_inv) run

/-- `appendTarget`'s second fragment: reads only. -/
theorem _root_.Blanc.MemWordAt.acrossReverseIndexPrefix {e : Sevm} {a b : Devm}
    {offset : Nat} {w : B256}
    (run : Line.Run e a appendReverseIndexPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold appendReverseIndexPrefix targetIndexKey at run
  rcases of_run_append [Ninst.sstore] run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord arrayLengthWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  exact (((window.acrossLine (by line_inv) r1).acrossLoadWord
    r2).acrossLoadWord r3).acrossLine (by line_inv) run

/-- `appendTarget`'s third fragment: reads only. -/
theorem _root_.Blanc.MemWordAt.acrossArrayLengthPrefix
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a appendArrayLengthPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold appendArrayLengthPrefix at run
  rcases of_run_append [Ninst.sstore] run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord arrayLengthWord) run with ⟨_s2, r2, run⟩
  exact ((window.acrossLine (by line_inv) r1).acrossLoadWord
    r2).acrossLine (by line_inv) run

/-! ### The same crossings on the bundles

Three windows crossing the same line is three instances of one lemma, and the
offsets are concrete, so each `miss` side condition is a `decide` on two
literals.  Bundling them keeps the route theorems reading like the single-window
ones. -/

theorem EntryWindows.of_memory_eq {a b : Devm} (h : b.memory = a.memory)
    (windows : EntryWindows a) : EntryWindows b :=
  ⟨MemWordAt.of_memory_eq h windows.1, MemWordAt.of_memory_eq h windows.2⟩

theorem EntryWindows.acrossZeroCheck {e : Sevm} {a b : Devm}
    (run : Line.Run e a setPauserKernelZeroCheck b)
    (windows : EntryWindows a) : EntryWindows b :=
  ⟨windows.1.acrossZeroCheck run, windows.2.acrossZeroCheck run⟩

theorem EntryWindows.acrossAppendPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a setPauserKernelAppendPrefix b)
    (windows : EntryWindows a) : EntryWindows b :=
  ⟨windows.1.acrossAppendPrefix (by decide) run,
    windows.2.acrossAppendPrefix (by decide) run⟩

theorem KernelWindows.of_memory_eq {a b : Devm} (h : b.memory = a.memory)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨EntryWindows.of_memory_eq h windows.1, MemWordAt.of_memory_eq h windows.2⟩

theorem KernelWindows.acrossLine {e : Sevm} {a b : Devm} {l : Line}
    (inv : Line.Inv Devm.memory l) (run : Line.Run e a l b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossLine inv run, windows.1.2.acrossLine inv run⟩,
    windows.2.acrossLine inv run⟩

theorem KernelWindows.acrossArrayEntryPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a appendArrayEntryPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossArrayEntryPrefix (by decide) run,
    windows.1.2.acrossArrayEntryPrefix (by decide) run⟩,
    windows.2.acrossArrayEntryPrefix (by decide) run⟩

theorem KernelWindows.acrossReverseIndexPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a appendReverseIndexPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossReverseIndexPrefix run,
    windows.1.2.acrossReverseIndexPrefix run⟩,
    windows.2.acrossReverseIndexPrefix run⟩

theorem KernelWindows.acrossArrayLengthPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a appendArrayLengthPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossArrayLengthPrefix run,
    windows.1.2.acrossArrayLengthPrefix run⟩,
    windows.2.acrossArrayLengthPrefix run⟩

theorem KernelWindows.acrossMemoryZeroCheck {e : Sevm} {a b : Devm} {k : B256}
    (run : Line.Run e a (memoryZeroCheck k) b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossMemoryZeroCheck run,
    windows.1.2.acrossMemoryZeroCheck run⟩,
    windows.2.acrossMemoryZeroCheck run⟩

/-- Inside `setPauserKernel` at the fresh registration world: the zero-target
arm is a certified-reverting call, and the previous-pauser test takes the
jumped arm, so the walk reaches `.call appendTargetSlot`. -/
theorem setPauserKernel_routeTo_appendCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm setPauserKernel (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (windows : EntryWindows devm)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line setPauserKernelZeroCheck h (fun _z zrun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) zrun).symm.trans hstor
  have e0 := windows.acrossZeroCheck zrun
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 8) (by rfl)
    (fun _s1 hpop1 arm => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  have e1 := EntryWindows.of_memory_eq hpop1.memory.symm e0
  refine routeTo_line setPauserKernelAppendPrefix arm
    (fun _s2 run2 tail2 => ?_)
  obtain ⟨branchWord, staged⟩ := freshWorld_previousPauserZero g1 e1.1 run2
  refine routeTo_branchRight_frame tail2 branchWord
    (fun _s3 _w3 hpop3 tail3 => ?_)
  exact callRoute _ _
    (KernelWindows.of_memory_eq hpop3.memory.symm
      ⟨e1.acrossAppendPrefix run2, staged⟩) tail3

/-- The `.call setPauserSlot` crossing, carrying the entry storage and the
staged memory word into the kernel. -/
theorem call_setPauserSlot_routeTo_appendCall {devm post : Devm}
    {current targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (.call setPauserSlot) (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (windows : EntryWindows devm)
    (callRoute : ∀ (current' : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current' tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo current h targetPath targetInstruction :=
  routeTo_call h (by rfl) fun _kernelStart burn tail =>
    setPauserKernel_routeTo_appendCall tail
      ((getStor_of_state burn.state).symm.trans hstor)
      (EntryWindows.of_memory_eq burn.memory.symm windows) callRoute

/-- The complete route from program entry to `appendTarget`'s own root, at the
fresh registration world.  Thirteen branches: six selector comparisons decided
on the concrete calldata selector, six settled by certified-reverting siblings,
and the kernel's storage-valued previous-pauser test.

The continuation also receives the three staged memory words, which is what the
`afterOldPauser` and `registerAfterSet` rows below need and the three
`appendTarget` rows ignore. -/
theorem runtimeMain_routeTo_appendCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry erun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) erun).symm.trans hstor
  have n0 := (Line.of_inv Devm.memory (by line_inv) erun).symm.trans hmem
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 4) (by rfl)
    (fun _body hpop arm => ?_)
  have g1 := (getStor_of_state hpop.state).symm.trans g0
  have n1 := hpop.memory.symm.trans n0
  exact dispatch_routeTo_registerPauser officialParams arm
    freshWorld_dataFacts.2.1
    (fun _current _devm' dstor dmem bodyTail =>
      registerPauser_routeTo_setPauserCall officialParams bodyTail
        (fun _c _stage _d rstor rmem staging callTail =>
          call_setPauserSlot_routeTo_appendCall callTail
            (rstor.trans (dstor.trans g1))
            (freshWorld_stagedEntry (rmem.trans (dmem.trans n1)) staging)
            callRoute))

/-- The array-entry write: `appendTarget`'s first `SSTORE`. -/
theorem runtimeMain_routeTo_appendArrayEntry {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendArrayEntryPath (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor hmem
    fun _current _devm' _window callTail =>
    routeTo_call callTail (by rfl) fun _bodyStart _burn body => by
      refine routeTo_line appendArrayEntryPrefix body
        (fun _s _run write => ?_)
      have pathEq :
          ([] ++ List.replicate appendArrayEntryPrefix.length
            Prog.SourceStep.rest) = appendArrayEntryPath.steps := by
        simp [appendArrayEntryPath, appendArrayEntryPrefix, mstoreAt, loadWord,
          tagTop]
      exact pathEq ▸ routeTo_head write appendArrayEntryPath

/-- The reverse-index write: `appendTarget`'s second `SSTORE`. -/
theorem runtimeMain_routeTo_appendReverseIndex {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendReverseIndexPath
      (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor hmem
    fun _current _devm' _window callTail =>
    routeTo_call callTail (by rfl) fun _bodyStart _burn body => by
      refine routeTo_line appendArrayEntryPrefix body
        (fun _s _run entry => ?_)
      refine routeTo_line appendReverseIndexPrefix entry
        (fun _s' _run' write => ?_)
      have pathEq :
          (([] ++ List.replicate appendArrayEntryPrefix.length
              Prog.SourceStep.rest) ++
            List.replicate appendReverseIndexPrefix.length
              Prog.SourceStep.rest) = appendReverseIndexPath.steps := by
        simp [appendReverseIndexPath, appendArrayEntryPrefix,
          appendReverseIndexPrefix, mstoreAt, loadWord, tagTop,
          targetIndexKey]
      exact pathEq ▸ routeTo_head write appendReverseIndexPath

/-- The array-length write: `appendTarget`'s third `SSTORE`. -/
theorem runtimeMain_routeTo_appendArrayLength {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendArrayLengthPath (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor hmem
    fun _current _devm' _window callTail =>
    routeTo_call callTail (by rfl) fun _bodyStart _burn body => by
      refine routeTo_line appendArrayEntryPrefix body
        (fun _s _run entry => ?_)
      refine routeTo_line appendReverseIndexPrefix entry
        (fun _s' _run' index => ?_)
      refine routeTo_line appendArrayLengthPrefix index
        (fun _s'' _run'' write => ?_)
      have pathEq :
          ((([] ++ List.replicate appendArrayEntryPrefix.length
                Prog.SourceStep.rest) ++
              List.replicate appendReverseIndexPrefix.length
                Prog.SourceStep.rest) ++
            List.replicate appendArrayLengthPrefix.length
              Prog.SourceStep.rest) = appendArrayLengthPath.steps := by
        simp [appendArrayLengthPath, appendArrayEntryPrefix,
          appendReverseIndexPrefix, appendArrayLengthPrefix, mstoreAt,
          loadWord, tagTop, targetIndexKey]
      exact pathEq ▸ routeTo_head write appendArrayLengthPath

/-! ### Pinning the three rows

`RuntimePersistentWrite.eq_setPauserAssignment_of_path`, generalized: the
inventory index that nominates a given source path names the row, and the only
row-specific input is one decidable index pin. -/

/-- A row whose nominated site sits at `path` is the row that `indexPin`
names. -/
theorem RuntimePersistentWrite.eq_of_path
    {row target : RuntimePersistentWrite} {site : Prog.SourceSite}
    {path : Prog.SourcePath}
    (indexPin : ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
        (fun s => s.path) = some path) → index = target.index)
    (found : row.sourceSite? officialParams = some site)
    (pathEq : site.path = path) :
    row = target := by
  unfold RuntimePersistentWrite.sourceSite? at found
  have mapped :
      (runtimePersistentSourceSites officialParams)[row.index]?.map
        (fun s => s.path) = some path := by
    rw [found]
    exact congrArg some pathEq
  have indexEq : row.index = target.index :=
    indexPin row.index
      (List.mem_range.mpr (by
        have bound := row.index_lt
        omega)) mapped
  exact RuntimePersistentWrite.index_injective indexEq

/-- Inventory indices `5`, `6` and `7` — `.appendArrayEntry`,
`.appendReverseIndex` and `.appendArrayLength` — are the only ones nominating
the three `appendTarget` paths.  One kernel evaluation settles all three. -/
theorem append_index_pins :
    (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some appendArrayEntryPath) → index = 5) ∧
      (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some appendReverseIndexPath) → index = 6) ∧
      (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some appendArrayLengthPath) → index = 7) := by
  decide +kernel

/-! ### The witnesses

Everything after the route is row-independent, so it is proved once.  The
`.pauseRegistry` alternative is refuted at the *frame root*, not at the write:
a pause invocation's authority payload asserts that the caller is the assigned
pauser of the calldata target, and at this world every assignment slot is zero
while the caller is the nonzero admin.

The tail is stated for an arbitrary expected role, because the rows below it
do not all carry the same one — `afterOld.newCount` permits `.adminRegistry`
alone and `register.retainedOldNewExpiry` permits `.adminExpiry` alone.  A row whose
`permittedRoles` is a singleton pays nothing for the refutation: its `roles`
premise closes the `.pauseRegistry` disjunct vacuously. -/

/-- The shared tail of every witness at the fresh registration world: a route
to a row's frozen path yields that row attained with the expected role. -/
theorem attainable_of_route {row : RuntimePersistentWrite}
    {expected : InvocationRole} {path : Prog.SourcePath}
    (pin : ∀ {r : RuntimePersistentWrite} {site : Prog.SourceSite},
      r.sourceSite? officialParams = some site → site.path = path → r = row)
    (roles : ∀ r ∈ row.permittedRoles,
      r = expected ∨ r = InvocationRole.pauseRegistry)
    (route : ∀ (devm post : Devm)
      (h : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm (runtime officialParams).main (.ok post)),
      Devm.getStor devm = Devm.getStor freshWorldPre →
      devm.memory = Mem.empty →
      Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row expected := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, hrun, _hexec, _hfilled,
    _hgas, _hexpiry, _hlogs, hcompile⟩ := freshRegistrationWorld_run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := route mid post hwalk (getStor_of_state hburn.state).symm
    hburn.memory.symm
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation := freshWorld_exactInvocation exc
  have instructionEq : occurrence.instruction = .reg .sstore :=
    hinstr.trans hinstrTarget
  obtain ⟨reached, rowSite, _rowMem, found, _classified, rowSitePc, _rowInstr,
    _unique, role, rolePermitted, authority⟩ :=
    Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot occurrence
      instructionEq (Exec.mem_rawFrameRoots_self exc) invocation sameFrame
  have routedMember : site ∈ runtimePersistentSourceSites officialParams := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hinstrTarget, isPersistentWriteInstruction]⟩
  have siteEq : rowSite = site :=
    runtimePersistentSourceSite_eq_of_pc
      (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
      routedMember (rowSitePc.trans hpc)
  have rowEq : reached = row := pin found (siteEq ▸ hpath)
  subst rowEq
  have roleEq : role = expected := by
    rcases roles role rolePermitted with rfl | rfl
    · rfl
    · exfalso
      cases authority with
      | pauseRegistry _endpoint _assignedGuard _liveGuard assigned _live
          _writeSite =>
          rw [show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).sevm = freshWorldSevm from rfl,
            freshWorld_currentTarget,
            show (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
                Exec.Deriv).devm = freshWorldPre from rfl,
            freshWorld_assignment_zero, freshWorld_admin] at assigned
          exact absurd assigned.symm (by decide)
  subst roleEq
  exact ⟨freshWorldOwner, ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩,
    ⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩, occurrence, rowSite,
    instructionEq, Exec.mem_rawFrameRoots_self exc, invocation, sameFrame,
    found, rowSitePc, authority⟩

/-- The `append.arrayEntry` row is attained with the `.adminRegistry` role. -/
theorem attainable_appendArrayEntry_adminRegistry :
    Attainable officialParams .appendArrayEntry .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.1 found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_appendArrayEntry h hstor hmem)

/-- The `append.reverseIndex` row is attained with the `.adminRegistry`
role. -/
theorem attainable_appendReverseIndex_adminRegistry :
    Attainable officialParams .appendReverseIndex .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.2.1 found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_appendReverseIndex h hstor hmem)

/-- The `append.arrayLength` row is attained with the `.adminRegistry` role. -/
theorem attainable_appendArrayLength_adminRegistry :
    Attainable officialParams .appendArrayLength .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.2.2 found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_appendArrayLength h hstor hmem)

/-! ## The `afterOld.newCount` row

Source function 16, one `.call` past `appendTarget`.  The fourteenth branch,
and the first whose word is **memory**-valued: `afterOldPauser` opens by
testing the staged new pauser, and -- unlike the kernel's previous-pauser test,
which the entry storage settles for *any* loaded key -- there is nothing to
read this word off except the memory the staging line wrote.  That is what the
window machinery above exists for, and it is the whole of the row's extra cost:
the route is otherwise `runtimeMain_routeTo_appendCall` continued through
`appendTarget`'s three writes.

Role pinning is free here.  `permittedRoles` lists `.adminRegistry` alone, so
the `.pauseRegistry` disjunct of `attainable_of_route`'s `roles` premise closes
by `decide` and no execution-level refutation is involved -- which is a
different fact from `not_attainable_afterOldNewCount_pauseRegistry` above, and
neither implies the other. -/

/-- `afterOldPauser`'s fall-through arm, from the branch to the `SSTORE`:
`newCountKey ++ [sload, push 1, add] ++ newCountKey`. -/
def afterOldNewCountPrefix : Line :=
  newCountKey ++ [Ninst.sload, Ninst.pushB256 1, Ninst.add] ++ newCountKey

/-- Structural source position of the `afterOld.newCount` `SSTORE`. -/
private def sourceRests (n : Nat) : List Prog.SourceStep :=
  List.replicate n .rest

def afterOldNewCountPath : Prog.SourcePath :=
  ⟨afterOldPauserSlot,
    sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++ sourceRests 11⟩

theorem _root_.Blanc.MemWordAt.acrossNewCountKey
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a newCountKey b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold newCountKey at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

theorem _root_.Blanc.MemWordAt.acrossNewCountPrefix
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a afterOldNewCountPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold afterOldNewCountPrefix at run
  rcases of_run_append newCountKey run with ⟨_s1, r1, run⟩
  rcases of_run_append [Ninst.sload, Ninst.pushB256 1, Ninst.add] run
    with ⟨_s2, r2, run⟩
  exact ((window.acrossNewCountKey r1).acrossLine (by line_inv)
    r2).acrossNewCountKey run

theorem KernelWindows.acrossNewCountPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a afterOldNewCountPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossNewCountPrefix run,
    windows.1.2.acrossNewCountPrefix run⟩,
    windows.2.acrossNewCountPrefix run⟩

/-- From program entry to `afterOldPauser`'s own root: the three
`appendTarget` writes crossed, then its tail call.  Both rows past
`appendTarget` start here. -/
theorem runtimeMain_routeTo_afterOldCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call afterOldPauserSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine runtimeMain_routeTo_appendCall h hstor hmem
    (fun _current _devm' windows callTail => ?_)
  refine routeTo_call callTail (by rfl) (fun _bodyStart burn body => ?_)
  have k0 := KernelWindows.of_memory_eq burn.memory.symm windows
  refine routeTo_line appendArrayEntryPrefix body (fun _s1 r1 entry => ?_)
  refine routeTo_line appendReverseIndexPrefix entry (fun _s2 r2 index => ?_)
  refine routeTo_line appendArrayLengthPrefix index
    (fun _s3 r3 lengthWrite => ?_)
  refine routeTo_line [Ninst.sstore] lengthWrite (fun _s4 r4 afterCall => ?_)
  exact callRoute _ _
    ((((k0.acrossArrayEntryPrefix r1).acrossReverseIndexPrefix
      r2).acrossArrayLengthPrefix r3).acrossLine (by line_inv) r4) afterCall

/-- `afterOldPauser`'s branch word at the fresh registration world: the staged
new pauser is `9`, so its `iszero` is zero and the walk falls through to the
new-count update rather than to `removeTarget`.

The staged window is the only premise, and it is the one thing the whole memory
apparatus is for. -/
theorem freshWorld_newPauserNonzero {devm devm' : Devm}
    (window : MemWordAt devm (newPauserWord * 32).toNat freshWorldPauser)
    (run : Line.Run freshWorldSevm devm (memoryZeroCheck newPauserWord) devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0 := by
  intro w rest hstack
  rw [memoryZeroCheck_word window run w rest hstack]
  decide

/-- Inside `afterOldPauser` at the fresh registration world: the entry test
falls through, so the walk reaches the new-count `SSTORE` and, past it, the
`.call finishSetPauserSlot`. -/
theorem afterOldPauser_routeTo_newCountArm {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm afterOldPauser (.ok post))
    (windows : KernelWindows devm)
    (armRoute : ∀ devm' : Devm, KernelWindows devm' →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm'
        (newCountKey +++ Ninst.sload ::: Ninst.pushB256 1 ::: Ninst.add :::
          newCountKey +++ Ninst.sstore ::: Func.call finishSetPauserSlot)
        (.ok post),
        Func.RunCompiledTo.RouteTo
          ⟨afterOldPauserSlot,
            List.replicate 3 .rest ++ [Prog.SourceStep.branchLeft]⟩ tail
          targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨afterOldPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line (memoryZeroCheck newPauserWord) h
    (fun _s5 r5 tail5 => ?_)
  refine routeTo_branchLeft_frame tail5
    (freshWorld_newPauserNonzero windows.1.1 r5) (fun _s6 hpop arm => ?_)
  have pathEq :
      ([] ++ List.replicate (memoryZeroCheck newPauserWord).length
            Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft] =
        List.replicate 3 Prog.SourceStep.rest ++
          [Prog.SourceStep.branchLeft] := by
    simp [memoryZeroCheck, loadWord]
  exact pathEq ▸ armRoute _
    (KernelWindows.of_memory_eq hpop.memory.symm
      (windows.acrossMemoryZeroCheck r5)) arm

/-- The complete route from program entry to the `afterOld.newCount` `SSTORE`:
`runtimeMain_routeTo_afterOldCall`, then the tail call into `afterOldPauser`
and its memory-valued entry test. -/
theorem runtimeMain_routeTo_afterOldNewCount {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h afterOldNewCountPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_afterOldCall h hstor hmem
    (fun _current _devm' windows callTail => ?_)
  refine routeTo_call callTail (by rfl)
    (fun _afterStart afterBurn afterBody => ?_)
  refine afterOldPauser_routeTo_newCountArm afterBody
    (KernelWindows.of_memory_eq afterBurn.memory.symm windows)
    (fun _devm'' _windows'' arm => ?_)
  refine routeTo_line afterOldNewCountPrefix arm (fun _s7 _r7 write => ?_)
  have pathEq :
      ((List.replicate 3 Prog.SourceStep.rest ++
            [Prog.SourceStep.branchLeft]) ++
          List.replicate afterOldNewCountPrefix.length Prog.SourceStep.rest) =
        afterOldNewCountPath.steps := by
    simp [afterOldNewCountPath, sourceRests, afterOldNewCountPrefix, loadWord,
      newCountKey, tagTop]
  exact pathEq ▸ routeTo_head write afterOldNewCountPath

/-- Inventory index `8` -- `.afterOldNewCount` -- is the only one nominating
`afterOldNewCountPath`. -/
theorem afterOldNewCount_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some afterOldNewCountPath) → index = 8 := by
  decide +kernel

/-- The `afterOld.newCount` row is attained with the `.adminRegistry` role. -/
theorem attainable_afterOldNewCount_adminRegistry :
    Attainable officialParams .afterOldNewCount .adminRegistry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path afterOldNewCount_index_pin found pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_afterOldNewCount h hstor hmem)

/-! ## The expiry row on `registerAfterSet`'s fresh arm

Source function 19, three `.call`s past `appendTarget`.  Four more branches,
three of them memory-valued and settled by the three windows the route already
carries: `finishSetPauser`'s continuation test reads the zero at
`continuationWord`, `registerAfterSet`'s first test reads the zero at
`previousPauserWord`, and its second reads the new pauser again.  The fourth is
`checkedHeartbeatExpiry`'s overflow test, whose sibling is
`Func.revertData (Panic(0x11))` and therefore free.

Role pinning is free again, and for the same reason as `afterOld.newCount`:
every `register.*` row permits `.adminExpiry` alone.

**Which row this is.**  `Attainable` pins a row through
`RuntimePersistentWrite.sourceSite?`, which is `RuntimePersistentWrite.index`
into the *structural* inventory, and the structural order of
`registerAfterSet`'s four expiry writes is measured, not assumed:
`Func.sourceSites` visits the fall-through arm first, and
`registerAfterSet`'s fall-through arm is the `previousCountKey` block.  So the
inventory positions are

* index 14 — 31 steps, `previousPauser ≠ 0` and old count retained;
* index 15 — 16 steps, the old pauser's expiry cleared;
* index 16 — 46 steps, the new pauser's expiry after that clear;
* index 17 — 24 steps, `previousPauser = 0`: the **fresh** registration.

The fresh registration world takes the jumped arm at the first test, so the row
it reaches is index 17, `.registerFreshExpiry`.
`.registerRetainedOldNewExpiry` — index 14 — is *not* attainable at this world
at all: its site sits behind `previousPauser ≠ 0`, which this registration is
not.

These two names were **transposed** until they were exchanged: index 14 carried
`.registerFreshExpiry` while its site is the retained arm, and index 17 the
reverse.  Nothing ever depended on them — every row is pinned by `sourceSite?`
— but reports and commits written before the exchange use the old pairing. -/

/-- `arithmeticPanic` is `Func.revertData` of a `Panic(0x11)` payload, so
`checkedHeartbeatExpiry`'s overflow arm is certified-reverting and its branch
costs no word.

`by rfl` -- what the other six reverting siblings on this route use -- does
*not* close this one, and the reason is worth recording: `Func.revertData`'s node
count is computed from its payload, so the certificate cannot reduce until
`signatureHash "Panic"` does, and the elaborator's `whnf` does not get there.
The kernel does, so this is the one certificate that needs `decide +kernel`.
`Func.revertSelector`, which the other reverters use, has a fixed shape and never
looks at its payload. -/
private theorem arithmeticPanic_revertsWithin :
    Func.alwaysRevertsWithin 16
      ((runtime officialParams).main :: (runtime officialParams).aux)
      (Func.call arithmeticPanicSlot) = true := by decide +kernel

/-- `finishSetPauser`'s whole prefix: the `PauserSet` event, then the
continuation test.  The `LOG` in the middle is the only instruction on this
route that `line_inv` has no instance for. -/
def finishSetPauserPrefix : Line :=
  loadWord newPauserWord ++ loadWord previousPauserWord ++
    loadWord targetWord ++ [Ninst.pushB256 pauserSetEvent] ++ logWith 3 0 0 ++
    memoryZeroCheck continuationWord

theorem _root_.Blanc.MemWordAt.acrossFinishPrefix
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a finishSetPauserPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold finishSetPauserPrefix at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 pauserSetEvent] run with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 3 0 0) run with ⟨_s5, r5, run⟩
  exact (((((window.acrossLoadWord r1).acrossLoadWord r2).acrossLoadWord
    r3).acrossLine (by line_inv) r4).acrossLogWith r5).acrossMemoryZeroCheck run

theorem KernelWindows.acrossFinishPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a finishSetPauserPrefix b)
    (windows : KernelWindows a) : KernelWindows b :=
  ⟨⟨windows.1.1.acrossFinishPrefix run, windows.1.2.acrossFinishPrefix run⟩,
    windows.2.acrossFinishPrefix run⟩

/-- `finishSetPauser`'s branch word at the fresh registration world: the
staging line wrote a zero continuation, so the walk returns to
`registerAfterSet` rather than to `pauseAfterSet`. -/
theorem freshWorld_continuationRegister {devm devm' : Devm}
    (window : MemWordAt devm (continuationWord * 32).toNat 0)
    (run : Line.Run freshWorldSevm devm finishSetPauserPrefix devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0 := by
  unfold finishSetPauserPrefix at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 pauserSetEvent] run with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 3 0 0) run with ⟨_s5, r5, run⟩
  have window5 := ((((window.acrossLoadWord r1).acrossLoadWord
    r2).acrossLoadWord r3).acrossLine (by line_inv) r4).acrossLogWith r5
  intro w rest hstack
  rw [memoryZeroCheck_word window5 run w rest hstack]
  decide

/-- `registerAfterSet`'s first branch word: the previous pauser is the zero the
kernel staged, so its `iszero` is not zero and the fresh-registration arm
runs. -/
theorem freshWorld_previousPauserAbsent {devm devm' : Devm}
    (window : MemWordAt devm (previousPauserWord * 32).toNat 0)
    (run : Line.Run freshWorldSevm devm (memoryZeroCheck previousPauserWord)
      devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0 := by
  intro w rest hstack
  rw [memoryZeroCheck_word window run w rest hstack]
  decide

/-- `checkedHeartbeatExpiry`'s overflow-checked addition, up to its branch. -/
def checkedExpiryPrefix : Line :=
  [Ninst.timestamp, Ninst.pushB256 heartbeatIntervalSlot, Ninst.sload,
   Ninst.add, Ninst.dup 0, Ninst.timestamp, Ninst.swap 0, Ninst.lt]

/-- From `checkedHeartbeatExpiry`'s fall-through arm to the expiry
`SSTORE`. -/
def registerFreshArmExpiryPrefix : Line :=
  [Ninst.dup 0] ++ mstoreAt 0 ++ loadWord newPauserWord ++ tagTop expiryRegion

/-- Structural source position of the expiry `SSTORE` on `registerAfterSet`'s
fresh arm: inventory index `17`. -/
def registerFreshArmExpiryPath : Prog.SourcePath :=
  ⟨registerAfterSetSlot,
    List.replicate 3 .rest ++ [.branchRight] ++ List.replicate 3 .rest ++
      [.branchLeft] ++ List.replicate 8 .rest ++ [.branchLeft] ++
      List.replicate 7 .rest⟩

/-- The complete route from program entry to the `register.retainedOldNewExpiry`
`SSTORE`: seventeen branches, of which exactly four are paid for — the
dispatcher's six selector comparisons are decided on the calldata selector,
seven more have certified-reverting siblings, and the remaining four read the
three staged memory words. -/
theorem runtimeMain_routeTo_registerFreshArmExpiry {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h registerFreshArmExpiryPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_afterOldCall h hstor hmem
    (fun _current _devm' windows callTail => ?_)
  refine routeTo_call callTail (by rfl)
    (fun _afterStart afterBurn afterBody => ?_)
  refine afterOldPauser_routeTo_newCountArm afterBody
    (KernelWindows.of_memory_eq afterBurn.memory.symm windows)
    (fun _devm'' windows'' arm => ?_)
  refine routeTo_line afterOldNewCountPrefix arm (fun _s1 r1 countWrite => ?_)
  refine routeTo_line [Ninst.sstore] countWrite (fun _s2 r2 finishCall => ?_)
  refine routeTo_call finishCall (by rfl) (fun _fStart fBurn fBody => ?_)
  have w0 := KernelWindows.of_memory_eq fBurn.memory.symm
    ((windows''.acrossNewCountPrefix r1).acrossLine (by line_inv) r2)
  refine routeTo_line finishSetPauserPrefix fBody (fun _s3 r3 tail3 => ?_)
  refine routeTo_branchRight_frame tail3
    (freshWorld_continuationRegister w0.1.2 r3)
    (fun _s4 _w4 hpop4 registerCall => ?_)
  have w1 := KernelWindows.of_memory_eq hpop4.memory.symm
    (w0.acrossFinishPrefix r3)
  refine routeTo_call registerCall (by rfl) (fun _rStart rBurn rBody => ?_)
  have w2 := KernelWindows.of_memory_eq rBurn.memory.symm w1
  refine routeTo_line (memoryZeroCheck previousPauserWord) rBody
    (fun _s5 r5 tail5 => ?_)
  refine routeTo_branchRight_frame tail5
    (freshWorld_previousPauserAbsent w2.2 r5)
    (fun _s6 _w6 hpop6 arm6 => ?_)
  have w3 := KernelWindows.of_memory_eq hpop6.memory.symm
    (w2.acrossMemoryZeroCheck r5)
  refine routeTo_line (memoryZeroCheck newPauserWord) arm6
    (fun _s7 r7 tail7 => ?_)
  refine routeTo_branchLeft tail7 (freshWorld_newPauserNonzero w3.1.1 r7)
    (fun _s8 arm8 => ?_)
  refine routeTo_line checkedExpiryPrefix arm8 (fun _s9 _r9 tail9 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail9 (fuel := 16)
    arithmeticPanic_revertsWithin (fun _s10 arm10 => ?_)
  refine routeTo_line registerFreshArmExpiryPrefix arm10
    (fun _s11 _r11 write => ?_)
  have pathEq :
      ((((((([] ++ List.replicate (memoryZeroCheck previousPauserWord).length
                    Prog.SourceStep.rest) ++ [Prog.SourceStep.branchRight]) ++
                List.replicate (memoryZeroCheck newPauserWord).length
                  Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
            List.replicate checkedExpiryPrefix.length Prog.SourceStep.rest) ++
          [Prog.SourceStep.branchLeft]) ++
        List.replicate registerFreshArmExpiryPrefix.length
          Prog.SourceStep.rest) = registerFreshArmExpiryPath.steps := by
    simp [registerFreshArmExpiryPath, memoryZeroCheck, checkedExpiryPrefix,
      registerFreshArmExpiryPrefix, loadWord, mstoreAt, tagTop]
  exact pathEq ▸ routeTo_head write registerFreshArmExpiryPath

/-- Inventory index `17` is the only one nominating
`registerFreshArmExpiryPath`. -/
theorem registerFreshArmExpiry_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some registerFreshArmExpiryPath) → index = 17 := by
  decide +kernel

/-- The inventory row at index `17`, `.registerFreshExpiry` — the expiry write
on `registerAfterSet`'s fresh arm — is attained with the `.adminExpiry` role.

The row is pinned by `sourceSite?`, not by its name; the name and the site
agree since the 14/17 exchange, and this one's site is the `previousPauser = 0`
write. -/
theorem attainable_registerFreshExpiry_adminExpiry :
    Attainable officialParams .registerFreshExpiry .adminExpiry :=
  attainable_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path registerFreshArmExpiry_index_pin found
        pathEq)
    (by decide)
    (fun _devm _post h hstor hmem =>
      runtimeMain_routeTo_registerFreshArmExpiry h hstor hmem)

/-! ## The main-function rows, at worlds of their own

Three inventory rows sit in the compiled **main function** rather than behind a
`.call`: index `0`, `setPauseDuration`'s configuration `SSTORE`; index `1`,
`setHeartbeatInterval`'s; and index `2`, the expiry `SSTORE` on `heartbeat`'s
success arm.  None of the three is reachable from the fresh registration walk,
whose calldata selects `registerPauser`, so `attainable_of_route` — welded as
it is to that one walk — cannot serve any of them, and each gets its own
concrete world.

Being main-function-resident is the one thing these routes pay more for.  No
`.call` restarts the source position, so a route has to carry its accumulated
steps the whole way and finish against the row's frozen sixty-odd-step path,
where `runtimeMain_routeTo_setPauserAssignment` could hand its arithmetic off
to `setPauserSlot`'s root.  Measured, that is a non-issue: the accumulated
steps are closed data, so they reduce definitionally and `routeTo_head` closes
the path equation with no rewriting step of its own.

Against it, **not one branch word is priced on the two configuration routes,
and only the dispatcher's are priced on the heartbeat one**.  Every crossing is
settled either on the concrete calldata selector or by a sibling arm that is
`Func.revert` or a `.call` to a `runtimeError`, which `routeTo_branch*_of_*RevertsOk`
refutes from the successful outcome alone.  Nothing storage-valued or
memory-valued survives a crossing on any of the three, so no `Devm.getStor`
chain and no memory image travel with these routes — including the heartbeat
one, whose registered-caller and strict-liveness facts are consumed by its
*body walk* and never by its route.

What the three legs share is stated once here and used three times: a world
skeleton (`breakerMsg`), and the tail from a routed run to an `Attainable`
witness (`attainable_of_entryRoute`).  What they do not share is the route.  A
route's crossing sequence is a function of its selector's position in the
5/4/4/4 dispatch topology and of its body's own guard cascade, and no two of
these three agree on either, so each is spelled out. -/

/-! ### A shared world skeleton

One deployment, three messages.  The worlds below differ in caller, storage,
timestamp, calldata, warm keys and gas, and in nothing else, so that difference
is exactly `breakerMsg`'s argument list.

A world is data, not a claim: nothing here is pinned or published, and what is
proved *about* a world is what carries weight. -/

/-- The CircuitBreaker deployment every world below installs. -/
def configWorldOwner : Adr := Nat.toAdr 100

/-- The admin caller.  `officialParams.admin` as an address. -/
def configWorldAdmin : Adr :=
  Nat.toAdr 0x3e40D73EB977Dc6a537aF587D48316feE66E9C8c

/-- The configured pause duration: `officialParams`' own initial value, which
sits strictly inside the immutable `[432000, 5184000]` bounds. -/
def configWorldDuration : B256 := 1814400

/-- Canonical direct-call calldata for `setPauseDuration(uint256)`. -/
def setPauseDurationCalldata (duration : B256) : Bytes :=
  abiSelectorBytes (selector "setPauseDuration" [.uint256]) ++ duration.toBytes

/-- The installed generated runtime bytes. -/
def configWorldCode : ByteArray :=
  ByteArray.mk (lidoCircuitBreakerCode officialParams).toArray

/-- World state: the CircuitBreaker account alone, carrying `stor`. -/
def breakerState (stor : Stor) : State :=
  State.set (.empty : State) configWorldOwner
    { Acct.nil with stor := stor, code := configWorldCode }

/-- A direct, non-static, zero-value message to that deployment.  Every world
in this section is one of these. -/
def breakerMsg (caller : Adr) (stor : Stor) (time : B256) (data : Bytes)
    (keys : Std.HashSet (Adr × B256)) (gas : Nat) : Msg :=
  { (default : Msg) with
    benv :=
      { (default : Benv) with
        state := breakerState stor
        stat :=
          { (default : BenvStat) with
            origState := breakerState stor
            time := time } }
    tenv := default
    caller := caller
    target := some configWorldOwner
    currentTarget := configWorldOwner
    gas := gas
    value := 0
    data := data
    codeAddress := some configWorldOwner
    code := configWorldCode
    depth := 0
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := keys
    disablePrecompiles := false }

/-- The deployment's storage at a world of the skeleton is the `stor` that
world was built from.  Both the current and the original state are that one
`stor`, so this lemma serves `getStorVal` and `getOrigStorVal` alike. -/
theorem breakerState_stor (stor : Stor) :
    ((breakerState stor).get configWorldOwner).stor = stor := by
  rw [breakerState, State.get_set_self]

private theorem breakerMsg_byteArray_ofList_toList (bs : Bytes) :
    (ByteArray.mk bs.toArray).toList = bs := by
  rw [ByteArray.toList_eq_toList_data]

/-- Every world of the skeleton installs the production runtime bytes. -/
theorem breakerMsg_codeBytes (caller : Adr) (stor : Stor) (time : B256)
    (data : Bytes) (keys : Std.HashSet (Adr × B256)) (gas : Nat) :
    (breakerMsg caller stor time data keys gas).code.toList =
      lidoCircuitBreakerCode officialParams := by
  simpa only [breakerMsg, configWorldCode] using
    breakerMsg_byteArray_ofList_toList (lidoCircuitBreakerCode officialParams)

/-! ### From a routed run to a witness

`attainable_of_route` above is welded to the fresh registration walk, and
consumes a storage and a memory antecedent that walk's route needs.  This is
the same tail with the world abstracted away and both antecedents gone: it
takes a run, a route from the program's own entry, and the two frame facts
`exactInvocation` wants.

It also drops that tail's `.pauseRegistry` refutation, because it does not need
it.  All three rows below have a **singleton** `permittedRoles`, so the reached
role is forced by membership and `roles` closes decidably.  A row with two
permitted roles could not use this form. -/

/-- The frame-carrying form: the route is handed the two facts the entry
`JUMPDEST` burn gives it about the state it starts from, so a route whose
branch words are read out of *storage* or out of the message's own empty
memory can be stated at all.

`attainable_of_entryRoute` below is this with both facts discarded, which is
all a route decided on the calldata selector needs.  The replacement routes
need both: `setPauserKernel`'s previous-pauser test reads the target's
assignment slot, and every later memory-valued test reads a word the staging
line wrote into memory that has to have been empty. -/
theorem attainable_of_entryRoute_frame {sevm : Sevm} {pre : Devm} {ca : Adr}
    {row : RuntimePersistentWrite} {expected : InvocationRole}
    {path : Prog.SourcePath}
    (owner : sevm.currentTarget = ca)
    (codeAddress : sevm.codeAddress = some ca)
    (pin : ∀ {r : RuntimePersistentWrite} {site : Prog.SourceSite},
      r.sourceSite? officialParams = some site → site.path = path → r = row)
    (roles : ∀ r ∈ row.permittedRoles, r = expected)
    (run : ∃ post,
      Prog.RunCompiledTo sevm pre (runtime officialParams) (.ok post) ∧
        some sevm.code.toList = Prog.compile (runtime officialParams))
    (route : ∀ (devm post : Devm),
      Devm.getStor devm = Devm.getStor pre → devm.memory = pre.memory →
      ∀ h : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        sevm devm (runtime officialParams).main (.ok post),
        Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row expected := by
  obtain ⟨post, hrun, hcompile⟩ := run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := route mid post (getStor_of_state hburn.state).symm
    hburn.memory.symm hwalk
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    sameFrame⟩ :=
    Prog.exec_of_runCompiledTo_routeTo hburn hroute hcompile
  have invocation :
      (⟨0, sevm, pre, .ok post, exc⟩ : Exec.Deriv).exactInvocation
        (runtime officialParams) ca ca :=
    ⟨rfl, owner, codeAddress, hcompile⟩
  have instructionEq : occurrence.instruction = .reg .sstore :=
    hinstr.trans hinstrTarget
  obtain ⟨reached, rowSite, _rowMem, found, _classified, rowSitePc, _rowInstr,
    _unique, role, rolePermitted, authority⟩ :=
    Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot occurrence
      instructionEq (Exec.mem_rawFrameRoots_self exc) invocation sameFrame
  have routedMember : site ∈ runtimePersistentSourceSites officialParams := by
    unfold runtimePersistentSourceSites
    rw [List.mem_filter]
    exact ⟨hmem, by simp [hinstrTarget, isPersistentWriteInstruction]⟩
  have siteEq : rowSite = site :=
    runtimePersistentSourceSite_eq_of_pc
      (RuntimePersistentWrite.mem_runtimePersistentSourceSites found)
      routedMember (rowSitePc.trans hpc)
  have rowEq : reached = row := pin found (siteEq ▸ hpath)
  subst rowEq
  have roleEq : role = expected := roles role rolePermitted
  subst roleEq
  exact ⟨ca, ⟨0, sevm, pre, .ok post, exc⟩, ⟨0, sevm, pre, .ok post, exc⟩,
    occurrence, rowSite, instructionEq, Exec.mem_rawFrameRoots_self exc,
    invocation, sameFrame, found, rowSitePc, authority⟩

/-- A concrete exact invocation whose walk is routed from the program entry to
a row's frozen source path attains that row, at whatever role its
`permittedRoles` singleton names. -/
theorem attainable_of_entryRoute {sevm : Sevm} {pre : Devm} {ca : Adr}
    {row : RuntimePersistentWrite} {expected : InvocationRole}
    {path : Prog.SourcePath}
    (owner : sevm.currentTarget = ca)
    (codeAddress : sevm.codeAddress = some ca)
    (pin : ∀ {r : RuntimePersistentWrite} {site : Prog.SourceSite},
      r.sourceSite? officialParams = some site → site.path = path → r = row)
    (roles : ∀ r ∈ row.permittedRoles, r = expected)
    (run : ∃ post,
      Prog.RunCompiledTo sevm pre (runtime officialParams) (.ok post) ∧
        some sevm.code.toList = Prog.compile (runtime officialParams))
    (route : ∀ (devm post : Devm)
      (h : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        sevm devm (runtime officialParams).main (.ok post)),
      Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row expected := by
  exact attainable_of_entryRoute_frame owner codeAddress pin roles run
    (fun devm post _hstor _hmem h => route devm post h)

/-! ## The `setPauseDuration.config` row, at its own world

An admin `setPauseDuration(1814400)` call on an otherwise untouched deployment.

The walk is one `func_run`: `setPauseDuration` is `setHeartbeatInterval`'s
exact structural twin, so the body reuses that family's measured charges (two
`MSTORE` expansions at `3`, a `LOG1` at `1262`, a warm zero-to-nonzero `SSTORE`
at `20000`) without restating any of its effects.  Effects are not restated
because attainment does not need them: an `Attainable` witness consumes `.ok`
and the route, and says nothing about what the write left behind. -/

/-! ### The world -/

/-- World state for the configuration call: empty storage, so the
configuration cell reads zero and the store is priced as a set. -/
def configWorldState : State := breakerState Stor.empty

/-- The one warm accessed key at message entry: the configuration slot the
body both reads and writes.  Warm at entry is a choice, not a fact about the
contract — it just keeps the walk's `SLOAD` and `SSTORE` on the same base
`Devm`, and membership is settled by the `insert` rather than by deciding a
`HashSet`. -/
def configWorldKeys : Std.HashSet (Adr × B256) :=
  Std.HashSet.emptyWithCapacity.insert (configWorldOwner, pauseDurationSlot)

/-- The concrete admin `setPauseDuration(1814400)` call.  The gas is the exact
inclusive charge: `setPauseDurationDispatchGas` plus the body's `21498`. -/
def configWorldMsg : Msg :=
  breakerMsg configWorldAdmin Stor.empty 0
    (setPauseDurationCalldata configWorldDuration) configWorldKeys 21649

def configWorldSevm : Sevm := initSevm configWorldMsg

def configWorldPre : Devm := initDevm configWorldMsg

/-! ### Frame, calldata and storage facts -/

theorem configWorld_currentTarget :
    configWorldSevm.currentTarget = configWorldOwner := rfl

theorem configWorld_value : configWorldSevm.value = 0 := rfl

theorem configWorld_static : configWorldSevm.isStatic = false := rfl

theorem configWorld_codeAddress :
    configWorldSevm.codeAddress = some configWorldSevm.currentTarget := rfl

theorem configWorld_admin :
    configWorldSevm.caller.toB256 = officialParams.admin := rfl

theorem configWorld_data :
    configWorldSevm.data = setPauseDurationCalldata configWorldDuration := rfl

theorem configWorld_codeBytes :
    configWorldSevm.code.toList = lidoCircuitBreakerCode officialParams :=
  breakerMsg_codeBytes configWorldAdmin Stor.empty 0
    (setPauseDurationCalldata configWorldDuration) configWorldKeys 21649

theorem configWorld_dataLength :
    configWorldSevm.data.length.toB256 = 36 := by
  rw [configWorld_data]
  simp only [setPauseDurationCalldata, List.length_append,
    abiSelectorBytes_length, B256.length_toBytes]
  decide +kernel

/-- The selector really is `setPauseDuration(uint256)`'s.  At a fully concrete
message this is one kernel evaluation — both the `keccak` of the signature and
the 36 calldata bytes are closed — so the hand-rolled bit reasoning
`registerPauserCalldata_spec` needs for a *generic* argument word is not
required here. -/
theorem configWorld_selector :
    Sevm.selector configWorldSevm = selector "setPauseDuration" [.uint256] := by
  decide +kernel

theorem configWorld_arg :
    Sevm.dataWord configWorldSevm (32 * 0 + 4) = configWorldDuration := by
  apply dataWord_of_append
    (pre := abiSelectorBytes (selector "setPauseDuration" [.uint256]))
    (w := configWorldDuration) (post := [])
  · rw [abiSelectorBytes_length]
    rfl
  · simpa [setPauseDurationCalldata] using configWorld_data

theorem configWorld_warm :
    (⟨configWorldSevm.currentTarget, pauseDurationSlot⟩ : Adr × B256) ∈
      configWorldPre.accessedStorageKeys :=
  Std.HashSet.mem_insert_self

theorem configWorld_old :
    configWorldPre.getStorVal configWorldSevm.currentTarget
      pauseDurationSlot = 0 := by
  change (configWorldState.get configWorldOwner).stor.get pauseDurationSlot = 0
  rw [configWorldState, breakerState_stor]
  rfl

theorem configWorld_orig :
    getOrigStorVal configWorldSevm configWorldSevm.currentTarget
      pauseDurationSlot = 0 := by
  change (configWorldState.get configWorldOwner).stor.get pauseDurationSlot = 0
  rw [configWorldState, breakerState_stor]
  rfl

/-- The configured duration clears both immutable bounds inclusively and is
nonzero, so the two guard branches fall through and the store is priced as a
set rather than an update. -/
theorem configWorld_bounds :
    officialParams.minPauseDuration ≤ configWorldDuration ∧
      configWorldDuration ≤ officialParams.maxPauseDuration ∧
      configWorldDuration ≠ 0 :=
  ⟨by decide, by decide, by decide⟩

/-! ### The walk

One `func_run` for the whole body, and one for the dispatcher.  Neither states
an effect: the storage word, the emitted `PauseDurationUpdated` record and the
poststate gas are all reachable from these derivations and none of them is
what `Attainable` consumes, so restating them would be surface without a
consumer. -/

private theorem configWorld_getStorVal_addLog {d : Devm} {l : Log} {a : Adr}
    {k : B256} : (d.addLog l).getStorVal a k = d.getStorVal a k := rfl

set_option maxRecDepth 16384 in
/-- Exact successful `setPauseDuration` body: the static-argument guard, the
admin guard and both configured-bound guards fall the right way, the
configuration cell is read for the event and then set, and the whole body costs
`21498` — `setHeartbeatInterval`'s measured warm zero-to-nonzero charge, which
is the same number because the two functions are structurally identical. -/
theorem setPauseDuration_body_runCompiledTo
    (fs : List Func) (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (duration : B256) (G : Nat)
    (hdata : sevm.data.length.toB256 <? 36 = 0)
    (hadmin : sevm.caller.toB256 = dp.admin)
    (harg : Sevm.dataWord sevm (32 * 0 + 4) = duration)
    (hmin : dp.minPauseDuration ≤ duration)
    (hmax : duration ≤ dp.maxPauseDuration)
    (hnonzero : duration ≠ 0)
    (hold : base.getStorVal sevm.currentTarget pauseDurationSlot = 0)
    (horig : getOrigStorVal sevm sevm.currentTarget pauseDurationSlot = 0)
    (hwarm : (⟨sevm.currentTarget, pauseDurationSlot⟩ : Adr × B256) ∈
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + 21498⟩)
        (setPauseDuration dp) (.ok post) := by
  have hsstoreCost : sstoreValueCost 0 0 duration = 20000 := by
    rw [sstoreValueCost, if_pos ⟨rfl, hnonzero.symm⟩, if_pos rfl]
    norm_num [gasStorageSet]
  apply Exists.intro
  unfold setPauseDuration requireStaticArgs onlyAdmin arg cdl pushDeployWord
    mstoreAt logWith
  func_run [0, 1, 0, 0, 3, 3, 1262, 20000]
  case h_val => simp [B256.eqCheck, hadmin]
  case h_val => rw [harg]; simp [B256.ltCheck, B256.not_lt.mpr hmin]
  case h_val => rw [harg]; simp [B256.gtCheck, B256.not_lt.mpr hmax]
  case h_ext =>
    rw [show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_empty_word
  case h_ext =>
    rw [show ((1 : B256) * 32).toNat = 32 by decide,
      show ((0 : B256) * 32).toNat = 0 by decide]
    exact Devm.extCost_of_size Mem.size_write_word (by decide)
  case h_cost =>
    rw [show ((2 : B256) * 32).toNat = 64 by decide,
      show ((0 : B256) * 32).toNat = 0 by decide,
      show ((1 : B256) * 32).toNat = 32 by decide]
    rw [Devm.extCost_of_size (by
      rw [Mem.size_write_word_at, Mem.size_write_word]) rfl]
    decide
  case h_cost =>
    simpa only [Devm.getStorVal_setMach, configWorld_getStorVal_addLog, horig,
      hold, harg] using hsstoreCost
  case a => exact Func.RunCompiledTo.last rfl

/-- Dispatcher charge from the runtime's entry `JUMPDEST` to
`setPauseDuration`'s first body instruction: two pivots taken to the right
subtree, two selector misses, the match, and the chain's `POP`. -/
def setPauseDurationDispatchGas : Nat := 151

set_option maxRecDepth 16384 in
/-- Exact dispatcher bridge for any terminal outcome of the selected
pause-duration setter body. -/
theorem setPauseDuration_dispatch_runCompiledTo
    (dp : DeployParams) (sevm : Sevm) (base : Devm)
    (bodyGas G : Nat) (out : Execution)
    (hdata : sevm.data.length.toB256 = 36)
    (hvalue : sevm.value = 0)
    (hselector : Sevm.selector sevm = selector "setPauseDuration" [.uint256])
    (hcode : sevm.code.toList = lidoCircuitBreakerCode dp)
    (hbody : Func.RunCompiledTo (runtimeMain dp :: aux) sevm
      (base.setMach ⟨[], Mem.empty, G + bodyGas⟩)
      (setPauseDuration dp) out) :
    Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty,
        G + setPauseDurationDispatchGas + bodyGas⟩)
      (runtime dp) out ∧
      some sevm.code.toList = Prog.compile (runtime dp) := by
  refine ⟨?_, ?_⟩
  · refine Prog.runCompiledTo_intro
      (mid := base.setMach ⟨[], Mem.empty, G + 150 + bodyGas⟩)
      (G := G + 150 + bodyGas) ?_ ?_ ?_
    · simp only [Devm.gasLeft_setMach, setPauseDurationDispatchGas, gJumpdest]
      omega
    · rfl
    · have hlt : sevm.data.length.toB256 <? 4 = 0 := by
        rw [hdata]
        decide
      have hor : B256.or 0 sevm.value = 0 := by
        rw [hvalue]
        decide
      have hselector' :
          Sevm.dataWord sevm 0 >>> B256.toNat 224 =
            selector "setPauseDuration" [.uint256] := hselector
      unfold runtime runtimeMain hybridDispatchWith splitDispatch
        linearDispatchWith firstSelector funcs
      simp only [List.take, List.drop, List.head?, Option.map, Option.getD]
      func_run (31) [0, 0,
        selector "setPauseDuration" [.uint256],
        0, 0, 0, 0, 1]
      have hboundary : G + 150 + bodyGas - 150 = G + bodyGas := by
        omega
      simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach, hboundary,
        runtimeMain, hybridDispatchWith, splitDispatch, firstSelector, funcs,
        List.take, List.drop, List.head?, Option.map, Option.getD,
        linearDispatchWith] using hbody
  · rw [hcode, lidoCircuitBreakerCode_compile]

/-- The concrete configuration call runs, gas-exactly, on the production
runtime. -/
theorem configWorld_run :
    ∃ post,
      Prog.RunCompiledTo configWorldSevm configWorldPre
        (runtime officialParams) (.ok post) ∧
      some configWorldSevm.code.toList =
        Prog.compile (runtime officialParams) := by
  obtain ⟨post, hbody⟩ :=
    setPauseDuration_body_runCompiledTo (runtimeMain officialParams :: aux)
      officialParams configWorldSevm configWorldPre configWorldDuration 0
      (by rw [configWorld_dataLength]; decide) configWorld_admin configWorld_arg
      configWorld_bounds.1 configWorld_bounds.2.1 configWorld_bounds.2.2
      configWorld_old configWorld_orig configWorld_warm configWorld_static
  obtain ⟨hrun, hcompile⟩ :=
    setPauseDuration_dispatch_runCompiledTo officialParams configWorldSevm
      configWorldPre 21498 0 (.ok post) configWorld_dataLength configWorld_value
      configWorld_selector configWorld_codeBytes hbody
  have hentry :
      configWorldPre.setMach ⟨[], Mem.empty,
        0 + setPauseDurationDispatchGas + 21498⟩ = configWorldPre := rfl
  rw [hentry] at hrun
  exact ⟨post, hrun, hcompile⟩

/-! ### The route

Ten crossings, none of them priced.  The five dispatcher crossings read the
calldata selector off the stack exactly as `dispatch_routeTo_registerPauser`
does — `routeTo_branch*_frame`, because the selector word has to survive each
comparison — and the five guards are settled by their certified-reverting
siblings, which need no frame at all. -/

/-- `setPauseDuration`'s dispatched entry: the selector chain's `POP` followed
by `requireStaticArgs 1`'s guard line. -/
def setPauseDurationEntryTest : Line :=
  [Ninst.pop, Ninst.pushB256 (Nat.toB256 (4 + 32 * 1)), Ninst.calldatasize,
   Ninst.lt]

/-- The configured-minimum guard line. -/
def pauseDurationMinTest (dp : DeployParams) : Line :=
  [pushDeployWord dp.minPauseDuration] ++ arg 0 ++ [Ninst.lt]

/-- The configured-maximum guard line. -/
def pauseDurationMaxTest (dp : DeployParams) : Line :=
  [pushDeployWord dp.maxPauseDuration] ++ arg 0 ++ [Ninst.gt]

/-- From the last guard to the configuration `SSTORE`: the old-value read, the
two staged event words, the `LOG1` and the new value. -/
def setPauseDurationConfigPrefix : Line :=
  [Ninst.pushB256 pauseDurationSlot, Ninst.sload] ++ mstoreAt 0 ++ arg 0 ++
    mstoreAt 1 ++ [Ninst.pushB256 pauseDurationUpdatedEvent] ++
    logWith 0 0 2 ++ arg 0 ++ [Ninst.pushB256 pauseDurationSlot]
/-- Structural source position of the `setPauseDuration.config` `SSTORE`:
inventory index `0`, source function `0`, sixty-four steps.  Unlike every other
path in this module it is not rooted at an auxiliary table slot, because no
`.call` intervenes between the program entry and this write. -/
def setPauseDurationConfigPath : Prog.SourcePath :=
  ⟨0,
    sourceRests 5 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 7 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 4 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 4 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 4 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 15⟩

set_option maxRecDepth 16384 in
/-- The complete route from program entry to the `setPauseDuration.config`
`SSTORE`, across all ten branches.  Only the calldata selector is an execution
premise: five crossings are decided on it and the other five have
certified-reverting siblings, so no branch word, no storage chain and no memory
image appear anywhere in the route.

The accumulated steps are closed data, so they reduce definitionally to
`setPauseDurationConfigPath.steps` and the head designation needs no rewriting
step of its own. -/
theorem runtimeMain_routeTo_setPauseDurationConfig (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (runtime dp).main (.ok post))
    (selectorEq :
      Sevm.selector sevm = selector "setPauseDuration" [.uint256]) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h setPauseDurationConfigPath
      (.reg .sstore) := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry _run tail => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail (fuel := 4) (by rfl)
    (fun _body arm => ?_)
  refine routeTo_line fsig arm (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack :=
    prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  refine routeTo_branchLeft_frame tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 ⟨_, hpop2.stack⟩
  refine routeTo_line (splitTest (selector "MIN_HEARTBEAT_INTERVAL" [])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  refine routeTo_branchLeft_frame tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 ⟨_, hpop4.stack⟩
  refine routeTo_line (linearTest (selector "MIN_HEARTBEAT_INTERVAL" [])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  refine routeTo_branchLeft_frame tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 hpop6 tail6 => ?_)
  have p6 := tail_of_stack_prefix p5 ⟨_, hpop6.stack⟩
  refine routeTo_line (linearTest (selector "heartbeatExpiry" [.address]))
    tail6 (fun _s7 run7 tail7 => ?_)
  have p7 := prefix_of_linearTest p6 run7
  refine routeTo_branchLeft_frame tail7
    (fun _w _rest hs => by rw [head_of_stack_prefix p7 hs]; decide)
    (fun _s8 hpop8 tail8 => ?_)
  have p8 := tail_of_stack_prefix p7 ⟨_, hpop8.stack⟩
  refine routeTo_line (linearTest (selector "setPauseDuration" [.uint256]))
    tail8 (fun _s9 run9 tail9 => ?_)
  have p9 := prefix_of_linearTest p8 run9
  refine routeTo_branchRight_frame tail9
    (fun _w _rest hs => by rw [head_of_stack_prefix p9 hs]; decide)
    (fun _s10 _w10 _hpop10 tail10 => ?_)
  refine routeTo_line setPauseDurationEntryTest tail10
    (fun _s11 _run11 tail11 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail11 (fuel := 4) (by rfl)
    (fun _s12 arm12 => ?_)
  refine routeTo_line (adminTest dp) arm12 (fun _s13 _run13 tail13 => ?_)
  refine routeTo_branchRight_of_leftRevertsOk tail13 (fuel := 8) (by rfl)
    (fun _s14 arm14 => ?_)
  refine routeTo_line (pauseDurationMinTest dp) arm14
    (fun _s15 _run15 tail15 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail15 (fuel := 8) (by rfl)
    (fun _s16 arm16 => ?_)
  refine routeTo_line (pauseDurationMaxTest dp) arm16
    (fun _s17 _run17 tail17 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail17 (fuel := 8) (by rfl)
    (fun _s18 arm18 => ?_)
  refine routeTo_line setPauseDurationConfigPrefix arm18
    (fun _s19 _run19 write => ?_)
  exact routeTo_head write setPauseDurationConfigPath

/-! ### Pinning the row, and the witness -/

/-- Only inventory index `0` — `.setPauseDurationConfig` — nominates a site
whose source path is `setPauseDurationConfigPath`. -/
theorem setPauseDurationConfig_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some setPauseDurationConfigPath) →
        index = 0 := by
  decide +kernel

/-- The `setPauseDuration.config` row is attained with the
`.adminConfiguration` role.

Unconditional, and at a *different* world from the six above:
`attainable_of_route` is tied to the fresh registration walk, whose calldata
selects `registerPauser`, so this row cannot borrow it.  What it borrows
instead is `attainable_of_entryRoute`, which is that tail with the world
abstracted away; the row-specific input is one index pin and one decidable
membership fact, because this row's `permittedRoles` is the singleton
`[.adminConfiguration]`. -/
theorem attainable_setPauseDurationConfig_adminConfiguration :
    Attainable officialParams .setPauseDurationConfig .adminConfiguration := by
  refine attainable_of_entryRoute (ca := configWorldOwner)
    configWorld_currentTarget ?_
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path setPauseDurationConfig_index_pin found
        pathEq)
    (by decide) configWorld_run
    (fun _devm _post h =>
      runtimeMain_routeTo_setPauseDurationConfig officialParams h
        configWorld_selector)
  rw [configWorld_codeAddress, configWorld_currentTarget]

/-! ## The `setHeartbeatInterval.config` row, at its own world

Inventory index `1`, and the cheapest leg in the module.  `setHeartbeatInterval`
is `setPauseDuration`'s exact structural twin — the same `requireStaticArgs 1`,
the same `onlyAdmin`, the same pair of configured-bound guards with
`.call`-to-error siblings, the same store-and-log tail — so the guard half of
its route is `setPauseDuration`'s with four names changed.

Nothing is restated for the walk itself.  `Blanc/LidoCircuitBreakerAccess.lean`
already carries this endpoint's exact dispatcher bridge and body theorems, and
that module sits in this one's import closure, so `intervalWorld_run` is one
application of `setHeartbeatInterval_runCompiledTo_zero_of_inclusive` rather
than a second `func_run` pair.  That is the whole reason index `0` needed its
own `setPauseDuration_body_runCompiledTo` and this row needs nothing: the AT3
family covers the interval setter and has no pause-duration counterpart.

The dispatcher half is **not** shared, because the two selectors land in
different chains of the 5/4/4/4 hybrid.  `setPauseDuration` is entry 16 of 17
and sits third in the fourth chain; `setHeartbeatInterval` is entry 9 and sits
**last** in the second.  Two consequences, both visible in the path: the top
pivot is taken jumped here and fall-through there, and a chain's last entry
compares without a `DUP` and enters its body without a `POP`, so this route's
matching crossing contributes `replicate 2 .rest` where `setPauseDuration`'s
contributes `replicate 3 .rest`, and its entry line is three instructions
rather than four.  Sixty-six steps against sixty-four. -/

/-! ### The world -/

/-- The configured heartbeat interval: `officialConstructorArgs`' own initial
value, which sits strictly inside the immutable `[2592000, 94608000]` bounds. -/
def intervalWorldInterval : B256 := 31536000

/-- The one warm accessed key at message entry: the configuration slot the body
both reads and writes.  Warm at entry is a choice, not a fact about the
contract, exactly as at the pause-duration world. -/
def intervalWorldKeys : Std.HashSet (Adr × B256) :=
  Std.HashSet.emptyWithCapacity.insert
    (configWorldOwner, heartbeatIntervalSlot)

/-- The concrete admin `setHeartbeatInterval(31536000)` call.  The gas is the
exact inclusive charge: `setHeartbeatIntervalDispatchGas` plus
`setHeartbeatIntervalBodyGasWarmSet`, which are `169` and `21498`. -/
def intervalWorldMsg : Msg :=
  breakerMsg configWorldAdmin Stor.empty 0
    (setHeartbeatIntervalCalldata intervalWorldInterval) intervalWorldKeys
    21667

def intervalWorldSevm : Sevm := initSevm intervalWorldMsg

def intervalWorldPre : Devm := initDevm intervalWorldMsg

/-! ### Frame, calldata and storage facts -/

theorem intervalWorld_currentTarget :
    intervalWorldSevm.currentTarget = configWorldOwner := rfl

theorem intervalWorld_value : intervalWorldSevm.value = 0 := rfl

theorem intervalWorld_static : intervalWorldSevm.isStatic = false := rfl

theorem intervalWorld_codeAddress :
    intervalWorldSevm.codeAddress = some intervalWorldSevm.currentTarget := rfl

theorem intervalWorld_admin :
    intervalWorldSevm.caller.toB256 = officialParams.admin := rfl

theorem intervalWorld_data :
    intervalWorldSevm.data =
      setHeartbeatIntervalCalldata intervalWorldInterval := rfl

theorem intervalWorld_codeBytes :
    intervalWorldSevm.code.toList = lidoCircuitBreakerCode officialParams :=
  breakerMsg_codeBytes configWorldAdmin Stor.empty 0
    (setHeartbeatIntervalCalldata intervalWorldInterval) intervalWorldKeys
    21667

theorem intervalWorld_dataLength :
    intervalWorldSevm.data.length.toB256 = 36 := by
  rw [intervalWorld_data]
  simp only [setHeartbeatIntervalCalldata, List.length_append,
    abiSelectorBytes_length, B256.length_toBytes]
  decide +kernel

/-- The selector really is `setHeartbeatInterval(uint256)`'s.  One kernel
evaluation at a fully concrete message, as at the pause-duration world. -/
theorem intervalWorld_selector :
    Sevm.selector intervalWorldSevm =
      selector "setHeartbeatInterval" [.uint256] := by
  decide +kernel

theorem intervalWorld_arg :
    Sevm.dataWord intervalWorldSevm (32 * 0 + 4) = intervalWorldInterval := by
  apply dataWord_of_append
    (pre := abiSelectorBytes (selector "setHeartbeatInterval" [.uint256]))
    (w := intervalWorldInterval) (post := [])
  · rw [abiSelectorBytes_length]
    rfl
  · simpa [setHeartbeatIntervalCalldata] using intervalWorld_data

theorem intervalWorld_warm :
    (⟨intervalWorldSevm.currentTarget, heartbeatIntervalSlot⟩ : Adr × B256) ∈
      intervalWorldPre.accessedStorageKeys :=
  Std.HashSet.mem_insert_self

theorem intervalWorld_old :
    intervalWorldPre.getStorVal intervalWorldSevm.currentTarget
      heartbeatIntervalSlot = 0 := by
  change ((breakerState Stor.empty).get configWorldOwner).stor.get
    heartbeatIntervalSlot = 0
  rw [breakerState_stor]
  rfl

theorem intervalWorld_orig :
    getOrigStorVal intervalWorldSevm intervalWorldSevm.currentTarget
      heartbeatIntervalSlot = 0 := by
  change ((breakerState Stor.empty).get configWorldOwner).stor.get
    heartbeatIntervalSlot = 0
  rw [breakerState_stor]
  rfl

/-- The configured interval clears both immutable bounds inclusively and is
nonzero, so the two guard branches fall through and the store is priced as a
set rather than an update. -/
theorem intervalWorld_bounds :
    officialParams.minHeartbeatInterval ≤ intervalWorldInterval ∧
      intervalWorldInterval ≤ officialParams.maxHeartbeatInterval ∧
      intervalWorldInterval ≠ 0 :=
  ⟨by decide, by decide, by decide⟩

/-- The concrete configuration call runs, gas-exactly, on the production
runtime.  Everything here comes from the landed AT3 family; this world supplies
only its premises. -/
theorem intervalWorld_run :
    ∃ post,
      Prog.RunCompiledTo intervalWorldSevm intervalWorldPre
        (runtime officialParams) (.ok post) ∧
      some intervalWorldSevm.code.toList =
        Prog.compile (runtime officialParams) := by
  obtain ⟨post, hrun, _hgas, _hstore, _hlogs, _hexpiries, hcompile⟩ :=
    setHeartbeatInterval_runCompiledTo_zero_of_inclusive officialParams
      intervalWorldSevm intervalWorldPre intervalWorldInterval 0
      intervalWorld_dataLength intervalWorld_value intervalWorld_selector
      intervalWorld_codeAddress intervalWorld_codeBytes intervalWorld_admin
      intervalWorld_arg intervalWorld_bounds.1 intervalWorld_bounds.2.1
      intervalWorld_old intervalWorld_orig intervalWorld_warm
      intervalWorld_static intervalWorld_bounds.2.2
  have hentry :
      intervalWorldPre.setMach ⟨[], Mem.empty,
        0 + setHeartbeatIntervalDispatchGas +
          setHeartbeatIntervalBodyGasWarmSet⟩ = intervalWorldPre := rfl
  rw [hentry] at hrun
  exact ⟨post, hrun, hcompile⟩

/-! ### The route

Eleven crossings, none of them priced.  Six read the calldata selector off the
stack — one more than the pause-duration route, because the second chain is
entered one pivot deeper — and the remaining five are the guard cascade, each
settled by a certified-reverting sibling. -/

/-- `setHeartbeatInterval`'s dispatched entry: `requireStaticArgs 1`'s guard
line, with no leading `POP`.  This is the last-entry difference — the matched
body of a chain's final entry is entered directly, because that entry's
comparison already consumed the selector. -/
def setHeartbeatIntervalEntryTest : Line :=
  [Ninst.pushB256 (Nat.toB256 (4 + 32 * 1)), Ninst.calldatasize, Ninst.lt]

/-- The configured-minimum guard line. -/
def heartbeatIntervalMinTest (dp : DeployParams) : Line :=
  [pushDeployWord dp.minHeartbeatInterval] ++ arg 0 ++ [Ninst.lt]

/-- The configured-maximum guard line. -/
def heartbeatIntervalMaxTest (dp : DeployParams) : Line :=
  [pushDeployWord dp.maxHeartbeatInterval] ++ arg 0 ++ [Ninst.gt]

/-- From the last guard to the configuration `SSTORE`: the old-value read, the
two staged event words, the `LOG1` and the new value. -/
def setHeartbeatIntervalConfigPrefix : Line :=
  [Ninst.pushB256 heartbeatIntervalSlot, Ninst.sload] ++ mstoreAt 0 ++
    arg 0 ++ mstoreAt 1 ++
    [Ninst.pushB256 heartbeatIntervalUpdatedEvent] ++
    logWith 0 0 2 ++ arg 0 ++ [Ninst.pushB256 heartbeatIntervalSlot]

/-- Structural source position of the `setHeartbeatInterval.config` `SSTORE`:
inventory index `1`, source function `0`, sixty-six steps.  Two more than the
pause-duration path despite one fewer instruction in the entry line, because
the second chain sits one pivot deeper than the fourth. -/
def setHeartbeatIntervalConfigPath : Prog.SourcePath :=
  ⟨0,
    sourceRests 5 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 7 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 2 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 4 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 4 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 15⟩

set_option maxRecDepth 16384 in
/-- The complete route from program entry to the `setHeartbeatInterval.config`
`SSTORE`, across all eleven branches.  Only the calldata selector is an
execution premise, exactly as on the pause-duration route.

The final selector comparison is the chain's last, so it is crossed with
`routeTo_branchRight` rather than the `_frame` form: nothing after it reads the
selector, because nothing after it has the selector. -/
theorem runtimeMain_routeTo_setHeartbeatIntervalConfig (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (runtime dp).main (.ok post))
    (selectorEq :
      Sevm.selector sevm = selector "setHeartbeatInterval" [.uint256]) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h setHeartbeatIntervalConfigPath
      (.reg .sstore) := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry _run tail => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail (fuel := 4) (by rfl)
    (fun _body arm => ?_)
  refine routeTo_line fsig arm (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack :=
    prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  refine routeTo_branchRight_frame tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 _w2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 ⟨_, hpop2.stack⟩
  refine routeTo_line (splitTest (selector "getPauser" [.address])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  refine routeTo_branchLeft_frame tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 ⟨_, hpop4.stack⟩
  refine routeTo_line (linearTest (selector "getPauser" [.address])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  refine routeTo_branchLeft_frame tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 hpop6 tail6 => ?_)
  have p6 := tail_of_stack_prefix p5 ⟨_, hpop6.stack⟩
  refine routeTo_line (linearTest (selector "getPausables" [])) tail6
    (fun _s7 run7 tail7 => ?_)
  have p7 := prefix_of_linearTest p6 run7
  refine routeTo_branchLeft_frame tail7
    (fun _w _rest hs => by rw [head_of_stack_prefix p7 hs]; decide)
    (fun _s8 hpop8 tail8 => ?_)
  have p8 := tail_of_stack_prefix p7 ⟨_, hpop8.stack⟩
  refine routeTo_line (linearTest (selector "heartbeatInterval" [])) tail8
    (fun _s9 run9 tail9 => ?_)
  have p9 := prefix_of_linearTest p8 run9
  refine routeTo_branchLeft_frame tail9
    (fun _w _rest hs => by rw [head_of_stack_prefix p9 hs]; decide)
    (fun _s10 hpop10 tail10 => ?_)
  have p10 := tail_of_stack_prefix p9 ⟨_, hpop10.stack⟩
  refine routeTo_line
    (lastLinearTest (selector "setHeartbeatInterval" [.uint256])) tail10
    (fun _s11 run11 tail11 => ?_)
  have p11 := prefix_of_lastLinearTest p10 run11
  refine routeTo_branchRight tail11
    (fun _w _rest hs => by rw [head_of_stack_prefix p11 hs]; decide)
    (fun _s12 arm12 => ?_)
  refine routeTo_line setHeartbeatIntervalEntryTest arm12
    (fun _s13 _run13 tail13 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail13 (fuel := 4) (by rfl)
    (fun _s14 arm14 => ?_)
  refine routeTo_line (adminTest dp) arm14 (fun _s15 _run15 tail15 => ?_)
  refine routeTo_branchRight_of_leftRevertsOk tail15 (fuel := 8) (by rfl)
    (fun _s16 arm16 => ?_)
  refine routeTo_line (heartbeatIntervalMinTest dp) arm16
    (fun _s17 _run17 tail17 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail17 (fuel := 8) (by rfl)
    (fun _s18 arm18 => ?_)
  refine routeTo_line (heartbeatIntervalMaxTest dp) arm18
    (fun _s19 _run19 tail19 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail19 (fuel := 8) (by rfl)
    (fun _s20 arm20 => ?_)
  refine routeTo_line setHeartbeatIntervalConfigPrefix arm20
    (fun _s21 _run21 write => ?_)
  exact routeTo_head write setHeartbeatIntervalConfigPath

/-! ### Pinning the row, and the witness -/

/-- Only inventory index `1` — `.setHeartbeatIntervalConfig` — nominates a site
whose source path is `setHeartbeatIntervalConfigPath`. -/
theorem setHeartbeatIntervalConfig_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some setHeartbeatIntervalConfigPath) →
        index = 1 := by
  decide +kernel

/-- The `setHeartbeatInterval.config` row is attained with the
`.adminConfiguration` role.

Unconditional.  Like the pause-duration row it consumes
`attainable_of_entryRoute`, and like it its `permittedRoles` is the singleton
`[.adminConfiguration]`, so the reached role is forced by membership and the
two rows are exact rather than merely sound. -/
theorem attainable_setHeartbeatIntervalConfig_adminConfiguration :
    Attainable officialParams .setHeartbeatIntervalConfig
      .adminConfiguration := by
  refine attainable_of_entryRoute (ca := configWorldOwner)
    intervalWorld_currentTarget ?_
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path setHeartbeatIntervalConfig_index_pin
        found pathEq)
    (by decide) intervalWorld_run
    (fun _devm _post h =>
      runtimeMain_routeTo_setHeartbeatIntervalConfig officialParams h
        intervalWorld_selector)
  rw [intervalWorld_codeAddress, intervalWorld_currentTarget]

/-! ## The `heartbeat.expiry` row, at its own world

Inventory index `2`, and the module's only witness at a role that is neither
`.admin*` nor reached from a configuration setter.  `RuntimeWriteAuthority`'s
`.heartbeatExpiry` constructor demands two entry facts — the caller's count
slot is nonzero, and the caller is *strictly* live at entry — so the world is
the first here with non-empty deployed storage: a registered pauser with a
live expiry, at a deployment carrying a configured heartbeat interval.

Both facts come back out of the derivation rather than being asserted: the
authority payload is produced by
`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot`, so this leg never
constructs a `RuntimeWriteAuthority` and never restates its fields.  What the
world supplies is what the *body walk* consumes, and
`Blanc/LidoCircuitBreakerAccess.lean` already owns that walk exactly as it owns
the interval setter's: `heartbeat_runCompiledTo_of_checkedExtension` takes the
registered/live/interval facts and the checked-extension arithmetic and returns
the gas-exact successful run.

The route is again unpriced past the dispatcher.  All three body crossings —
the registered-caller test, the strict-liveness test and
`checkedHeartbeatExpiry`'s overflow test — have a sibling arm that is a `.call`
to a `runtimeError` or to `arithmeticPanic`, so the successful outcome settles
them without the storage or the timestamp appearing anywhere in the route.
Note what that means: the route does *not* prove the caller is a live pauser.
The body walk does, and the authority theorem re-derives it at the write. -/

/-! ### The world -/

/-- The registered pauser making the call, as an address. -/
def heartbeatWorldCaller : Adr := Nat.toAdr 9

/-- The same pauser as a storage-key payload. -/
def heartbeatWorldPauser : B256 := 9

/-- The pauser's assignment count.  Only its being nonzero is load-bearing. -/
def heartbeatWorldCount : B256 := 1

/-- Block timestamp at the heartbeat. -/
def heartbeatWorldTime : B256 := 10

/-- The pauser's expiry at entry: nonzero and strictly after the timestamp, so
the caller is live and the guard falls the right way. -/
def heartbeatWorldOldExpiry : B256 := 100

/-- The deployment's configured heartbeat interval. -/
def heartbeatWorldInterval : B256 := 2592000

/-- The expiry the heartbeat installs, `time + interval` computed without
overflow. -/
def heartbeatWorldExpiry : B256 := 2592010

/-- The deployed account storage: the configured interval, plus one registered
and live pauser. -/
def heartbeatWorldStor : Stor :=
  ((Stor.empty.set heartbeatIntervalSlot heartbeatWorldInterval).set
    (countSlot heartbeatWorldPauser) heartbeatWorldCount).set
    (expirySlot heartbeatWorldPauser) heartbeatWorldOldExpiry

/-- The three warm accessed keys at message entry: the two the guards read and
the interval the extension reads.  Warm at entry is a choice, not a fact about
the contract; it fixes the walk on the AT3 family's warm-update charge. -/
def heartbeatWorldKeys : Std.HashSet (Adr × B256) :=
  ((Std.HashSet.emptyWithCapacity.insert
    (configWorldOwner, heartbeatIntervalSlot)).insert
    (configWorldOwner, countSlot heartbeatWorldPauser)).insert
    (configWorldOwner, expirySlot heartbeatWorldPauser)

/-- The concrete registered-pauser `heartbeat()` call.  The gas is the exact
inclusive charge: `heartbeatDispatchGas` plus
`heartbeatBodySuccessGasWarmUpdate`, which are `192` and `4693`. -/
def heartbeatWorldMsg : Msg :=
  breakerMsg heartbeatWorldCaller heartbeatWorldStor heartbeatWorldTime
    heartbeatCalldata heartbeatWorldKeys 4885

def heartbeatWorldSevm : Sevm := initSevm heartbeatWorldMsg

def heartbeatWorldPre : Devm := initDevm heartbeatWorldMsg

/-! ### Slot separation

Three slots, three regions, all payloads below `2 ^ 252`, so
`slot_ne_of_region_ne` separates any two of them by region alone.  This is the
only place in the module that needs storage-key separation at all — the two
configuration worlds write one slot each. -/

private theorem heartbeatWorld_payload_one : (1 : B256).toNat < 2 ^ 252 := by
  change (1 : Nat) < 2 ^ 252
  norm_num

private theorem heartbeatWorld_payload_pauser :
    heartbeatWorldPauser.toNat < 2 ^ 252 := by
  unfold heartbeatWorldPauser
  change (9 : Nat) < 2 ^ 252
  norm_num

private theorem heartbeatWorld_expiry_ne_count :
    expirySlot heartbeatWorldPauser ≠ countSlot heartbeatWorldPauser := by
  simpa only [expirySlot, countSlot] using
    slot_ne_of_region_ne (leftRegion := expiryRegion)
      (rightRegion := countRegion) (left := heartbeatWorldPauser)
      (right := heartbeatWorldPauser)
      (by norm_num [expiryRegion]) (by norm_num [countRegion])
      heartbeatWorld_payload_pauser heartbeatWorld_payload_pauser
      (by norm_num [expiryRegion, countRegion])

private theorem heartbeatWorld_expiry_ne_interval :
    expirySlot heartbeatWorldPauser ≠ heartbeatIntervalSlot := by
  simpa only [expirySlot, heartbeatIntervalSlot] using
    slot_ne_of_region_ne (leftRegion := expiryRegion)
      (rightRegion := configRegion) (left := heartbeatWorldPauser)
      (right := (1 : B256))
      (by norm_num [expiryRegion]) (by norm_num [configRegion])
      heartbeatWorld_payload_pauser heartbeatWorld_payload_one
      (by norm_num [expiryRegion, configRegion])

private theorem heartbeatWorld_count_ne_interval :
    countSlot heartbeatWorldPauser ≠ heartbeatIntervalSlot := by
  simpa only [countSlot, heartbeatIntervalSlot] using
    slot_ne_of_region_ne (leftRegion := countRegion)
      (rightRegion := configRegion) (left := heartbeatWorldPauser)
      (right := (1 : B256))
      (by norm_num [countRegion]) (by norm_num [configRegion])
      heartbeatWorld_payload_pauser heartbeatWorld_payload_one
      (by norm_num [countRegion, configRegion])

/-! ### Frame, calldata and storage facts -/

theorem heartbeatWorld_currentTarget :
    heartbeatWorldSevm.currentTarget = configWorldOwner := rfl

theorem heartbeatWorld_value : heartbeatWorldSevm.value = 0 := rfl

theorem heartbeatWorld_static : heartbeatWorldSevm.isStatic = false := rfl

theorem heartbeatWorld_codeAddress :
    heartbeatWorldSevm.codeAddress = some heartbeatWorldSevm.currentTarget :=
  rfl

theorem heartbeatWorld_time :
    heartbeatWorldSevm.benvStat.time = heartbeatWorldTime := rfl

theorem heartbeatWorld_data : heartbeatWorldSevm.data = heartbeatCalldata := rfl

theorem heartbeatWorld_codeBytes :
    heartbeatWorldSevm.code.toList = lidoCircuitBreakerCode officialParams :=
  breakerMsg_codeBytes heartbeatWorldCaller heartbeatWorldStor
    heartbeatWorldTime heartbeatCalldata heartbeatWorldKeys 4885

theorem heartbeatWorld_dataLength :
    heartbeatWorldSevm.data.length.toB256 = 4 := by
  rw [heartbeatWorld_data]
  simp only [heartbeatCalldata, abiSelectorBytes_length]
  decide +kernel

/-- The selector really is `heartbeat()`'s.  One kernel evaluation at a fully
concrete message. -/
theorem heartbeatWorld_selector :
    Sevm.selector heartbeatWorldSevm = selector "heartbeat" [] := by
  decide +kernel

theorem heartbeatWorld_count :
    heartbeatWorldPre.getStorVal heartbeatWorldSevm.currentTarget
      (countSlot heartbeatWorldSevm.caller.toB256) = heartbeatWorldCount := by
  change ((breakerState heartbeatWorldStor).get configWorldOwner).stor.get
    (countSlot heartbeatWorldPauser) = heartbeatWorldCount
  rw [breakerState_stor, heartbeatWorldStor,
    Stor.get_set_ne _ heartbeatWorld_expiry_ne_count, Stor.get_set_self]

theorem heartbeatWorld_oldExpiry :
    heartbeatWorldPre.getStorVal heartbeatWorldSevm.currentTarget
      (expirySlot heartbeatWorldSevm.caller.toB256) =
      heartbeatWorldOldExpiry := by
  change ((breakerState heartbeatWorldStor).get configWorldOwner).stor.get
    (expirySlot heartbeatWorldPauser) = heartbeatWorldOldExpiry
  rw [breakerState_stor, heartbeatWorldStor, Stor.get_set_self]

theorem heartbeatWorld_origExpiry :
    getOrigStorVal heartbeatWorldSevm heartbeatWorldSevm.currentTarget
      (expirySlot heartbeatWorldSevm.caller.toB256) =
      heartbeatWorldOldExpiry := by
  change ((breakerState heartbeatWorldStor).get configWorldOwner).stor.get
    (expirySlot heartbeatWorldPauser) = heartbeatWorldOldExpiry
  rw [breakerState_stor, heartbeatWorldStor, Stor.get_set_self]

theorem heartbeatWorld_intervalValue :
    heartbeatWorldPre.getStorVal heartbeatWorldSevm.currentTarget
      heartbeatIntervalSlot = heartbeatWorldInterval := by
  change ((breakerState heartbeatWorldStor).get configWorldOwner).stor.get
    heartbeatIntervalSlot = heartbeatWorldInterval
  rw [breakerState_stor, heartbeatWorldStor,
    Stor.get_set_ne _ heartbeatWorld_expiry_ne_interval,
    Stor.get_set_ne _ heartbeatWorld_count_ne_interval, Stor.get_set_self]

theorem heartbeatWorld_warmCount :
    (⟨heartbeatWorldSevm.currentTarget,
      countSlot heartbeatWorldSevm.caller.toB256⟩ : Adr × B256) ∈
      heartbeatWorldPre.accessedStorageKeys := by
  change (configWorldOwner, countSlot heartbeatWorldPauser) ∈
    heartbeatWorldKeys
  rw [heartbeatWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr Std.HashSet.mem_insert_self)

theorem heartbeatWorld_warmExpiry :
    (⟨heartbeatWorldSevm.currentTarget,
      expirySlot heartbeatWorldSevm.caller.toB256⟩ : Adr × B256) ∈
      heartbeatWorldPre.accessedStorageKeys := by
  change (configWorldOwner, expirySlot heartbeatWorldPauser) ∈
    heartbeatWorldKeys
  rw [heartbeatWorldKeys]
  exact Std.HashSet.mem_insert_self

theorem heartbeatWorld_warmInterval :
    (⟨heartbeatWorldSevm.currentTarget, heartbeatIntervalSlot⟩ :
      Adr × B256) ∈ heartbeatWorldPre.accessedStorageKeys := by
  change (configWorldOwner, heartbeatIntervalSlot) ∈ heartbeatWorldKeys
  rw [heartbeatWorldKeys]
  exact Std.HashSet.mem_insert.mpr (Or.inr (Std.HashSet.mem_insert.mpr
    (Or.inr Std.HashSet.mem_insert_self)))

/-- The caller is strictly live at entry, its expiry is nonzero, and the
heartbeat genuinely moves it. -/
theorem heartbeatWorld_live :
    heartbeatWorldTime < heartbeatWorldOldExpiry ∧
      heartbeatWorldOldExpiry ≠ 0 ∧
      heartbeatWorldOldExpiry ≠ heartbeatWorldExpiry ∧
      heartbeatWorldCount ≠ 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- `time + interval` is exactly the installed expiry, and does not wrap. -/
theorem heartbeatWorld_extension :
    CheckedHeartbeatExtension heartbeatWorldTime heartbeatWorldInterval
      heartbeatWorldExpiry :=
  ⟨by decide, by decide⟩

/-- The concrete heartbeat call runs, gas-exactly, on the production runtime.
Everything here comes from the landed AT3 family; this world supplies only its
premises. -/
theorem heartbeatWorld_run :
    ∃ post,
      Prog.RunCompiledTo heartbeatWorldSevm heartbeatWorldPre
        (runtime officialParams) (.ok post) ∧
      some heartbeatWorldSevm.code.toList =
        Prog.compile (runtime officialParams) := by
  obtain ⟨post, hrun, _hgas, _hstore, _hlogs, hcompile⟩ :=
    heartbeat_runCompiledTo_of_checkedExtension officialParams
      heartbeatWorldSevm heartbeatWorldPre heartbeatWorldCount
      heartbeatWorldOldExpiry heartbeatWorldTime heartbeatWorldInterval
      heartbeatWorldExpiry 0
      heartbeatWorld_dataLength heartbeatWorld_value heartbeatWorld_selector
      heartbeatWorld_codeAddress heartbeatWorld_codeBytes heartbeatWorld_time
      heartbeatWorld_count heartbeatWorld_live.2.2.2 heartbeatWorld_oldExpiry
      heartbeatWorld_origExpiry heartbeatWorld_intervalValue
      heartbeatWorld_warmCount heartbeatWorld_warmExpiry
      heartbeatWorld_warmInterval heartbeatWorld_static heartbeatWorld_live.1
      heartbeatWorld_live.2.1 heartbeatWorld_live.2.2.1
      heartbeatWorld_extension
  have hentry :
      heartbeatWorldPre.setMach ⟨[], Mem.empty,
        0 + heartbeatDispatchGas + heartbeatBodySuccessGasWarmUpdate⟩ =
        heartbeatWorldPre := rfl
  rw [hentry] at hrun
  exact ⟨post, hrun, hcompile⟩

/-! ### The route

Eleven crossings.  Six are the dispatcher's, read off the calldata selector;
the remaining five — the entry guard and the three body guards, plus
`checkedHeartbeatExpiry`'s overflow test — are settled by certified-reverting
siblings.  `arithmeticPanic_revertsWithin` above is reused for the last of
them; it is the one certificate on any route in this module that needs
`decide +kernel`. -/

/-- `heartbeat`'s registered-caller test: the caller's count slot, loaded and
tested for zero. -/
def heartbeatCountTest : Line :=
  [Ninst.caller] ++ tagTop countRegion ++ [Ninst.sload, Ninst.iszero]

/-- `heartbeat`'s strict-liveness test: the caller's expiry slot against the
block timestamp.  The comparison is `timestamp < expiry`, so the successful arm
is the *jumped* one. -/
def heartbeatLiveTest : Line :=
  [Ninst.caller] ++ tagTop expiryRegion ++
    [Ninst.sload, Ninst.timestamp, Ninst.lt]

/-- `checkedHeartbeatExpiry`'s whole line, from the timestamp to the Solidity
0.8 overflow comparison. -/
def checkedHeartbeatExpiryTest : Line :=
  [Ninst.timestamp, Ninst.pushB256 heartbeatIntervalSlot, Ninst.sload,
   Ninst.add, Ninst.dup 0, Ninst.timestamp, Ninst.swap 0, Ninst.lt]

/-- From the overflow guard to the expiry `SSTORE`: the computed expiry is
duplicated, staged for the event, and the caller's expiry key is built. -/
def heartbeatExpiryStorePrefix : Line :=
  [Ninst.dup 0] ++ mstoreAt 0 ++ [Ninst.caller] ++ tagTop expiryRegion

/-- Structural source position of the `heartbeat.expiry` `SSTORE`: inventory
index `2`, source function `0`, sixty-five steps. -/
def heartbeatExpiryPath : Prog.SourcePath :=
  ⟨0,
    sourceRests 5 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 7 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 3 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 2 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 5 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 6 ++ [Prog.SourceStep.branchRight] ++
      sourceRests 8 ++ [Prog.SourceStep.branchLeft] ++
      sourceRests 6⟩

set_option maxRecDepth 16384 in
/-- The complete route from program entry to the `heartbeat.expiry` `SSTORE`,
across all eleven branches.  Only the calldata selector is an execution
premise: the registered-caller and strict-liveness facts this row's authority
carries are *not* used here, because each of their guards has a
certified-reverting sibling and a successful outcome already excludes it.

Stated at `officialParams` where its two siblings are stated at an arbitrary
`dp`, and the reason is `arithmeticPanic`.  Every other reverting sibling on
every route in this module is certified `by rfl`, which reduces under a free
deployment parameter; `arithmeticPanic` is `Func.revertData` of a `Panic(0x11)`
payload, whose certificate needs `decide +kernel` (see
`arithmeticPanic_revertsWithin`), and `decide` refuses an expected type
containing a free variable.  MEASURED, not assumed: the generic form was
attempted and rejected with exactly that message.  Nothing needs the generic
form — the witness instantiates at `officialParams` — so the premise is not
carried as a hypothesis either. -/
theorem runtimeMain_routeTo_heartbeatExpiry
    {sevm : Sevm} {devm post : Devm}
    (h : Func.RunCompiledTo ((runtime officialParams).main ::
      (runtime officialParams).aux) sevm devm
      (runtime officialParams).main (.ok post))
    (selectorEq : Sevm.selector sevm = selector "heartbeat" []) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h heartbeatExpiryPath
      (.reg .sstore) := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry _run tail => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail (fuel := 4) (by rfl)
    (fun _body arm => ?_)
  refine routeTo_line fsig arm (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack :=
    prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  refine routeTo_branchRight_frame tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 _w2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 ⟨_, hpop2.stack⟩
  refine routeTo_line (splitTest (selector "getPauser" [.address])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  refine routeTo_branchRight_frame tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 _w4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 ⟨_, hpop4.stack⟩
  refine routeTo_line (linearTest (selector "pauseDuration" [])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  refine routeTo_branchLeft_frame tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 hpop6 tail6 => ?_)
  have p6 := tail_of_stack_prefix p5 ⟨_, hpop6.stack⟩
  refine routeTo_line (linearTest (selector "MAX_PAUSE_DURATION" [])) tail6
    (fun _s7 run7 tail7 => ?_)
  have p7 := prefix_of_linearTest p6 run7
  refine routeTo_branchLeft_frame tail7
    (fun _w _rest hs => by rw [head_of_stack_prefix p7 hs]; decide)
    (fun _s8 hpop8 tail8 => ?_)
  have p8 := tail_of_stack_prefix p7 ⟨_, hpop8.stack⟩
  refine routeTo_line (linearTest (selector "ADMIN" [])) tail8
    (fun _s9 run9 tail9 => ?_)
  have p9 := prefix_of_linearTest p8 run9
  refine routeTo_branchLeft_frame tail9
    (fun _w _rest hs => by rw [head_of_stack_prefix p9 hs]; decide)
    (fun _s10 hpop10 tail10 => ?_)
  have p10 := tail_of_stack_prefix p9 ⟨_, hpop10.stack⟩
  refine routeTo_line
    (linearTest (selector "registerPauser" [.address, .address])) tail10
    (fun _s11 run11 tail11 => ?_)
  have p11 := prefix_of_linearTest p10 run11
  refine routeTo_branchLeft_frame tail11
    (fun _w _rest hs => by rw [head_of_stack_prefix p11 hs]; decide)
    (fun _s12 hpop12 tail12 => ?_)
  have p12 := tail_of_stack_prefix p11 ⟨_, hpop12.stack⟩
  refine routeTo_line (lastLinearTest (selector "heartbeat" [])) tail12
    (fun _s13 run13 tail13 => ?_)
  have p13 := prefix_of_lastLinearTest p12 run13
  refine routeTo_branchRight tail13
    (fun _w _rest hs => by rw [head_of_stack_prefix p13 hs]; decide)
    (fun _s14 arm14 => ?_)
  refine routeTo_line heartbeatCountTest arm14 (fun _s15 _run15 tail15 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail15 (fuel := 8) (by rfl)
    (fun _s16 arm16 => ?_)
  refine routeTo_line heartbeatLiveTest arm16 (fun _s17 _run17 tail17 => ?_)
  refine routeTo_branchRight_of_leftRevertsOk tail17 (fuel := 8) (by rfl)
    (fun _s18 arm18 => ?_)
  refine routeTo_line checkedHeartbeatExpiryTest arm18
    (fun _s19 _run19 tail19 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail19 (fuel := 16)
    arithmeticPanic_revertsWithin (fun _s20 arm20 => ?_)
  refine routeTo_line heartbeatExpiryStorePrefix arm20
    (fun _s21 _run21 write => ?_)
  exact routeTo_head write heartbeatExpiryPath

/-! ### Pinning the row, and the witness -/

/-- Only inventory index `2` — `.heartbeatExpiry` — nominates a site whose
source path is `heartbeatExpiryPath`. -/
theorem heartbeatExpiry_index_pin :
    ∀ index ∈ List.range 20,
      ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some heartbeatExpiryPath) →
        index = 2 := by
  decide +kernel

/-- The `heartbeat.expiry` row is attained with the `.heartbeatExpiry` role.

Unconditional.  Its `permittedRoles` is the singleton `[.heartbeatExpiry]`, so
like the two configuration rows the reached role is forced by membership; and
because the role is reached rather than merely permitted, that entry too is
exact rather than a sound upper bound.

What this does **not** say is worth stating.  `.heartbeatExpiry` and
`.adminConfiguration` are the two roles whose `writeSite` pins agree — both
live in the main function — so no refutation in this module separates them, and
this witness settles only that the listed role is attained at its own row. -/
theorem attainable_heartbeatExpiry_heartbeatExpiry :
    Attainable officialParams .heartbeatExpiry .heartbeatExpiry := by
  refine attainable_of_entryRoute (ca := configWorldOwner)
    heartbeatWorld_currentTarget ?_
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path heartbeatExpiry_index_pin found pathEq)
    (by decide) heartbeatWorld_run
    (fun _devm _post h =>
      runtimeMain_routeTo_heartbeatExpiry h heartbeatWorld_selector)
  rw [heartbeatWorld_codeAddress, heartbeatWorld_currentTarget]


/-! ## The three expiry rows on `registerAfterSet`'s replacement arms

Inventory indices `14`, `15` and `16`, all in source function 19 and all
behind `previousPauser ≠ 0`, so none of them is reachable at the fresh
registration world of the sections above.  They are attained at the two
concrete replacement worlds of
`Blanc/LidoCircuitBreakerReplacementWorld.lean` instead: one call reassigns a
target whose old pauser keeps another assignment (index 14, the retained arm),
and one reassigns a target whose old pauser keeps none (indices 15 and 16, the
old-last arm, whose two writes are two split points of one walk).

**Which rows these are.**  Read the note under *The expiry row on
`registerAfterSet`'s fresh arm* first.  `Func.sourceSites` visits
`registerAfterSet`'s fall-through arm — the `previousPauser ≠ 0` subtree —
before its jumped one, so the four expiry writes are ordered

* index 14 — `previousPauser ≠ 0`, old count retained, constructor named
  `.registerRetainedOldNewExpiry`;
* index 15 — the old pauser's expiry cleared, `.registerLastOldClear`;
* index 16 — the new pauser's expiry after that clear,
  `.registerLastOldNewExpiry`;
* index 17 — `previousPauser = 0`, the fresh registration, constructor named
  `.registerFreshExpiry`.

Nothing here depends on the names: every row is pinned by `sourceSite?` through
its own index pin, and the paths below were read off
`runtimePersistentSourceSites officialParams` rather than off the names.  That
independence is why the 14/17 name exchange changed no proof.

**What the replacement route costs above the fresh one.**  Two things, and
both are consequences of the arm being taken because storage says so.

First, the kernel's previous-pauser test can no longer keep its loaded key
anonymous.  At the fresh world *every* assignment slot holds zero, so the test
is settled for whatever word memory happens to supply; here the answer depends
on the slot being the registered target's, so the route carries a fourth memory
window — the target word — and reads the key back off it.

Second, `registerAfterSet`'s own old-count test is **storage**-valued at a
point where the walk has already written storage three times, which is a
situation no earlier route met.  What travels is not the whole store but the
one cell the test reads: `ReplOldCount` below is the old pauser's count slot
and nothing else.  It is established at message entry, carried across the
assignment write (a different region), *changed* by the kernel's own decrement,
carried across `afterOldPauser`'s increment (a different pauser's slot), and
finally read.  Those crossings are the reason `sstore_getStor_set` and
`sstore_getStor_setStorVal` appear in this module at all: the decrement needs
the written *value*, and the two writes it has to survive need only their
*keys*. -/

section Replacement

/-! ### The four windows, the tracked cell, and the lines they cross -/

/-- The three words `registerPauser`'s staging line lays down at a replacement
world.  The **target** window is the one `EntryWindows` has no counterpart for:
the fresh route never needs to name the loaded target word, and this one does.
-/
def ReplStagedWindows (devm : Devm) : Prop :=
  MemWordAt devm (targetWord * 32).toNat replWorldTarget ∧
    MemWordAt devm (newPauserWord * 32).toNat replWorldNewPauser ∧
    MemWordAt devm (continuationWord * 32).toNat 0

/-- Those three, plus the old pauser that `setPauserKernel` stages out of
storage. -/
def ReplKernelWindows (devm : Devm) : Prop :=
  ReplStagedWindows devm ∧
    MemWordAt devm (previousPauserWord * 32).toNat replWorldOldPauser

/-- The one storage cell the replacement route follows: the old pauser's
assignment count, at the deployment that owns it. -/
def ReplOldCount (devm : Devm) (value : B256) : Prop :=
  (Devm.getStor devm replWorldOwner).get (countSlot replWorldOldPauser) = value

/-- Transport all four windows across one crossing at once.  Every window
obligation on this route has the same shape, so the crossings below are one
line each. -/
theorem ReplKernelWindows.map {a b : Devm}
    (f : ∀ (offset : Nat) (w : B256), MemWordAt a offset w →
      MemWordAt b offset w)
    (windows : ReplKernelWindows a) : ReplKernelWindows b :=
  ⟨⟨f _ _ windows.1.1, f _ _ windows.1.2.1, f _ _ windows.1.2.2⟩,
    f _ _ windows.2⟩

/-- The kernel's assignment line writes at `previousPauserWord`, which is
below the target window and above the two the staging line left at
`newPauserWord` and `continuationWord`; none of the three overlaps it. -/
theorem ReplStagedWindows.acrossAppendPrefix {e : Sevm} {a b : Devm}
    (run : Line.Run e a setPauserKernelAppendPrefix b)
    (windows : ReplStagedWindows a) : ReplStagedWindows b :=
  ⟨windows.1.acrossAppendPrefix (by decide) run,
    windows.2.1.acrossAppendPrefix (by decide) run,
    windows.2.2.acrossAppendPrefix (by decide) run⟩

theorem ReplStagedWindows.map {a b : Devm}
    (f : ∀ (offset : Nat) (w : B256), MemWordAt a offset w →
      MemWordAt b offset w)
    (windows : ReplStagedWindows a) : ReplStagedWindows b :=
  ⟨f _ _ windows.1, f _ _ windows.2.1, f _ _ windows.2.2⟩

theorem ReplOldCount.acrossLine {e : Sevm} {a b : Devm} {l : Line}
    {value : B256} (inv : Line.Inv Devm.getStor l) (run : Line.Run e a l b)
    (hcount : ReplOldCount a value) : ReplOldCount b value := by
  unfold ReplOldCount at *
  rw [← Line.of_inv Devm.getStor inv run]
  exact hcount

theorem ReplOldCount.of_state {a b : Devm} {value : B256}
    (h : a.state = b.state) (hcount : ReplOldCount a value) :
    ReplOldCount b value := by
  unfold ReplOldCount at *
  rw [← getStor_of_state h]
  exact hcount

/-- The kernel's replacement arm, from the previous-pauser branch to the
`.call afterOldPauserSlot`: the old pauser's count is read, decremented and
written back. -/
def setPauserKernelDecrementPrefix : Line :=
  previousCountKey ++
    [Ninst.sload, Ninst.pushB256 1, Ninst.swap 0, Ninst.sub] ++
    previousCountKey ++ [Ninst.sstore]

/-- `afterOldPauser`'s fall-through arm continued across its own `SSTORE`.
The fresh route splits at that write because the write *is* its row; this one
crosses it. -/
def afterOldNewCountLine : Line := afterOldNewCountPrefix ++ [Ninst.sstore]

/-- `registerAfterSet`'s replacement arm, from the previous-pauser branch to
the old-count branch. -/
def registerPreviousCountCheck : Line :=
  previousCountKey ++ [Ninst.sload, Ninst.iszero]

/-- `registerAfterSet`'s old-last arm, from the old-count branch to the
retiring pauser's expiry clear. -/
def registerOldLastClearPrefix : Line :=
  Ninst.pushB256 0 :: (loadWord previousPauserWord ++ tagTop expiryRegion)

/-- From that clear to the new pauser's own expiry test: the zero-payload
`HeartbeatUpdated(oldPauser)` record, then the test. -/
def registerOldLastRecordPrefix : Line :=
  [Ninst.sstore, Ninst.pushB256 0] ++ mstoreAt 0 ++
    loadWord previousPauserWord ++
    [Ninst.pushB256 heartbeatUpdatedEvent] ++ logWith 1 0 1 ++
    memoryZeroCheck newPauserWord

theorem _root_.Blanc.MemWordAt.acrossPreviousCountKey
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a previousCountKey b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold previousCountKey at run
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s1, r1, run⟩
  exact (window.acrossLoadWord r1).acrossLine (by line_inv) run

theorem _root_.Blanc.MemWordAt.acrossDecrementPrefix
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a setPauserKernelDecrementPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold setPauserKernelDecrementPrefix at run
  rcases of_run_append previousCountKey run with ⟨_s1, r1, run⟩
  rcases of_run_append
    [Ninst.sload, Ninst.pushB256 1, Ninst.swap 0, Ninst.sub] run
    with ⟨_s2, r2, run⟩
  rcases of_run_append previousCountKey run with ⟨_s3, r3, run⟩
  exact (((window.acrossPreviousCountKey r1).acrossLine (by line_inv)
    r2).acrossPreviousCountKey r3).acrossLine (by line_inv) run

theorem _root_.Blanc.MemWordAt.acrossNewCountLine
    {e : Sevm} {a b : Devm} {offset : Nat}
    {w : B256} (run : Line.Run e a afterOldNewCountLine b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold afterOldNewCountLine at run
  rcases of_run_append afterOldNewCountPrefix run with ⟨_s1, r1, run⟩
  exact (window.acrossNewCountPrefix r1).acrossLine (by line_inv) run

theorem _root_.Blanc.MemWordAt.acrossPreviousCountCheck {e : Sevm} {a b : Devm}
    {offset : Nat} {w : B256}
    (run : Line.Run e a registerPreviousCountCheck b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold registerPreviousCountCheck at run
  rcases of_run_append previousCountKey run with ⟨_s1, r1, run⟩
  exact (window.acrossPreviousCountKey r1).acrossLine (by line_inv) run

theorem _root_.Blanc.MemWordAt.acrossOldLastClearPrefix {e : Sevm} {a b : Devm}
    {offset : Nat} {w : B256}
    (run : Line.Run e a registerOldLastClearPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold registerOldLastClearPrefix at run
  rcases Line.of_run_cons run with ⟨_s1, q1, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s2, r2, run⟩
  exact ((window.acrossNinst q1).acrossLoadWord r2).acrossLine (by line_inv) run

/-- The old-last record fragment.  Its one write is `mstoreAt 0`, the scratch
word every expiry record is built in, which misses all four windows. -/
theorem _root_.Blanc.MemWordAt.acrossOldLastRecordPrefix {e : Sevm} {a b : Devm}
    {offset : Nat} {w : B256}
    (miss : offset + 32 ≤ ((0 : B256) * 32).toNat ∨
      ((0 : B256) * 32).toNat + 32 ≤ offset)
    (run : Line.Run e a registerOldLastRecordPrefix b)
    (window : MemWordAt a offset w) : MemWordAt b offset w := by
  unfold registerOldLastRecordPrefix at run
  rcases of_run_append [Ninst.sstore, Ninst.pushB256 0] run with ⟨_s1, r1, run⟩
  rcases of_run_append (mstoreAt 0) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 heartbeatUpdatedEvent] run
    with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 1 0 1) run with ⟨_s5, r5, run⟩
  exact (((((window.acrossLine (by line_inv) r1).acrossMstoreAt miss
    r2).acrossLoadWord r3).acrossLine (by line_inv) r4).acrossLogWith
    r5).acrossMemoryZeroCheck run

/-! ### The staged words at a replacement world -/

/-- What the staging line stages: the call's two arguments at `targetWord` and
`newPauserWord`, and a zero continuation.  Same shape as
`freshWorld_stagedEntry`, with the target window kept rather than dropped. -/
theorem replWorld_stagedEntry {oldCount : B256} {gas : Nat} {stage post : Devm}
    (hmem : stage.memory = Mem.empty)
    (run : Line.Run (replWorldSevm oldCount gas) stage registerStagingLine
      post) :
    ReplStagedWindows post := by
  unfold registerStagingLine at run
  rcases of_run_append (arg 0) run with ⟨s1, r1, run⟩
  have p1 : Sevm.argWord (replWorldSevm oldCount gas) 0 :: [] <<+ s1.stack :=
    prefix_of_arg nil_pref r1
  have i1 : MemImage s1 [] :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r1).symm
      ⟨by rw [hmem]; exact Mem.wf_empty, by rw [hmem]; exact Mem.reads_empty⟩
  rcases of_run_append (mstoreAt targetWord) run with ⟨_s2, r2, run⟩
  obtain ⟨p2, hm2⟩ := of_run_mstoreAt_val r2 p1
  have w2 : MemWordAt _s2 (targetWord * 32).toNat replWorldTarget := by
    rw [← (replWorld_dataFacts oldCount gas).2.2.1]
    exact MemWordAt.of_write i1 hm2
  rcases of_run_append (arg 1) run with ⟨_s3, r3, run⟩
  have p3 := prefix_of_arg p2 r3
  have i3 : MemImage _s3 _ :=
    MemImage.of_memory_eq (Line.of_inv Devm.memory (by line_inv) r3).symm
      (i1.write hm2)
  rcases of_run_append (mstoreAt newPauserWord) run with ⟨_s4, r4, run⟩
  obtain ⟨p4, hm4⟩ := of_run_mstoreAt_val r4 p3
  have w4 : MemWordAt _s4 (newPauserWord * 32).toNat replWorldNewPauser := by
    rw [← (replWorld_dataFacts oldCount gas).2.2.2]
    exact MemWordAt.of_write i3 hm4
  have t4 : MemWordAt _s4 (targetWord * 32).toNat replWorldTarget :=
    (w2.acrossLine (by line_inv) r3).acrossMstoreAt (by decide) r4
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s5, r5, run⟩
  have p5 : (0 : B256) :: [] <<+ _s5.stack := by
    rcases Line.of_run_cons r5 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) p4
  rcases of_run_append (mstoreAt previousPauserWord) run with ⟨_s6, r6, run⟩
  obtain ⟨p6, _⟩ := of_run_mstoreAt_val r6 p5
  rcases of_run_append [Ninst.pushB256 0] run with ⟨_s7, r7, run⟩
  have p7 : (0 : B256) :: [] <<+ _s7.stack := by
    rcases Line.of_run_cons r7 with ⟨_u, qu, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qu) p6
  have t7 := ((t4.acrossLine (by line_inv) r5).acrossMstoreAt (by decide)
    r6).acrossLine (by line_inv) r7
  have n7 := ((w4.acrossLine (by line_inv) r5).acrossMstoreAt (by decide)
    r6).acrossLine (by line_inv) r7
  obtain ⟨_img7, image7⟩ := n7.memImage
  obtain ⟨_p8, hm8⟩ := of_run_mstoreAt_val run p7
  exact ⟨t7.acrossMstoreAt (by decide) run, n7.acrossMstoreAt (by decide) run,
    MemWordAt.of_write image7 hm8⟩

/-! ### The four priced crossings

Two branch words and two storage transitions.  Everything else on the route is
either a selector comparison, a certified-reverting sibling, or a memory word
read straight back off a window. -/

/-- The kernel's second branch word at a replacement world, with the two facts
the rest of the route reads off the same crossing: the old pauser lands in
memory, and the old pauser's count cell is untouched by the assignment write.

The target window is what makes any of this statable.  At the fresh world the
loaded key may stay anonymous because *every* assignment slot holds zero; here
the answer depends on the slot being the registered target's own, so the key
has to be named first. -/
theorem replWorld_previousPauserPresent {oldCount : B256} {gas : Nat}
    {devm devm' : Devm}
    (hstor : Devm.getStor devm = Devm.getStor (replWorldPre oldCount gas))
    (window : MemWordAt devm (targetWord * 32).toNat replWorldTarget)
    (run : Line.Run (replWorldSevm oldCount gas) devm
      setPauserKernelAppendPrefix devm') :
    (∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0) ∧
      MemWordAt devm' (previousPauserWord * 32).toNat replWorldOldPauser ∧
      ReplOldCount devm' oldCount := by
  unfold setPauserKernelAppendPrefix at run
  rcases of_run_append setPauserKernelAssignmentPrefix run with ⟨sA, rA, run⟩
  have hstorA : Devm.getStor sA = Devm.getStor (replWorldPre oldCount gas) :=
    (Line.of_inv Devm.getStor
      (by unfold setPauserKernelAssignmentPrefix; line_inv) rA).symm.trans hstor
  unfold setPauserKernelAssignmentPrefix at rA
  rcases Line.of_run_cons rA with ⟨s1, q1, rA⟩
  rcases Line.of_run_cons rA with ⟨s2, q2, rA⟩
  have p2 : replWorldTarget :: [] <<+ s2.stack :=
    prefix_of_loadWord_window window nil_pref
      (Line.Run.cons q1 (Line.Run.cons q2 Line.Run.nil))
  rcases Line.of_run_cons rA with ⟨s3, q3, rA⟩
  have p3 := prefix_of_push (of_run_pushB256 q3) p2
  rcases Line.of_run_cons rA with ⟨s4, q4, rA⟩
  have p4 : assignmentSlot replWorldTarget :: [] <<+ s4.stack :=
    prefix_of_or q4 p3
  have hstor4 : Devm.getStor s4 = Devm.getStor (replWorldPre oldCount gas) := by
    rw [← hstor]
    exact (Line.of_inv Devm.getStor (by line_inv)
      (Line.Run.cons q1 (Line.Run.cons q2 (Line.Run.cons q3
        (Line.Run.cons q4 Line.Run.nil))))).symm
  rcases Line.of_run_cons rA with ⟨s5, q5, rA⟩
  obtain ⟨v, p5, hv⟩ := prefix_of_sload q5 p4
  have hold : v = replWorldOldPauser := by
    rw [hv, replWorld_currentTarget,
      show Devm.getStorVal s4 replWorldOwner (assignmentSlot replWorldTarget) =
          (replWorldPre oldCount gas).getStorVal replWorldOwner
            (assignmentSlot replWorldTarget) from
        congrArg (fun f : Adr → Stor =>
          (f replWorldOwner).get (assignmentSlot replWorldTarget)) hstor4,
      replWorld_getStorVal]
    exact replWorld_stor_assignment oldCount
  rcases Line.of_run_cons rA with ⟨s6, q6, rA⟩
  have p6 : v :: v :: [] <<+ s6.stack := prefix_of_dup_val q6 (by show_nth) p5
  rcases Line.of_run_cons rA with ⟨s7, q7, rA⟩
  have p7 := prefix_of_push (of_run_pushB256 q7) p6
  rcases Line.of_run_cons rA with ⟨s8, q8, rA⟩
  obtain ⟨p8, hmem8⟩ := prefix_of_mstore_val q8 p7
  have target7 : MemWordAt s7 (targetWord * 32).toNat replWorldTarget :=
    ((((((window.acrossNinst q1).acrossMload q2).acrossNinst q3).acrossNinst
      q4).acrossNinst q5).acrossNinst q6).acrossNinst q7
  obtain ⟨_img7, image7⟩ := target7.memImage
  have staged : MemWordAt s8 (previousPauserWord * 32).toNat
      replWorldOldPauser := by
    rw [← hold]
    exact MemWordAt.of_write image7 hmem8
  have target8 : MemWordAt s8 (targetWord * 32).toNat replWorldTarget :=
    (((((window.acrossNinst q1).acrossMload q2).acrossNinst q3).acrossNinst
      q4).acrossNinst q5).acrossNinst q6 |>.acrossMstoreAt (by decide)
      (Line.Run.cons q7 (Line.Run.cons q8 Line.Run.nil))
  rcases Line.of_run_cons rA with ⟨s9, q9, rA⟩
  have p9 := prefix_of_push (of_run_pushB256 q9) p8
  rcases Line.of_run_cons rA with ⟨s10, q10, rA⟩
  obtain ⟨n, p10⟩ := prefix_of_mload q10 p9
  have target10 : MemWordAt s10 (targetWord * 32).toNat replWorldTarget :=
    (target8.acrossNinst q9).acrossMload q10
  rcases Line.of_run_cons rA with ⟨s11, q11, rA⟩
  rcases Line.of_run_cons rA with ⟨s12, q12, rA⟩
  have p12 : replWorldTarget :: n :: v :: [] <<+ s12.stack :=
    prefix_of_loadWord_window target10 p10
      (Line.Run.cons q11 (Line.Run.cons q12 Line.Run.nil))
  rcases Line.of_run_cons rA with ⟨s13, q13, rA⟩
  have p13 := prefix_of_push (of_run_pushB256 q13) p12
  rcases Line.of_run_cons rA with ⟨s14, q14, hnilA⟩
  cases hnilA
  have p14 : assignmentSlot replWorldTarget :: n :: v :: [] <<+ sA.stack :=
    prefix_of_or q14 p13
  have staged14 : MemWordAt sA (previousPauserWord * 32).toNat
      replWorldOldPauser :=
    ((((staged.acrossNinst q9).acrossMload q10).acrossNinst q11).acrossMload
      q12).acrossNinst q13 |>.acrossNinst q14
  rcases Line.of_run_cons run with ⟨s15, q15, run⟩
  rcases Line.of_run_cons run with ⟨s16, q16, hnil⟩
  cases hnil
  have p15 := prefix_of_sstore q15 p14
  have p16 := prefix_of_iszero q16 p15
  obtain ⟨_u, hset⟩ := sstore_getStor_setStorVal q15 p14
  rw [replWorld_currentTarget] at hset
  refine ⟨fun w rest hstack => ?_, (staged14.acrossNinst q15).acrossNinst q16,
    ?_⟩
  · rw [head_of_stack_prefix p16 hstack, hold]
    decide
  · show (Devm.getStor devm' replWorldOwner).get
      (countSlot replWorldOldPauser) = oldCount
    rw [← Line.of_inv Devm.getStor (by line_inv)
        (Line.Run.cons q16 Line.Run.nil),
      hset, Stor.get_set_ne _ replWorld_assignment_ne_oldCount, hstorA,
      replWorld_getStor]
    exact replWorld_stor_oldCount oldCount

/-- The kernel's own decrement: the old pauser's count cell holds one less
than it did. -/
theorem replWorld_countDecrement {oldCount : B256} {gas : Nat}
    {devm devm' : Devm} {value : B256}
    (window : MemWordAt devm (previousPauserWord * 32).toNat
      replWorldOldPauser)
    (hcount : ReplOldCount devm value)
    (run : Line.Run (replWorldSevm oldCount gas) devm
      setPauserKernelDecrementPrefix devm') :
    ReplOldCount devm' (value - 1) := by
  unfold setPauserKernelDecrementPrefix at run
  rcases of_run_append previousCountKey run with ⟨s1, r1, run⟩
  have hstor1 : Devm.getStor s1 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor
      (by unfold previousCountKey loadWord tagTop; line_inv) r1).symm
  have p1 : countSlot replWorldOldPauser :: [] <<+ s1.stack := by
    unfold previousCountKey at r1
    rcases of_run_append (loadWord previousPauserWord) r1 with ⟨_u1, l1, r1⟩
    have pu := prefix_of_loadWord_window window nil_pref l1
    unfold tagTop at r1
    rcases Line.of_run_cons r1 with ⟨_u2, o1, r1⟩
    rcases Line.of_run_cons r1 with ⟨_u3, o2, hnil⟩
    cases hnil
    exact prefix_of_or o2 (prefix_of_push (of_run_pushB256 o1) pu)
  have window1 := window.acrossPreviousCountKey r1
  rcases of_run_append
    [Ninst.sload, Ninst.pushB256 1, Ninst.swap 0, Ninst.sub] run
    with ⟨s2, r2, run⟩
  have hstor2 : Devm.getStor s2 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) r2).symm.trans hstor1
  have p2 : (value - 1) :: [] <<+ s2.stack := by
    rcases Line.of_run_cons r2 with ⟨_u1, o1, r2⟩
    obtain ⟨c, pc, hc⟩ := prefix_of_sload o1 p1
    have hcv : c = value := by
      rw [hc, replWorld_currentTarget]
      show (Devm.getStor s1 replWorldOwner).get
        (countSlot replWorldOldPauser) = value
      rw [hstor1]
      exact hcount
    rcases Line.of_run_cons r2 with ⟨_u2, o2, r2⟩
    have pd := prefix_of_push (of_run_pushB256 o2) pc
    rcases Line.of_run_cons r2 with ⟨_u3, o3, r2⟩
    have hswap : Stack.Swap (0 : Fin 16).val
        ((1 : B256) :: c :: []) (c :: (1 : B256) :: []) := Stack.swapCore_zero
    have ps := Stack.prefix_of_swap hswap (of_run_swap o3) pd
    rcases Line.of_run_cons r2 with ⟨_u4, o4, hnil⟩
    cases hnil
    rw [← hcv]
    exact prefix_of_sub o4 ps
  have window2 := window1.acrossLine (by line_inv) r2
  rcases of_run_append previousCountKey run with ⟨s3, r3, run⟩
  have hstor3 : Devm.getStor s3 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor
      (by unfold previousCountKey loadWord tagTop; line_inv) r3).symm.trans
      hstor2
  have p3 : countSlot replWorldOldPauser :: (value - 1) :: [] <<+ s3.stack := by
    unfold previousCountKey at r3
    rcases of_run_append (loadWord previousPauserWord) r3 with ⟨_u1, l1, r3⟩
    have pu := prefix_of_loadWord_window window2 p2 l1
    unfold tagTop at r3
    rcases Line.of_run_cons r3 with ⟨_u2, o1, r3⟩
    rcases Line.of_run_cons r3 with ⟨_u3, o2, hnil⟩
    cases hnil
    exact prefix_of_or o2 (prefix_of_push (of_run_pushB256 o1) pu)
  rcases Line.of_run_cons run with ⟨s4, q4, hnil⟩
  cases hnil
  have hset := sstore_getStor_set q4 p3
  rw [replWorld_currentTarget] at hset
  show (Devm.getStor devm' replWorldOwner).get
    (countSlot replWorldOldPauser) = value - 1
  rw [hset, Stor.get_set_self]

/-- `afterOldPauser`'s increment lands on the *new* pauser's count slot, so the
cell the route follows keeps its word. -/
theorem replWorld_newCountWrite {oldCount : B256} {gas : Nat}
    {devm devm' : Devm} {value : B256}
    (window : MemWordAt devm (newPauserWord * 32).toNat replWorldNewPauser)
    (hcount : ReplOldCount devm value)
    (run : Line.Run (replWorldSevm oldCount gas) devm afterOldNewCountLine
      devm') :
    ReplOldCount devm' value := by
  unfold afterOldNewCountLine afterOldNewCountPrefix at run
  rcases of_run_append newCountKey run with ⟨s1, r1, run⟩
  have hstor1 : Devm.getStor s1 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor
      (by unfold newCountKey loadWord tagTop; line_inv) r1).symm
  have p1 : countSlot replWorldNewPauser :: [] <<+ s1.stack := by
    unfold newCountKey at r1
    rcases of_run_append (loadWord newPauserWord) r1 with ⟨_u1, l1, r1⟩
    have pu := prefix_of_loadWord_window window nil_pref l1
    unfold tagTop at r1
    rcases Line.of_run_cons r1 with ⟨_u2, o1, r1⟩
    rcases Line.of_run_cons r1 with ⟨_u3, o2, hnil⟩
    cases hnil
    exact prefix_of_or o2 (prefix_of_push (of_run_pushB256 o1) pu)
  have window1 := window.acrossNewCountKey r1
  rcases of_run_append [Ninst.sload, Ninst.pushB256 1, Ninst.add] run
    with ⟨s2, r2, run⟩
  have hstor2 : Devm.getStor s2 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) r2).symm.trans hstor1
  have p2 : ∃ z : B256, z :: [] <<+ s2.stack := by
    rcases Line.of_run_cons r2 with ⟨_u1, o1, r2⟩
    obtain ⟨_c, pc, _hc⟩ := prefix_of_sload o1 p1
    rcases Line.of_run_cons r2 with ⟨_u2, o2, r2⟩
    have pd := prefix_of_push (of_run_pushB256 o2) pc
    rcases Line.of_run_cons r2 with ⟨_u3, o3, hnil⟩
    cases hnil
    exact ⟨_, prefix_of_add o3 pd⟩
  have window2 := window1.acrossLine (by line_inv) r2
  obtain ⟨z, pz⟩ := p2
  rcases of_run_append newCountKey run with ⟨s3, r3, run⟩
  have hstor3 : Devm.getStor s3 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor
      (by unfold newCountKey loadWord tagTop; line_inv) r3).symm.trans hstor2
  have p3 : countSlot replWorldNewPauser :: z :: [] <<+ s3.stack := by
    unfold newCountKey at r3
    rcases of_run_append (loadWord newPauserWord) r3 with ⟨_u1, l1, r3⟩
    have pu := prefix_of_loadWord_window window2 pz l1
    unfold tagTop at r3
    rcases Line.of_run_cons r3 with ⟨_u2, o1, r3⟩
    rcases Line.of_run_cons r3 with ⟨_u3, o2, hnil⟩
    cases hnil
    exact prefix_of_or o2 (prefix_of_push (of_run_pushB256 o1) pu)
  rcases Line.of_run_cons run with ⟨s4, q4, hnil⟩
  cases hnil
  obtain ⟨_u, hset⟩ := sstore_getStor_setStorVal q4 p3
  rw [replWorld_currentTarget] at hset
  show (Devm.getStor devm' replWorldOwner).get
    (countSlot replWorldOldPauser) = value
  rw [hset, Stor.get_set_ne _ replWorld_newCount_ne_oldCount, hstor3]
  exact hcount

/-- `registerAfterSet`'s old-count branch word: `iszero` of the cell the route
has followed since message entry. -/
theorem replWorld_previousCountWord {oldCount : B256} {gas : Nat}
    {devm devm' : Devm} {value : B256}
    (window : MemWordAt devm (previousPauserWord * 32).toNat
      replWorldOldPauser)
    (hcount : ReplOldCount devm value)
    (run : Line.Run (replWorldSevm oldCount gas) devm
      registerPreviousCountCheck devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest →
      w = (value =? 0) := by
  unfold registerPreviousCountCheck at run
  rcases of_run_append previousCountKey run with ⟨s1, r1, run⟩
  have hstor1 : Devm.getStor s1 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor
      (by unfold previousCountKey loadWord tagTop; line_inv) r1).symm
  have p1 : countSlot replWorldOldPauser :: [] <<+ s1.stack := by
    unfold previousCountKey at r1
    rcases of_run_append (loadWord previousPauserWord) r1 with ⟨_u1, l1, r1⟩
    have pu := prefix_of_loadWord_window window nil_pref l1
    unfold tagTop at r1
    rcases Line.of_run_cons r1 with ⟨_u2, o1, r1⟩
    rcases Line.of_run_cons r1 with ⟨_u3, o2, hnil⟩
    cases hnil
    exact prefix_of_or o2 (prefix_of_push (of_run_pushB256 o1) pu)
  rcases Line.of_run_cons run with ⟨_s2, q2, run⟩
  obtain ⟨c, p2, hc⟩ := prefix_of_sload q2 p1
  have hcv : c = value := by
    rw [hc, replWorld_currentTarget]
    show (Devm.getStor s1 replWorldOwner).get
      (countSlot replWorldOldPauser) = value
    rw [hstor1]
    exact hcount
  rcases Line.of_run_cons run with ⟨_s3, q3, hnil⟩
  cases hnil
  intro w rest hstack
  rw [head_of_stack_prefix (prefix_of_iszero q3 p2) hstack, hcv]

/-! ### The two memory-valued branch words the replacement arm reads -/

/-- `registerAfterSet`'s first test: the previous pauser the kernel staged is
nonzero, so the walk takes the replacement arm rather than the fresh one. -/
theorem replWorld_previousPauserRegistered {e : Sevm} {devm devm' : Devm}
    (window : MemWordAt devm (previousPauserWord * 32).toNat
      replWorldOldPauser)
    (run : Line.Run e devm (memoryZeroCheck previousPauserWord) devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0 := by
  intro w rest hstack
  rw [memoryZeroCheck_word window run w rest hstack]
  decide

/-- The staged new pauser is nonzero, so every `newPauser`-valued test falls
through to the arm that stores an expiry. -/
theorem replWorld_newPauserNonzero {e : Sevm} {devm devm' : Devm}
    (window : MemWordAt devm (newPauserWord * 32).toNat replWorldNewPauser)
    (run : Line.Run e devm (memoryZeroCheck newPauserWord) devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0 := by
  intro w rest hstack
  rw [memoryZeroCheck_word window run w rest hstack]
  decide

/-- The same test at the far end of the old-last record fragment, where the
window has to survive an `SSTORE`, a scratch-word write, a `LOG` and two
`MLOAD`s first. -/
theorem replWorld_newPauserNonzero_afterRecord {e : Sevm} {devm devm' : Devm}
    (window : MemWordAt devm (newPauserWord * 32).toNat replWorldNewPauser)
    (run : Line.Run e devm registerOldLastRecordPrefix devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w = 0 := by
  unfold registerOldLastRecordPrefix at run
  rcases of_run_append [Ninst.sstore, Ninst.pushB256 0] run with ⟨_s1, r1, run⟩
  rcases of_run_append (mstoreAt 0) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 heartbeatUpdatedEvent] run
    with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 1 0 1) run with ⟨_s5, r5, run⟩
  have window5 := ((((window.acrossLine (by line_inv) r1).acrossMstoreAt
    (by decide) r2).acrossLoadWord r3).acrossLine (by line_inv)
    r4).acrossLogWith r5
  intro w rest hstack
  rw [memoryZeroCheck_word window5 run w rest hstack]
  decide

/-- `finishSetPauser`'s continuation test, world-independent: the staging line
wrote a zero continuation, so the walk returns to `registerAfterSet` rather
than to `pauseAfterSet`.  `freshWorld_continuationRegister` is this at one
fixed world; nothing in either proof reads the world. -/
theorem continuationRegister_of_finishPrefix {e : Sevm} {devm devm' : Devm}
    (window : MemWordAt devm (continuationWord * 32).toNat 0)
    (run : Line.Run e devm finishSetPauserPrefix devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0 := by
  unfold finishSetPauserPrefix at run
  rcases of_run_append (loadWord newPauserWord) run with ⟨_s1, r1, run⟩
  rcases of_run_append (loadWord previousPauserWord) run with ⟨_s2, r2, run⟩
  rcases of_run_append (loadWord targetWord) run with ⟨_s3, r3, run⟩
  rcases of_run_append [Ninst.pushB256 pauserSetEvent] run with ⟨_s4, r4, run⟩
  rcases of_run_append (logWith 3 0 0) run with ⟨_s5, r5, run⟩
  have window5 := ((((window.acrossLoadWord r1).acrossLoadWord
    r2).acrossLoadWord r3).acrossLine (by line_inv) r4).acrossLogWith r5
  intro w rest hstack
  rw [memoryZeroCheck_word window5 run w rest hstack]
  decide

/-! ### The shared leg: program entry to `registerAfterSet`'s own root

Fifteen branch crossings, of which three are priced: the kernel's
storage-valued previous-pauser test, `afterOldPauser`'s memory-valued
new-pauser test and `finishSetPauser`'s memory-valued continuation test.  Of
the other twelve, six are the dispatcher's selector comparisons, decided on the
concrete calldata selector, and six have certified-reverting siblings.

Both replacement worlds take this leg, so it is stated once, parametrically in
the old pauser's entry count and in the message gas.  Each row's own route adds
four more crossings past `registerAfterSet`'s root, of which the arm-selecting
two — the staged previous pauser and the decremented count — are priced. -/

theorem runtimeMain_routeTo_replacementRegisterAfterSetCall
    {oldCount : B256} {gas : Nat} {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      (replWorldSevm oldCount gas) devm (runtime officialParams).main
      (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor (replWorldPre oldCount gas))
    (hmem : devm.memory = Mem.empty)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      ReplKernelWindows devm' → ReplOldCount devm' (oldCount - 1) →
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        (replWorldSevm oldCount gas) devm' (Func.call registerAfterSetSlot)
        (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry erun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) erun).symm.trans hstor
  have n0 := (Line.of_inv Devm.memory (by line_inv) erun).symm.trans hmem
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 4) (by rfl)
    (fun _body hpop arm => ?_)
  have g1 := (getStor_of_state hpop.state).symm.trans g0
  have n1 := hpop.memory.symm.trans n0
  refine dispatch_routeTo_registerPauser officialParams arm
    (replWorld_dataFacts oldCount gas).2.1
    (fun _current _d0 dstor dmem bodyTail => ?_)
  refine registerPauser_routeTo_setPauserCall officialParams bodyTail
    (fun _c _stage d1 rstor rmem staging callTail => ?_)
  have gk : Devm.getStor d1 = Devm.getStor (replWorldPre oldCount gas) :=
    rstor.trans (dstor.trans g1)
  have windows := replWorld_stagedEntry (rmem.trans (dmem.trans n1)) staging
  refine routeTo_call callTail (by rfl) (fun _kStart kBurn kBody => ?_)
  have gk0 := (getStor_of_state kBurn.state).symm.trans gk
  have wk0 :=
    windows.map (fun _ _ w => MemWordAt.of_memory_eq kBurn.memory.symm w)
  refine routeTo_line setPauserKernelZeroCheck kBody (fun _z zrun tail0 => ?_)
  have gk1 := (Line.of_inv Devm.getStor (by line_inv) zrun).symm.trans gk0
  have wk1 := wk0.map (fun _ _ w => w.acrossZeroCheck zrun)
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail0 (fuel := 8) (by rfl)
    (fun _s1 hpop1 arm1 => ?_)
  have gk2 := (getStor_of_state hpop1.state).symm.trans gk1
  have wk2 := wk1.map (fun _ _ w => MemWordAt.of_memory_eq hpop1.memory.symm w)
  refine routeTo_line setPauserKernelAppendPrefix arm1
    (fun _s2 run2 tail2 => ?_)
  obtain ⟨branchWord, staged, countCell⟩ :=
    replWorld_previousPauserPresent gk2 wk2.1 run2
  refine routeTo_branchLeft_frame tail2 branchWord (fun _s3 hpop3 arm3 => ?_)
  have wk3 : ReplKernelWindows _s3 :=
    ReplKernelWindows.map (fun _ _ w => MemWordAt.of_memory_eq hpop3.memory.symm w)
      ⟨wk2.acrossAppendPrefix run2, staged⟩
  have c3 := countCell.of_state hpop3.state
  refine routeTo_line setPauserKernelDecrementPrefix arm3
    (fun _s4 run4 tail4 => ?_)
  have c4 := replWorld_countDecrement wk3.2 c3 run4
  have wk4 := wk3.map (fun _ _ w => w.acrossDecrementPrefix run4)
  refine routeTo_call tail4 (by rfl) (fun _aStart aBurn aBody => ?_)
  have c5 := c4.of_state aBurn.state
  have wk5 := wk4.map (fun _ _ w => MemWordAt.of_memory_eq aBurn.memory.symm w)
  refine routeTo_line (memoryZeroCheck newPauserWord) aBody
    (fun _s6 r6 tail6 => ?_)
  refine routeTo_branchLeft_frame tail6
    (replWorld_newPauserNonzero wk5.1.2.1 r6) (fun _s7 hpop7 arm7 => ?_)
  have c7 := (c5.acrossLine (by line_inv) r6).of_state hpop7.state
  have wk7 := (wk5.map (fun _ _ w => w.acrossMemoryZeroCheck r6)).map
    (fun _ _ w => MemWordAt.of_memory_eq hpop7.memory.symm w)
  refine routeTo_line afterOldNewCountLine arm7 (fun _s8 r8 tail8 => ?_)
  have c8 := replWorld_newCountWrite wk7.1.2.1 c7 r8
  have wk8 := wk7.map (fun _ _ w => w.acrossNewCountLine r8)
  refine routeTo_call tail8 (by rfl) (fun _fStart fBurn fBody => ?_)
  have c9 := c8.of_state fBurn.state
  have wk9 := wk8.map (fun _ _ w => MemWordAt.of_memory_eq fBurn.memory.symm w)
  refine routeTo_line finishSetPauserPrefix fBody (fun _s10 r10 tail10 => ?_)
  refine routeTo_branchRight_frame tail10
    (continuationRegister_of_finishPrefix wk9.1.2.2 r10)
    (fun _s11 _w11 hpop11 registerCall => ?_)
  have c11 := (c9.acrossLine (by line_inv) r10).of_state hpop11.state
  have wk11 := (wk9.map (fun _ _ w => w.acrossFinishPrefix r10)).map
    (fun _ _ w => MemWordAt.of_memory_eq hpop11.memory.symm w)
  exact callRoute _ _ wk11 c11 registerCall

/-! ### The three paths, and the three routes -/

/-- Structural source position of the expiry `SSTORE` on `registerAfterSet`'s
retained arm: inventory index `14`. -/
def registerRetainedArmExpiryPath : Prog.SourcePath :=
  ⟨registerAfterSetSlot,
    sourceRests 3 ++ [Prog.SourceStep.branchLeft] ++ sourceRests 6 ++
      [Prog.SourceStep.branchLeft] ++ sourceRests 3 ++
      [Prog.SourceStep.branchLeft] ++ sourceRests 8 ++
      [Prog.SourceStep.branchLeft] ++ sourceRests 7⟩

/-- Structural source position of the retiring pauser's expiry clear:
inventory index `15`. -/
def registerOldLastClearPath : Prog.SourcePath :=
  ⟨registerAfterSetSlot,
    List.replicate 3 .rest ++ [.branchLeft] ++ List.replicate 6 .rest ++
      [.branchRight] ++ List.replicate 5 .rest⟩

/-- Structural source position of the new pauser's expiry write on the
old-last arm: inventory index `16`. -/
def registerOldLastNewExpiryPath : Prog.SourcePath :=
  ⟨registerAfterSetSlot,
    List.replicate 3 .rest ++ [.branchLeft] ++ List.replicate 6 .rest ++
      [.branchRight] ++ List.replicate 18 .rest ++ [.branchLeft] ++
      List.replicate 8 .rest ++ [.branchLeft] ++ List.replicate 7 .rest⟩

/-- The complete route to the retained arm's expiry `SSTORE`.  Past
`registerAfterSet`'s root: the previous-pauser test takes the replacement arm,
the old-count test finds `2 - 1` and takes the retained arm, and the tail is
the fresh arm's own — same new-pauser test, same overflow check, same write
line. -/
theorem runtimeMain_routeTo_registerRetainedArmExpiry {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      (replWorldSevm replRetainedWorldCount replRetainedWorldGas) devm
      (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm =
      Devm.getStor (replWorldPre replRetainedWorldCount replRetainedWorldGas))
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h registerRetainedArmExpiryPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_replacementRegisterAfterSetCall h hstor hmem
    (fun _current _d windows hcount callTail => ?_)
  refine routeTo_call callTail (by rfl) (fun _rStart rBurn rBody => ?_)
  have w0 :=
    windows.map (fun _ _ w => MemWordAt.of_memory_eq rBurn.memory.symm w)
  have c0 := hcount.of_state rBurn.state
  refine routeTo_line (memoryZeroCheck previousPauserWord) rBody
    (fun _s1 r1 tail1 => ?_)
  refine routeTo_branchLeft_frame tail1
    (replWorld_previousPauserRegistered w0.2 r1) (fun _s2 hpop2 arm2 => ?_)
  have w2 := (w0.map (fun _ _ w => w.acrossMemoryZeroCheck r1)).map
    (fun _ _ w => MemWordAt.of_memory_eq hpop2.memory.symm w)
  have c2 := (c0.acrossLine (by line_inv) r1).of_state hpop2.state
  refine routeTo_line registerPreviousCountCheck arm2 (fun _s3 r3 tail3 => ?_)
  refine routeTo_branchLeft_frame tail3
    (fun w rest hs => by
      rw [replWorld_previousCountWord w2.2 c2 r3 w rest hs]
      decide)
    (fun _s4 hpop4 arm4 => ?_)
  have w4 := (w2.map (fun _ _ w => w.acrossPreviousCountCheck r3)).map
    (fun _ _ w => MemWordAt.of_memory_eq hpop4.memory.symm w)
  refine routeTo_line (memoryZeroCheck newPauserWord) arm4
    (fun _s5 r5 tail5 => ?_)
  refine routeTo_branchLeft tail5 (replWorld_newPauserNonzero w4.1.2.1 r5)
    (fun _s6 arm6 => ?_)
  refine routeTo_line checkedExpiryPrefix arm6 (fun _s7 _r7 tail7 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail7 (fuel := 16)
    arithmeticPanic_revertsWithin (fun _s8 arm8 => ?_)
  refine routeTo_line registerFreshArmExpiryPrefix arm8
    (fun _s9 _r9 write => ?_)
  have pathEq :
      ((((((((([] ++ List.replicate (memoryZeroCheck previousPauserWord).length
                          Prog.SourceStep.rest) ++
                      [Prog.SourceStep.branchLeft]) ++
                    List.replicate registerPreviousCountCheck.length
                      Prog.SourceStep.rest) ++
                  [Prog.SourceStep.branchLeft]) ++
                List.replicate (memoryZeroCheck newPauserWord).length
                  Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
            List.replicate checkedExpiryPrefix.length Prog.SourceStep.rest) ++
          [Prog.SourceStep.branchLeft]) ++
        List.replicate registerFreshArmExpiryPrefix.length
          Prog.SourceStep.rest) = registerRetainedArmExpiryPath.steps := by
    simp [registerRetainedArmExpiryPath, sourceRests, memoryZeroCheck,
      checkedExpiryPrefix, registerFreshArmExpiryPrefix, registerPreviousCountCheck,
      previousCountKey, loadWord, mstoreAt, tagTop]
  exact pathEq ▸ routeTo_head write registerRetainedArmExpiryPath

/-- The complete route to the retiring pauser's expiry clear: the same leg,
with the old-count test finding `1 - 1` and taking the old-last arm. -/
theorem runtimeMain_routeTo_registerOldLastClear {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      (replWorldSevm replOldLastWorldCount replOldLastWorldGas) devm
      (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm =
      Devm.getStor (replWorldPre replOldLastWorldCount replOldLastWorldGas))
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h registerOldLastClearPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_replacementRegisterAfterSetCall h hstor hmem
    (fun _current _d windows hcount callTail => ?_)
  refine routeTo_call callTail (by rfl) (fun _rStart rBurn rBody => ?_)
  have w0 :=
    windows.map (fun _ _ w => MemWordAt.of_memory_eq rBurn.memory.symm w)
  have c0 := hcount.of_state rBurn.state
  refine routeTo_line (memoryZeroCheck previousPauserWord) rBody
    (fun _s1 r1 tail1 => ?_)
  refine routeTo_branchLeft_frame tail1
    (replWorld_previousPauserRegistered w0.2 r1) (fun _s2 hpop2 arm2 => ?_)
  have w2 := (w0.map (fun _ _ w => w.acrossMemoryZeroCheck r1)).map
    (fun _ _ w => MemWordAt.of_memory_eq hpop2.memory.symm w)
  have c2 := (c0.acrossLine (by line_inv) r1).of_state hpop2.state
  refine routeTo_line registerPreviousCountCheck arm2 (fun _s3 r3 tail3 => ?_)
  refine routeTo_branchRight tail3
    (fun w rest hs => by
      rw [replWorld_previousCountWord w2.2 c2 r3 w rest hs]
      decide)
    (fun _s4 arm4 => ?_)
  refine routeTo_line registerOldLastClearPrefix arm4
    (fun _s5 _r5 write => ?_)
  have pathEq :
      ((((([] ++ List.replicate (memoryZeroCheck previousPauserWord).length
                    Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
              List.replicate registerPreviousCountCheck.length
                Prog.SourceStep.rest) ++ [Prog.SourceStep.branchRight]) ++
          List.replicate registerOldLastClearPrefix.length
            Prog.SourceStep.rest) = registerOldLastClearPath.steps := by
    simp [registerOldLastClearPath, memoryZeroCheck, registerPreviousCountCheck,
      registerOldLastClearPrefix, previousCountKey, loadWord, tagTop]
  exact pathEq ▸ routeTo_head write registerOldLastClearPath

/-- The complete route to the new pauser's expiry write on the old-last arm:
the clear crossed, the zero-payload record emitted, and then the same
new-pauser test, overflow check and write line the other two expiry rows
end with. -/
theorem runtimeMain_routeTo_registerOldLastNewExpiry {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      (replWorldSevm replOldLastWorldCount replOldLastWorldGas) devm
      (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm =
      Devm.getStor (replWorldPre replOldLastWorldCount replOldLastWorldGas))
    (hmem : devm.memory = Mem.empty) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h registerOldLastNewExpiryPath
      (.reg .sstore) := by
  refine runtimeMain_routeTo_replacementRegisterAfterSetCall h hstor hmem
    (fun _current _d windows hcount callTail => ?_)
  refine routeTo_call callTail (by rfl) (fun _rStart rBurn rBody => ?_)
  have w0 :=
    windows.map (fun _ _ w => MemWordAt.of_memory_eq rBurn.memory.symm w)
  have c0 := hcount.of_state rBurn.state
  refine routeTo_line (memoryZeroCheck previousPauserWord) rBody
    (fun _s1 r1 tail1 => ?_)
  refine routeTo_branchLeft_frame tail1
    (replWorld_previousPauserRegistered w0.2 r1) (fun _s2 hpop2 arm2 => ?_)
  have w2 := (w0.map (fun _ _ w => w.acrossMemoryZeroCheck r1)).map
    (fun _ _ w => MemWordAt.of_memory_eq hpop2.memory.symm w)
  have c2 := (c0.acrossLine (by line_inv) r1).of_state hpop2.state
  refine routeTo_line registerPreviousCountCheck arm2 (fun _s3 r3 tail3 => ?_)
  refine routeTo_branchRight_frame tail3
    (fun w rest hs => by
      rw [replWorld_previousCountWord w2.2 c2 r3 w rest hs]
      decide)
    (fun _s4 _w4 hpop4 arm4 => ?_)
  have w4 := (w2.map (fun _ _ w => w.acrossPreviousCountCheck r3)).map
    (fun _ _ w => MemWordAt.of_memory_eq hpop4.memory.symm w)
  refine routeTo_line registerOldLastClearPrefix arm4
    (fun _s5 r5 clearWrite => ?_)
  refine routeTo_line registerOldLastRecordPrefix clearWrite
    (fun _s6 r6 tail6 => ?_)
  have w5 := w4.map (fun _ _ w => w.acrossOldLastClearPrefix r5)
  refine routeTo_branchLeft tail6
    (replWorld_newPauserNonzero_afterRecord w5.1.2.1 r6) (fun _s7 arm7 => ?_)
  refine routeTo_line checkedExpiryPrefix arm7 (fun _s8 _r8 tail8 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail8 (fuel := 16)
    arithmeticPanic_revertsWithin (fun _s9 arm9 => ?_)
  refine routeTo_line registerFreshArmExpiryPrefix arm9
    (fun _s10 _r10 write => ?_)
  have pathEq :
      (((((((((([] ++
                          List.replicate
                            (memoryZeroCheck previousPauserWord).length
                            Prog.SourceStep.rest) ++
                        [Prog.SourceStep.branchLeft]) ++
                      List.replicate registerPreviousCountCheck.length
                        Prog.SourceStep.rest) ++
                    [Prog.SourceStep.branchRight]) ++
                  List.replicate registerOldLastClearPrefix.length
                    Prog.SourceStep.rest) ++
                List.replicate registerOldLastRecordPrefix.length
                  Prog.SourceStep.rest) ++ [Prog.SourceStep.branchLeft]) ++
            List.replicate checkedExpiryPrefix.length Prog.SourceStep.rest) ++
          [Prog.SourceStep.branchLeft]) ++
        List.replicate registerFreshArmExpiryPrefix.length
          Prog.SourceStep.rest) = registerOldLastNewExpiryPath.steps := by
    simp [registerOldLastNewExpiryPath, memoryZeroCheck,
      registerPreviousCountCheck, registerOldLastClearPrefix,
      registerOldLastRecordPrefix, checkedExpiryPrefix,
      registerFreshArmExpiryPrefix, previousCountKey, loadWord, mstoreAt,
      tagTop, logWith]
  exact pathEq ▸ routeTo_head write registerOldLastNewExpiryPath

/-! ### Pinning the three rows, and the witnesses -/

/-- Inventory indices `14`, `15` and `16` are the only ones nominating the
three replacement-arm paths.  One kernel evaluation settles all three, as for
the `appendTarget` rows. -/
theorem registerReplacementArm_index_pins :
    (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some registerRetainedArmExpiryPath) →
          index = 14) ∧
      (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some registerOldLastClearPath) → index = 15) ∧
      (∀ index ∈ List.range 20,
        ((runtimePersistentSourceSites officialParams)[index]?.map
          (fun s => s.path) = some registerOldLastNewExpiryPath) →
          index = 16) := by
  decide +kernel

/-- The inventory row at index `14`, `.registerRetainedOldNewExpiry` — the
expiry write on `registerAfterSet`'s **retained** arm — is attained with the
`.adminExpiry` role.

The row is pinned by `sourceSite?`, not by its name; this one's site sits
behind `previousPauser ≠ 0`, which no fresh registration reaches. -/
theorem attainable_registerRetainedOldNewExpiry_adminExpiry :
    Attainable officialParams .registerRetainedOldNewExpiry .adminExpiry := by
  refine attainable_of_entryRoute_frame (ca := replWorldOwner)
    (replWorld_currentTarget _ _) ?_
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path registerReplacementArm_index_pins.1
        found pathEq)
    (by decide) replRetainedWorld_run
    (fun _devm _post hstor hmem hrun =>
      runtimeMain_routeTo_registerRetainedArmExpiry hrun hstor hmem)
  rw [replWorld_codeAddress, replWorld_currentTarget]

/-- The inventory row at index `15` — the retiring pauser's expiry clear — is
attained with the `.adminExpiry` role. -/
theorem attainable_registerLastOldClear_adminExpiry :
    Attainable officialParams .registerLastOldClear .adminExpiry := by
  refine attainable_of_entryRoute_frame (ca := replWorldOwner)
    (replWorld_currentTarget _ _) ?_
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path registerReplacementArm_index_pins.2.1
        found pathEq)
    (by decide) replOldLastWorld_run
    (fun _devm _post hstor hmem hrun =>
      runtimeMain_routeTo_registerOldLastClear hrun hstor hmem)
  rw [replWorld_codeAddress, replWorld_currentTarget]

/-- The inventory row at index `16` — the new pauser's expiry write after that
clear — is attained with the `.adminExpiry` role, at the same walk. -/
theorem attainable_registerLastOldNewExpiry_adminExpiry :
    Attainable officialParams .registerLastOldNewExpiry .adminExpiry := by
  refine attainable_of_entryRoute_frame (ca := replWorldOwner)
    (replWorld_currentTarget _ _) ?_
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path registerReplacementArm_index_pins.2.2
        found pathEq)
    (by decide) replOldLastWorld_run
    (fun _devm _post hstor hmem hrun =>
      runtimeMain_routeTo_registerOldLastNewExpiry hrun hstor hmem)
  rw [replWorld_codeAddress, replWorld_currentTarget]

end Replacement

/-! Compatibility names retained after hoisting the generic memory-image
carrier.  The implementations live in the carrier namespace so generalized
field notation continues to find them. -/
abbrev MemWordAt.acrossMemoryZeroCheck :=
  @Blanc.MemWordAt.acrossMemoryZeroCheck
abbrev MemWordAt.acrossZeroCheck := @Blanc.MemWordAt.acrossZeroCheck
abbrev MemWordAt.acrossAppendPrefix := @Blanc.MemWordAt.acrossAppendPrefix
abbrev MemWordAt.acrossArrayEntryPrefix :=
  @Blanc.MemWordAt.acrossArrayEntryPrefix
abbrev MemWordAt.acrossReverseIndexPrefix :=
  @Blanc.MemWordAt.acrossReverseIndexPrefix
abbrev MemWordAt.acrossArrayLengthPrefix :=
  @Blanc.MemWordAt.acrossArrayLengthPrefix
abbrev MemWordAt.acrossNewCountKey := @Blanc.MemWordAt.acrossNewCountKey
abbrev MemWordAt.acrossNewCountPrefix := @Blanc.MemWordAt.acrossNewCountPrefix
abbrev MemWordAt.acrossFinishPrefix := @Blanc.MemWordAt.acrossFinishPrefix
abbrev MemWordAt.acrossPreviousCountKey :=
  @Blanc.MemWordAt.acrossPreviousCountKey
abbrev MemWordAt.acrossDecrementPrefix :=
  @Blanc.MemWordAt.acrossDecrementPrefix
abbrev MemWordAt.acrossNewCountLine := @Blanc.MemWordAt.acrossNewCountLine
abbrev MemWordAt.acrossPreviousCountCheck :=
  @Blanc.MemWordAt.acrossPreviousCountCheck
abbrev MemWordAt.acrossOldLastClearPrefix :=
  @Blanc.MemWordAt.acrossOldLastClearPrefix
abbrev MemWordAt.acrossOldLastRecordPrefix :=
  @Blanc.MemWordAt.acrossOldLastRecordPrefix

end Blanc.LidoCircuitBreaker
