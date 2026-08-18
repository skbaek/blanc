import Blanc.SourceAttainment
import Blanc.LidoCircuitBreakerAuthority
import Blanc.LidoCircuitBreakerRegistrationWorld

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
six persistent writes, and four of them are attained here with the
`.adminRegistry` role: `.setPauserAssignment` (source function 14) and the
three `appendTarget` rows `.appendArrayEntry`, `.appendReverseIndex` and
`.appendArrayLength` (source function 15).  One world, one derivation, four
rows — the later three cost only their own route, because everything after the
route is row-independent (`attainable_adminRegistry_of_route`).

Three facts made the first route cheap, and all three generalize.  A
`REVERT`-only arm cannot produce an `.ok` outcome at all, so six of the twelve
branch crossings need no branch word and no cleanliness antecedent; the six
that remain are the dispatcher's selector comparisons, which are decided on the
concrete calldata selector alone; and the same-frame premise comes back from
the routed bridge already proved, so no frame-entry-freedom certificate is
involved — see *Same-frame reachability, and why no certificate is needed*
below.

The `appendTarget` rows add a thirteenth branch, and it is the first one on
this flow whose sibling is not certified-reverting: `setPauserKernel`'s
previous-pauser test.  Its word is *storage-valued*, so the entry storage has
to survive every earlier crossing — which is why the route now carries a
`Devm.getStor` chain and the shared kit gained its `routeTo_branch*_frame`
family.  See *The `appendTarget` rows* below for why no memory image is
threaded with it.
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
role payloads are already incompatible at the source-site level. -/

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

set_option maxRecDepth 16384 in
/-- The six selector crossings of `hybridDispatchWith`, on a walk whose
calldata selects `registerPauser`: two `splitDispatch` pivots taken jumped,
then three `linearDispatchWith` misses and the match.

The continuation is quantified over the reached source path, because the
`.call setPauserSlot` further down restarts the position at the callee's root:
no dispatcher path arithmetic survives it, so none is done here. -/
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
      ∀ tail : Func.RunCompiledTo fs sevm devm' (registerPauser dp) out,
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line fsig h (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack := prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  have g0 : Devm.getStor s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) run0).symm
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  have g1 := (Line.of_inv Devm.getStor (by line_inv) run1).symm.trans g0
  refine routeTo_branchRight_frame tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 _w2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 ⟨_, hpop2.stack⟩
  have g2 := (getStor_of_state hpop2.state).symm.trans g1
  refine routeTo_line (splitTest (selector "getPauser" [.address])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  have g3 := (Line.of_inv Devm.getStor (by line_inv) run3).symm.trans g2
  refine routeTo_branchRight_frame tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 _w4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 ⟨_, hpop4.stack⟩
  have g4 := (getStor_of_state hpop4.state).symm.trans g3
  refine routeTo_line (linearTest (selector "pauseDuration" [])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  have g5 := (Line.of_inv Devm.getStor (by line_inv) run5).symm.trans g4
  refine routeTo_branchLeft_frame tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 hpop6 tail6 => ?_)
  have p6 := tail_of_stack_prefix p5 ⟨_, hpop6.stack⟩
  have g6 := (getStor_of_state hpop6.state).symm.trans g5
  refine routeTo_line (linearTest (selector "MAX_PAUSE_DURATION" [])) tail6
    (fun _s7 run7 tail7 => ?_)
  have p7 := prefix_of_linearTest p6 run7
  have g7 := (Line.of_inv Devm.getStor (by line_inv) run7).symm.trans g6
  refine routeTo_branchLeft_frame tail7
    (fun _w _rest hs => by rw [head_of_stack_prefix p7 hs]; decide)
    (fun _s8 hpop8 tail8 => ?_)
  have p8 := tail_of_stack_prefix p7 ⟨_, hpop8.stack⟩
  have g8 := (getStor_of_state hpop8.state).symm.trans g7
  refine routeTo_line (linearTest (selector "ADMIN" [])) tail8
    (fun _s9 run9 tail9 => ?_)
  have p9 := prefix_of_linearTest p8 run9
  have g9 := (Line.of_inv Devm.getStor (by line_inv) run9).symm.trans g8
  refine routeTo_branchLeft_frame tail9
    (fun _w _rest hs => by rw [head_of_stack_prefix p9 hs]; decide)
    (fun _s10 hpop10 tail10 => ?_)
  have p10 := tail_of_stack_prefix p9 ⟨_, hpop10.stack⟩
  have g10 := (getStor_of_state hpop10.state).symm.trans g9
  refine routeTo_line
    (linearTest (selector "registerPauser" [.address, .address])) tail10
    (fun _s11 run11 tail11 => ?_)
  have p11 := prefix_of_linearTest p10 run11
  have g11 := (Line.of_inv Devm.getStor (by line_inv) run11).symm.trans g10
  refine routeTo_branchRight_frame tail11
    (fun _w _rest hs => by rw [head_of_stack_prefix p11 hs]; decide)
    (fun _s12 _w12 hpop12 tail12 => ?_)
  have g12 := (getStor_of_state hpop12.state).symm.trans g11
  refine routeTo_line [Ninst.pop] tail12 (fun _s13 run13 tail13 => ?_)
  exact bodyRoute _ _
    ((Line.of_inv Devm.getStor (by line_inv) run13).symm.trans g12) tail13

/-! ## The `registerPauser` guard cascade

Four branches, and not one of them costs a branch word: every arm this walk
does *not* take is `Func.rev` or a `.call` to one, so the successful outcome
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

set_option maxRecDepth 8192 in
/-- From `registerPauser`'s entry to its `.call setPauserSlot`: the static
argument-length guard, two canonical-address guards and the admin guard,
crossed on the strength of the successful outcome alone. -/
theorem registerPauser_routeTo_setPauserCall (dp : DeployParams)
    {sevm : Sevm} {devm post : Devm}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux) sevm devm
      (registerPauser dp) (.ok post))
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      Devm.getStor devm' = Devm.getStor devm →
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm devm' (Func.call setPauserSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line registerStaticArgsTest h (fun _s0 r0 tail0 => ?_)
  have g0 : Devm.getStor _s0 = Devm.getStor devm :=
    (Line.of_inv Devm.getStor (by line_inv) r0).symm
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail0 (fuel := 4) (by rfl)
    (fun _s1 hpop1 tail1 => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  refine routeTo_line (arg 0 ++ checkNonAddress) tail1 (fun _s2 r2 tail2 => ?_)
  have g2 := (Line.of_inv Devm.getStor (by line_inv) r2).symm.trans g1
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail2 (fuel := 4) (by rfl)
    (fun _s3 hpop3 tail3 => ?_)
  have g3 := (getStor_of_state hpop3.state).symm.trans g2
  refine routeTo_line (arg 1 ++ checkNonAddress) tail3 (fun _s4 r4 tail4 => ?_)
  have g4 := (Line.of_inv Devm.getStor (by line_inv) r4).symm.trans g3
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail4 (fuel := 4) (by rfl)
    (fun _s5 hpop5 tail5 => ?_)
  have g5 := (getStor_of_state hpop5.state).symm.trans g4
  refine routeTo_line (adminTest dp) tail5 (fun _s6 r6 tail6 => ?_)
  have g6 := (Line.of_inv Devm.getStor
    (by unfold adminTest pushDeployWord; line_inv) r6).symm.trans g5
  refine routeTo_branchRight_of_leftRevertsOk_frame tail6 (fuel := 8) (by rfl)
    (fun _s7 _w7 hpop7 tail7 => ?_)
  have g7 := (getStor_of_state hpop7.state).symm.trans g6
  refine routeTo_line registerStagingLine tail7 (fun _s8 r8 tail8 => ?_)
  exact callRoute _ _
    ((Line.of_inv Devm.getStor (by line_inv) r8).symm.trans g7) tail8

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

set_option maxRecDepth 16384 in
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
    (fun _current _devm' _stor bodyTail =>
      registerPauser_routeTo_setPauserCall dp bodyTail
        (fun _c _d _stor' callTail =>
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

set_option maxRecDepth 20000 in
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

What the route deliberately does *not* need is the memory image.  The key is
`slot assignmentRegion m` for **whatever** word `m` the kernel loaded, and this
world's storage is zero at *every* assignment slot — `heartbeatIntervalSlot` is
the only nonzero cell and it is in the config region.  Separating the two takes
no payload bound and no calldata fact, only one bit of the region tag, so no
memory image is threaded anywhere. -/

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
previous pauser is zero, so the `iszero` above it is not.

The only premise is that the walk has written no storage yet, which is exactly
what the `Devm.getStor` chain carries down from message entry.  The loaded
target word stays anonymous — see this section's note. -/
theorem freshWorld_previousPauserZero {devm devm' : Devm}
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (run : Line.Run freshWorldSevm devm setPauserKernelAppendPrefix devm') :
    ∀ (w : B256) (rest : Stack), devm'.stack = w :: rest → w ≠ 0 := by
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
  have p8 := prefix_of_mstore q8 p7
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
  intro w rest hstack
  rw [head_of_stack_prefix p16 hstack, hzero]
  decide

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

/-- Inside `setPauserKernel` at the fresh registration world: the zero-target
arm is a certified-reverting call, and the previous-pauser test takes the
jumped arm, so the walk reaches `.call appendTargetSlot`. -/
theorem setPauserKernel_routeTo_appendCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm setPauserKernel (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨setPauserSlot, []⟩ h targetPath
      targetInstruction := by
  refine routeTo_line setPauserKernelZeroCheck h (fun _z zrun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) zrun).symm.trans hstor
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 8) (by rfl)
    (fun _s1 hpop1 arm => ?_)
  have g1 := (getStor_of_state hpop1.state).symm.trans g0
  refine routeTo_line setPauserKernelAppendPrefix arm
    (fun _s2 run2 tail2 => ?_)
  refine routeTo_branchRight_frame tail2
    (freshWorld_previousPauserZero g1 run2) (fun _s3 _w3 _hpop3 tail3 => ?_)
  exact callRoute _ _ tail3

/-- The `.call setPauserSlot` crossing, carrying the entry storage into the
kernel. -/
theorem call_setPauserSlot_routeTo_appendCall {devm post : Devm}
    {current targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (.call setPauserSlot) (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (callRoute : ∀ (current' : Prog.SourcePath) (devm' : Devm),
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current' tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo current h targetPath targetInstruction :=
  routeTo_call h (by rfl) fun _kernelStart burn tail =>
    setPauserKernel_routeTo_appendCall tail
      ((getStor_of_state burn.state).symm.trans hstor) callRoute

set_option maxRecDepth 16384 in
/-- The complete route from program entry to `appendTarget`'s own root, at the
fresh registration world.  Thirteen branches: six selector comparisons decided
on the concrete calldata selector, six settled by certified-reverting siblings,
and the kernel's storage-valued previous-pauser test. -/
theorem runtimeMain_routeTo_appendCall {devm post : Devm}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre)
    (callRoute : ∀ (current : Prog.SourcePath) (devm' : Devm),
      ∀ tail : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm' (Func.call appendTargetSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h targetPath targetInstruction := by
  refine routeTo_line runtimeMainEntryPrefix h (fun _entry erun tail => ?_)
  have g0 := (Line.of_inv Devm.getStor (by line_inv) erun).symm.trans hstor
  refine routeTo_branchLeft_of_rightRevertsOk_frame tail (fuel := 4) (by rfl)
    (fun _body hpop arm => ?_)
  have g1 := (getStor_of_state hpop.state).symm.trans g0
  exact dispatch_routeTo_registerPauser officialParams arm
    freshWorld_dataFacts.2.1
    (fun _current _devm' dstor bodyTail =>
      registerPauser_routeTo_setPauserCall officialParams bodyTail
        (fun _c _d rstor callTail =>
          call_setPauserSlot_routeTo_appendCall callTail
            (rstor.trans (dstor.trans g1)) callRoute))

/-- The array-entry write: `appendTarget`'s first `SSTORE`. -/
theorem runtimeMain_routeTo_appendArrayEntry {devm post : Devm}
    (h : Func.RunCompiledTo
      ((runtime officialParams).main :: (runtime officialParams).aux)
      freshWorldSevm devm (runtime officialParams).main (.ok post))
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendArrayEntryPath (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor fun _current _devm' callTail =>
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
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendReverseIndexPath
      (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor fun _current _devm' callTail =>
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
    (hstor : Devm.getStor devm = Devm.getStor freshWorldPre) :
    Func.RunCompiledTo.RouteTo ⟨0, []⟩ h appendArrayLengthPath (.reg .sstore) :=
  runtimeMain_routeTo_appendCall h hstor fun _current _devm' callTail =>
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

set_option maxRecDepth 20000 in
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

/-! ### The three witnesses

Everything after the route is row-independent, so it is proved once.  The
`.pauseRegistry` alternative is refuted at the *frame root*, not at the write:
a pause invocation's authority payload asserts that the caller is the assigned
pauser of the calldata target, and at this world every assignment slot is zero
while the caller is the nonzero admin. -/

/-- The shared tail of every witness at the fresh registration world: a route
to a row's frozen path yields that row attained with the `.adminRegistry`
role. -/
theorem attainable_adminRegistry_of_route {row : RuntimePersistentWrite}
    {path : Prog.SourcePath}
    (pin : ∀ {r : RuntimePersistentWrite} {site : Prog.SourceSite},
      r.sourceSite? officialParams = some site → site.path = path → r = row)
    (roles : ∀ r ∈ row.permittedRoles,
      r = InvocationRole.adminRegistry ∨ r = InvocationRole.pauseRegistry)
    (route : ∀ (devm post : Devm)
      (h : Func.RunCompiledTo
        ((runtime officialParams).main :: (runtime officialParams).aux)
        freshWorldSevm devm (runtime officialParams).main (.ok post)),
      Devm.getStor devm = Devm.getStor freshWorldPre →
      Func.RunCompiledTo.RouteTo ⟨0, []⟩ h path (.reg .sstore)) :
    Attainable officialParams row .adminRegistry := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, hrun, _hexec, _hfilled,
    _hgas, _hexpiry, _hlogs, hcompile⟩ := freshRegistrationWorld_run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := route mid post hwalk (getStor_of_state hburn.state).symm
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
  have roleEq : role = .adminRegistry := by
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
  attainable_adminRegistry_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.1 found pathEq)
    (by decide)
    (fun _devm _post h hstor => runtimeMain_routeTo_appendArrayEntry h hstor)

/-- The `append.reverseIndex` row is attained with the `.adminRegistry`
role. -/
theorem attainable_appendReverseIndex_adminRegistry :
    Attainable officialParams .appendReverseIndex .adminRegistry :=
  attainable_adminRegistry_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.2.1 found pathEq)
    (by decide)
    (fun _devm _post h hstor => runtimeMain_routeTo_appendReverseIndex h hstor)

/-- The `append.arrayLength` row is attained with the `.adminRegistry` role. -/
theorem attainable_appendArrayLength_adminRegistry :
    Attainable officialParams .appendArrayLength .adminRegistry :=
  attainable_adminRegistry_of_route
    (fun found pathEq =>
      RuntimePersistentWrite.eq_of_path append_index_pins.2.2 found pathEq)
    (by decide)
    (fun _devm _post h hstor => runtimeMain_routeTo_appendArrayLength h hstor)

end Blanc.LidoCircuitBreaker
