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

The rest of this module builds the first positive witness, at the concrete
admin registration of `Blanc/LidoCircuitBreakerRegistrationWorld.lean`:
`(.setPauserAssignment, .adminRegistry)` is attained.  Everything it needs is
proved here except one certificate — that the registration derivation enters
no child frame — which is stated and discussed under *The frame-entry-freedom
certificate*.

Two facts made the route cheap, and both generalize to every other row behind
this same flow.  A `REVERT`-only arm cannot produce an `.ok` outcome at all,
so six of the twelve branch crossings need no branch word and no cleanliness
antecedent; and the six that remain are the dispatcher's selector
comparisons, which are decided on the concrete calldata selector alone.
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
`apply`d and why `routeTo_line`'s prefix argument must be a list literal.

This is the leg the
`.setPauserAssignment` row's attainment witness ends with: from the callee root
of `setPauserKernel` down to the assignment `SSTORE`: seventeen crossed source
nodes, one branch, and the designated head.  Nothing here reduces a program
counter.

The three legs in this section take **branch-word** hypotheses, which is what
the shared kit's branch lemmas ask for.  At a successful outcome none of those
words has to be computed — see *Wrong-arm refutation at a successful outcome*
below — so `setPauserKernel_routeTo_assignment_ok`,
`runtimeMain_routeTo_setPauserAssignment` and
`call_setPauserSlot_routeTo_assignment_ok` supersede them for the witness.
These remain as the general-outcome forms. -/

/-- The kernel's zero-check prefix, spelled as a list literal: the unifier has
to see `prepend`'s argument in constructor form to expose the walk's head, so
`loadWord targetWord ++ [iszero]` does not work in that position. -/
def setPauserKernelZeroCheck : Line :=
  [Ninst.pushB256 (targetWord * 32), Ninst.mload, Ninst.iszero]

/-- The kernel's assignment prefix, from the fall-through arm to the `SSTORE`;
`targetKey ++ [sload, dup 0] ++ mstoreAt previousPauserWord ++
loadWord newPauserWord ++ targetKey`, spelled literally for the same reason. -/
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
  routeTo_call h lookup fun kernelStart tail =>
    setPauserKernel_routeTo_assignment tail (nonzeroTarget kernelStart)

/-! ## Wrong-arm refutation at a successful outcome

`Blanc/SourceAttainment.lean`'s `routeTo_branchLeft_of_rightReverts` takes
`Execution.commits out = true`, and at an `.ok post` outcome that is
`post.error.isNone` — a *cleanliness* fact, which
`freshRegistrationWorld_settles` carries as an explicit antecedent precisely
because nothing landed propagates `Devm.error` across a compiled walk.

No such antecedent is needed.  A `REVERT` terminal cannot produce an `.ok`
outcome *at all* — every arm of `Linst.run`'s `.rev` case ends in `.error` —
so a certified-reverting arm under an `.ok` walk is not merely
non-committing, it is impossible.  The two lemmas below are the `.ok`-outcome
strengthening of the shared kit, and they are what makes six of this file's
twelve branch crossings free. -/

/-- `REVERT` cannot produce a successful outcome, however its operand reads
fail.  The `.ok` half of `Linst.not_commits_of_run_rev`'s case analysis. -/
theorem Linst.not_run_rev_ok {sevm : Sevm} {devm post : Devm}
    (run : Linst.Run sevm devm .rev (.ok post)) : False := by
  simp only [Linst.Run, Linst.run] at run
  rcases Except.bind_eq_ok run with ⟨_v1, _h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_v2, _h3, h4⟩
  rcases Except.bind_eq_ok h4 with ⟨_v3, _h5, h6⟩
  contradiction

/-- A certified-reverting body has no successful walk.  Same induction as
`Func.RunCompiledTo.not_commits_of_alwaysRevertsWithin`, with the outcome
pinned to `.ok` and the conclusion strengthened to `False`. -/
theorem Func.RunCompiledTo.not_ok_of_alwaysRevertsWithin
    {fs : List Func} {sevm : Sevm} :
    ∀ (fuel : Nat) {devm : Devm} {body : Func} {post : Devm},
      Func.RunCompiledTo fs sevm devm body (.ok post) →
      Func.alwaysRevertsWithin fuel fs body = true → False := by
  intro fuel
  induction fuel with
  | zero =>
      intro _devm _body _post _run certified
      simp [Func.alwaysRevertsWithin] at certified
  | succ fuel ih =>
      intro devm body post run certified
      cases body with
      | branch left right =>
          simp only [Func.alwaysRevertsWithin, Bool.and_eq_true] at certified
          cases run with
          | zero room pop tail => exact ih tail certified.1
          | succ nonzero room pop tail => exact ih tail certified.2
      | last terminal =>
          simp only [Func.alwaysRevertsWithin, beq_iff_eq] at certified
          subst certified
          cases run with
          | last terminalRun => exact Linst.not_run_rev_ok terminalRun
      | next instruction tail =>
          simp only [Func.alwaysRevertsWithin] at certified
          cases run with
          | next instructionRun rest => exact ih rest certified
      | call index =>
          cases hlookup : fs[index]? with
          | none => simp [Func.alwaysRevertsWithin, hlookup] at certified
          | some called =>
              simp only [Func.alwaysRevertsWithin, hlookup] at certified
              cases run with
              | call lookup room burn rest =>
                  have bodyEq := Option.some.inj (hlookup.symm.trans lookup)
                  subst bodyEq
                  exact ih rest certified

section OkKit

variable {fs : List Func} {sevm : Sevm} {post : Devm}

/-- Take the fall-through arm of a successful walk whose jumped arm can only
revert.  No branch word, and no cleanliness antecedent. -/
theorem routeTo_branchLeft_of_rightRevertsOk {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst} {fuel : Nat}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) (.ok post))
    (rightReverts : Func.alwaysRevertsWithin fuel fs right = true)
    (armRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm devm' left (.ok post),
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchLeft]⟩
          tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  cases h with
  | zero room pop tail =>
      exact .branchLeft (room := room) (pop := pop) (tail := tail)
        (armRoute _ tail)
  | succ nonzero room pop tail =>
      exact (Func.RunCompiledTo.not_ok_of_alwaysRevertsWithin fuel tail
        rightReverts).elim

/-- The mirrored form: take the jumped arm when the fall-through arm can only
revert. -/
theorem routeTo_branchRight_of_leftRevertsOk {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst} {fuel : Nat}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) (.ok post))
    (leftReverts : Func.alwaysRevertsWithin fuel fs left = true)
    (armRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm devm' right (.ok post),
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchRight]⟩
          tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  cases h with
  | zero room pop tail =>
      exact (Func.RunCompiledTo.not_ok_of_alwaysRevertsWithin fuel tail
        leftReverts).elim
  | succ nonzero room pop tail =>
      exact .branchRight (nonzero := nonzero) (room := room) (pop := pop)
        (tail := tail) (armRoute _ tail)

end OkKit

/-! ## Branch crossings that keep the stack

The shared kit's `routeTo_branchLeft`/`routeTo_branchRight` quantify their
continuation over *every* `Devm`, so the walk's own `Devm.PopBurnBy` — the
only thing relating the post-branch stack to the pre-branch one — is
discarded at each crossing.  That is fine for a single branch and fatal for a
dispatcher: the six selector comparisons this file crosses each need the
selector word that the *previous* crossing popped down to.

These two are the shared kit's lemmas with the pop's stack equation handed to
the continuation.  Everything else is identical. -/

section StackKit

variable {fs : List Func} {sevm : Sevm} {out : Execution}

theorem routeTo_branchLeft_stack {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (branchWord : ∀ w : B256, ∀ rest : Stack, devm.stack = w :: rest → w = 0)
    (armRoute : ∀ devm' : Devm, (∃ w : B256, devm.stack = w :: devm'.stack) →
      ∀ tail : Func.RunCompiledTo fs sevm devm' left out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchLeft]⟩
          tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  cases h with
  | zero room pop tail =>
      exact .branchLeft (room := room) (pop := pop) (tail := tail)
        (armRoute _ ⟨0, pop.stack⟩ tail)
  | succ nonzero room pop tail => exact absurd (branchWord _ _ pop.stack) nonzero

theorem routeTo_branchRight_stack {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {targetPath : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (branchWord : ∀ w : B256, ∀ rest : Stack, devm.stack = w :: rest → w ≠ 0)
    (armRoute : ∀ devm' : Devm, (∃ w : B256, devm.stack = w :: devm'.stack) →
      ∀ tail : Func.RunCompiledTo fs sevm devm' right out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchRight]⟩
          tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  cases h with
  | zero room pop tail => exact absurd rfl (branchWord _ _ pop.stack)
  | succ nonzero room pop tail =>
      exact .branchRight (nonzero := nonzero) (room := room) (pop := pop)
        (tail := tail) (armRoute _ ⟨_, pop.stack⟩ tail)

end StackKit

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

`Blanc/SourceAttainment.lean`'s route-construction kit warns that
`routeTo_line`'s prefix must be a list literal, and names
`loadWord targetWord ++ [iszero]` as a shape that fails to unify.  **That note
is stale**: both `fsig` and `arg k ++ checkNonAddress` are passed to
`routeTo_line` below and unify without complaint, so no combinator-duplicating
`def` was needed for them.  The `def`s that remain — `splitTest`,
`linearTest`, and the guard-cascade lines further down — name lines that have
no combinator form, not workarounds. -/

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
      ∀ tail : Func.RunCompiledTo fs sevm devm' (registerPauser dp) out,
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line fsig h (fun s0 run0 tail0 => ?_)
  have p0 : Sevm.selector sevm :: [] <<+ s0.stack := prefix_of_fsig nil_pref run0
  rw [selectorEq] at p0
  refine routeTo_line (splitTest (selector "pause" [.address])) tail0
    (fun _s1 run1 tail1 => ?_)
  have p1 := prefix_of_splitTest p0 run1
  refine routeTo_branchRight_stack tail1
    (fun _w _rest hs => by rw [head_of_stack_prefix p1 hs]; decide)
    (fun _s2 hpop2 tail2 => ?_)
  have p2 := tail_of_stack_prefix p1 hpop2
  refine routeTo_line (splitTest (selector "getPauser" [.address])) tail2
    (fun _s3 run3 tail3 => ?_)
  have p3 := prefix_of_splitTest p2 run3
  refine routeTo_branchRight_stack tail3
    (fun _w _rest hs => by rw [head_of_stack_prefix p3 hs]; decide)
    (fun _s4 hpop4 tail4 => ?_)
  have p4 := tail_of_stack_prefix p3 hpop4
  refine routeTo_line (linearTest (selector "pauseDuration" [])) tail4
    (fun _s5 run5 tail5 => ?_)
  have p5 := prefix_of_linearTest p4 run5
  refine routeTo_branchLeft_stack tail5
    (fun _w _rest hs => by rw [head_of_stack_prefix p5 hs]; decide)
    (fun _s6 hpop6 tail6 => ?_)
  have p6 := tail_of_stack_prefix p5 hpop6
  refine routeTo_line (linearTest (selector "MAX_PAUSE_DURATION" [])) tail6
    (fun _s7 run7 tail7 => ?_)
  have p7 := prefix_of_linearTest p6 run7
  refine routeTo_branchLeft_stack tail7
    (fun _w _rest hs => by rw [head_of_stack_prefix p7 hs]; decide)
    (fun _s8 hpop8 tail8 => ?_)
  have p8 := tail_of_stack_prefix p7 hpop8
  refine routeTo_line (linearTest (selector "ADMIN" [])) tail8
    (fun _s9 run9 tail9 => ?_)
  have p9 := prefix_of_linearTest p8 run9
  refine routeTo_branchLeft_stack tail9
    (fun _w _rest hs => by rw [head_of_stack_prefix p9 hs]; decide)
    (fun _s10 hpop10 tail10 => ?_)
  have p10 := tail_of_stack_prefix p9 hpop10
  refine routeTo_line
    (linearTest (selector "registerPauser" [.address, .address])) tail10
    (fun _s11 run11 tail11 => ?_)
  have p11 := prefix_of_linearTest p10 run11
  refine routeTo_branchRight_stack tail11
    (fun _w _rest hs => by rw [head_of_stack_prefix p11 hs]; decide)
    (fun _s12 _hpop12 tail12 => ?_)
  refine routeTo_line [Ninst.pop] tail12 (fun _s13 _run13 tail13 => ?_)
  exact bodyRoute _ _ tail13

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
      ∀ tail : Func.RunCompiledTo ((runtime dp).main :: (runtime dp).aux)
        sevm devm' (Func.call setPauserSlot) (.ok post),
        Func.RunCompiledTo.RouteTo current tail targetPath targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h targetPath
      targetInstruction := by
  refine routeTo_line registerStaticArgsTest h (fun _s0 _r0 tail0 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail0 (fuel := 4) (by rfl)
    (fun _s1 tail1 => ?_)
  refine routeTo_line (arg 0 ++ checkNonAddress) tail1 (fun _s2 _r2 tail2 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail2 (fuel := 4) (by rfl)
    (fun _s3 tail3 => ?_)
  refine routeTo_line (arg 1 ++ checkNonAddress) tail3 (fun _s4 _r4 tail4 => ?_)
  refine routeTo_branchLeft_of_rightRevertsOk tail4 (fuel := 4) (by rfl)
    (fun _s5 tail5 => ?_)
  refine routeTo_line (adminTest dp) tail5 (fun _s6 _r6 tail6 => ?_)
  refine routeTo_branchRight_of_leftRevertsOk tail6 (fuel := 8) (by rfl)
    (fun _s7 tail7 => ?_)
  refine routeTo_line registerStagingLine tail7 (fun _s8 _r8 tail8 => ?_)
  exact callRoute _ _ tail8

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
  routeTo_call h (by rfl) fun _kernelStart tail =>
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
    (fun _current _devm' bodyTail =>
      registerPauser_routeTo_setPauserCall dp bodyTail
        (fun _c _d callTail => call_setPauserSlot_routeTo_assignment_ok dp callTail))

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

/-! ## The frame-entry-freedom certificate

The one obligation `Prog.exec_of_runCompiledTo_routeTo_parentPrefix` leaves
inside its existential, named at this world.  Everything else the positive
witness needs is proved below; this is not.

It is *true* — the runtime's only two frame-entering sites are the `CALL` and
`STATICCALL` of `pauseAfterSet`, and an admin registration reaches neither —
but nothing landed proves it for a bridge-built derivation.  The direct-pause
control gets the matching fact as *data*: its chronology threads a bespoke
`Func.RunCompiledTo`-indexed path predicate
(`Blanc/LidoCircuitBreakerRegistry.lean`'s private `DirectPausePath`) whose
every `.next` node carries a childless side condition, and
`directPause_zeroCode_postWrite_error_control` exports the resulting
`∀ occurrence, instruction ≠ .exec .call ∧ instruction ≠ .exec .statcall`.
The fresh-registration chronology carries no such predicate, and
`runtimeExec_instruction_exact` only *narrows* a reached frame-entering
instruction to `CALL`/`STATICCALL` — it does not exclude one.

So the gap is stated below in exactly the direct-pause control's shape, and
`frameEntryFree_of_noExternalCall` shows that shape is all the bridge needs.
Closing it needs either a registration-side path predicate or a
contract-neutral source-level `.exec`-freedom certificate consumed against a
sealed walk, in the style of `Func.alwaysRevertsWithin`. -/

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

/-- The open gap, in the direct-pause control's own shape: no occurrence of a
fresh-registration derivation is an external call. -/
def FreshRegistrationNoExternalCall : Prop :=
  ∀ (post : Devm) (exc : Exec 0 freshWorldSevm freshWorldPre (.ok post))
    (occurrence : Exec.NinstOccurrence
      (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ : Exec.Deriv)),
    occurrence.instruction ≠ .exec .call ∧
      occurrence.instruction ≠ .exec .statcall

/-- No same-frame reached node of a fresh-registration derivation decodes a
frame-entering instruction. -/
def FreshRegistrationFrameEntryFree : Prop :=
  ∀ (post : Devm) (exc : Exec 0 freshWorldSevm freshWorldPre (.ok post))
    (node : Exec.Deriv),
    Exec.Deriv.ParentPrefix
      (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ : Exec.Deriv) node →
    ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x)

/-- Excluding the runtime's two external-call opcodes excludes every
frame-entering instruction: `runtimeExec_instruction_exact` supplies the rest,
because `CREATE`, `CREATE2`, `CALLCODE` and `DELEGATECALL` are absent from the
runtime's structural source map. -/
theorem frameEntryFree_of_noExternalCall
    (noExternal : FreshRegistrationNoExternalCall) :
    FreshRegistrationFrameEntryFree := by
  intro post exc node prefixed x decoded
  rcases Exec.exists_ninstOccurrence_of_mem_rawNodes
      (root := (⟨0, freshWorldSevm, freshWorldPre, .ok post, exc⟩ :
        Exec.Deriv))
      (Exec.mem_rawNodes_of_parentPrefix_root prefixed) decoded with
    ⟨occurrence, -, instructionEq⟩
  rcases runtimeExec_instruction_exact (freshWorld_exactInvocation exc)
      prefixed decoded with rfl | rfl
  · exact (noExternal post exc occurrence).1 instructionEq
  · exact (noExternal post exc occurrence).2 instructionEq

/-! ## The positive witness -/

/-- The first positive attainment witness, modulo frame-entry freedom: the
concrete admin registration of `Blanc/LidoCircuitBreakerRegistrationWorld.lean`
reaches the `.setPauserAssignment` row's own frozen source site with the
`.adminRegistry` invocation role.

Nothing in `Attainable` is relaxed, existentially hidden or hypothesised: the
row is named, the role is named, and the frame premises are the ones
`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` consumes.  The
single antecedent is the certificate above. -/
theorem attainable_setPauserAssignment_adminRegistry_of_frameEntryFree
    (free : FreshRegistrationFrameEntryFree) :
    Attainable officialParams .setPauserAssignment .adminRegistry := by
  obtain ⟨_trace, post, _htrace, _hentries, _hwitness, hrun, _hexec, _hfilled,
    _hgas, _hexpiry, _hlogs, hcompile⟩ := freshRegistrationWorld_run
  obtain ⟨mid, hburn, hwalk⟩ := hrun
  have hroute := runtimeMain_routeTo_setPauserAssignment officialParams hwalk
    freshWorld_dataFacts.2.1
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    package⟩ :=
    Prog.exec_of_runCompiledTo_routeTo_parentPrefix hburn hroute hcompile
  obtain ⟨_descendants, _frameRoots, sameFrame⟩ := package (free post exc)
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

/-- The same witness from the direct-pause control's own certificate shape.
This is the form a registration chronology would export, so it is the exact
statement of what is still missing. -/
theorem attainable_setPauserAssignment_adminRegistry_of_noExternalCall
    (noExternal : FreshRegistrationNoExternalCall) :
    Attainable officialParams .setPauserAssignment .adminRegistry :=
  attainable_setPauserAssignment_adminRegistry_of_frameEntryFree
    (frameEntryFree_of_noExternalCall noExternal)

end Blanc.LidoCircuitBreaker
