import Blanc.SourceAttainment
import Blanc.LidoCircuitBreakerAuthority
import Blanc.LidoCircuitBreakerFreshRegistration
import Batteries.Tactic.OpenPrivate

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
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

open private RuntimePersistentWrite.sourceFunctionIndex
  RuntimePersistentWrite.sourceSite?_functionIndex
  runtimePersistentSourceSite_eq_of_pc
  from Blanc.LidoCircuitBreakerAuthority

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

/-! ## A route-inversion kit

`Blanc/SourceAttainment.lean` decorates a `Func.RunCompiledTo` derivation, and
every forward walk in this repository (`func_run`) produces such a derivation
*opaquely*: the tactic applies introduction lemmas and hands back a sealed
proof term.  A consumer therefore has to recover the route from the derivation
rather than build the two together.

Because `Func.RunCompiledTo` is a `Prop`, definitional proof irrelevance makes
`RouteTo`'s derivation index vacuous, so every lemma below is stated in
continuation form: the caller never names an intermediate `Devm`, and one
`cases` per source node recovers exactly the premises the corresponding
`RouteTo` constructor wants.  The `.next` and `.call` crossings are free in
this style.  A `.branch` crossing is not: the sealed derivation does not record
which arm ran, so the caller must supply the branch word, which is why
`routeTo_line` also hands back the crossed `Line.Run`. -/

section RouteKit

variable {fs : List Func} {sevm : Sevm} {out : Execution}

/-- Designate the current `.next` head as the route's target. -/
theorem routeTo_head {devm : Devm} {instruction : Ninst} {body : Func}
    (h : Func.RunCompiledTo fs sevm devm (.next instruction body) out)
    (path : Prog.SourcePath) :
    Func.RunCompiledTo.RouteTo path h path instruction := by
  cases h with
  | next instructionRun tail =>
      exact .head (instructionRun := instructionRun) (tail := tail)

/-- Cross one `.next` node, keeping the crossed instruction's own step. -/
theorem routeTo_next {devm : Devm} {instruction : Ninst} {body : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.next instruction body) out)
    (tailRoute : ∀ devm' : Devm,
      Ninst.RunCompiled sevm devm instruction devm' →
      ∀ tail : Func.RunCompiledTo fs sevm devm' body out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.rest]⟩ tail
          target targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h target
      targetInstruction := by
  cases h with
  | next instructionRun tail =>
      exact .rest (instructionRun := instructionRun) (tail := tail)
        (tailRoute _ instructionRun tail)

/-- Cross a whole straight-line prefix in one step, handing the continuation
the `Line.Run` it needs to compute the stack at the next branch.  One
induction here replaces one `cases` per instruction at every use site. -/
theorem routeTo_line {body : Func} {functionIndex : Nat}
    {target : Prog.SourcePath} {targetInstruction : Ninst} :
    ∀ (line : Line) {devm : Devm} {steps : List Prog.SourceStep}
      (h : Func.RunCompiledTo fs sevm devm (line +++ body) out),
      (∀ devm' : Devm, Line.Run sevm devm line devm' →
        ∀ tail : Func.RunCompiledTo fs sevm devm' body out,
          Func.RunCompiledTo.RouteTo
            ⟨functionIndex, steps ++ List.replicate line.length .rest⟩ tail
            target targetInstruction) →
      Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h target
        targetInstruction
  | [], devm, steps, h, bodyRoute => by
      have route := bodyRoute devm .nil h
      simp only [List.length_nil, List.replicate_zero, List.append_nil]
        at route
      exact route
  | instruction :: line, devm, steps, h, bodyRoute => by
      refine routeTo_next h (fun devm' instructionRun tail => ?_)
      refine routeTo_line line tail (fun devm'' lineRun tailBody => ?_)
      have appended :
          (steps ++ [Prog.SourceStep.rest]) ++
              List.replicate line.length .rest =
            steps ++ List.replicate (instruction :: line).length .rest := by
        simp [List.replicate_succ]
      rw [appended]
      exact bodyRoute devm''
        (.cons (Ninst.Run.of_runCompiled instructionRun) lineRun) tailBody

/-- Cross an internal `.call`, restarting the source position at the callee's
root exactly as `Prog.sourceSites` does. -/
theorem routeTo_call {devm : Devm} {index : Nat} {body : Func}
    {current target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.call index) out)
    (lookup : fs[index]? = some body)
    (bodyRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm devm' body out,
        Func.RunCompiledTo.RouteTo ⟨index, []⟩ tail target targetInstruction) :
    Func.RunCompiledTo.RouteTo current h target targetInstruction := by
  cases h with
  | call lookup' room burn tail =>
      have bodyEq : body = _ := Option.some.inj (lookup.symm.trans lookup')
      subst bodyEq
      exact .call (lookup := lookup') (room := room) (burn := burn)
        (tail := tail) (bodyRoute _ tail)

/-- Take a `.branch`'s fall-through arm.  The sealed derivation does not say
which arm ran, so the caller supplies the branch word. -/
theorem routeTo_branchLeft {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (branchWord : ∀ w : B256, ∀ rest : Stack, devm.stack = w :: rest → w = 0)
    (armRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm devm' left out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchLeft]⟩
          tail target targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h target
      targetInstruction := by
  cases h with
  | zero room pop tail =>
      exact .branchLeft (room := room) (pop := pop) (tail := tail)
        (armRoute _ tail)
  | succ nonzero room pop tail =>
      exact absurd (branchWord _ _ pop.stack) nonzero

/-- Take a `.branch`'s jumped arm, under the same obligation. -/
theorem routeTo_branchRight {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {target : Prog.SourcePath} {targetInstruction : Ninst}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (branchWord : ∀ w : B256, ∀ rest : Stack, devm.stack = w :: rest → w ≠ 0)
    (armRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm devm' right out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchRight]⟩
          tail target targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h target
      targetInstruction := by
  cases h with
  | zero room pop tail => exact absurd rfl (branchWord _ _ pop.stack)
  | succ nonzero room pop tail =>
      exact .branchRight (nonzero := nonzero) (room := room) (pop := pop)
        (tail := tail) (armRoute _ tail)

end RouteKit

/-! ## The last leg of the `setPauser.assignment` route

The kit above, exercised on the exact production `Func`.  This is the leg the
`.setPauserAssignment` row's attainment witness ends with: from the callee root
of `setPauserKernel` down to the assignment `SSTORE`: seventeen crossed source
nodes, one branch, and the designated head.  Nothing here reduces a program
counter. -/

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

/-! ## What a positive witness still needs

`Attainable officialParams .setPauserAssignment .adminRegistry` is not proved
here, and the three legs above say exactly what is missing.

* **Branch words.**  Every leg's execution premise is a branch word, and the
  sealed `Func.RunCompiledTo` derivation does not record which arm ran.
  Twelve branches separate program entry from the assignment `SSTORE`: one
  entry guard in `runtimeMain`, two `splitDispatch` pivots and four
  `linearDispatchWith` selector tests in `hybridDispatchWith`, four in
  `registerPauser`'s guard cascade, and the one this file crosses in
  `setPauserKernel`.
  `Blanc/CommonProofs.lean`'s `prefix_of_*` family propagates a stack prefix
  across an `Ninst.Run`, which is what `routeTo_line`'s `Line.Run` witness was
  put there to feed; `prefix_of_callvalue`, `prefix_of_calldatasize` and a
  `pushB256` prefix lemma have no `prefix_of_*` form yet.
* **A concrete admin registration.**  `Attainable` is closed, so the witness
  has to instantiate `registerPauser_runCompiledTo_freshNonzero` at a concrete
  world and discharge its whole hypothesis block, the way
  `directPauseControl_*` does for the direct-`pause` control.  There is no
  registration analogue of that control yet.
* **`ParentPrefix`.**  `Prog.exec_of_runCompiledTo_routeTo` yields an
  occurrence with `reached`, not with `Exec.Deriv.ParentPrefix`.  Bridging
  needs `Exec.rawFrameDescendants = []`, which
  `Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt` reduces to "no
  reached node decodes as `.exec`" — a certificate the direct-`pause` control
  carries explicitly and that a registration control would have to carry too.

None of the three is a defeq-tower problem; the route skeleton above is free. -/

end Blanc.LidoCircuitBreaker
