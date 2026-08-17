-- SourceAttainment.lean : forward source attribution for `Func.RunCompiledTo`.
--
-- `Blanc/Reverts.lean`'s bridge (`Func.exec_of_runCompiledTo_core`) builds an
-- `Exec` forward from a gas-exact walk, with every program counter a closed
-- arithmetic term -- and then seals the whole construction into
-- `Nonempty (Exec pc sevm devm ex)`, discarding the pcs it was born knowing.
-- `Blanc/ExecutionOccurrence.lean`'s source machinery
-- (`Exec.Deriv.SourceCursor`) recovers source attribution in the *backward*
-- direction, from a nominated reached node.  This module closes the gap in the
-- forward direction: from a `Func.RunCompiledTo` derivation plus a route
-- decoration, it constructs an `Exec` occurrence whose source site is known by
-- construction -- path identity plus inventory membership.
--
-- Two design facts carry the whole module.
--
-- * **Row naming needs no pc reduction.**  `Func.sourceSites` computes site
--   pcs with the *identical* arithmetic the walk performs (`.next` steps
--   `pc + instruction.size`; a fall-through arm starts at `pc + 4`; a jumped
--   arm starts at `loc + 1 = pc + compsize left + 5`).  So the bridge
--   maintains (a) a concrete `Prog.SourcePath` and (b) membership of the
--   designated site in `program.sourceSites` structurally, and never reduces
--   a pc numerically.  A consumer forces the concrete pc later by `decide`
--   against its own concrete, `Nodup` inventory.
-- * **An occurrence depends on its root only through `reached`.**  Every
--   other field of `Exec.NinstOccurrence` mentions the occurrence's own node,
--   so transferring an occurrence across an extension of the derivation is
--   transferring one list membership.
--
-- The decoration (`Func.RunCompiledTo.RouteTo`) is instruction-generic: the
-- designated head is whatever `Ninst` sits there.  Nothing in this module
-- mentions a concrete program or instruction kind.
--
-- Two ergonomic traps sit in front of every consumer, and both are documented
-- in full under *The route-construction kit* below: `RouteTo`'s constructors
-- cannot be `apply`d (proof irrelevance leaves their data arguments
-- unassigned, so use the `routeTo_*` kit), and `routeTo_line`'s prefix
-- argument must be a list literal rather than a `++` of combinators.

import Blanc.Reverts
import Blanc.ExecutionOccurrence

namespace Blanc

open Jaune

/-! ## Membership transfer across derivation extensions

The two facts that let a constructed occurrence survive the wrapping of its
derivation into a larger one: a `.cont` prepend keeps every raw node, and the
instruction-step wrapper (`Ninst.exec_of_stepRun`'s construction) keeps every
raw node of its tail.  The second lemma is `Ninst.exec_of_stepRun`
(`Blanc/Compiled.lean`) with the construction's shape exposed just enough to
name the membership transfer; its intended final home is beside the original. -/

/-- Prepending a `.cont` step preserves raw-chronology membership. -/
lemma Exec.mem_rawNodes_cont {pc pc' : Nat} {sevm : Sevm}
    {devm devm' : Devm} {exn : Execution} {node : Exec.Deriv}
    (hstep : Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm')
    (next : Exec pc' sevm devm' exn)
    (hn : node ∈ Exec.rawNodes next) :
    node ∈ Exec.rawNodes (Exec.cont hstep next) := by
  simp only [Exec.rawNodes, List.mem_cons]
  exact Or.inr hn

/-- `Ninst.exec_of_stepRun`, with the produced derivation's raw chronology
containing the tail's.  The case analysis is the original's; only the
conclusion is richer. -/
lemma Ninst.exec_of_stepRun_extend {pc : Nat} {sevm : Sevm}
    {devm devmMid : Devm} {n : Ninst} {xl : Xlot} {exn : Execution}
    (h_at : Ninst.At sevm.code pc n)
    (h_filled : xl.Filled)
    (h_step : Ninst.StepRun pc sevm devm n xl (.ok devmMid))
    (tail : Exec (pc + n.size) sevm devmMid exn) :
    ∃ exc : Exec pc sevm devm exn,
      ∀ node : Exec.Deriv, node ∈ Exec.rawNodes tail →
        node ∈ Exec.rawNodes exc := by
  have hstep : Evm.step ⟨pc, sevm, devm⟩ = Ninst.step ⟨pc, sevm, devm⟩ n :=
    Evm.step_next h_at
  cases n with
  | reg r =>
    rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_step
    have hcont : Evm.step ⟨pc, sevm, devm⟩ =
        .cont (pc + Ninst.size (.reg r)) devmMid := by
      rw [hstep, Ninst.step_reg, ← h_step.2]
      rfl
    refine ⟨.cont hcont tail, fun node hn => ?_⟩
    simp only [Exec.rawNodes, List.mem_cons]
    exact Or.inr hn
  | push xs le =>
    rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_step
    have hcont : Evm.step ⟨pc, sevm, devm⟩ =
        .cont (pc + Ninst.size (.push xs le)) devmMid := by
      rw [hstep, Ninst.step_push, ← h_step.2]
      rfl
    refine ⟨.cont hcont tail, fun node hn => ?_⟩
    simp only [Exec.rawNodes, List.mem_cons]
    exact Or.inr hn
  | exec x =>
    rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at h_step
    cases hx : Xinst.step sevm devm x with
    | done e =>
      rw [hx] at h_step
      simp only [XStep.Run] at h_step
      have hcont : Evm.step ⟨pc, sevm, devm⟩ =
          .cont (pc + Ninst.size (.exec x)) devmMid := by
        rw [hstep, Ninst.step_exec, hx, ← h_step.2]
        rfl
      refine ⟨.cont hcont tail, fun node hn => ?_⟩
      simp only [Exec.rawNodes, List.mem_cons]
      exact Or.inr hn
    | spawn fr rsm =>
      rw [hx] at h_step
      rcases h_step with ⟨r, hframe, hex⟩
      have hstep' : Evm.step ⟨pc, sevm, devm⟩ = .spawn fr rsm (pc + 1) := by
        rw [hstep, Ninst.step_exec, hx]
        rfl
      unfold RunFrame at hframe
      rcases henter : fr.enter with r' | cevm <;>
        simp only [henter] at hframe
      · refine ⟨.doneOk hstep' henter (hframe.2 ▸ hex.symm) tail,
          fun node hn => ?_⟩
        simp only [Exec.rawNodes, List.mem_cons]
        exact Or.inr hn
      · rcases hframe with ⟨raw, hxl, hr⟩
        subst hxl
        obtain ⟨excChild⟩ : Nonempty (Exec cevm.pc cevm.sta cevm.dyna raw) :=
          h_filled
        have hresume : rsm.run (fr.settle raw) = .ok devmMid := by
          rw [← hr]
          exact hex.symm
        refine ⟨.runOk hstep' henter excChild hresume tail,
          fun node hn => ?_⟩
        simp only [Exec.rawNodes, List.mem_cons, List.mem_append]
        exact Or.inr (Or.inr hn)

/-! ## The route decoration

A `Func.RunCompiledTo.RouteTo current run target instruction` decoration walks
alongside a `Func.RunCompiledTo` derivation from the source position `current`,
descends through the derivation's structural rules while accumulating the
matching `Prog.SourceStep`s, and designates one `.next` head as the target.
The final source position and the designated instruction ride along as
indices, so a route pins its target's identity syntactically.

The constructors mirror the derivation's: `head` and `rest` split `.next`
(designate here versus descend), `branchLeft` mirrors `.zero`, `branchRight`
mirrors `.succ`, and `call` mirrors `.call`, restarting the position at the
callee's root exactly as `Prog.sourceSites` does.  `.last` has no mirror: a
terminal instruction is not a `.next` head, so no route ends there. -/

/-- A route through a `Func.RunCompiledTo` derivation to one designated
`.next` head, carrying the source position alongside the walk. -/
inductive Func.RunCompiledTo.RouteTo :
    ∀ {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
      {out : Execution}, Prog.SourcePath →
      Func.RunCompiledTo fs sevm pre body out →
      Prog.SourcePath → Ninst → Prop
  | head {fs sevm pre post instruction body out}
      {functionIndex : Nat} {steps : List Prog.SourceStep}
      {instructionRun : Ninst.RunCompiled sevm pre instruction post}
      {tail : Func.RunCompiledTo fs sevm post body out} :
      Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩
        (.next instructionRun tail) ⟨functionIndex, steps⟩ instruction
  | rest {fs sevm pre post instruction body out}
      {functionIndex : Nat} {steps : List Prog.SourceStep}
      {target : Prog.SourcePath} {targetInstruction : Ninst}
      {instructionRun : Ninst.RunCompiled sevm pre instruction post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (tailRoute : Func.RunCompiledTo.RouteTo
        ⟨functionIndex, steps ++ [.rest]⟩ tail target targetInstruction) :
      Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩
        (.next instructionRun tail) target targetInstruction
  | branchLeft {fs sevm pre post leftArm rightArm out}
      {functionIndex : Nat} {steps : List Prog.SourceStep}
      {target : Prog.SourcePath} {targetInstruction : Ninst}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre post}
      {tail : Func.RunCompiledTo fs sevm post leftArm out}
      (armRoute : Func.RunCompiledTo.RouteTo
        ⟨functionIndex, steps ++ [.branchLeft]⟩ tail target
        targetInstruction) :
      Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩
        (.zero (g := rightArm) room pop tail) target targetInstruction
  | branchRight {fs sevm pre post leftArm rightArm out}
      {functionIndex : Nat} {steps : List Prog.SourceStep}
      {target : Prog.SourcePath} {targetInstruction : Ninst}
      {word : B256} {nonzero : word ≠ 0}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [word] (gVerylow + gHigh + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post rightArm out}
      (armRoute : Func.RunCompiledTo.RouteTo
        ⟨functionIndex, steps ++ [.branchRight]⟩ tail target
        targetInstruction) :
      Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩
        (.succ (f := leftArm) nonzero room pop tail) target targetInstruction
  | call {fs sevm pre post index body out}
      {current target : Prog.SourcePath} {targetInstruction : Ninst}
      {lookup : fs[index]? = some body}
      {room : pre.stack.length < 1024}
      {burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (bodyRoute : Func.RunCompiledTo.RouteTo ⟨index, []⟩
        tail target targetInstruction) :
      Func.RunCompiledTo.RouteTo current (.call lookup room burn tail)
        target targetInstruction

/-! ## The route-construction kit

**The constructors above cannot be used with `apply` or `refine`.**
`Func.RunCompiledTo` is a `Prop`, so definitional proof irrelevance unifies
`RouteTo`'s derivation index against *any* derivation of the right type
without ever assigning the constructor's data arguments (`instructionRun`,
`tail`, `post`, and the branch/call side conditions).  `apply
Func.RunCompiledTo.RouteTo.head` therefore succeeds on unification and leaves
unsolvable metavariables behind.  Every consumer hits this; nobody should
re-derive the diagnosis.

The kit below is the supported way in.  Each lemma takes the derivation as an
ordinary hypothesis, does one `cases` on it — which *does* bind the data
arguments — and hands the recovered premises to a continuation.  A caller
therefore never names an intermediate `Devm`, and never applies a constructor
directly.  This matters because every forward walk in this repository is
produced opaquely (`func_run` applies introduction lemmas and returns a sealed
proof term), so a consumer must recover its route from the derivation rather
than build the two together.

The `.next` and `.call` crossings are free in this style.  A `.branch`
crossing is not: the sealed derivation does not record which arm ran, so the
caller supplies the branch word.  That is why `routeTo_line` also hands back
the crossed `Line.Run` — without it the caller cannot compute the stack, and
hence the branch word, at the next branch.

**Second trap: `prepend`'s argument must be a list literal.**  `routeTo_line`
unifies the walked body against `line +++ body`, and the unifier has to see
`line` in constructor form to expose the walk's head.  So

    routeTo_line (loadWord targetWord ++ [iszero]) h    -- fails to unify
    routeTo_line [pushB256 (targetWord * 32), mload, iszero] h    -- succeeds

Spell the crossed prefix out as a literal (a `def` whose body is a literal is
fine), even where a combinator would read better. -/

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
induction here replaces one `cases` per instruction at every use site.

`line` must be supplied as a list literal; see this section's note. -/
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

/-! ## Wrong-arm refutation

A `.branch` crossing is the kit's one priced step: `routeTo_branchLeft` and
`routeTo_branchRight` make the caller supply the branch word, which means
propagating a stack prefix down to the branch.  On a long dispatcher that is
the dominant cost of a route.

Often it is avoidable.  If the arm *not* taken can only ever revert, then a
walk whose outcome commits cannot have gone that way, and the arm is settled
without computing anything about the stack.  `Func.alwaysRevertsWithin` is the
executable certificate for "can only revert", and the two route lemmas below
consume it in place of a branch word.

The refutation is post-hoc, which is the point: it works on a *sealed*
derivation, since it reads only the derivation's outcome index. -/

/-- Executable finite certificate that a source body, and every table body it
can reach within `fuel`, can only end in `REVERT`.  A zero fuel is
deliberately false, so a successful certificate can never hide a recursive
call cycle. -/
def Func.alwaysRevertsWithin : Nat → List Func → Func → Bool
  | 0, _, _ => false
  | fuel + 1, fs, .branch left right =>
      alwaysRevertsWithin fuel fs left && alwaysRevertsWithin fuel fs right
  | _fuel + 1, _, .last terminal => terminal == Linst.rev
  | fuel + 1, fs, .next _instruction tail => alwaysRevertsWithin fuel fs tail
  | fuel + 1, fs, .call index =>
      match fs[index]? with
      | none => false
      | some body => alwaysRevertsWithin fuel fs body

/-- `REVERT` never commits, however its operand reads fail.  Every arm of
`Linst.run`'s `.rev` case ends in `.error`, so no `.ok` outcome has a `.rev`
derivation. -/
theorem Linst.not_commits_of_run_rev {sevm : Sevm} {devm : Devm}
    {out : Execution} (run : Linst.Run sevm devm .rev out) :
    Execution.commits out = false := by
  cases out with
  | error _ => rfl
  | ok post =>
      exfalso
      simp only [Linst.Run, Linst.run] at run
      rcases Except.bind_eq_ok run with ⟨v1, h1, h2⟩
      rcases Except.bind_eq_ok h2 with ⟨v2, h3, h4⟩
      rcases Except.bind_eq_ok h4 with ⟨v3, h5, h6⟩
      contradiction

/-- Soundness of the certificate against an arbitrary sealed walk: a certified
body cannot produce a committing outcome.  The induction follows the
derivation's own branch and call structure; the Boolean is only the finite
source certificate that closes each path. -/
theorem Func.RunCompiledTo.not_commits_of_alwaysRevertsWithin
    {fs : List Func} {sevm : Sevm} :
    ∀ (fuel : Nat) {devm : Devm} {body : Func} {out : Execution},
      Func.RunCompiledTo fs sevm devm body out →
      Func.alwaysRevertsWithin fuel fs body = true →
      Execution.commits out = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro _devm _body _out _run certified
      simp [Func.alwaysRevertsWithin] at certified
  | succ fuel ih =>
      intro devm body out run certified
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
          | last terminalRun => exact Linst.not_commits_of_run_rev terminalRun
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

section WrongArm

variable {fs : List Func} {sevm : Sevm} {out : Execution}

/-- Take a `.branch`'s fall-through arm without computing the branch word: the
jumped arm can only revert, and this walk's outcome commits. -/
theorem routeTo_branchLeft_of_rightReverts {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {target : Prog.SourcePath} {targetInstruction : Ninst} {fuel : Nat}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (rightReverts : Func.alwaysRevertsWithin fuel fs right = true)
    (committed : Execution.commits out = true)
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
      rw [Func.RunCompiledTo.not_commits_of_alwaysRevertsWithin fuel tail
        rightReverts] at committed
      exact absurd committed (by simp)

/-- Take a `.branch`'s jumped arm under the mirrored certificate. -/
theorem routeTo_branchRight_of_leftReverts {devm : Devm} {left right : Func}
    {functionIndex : Nat} {steps : List Prog.SourceStep}
    {target : Prog.SourcePath} {targetInstruction : Ninst} {fuel : Nat}
    (h : Func.RunCompiledTo fs sevm devm (.branch left right) out)
    (leftReverts : Func.alwaysRevertsWithin fuel fs left = true)
    (committed : Execution.commits out = true)
    (armRoute : ∀ devm' : Devm,
      ∀ tail : Func.RunCompiledTo fs sevm devm' right out,
        Func.RunCompiledTo.RouteTo ⟨functionIndex, steps ++ [.branchRight]⟩
          tail target targetInstruction) :
    Func.RunCompiledTo.RouteTo ⟨functionIndex, steps⟩ h target
      targetInstruction := by
  cases h with
  | zero room pop tail =>
      rw [Func.RunCompiledTo.not_commits_of_alwaysRevertsWithin fuel tail
        leftReverts] at committed
      exact absurd committed (by simp)
  | succ nonzero room pop tail =>
      exact .branchRight (nonzero := nonzero) (room := room) (pop := pop)
        (tail := tail) (armRoute _ tail)

end WrongArm

/-! ## The strengthened bridge

The same induction as `Func.exec_of_runCompiledTo_core`, on the decoration
instead of the bare derivation, with the same hypotheses plus one: the sites
of the current source position are included in the program's inventory.  At
the designated head the derivation is bridged whole and its root node *is*
the occurrence; along the route each case rebuilds exactly the `Exec` nodes
the plain bridge builds and transfers the deeper occurrence across them.

The conclusion names the site by path identity and inventory membership, and
never by a reduced pc: `occurrence.node.pc = site.pc` is `rfl`-true of the
constructed site, and which *number* that is stays a question about
`program.sourceSites` that a consumer settles by `decide`.

The instruction is named the same way, and in both directions: the chain
`occurrence.instruction = site.instruction = instruction` closes the route's
own index against the reached occurrence, so a consumer that routed to a
concrete `Ninst` recovers `occurrence.instruction = instruction` without
`decide`ing against an inventory for a fact the route already fixed. -/

theorem Func.exec_of_runCompiledTo_routeTo_core :
    ∀ {f₀ : Func} {fs' : List Func} {sevm : Sevm} {FS : List Func}
      {devm : Devm} {p : Func} {ex : Execution}
      {h_run : Func.RunCompiledTo FS sevm devm p ex}
      {path target : Prog.SourcePath} {instruction : Ninst},
      Func.RunCompiledTo.RouteTo path h_run target instruction →
      some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩ →
      FS = f₀ :: fs' →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (f₀ :: fs')) pc p) →
        noPushBefore sevm.code pc 32 = true →
        (∀ site ∈ Func.sourceSites path.functionIndex path.steps pc p,
          site ∈ Prog.sourceSites ⟨f₀, fs'⟩) →
        ∃ exc : Exec pc sevm devm ex,
          ∃ occurrence : Exec.NinstOccurrence ⟨pc, sevm, devm, ex, exc⟩,
            ∃ site : Prog.SourceSite,
              site.path = target ∧
              site ∈ Prog.sourceSites ⟨f₀, fs'⟩ ∧
              occurrence.node.pc = site.pc ∧
              occurrence.instruction = site.instruction ∧
              site.instruction = instruction := by
  intro f₀ fs' sevm FS devm p ex h_run path target instruction h_route
  induction h_route with
  | @head pre post instr body out functionIndex steps
      instructionRun tail =>
    intro h_eq hFS pc sub hb included
    obtain ⟨exc⟩ := Func.exec_of_runCompiledTo_core
      (Func.RunCompiledTo.next instructionRun tail) h_eq hFS pc sub hb
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
    rw [← of_pure_eq_some h_rw] at h_slice
    have h_at : Ninst.At sevm.code pc instr :=
      Ninst.at_of_slice (List.slice_prefix h_slice)
    obtain ⟨occurrence, hnode, hinstr⟩ :=
      Exec.exists_ninstOccurrence_of_mem_rawNodes
        (root := ⟨pc, sevm, pre, out, exc⟩)
        (node := ⟨pc, sevm, pre, out, exc⟩)
        (Exec.mem_rawNodes_self exc) h_at
    refine ⟨exc, occurrence, ⟨⟨functionIndex, steps⟩, pc, instr⟩, rfl,
      included _ (by simp [Func.sourceSites]), ?_, hinstr, rfl⟩
    rw [hnode]
  | @rest pre post instr body out functionIndex steps target
      targetInstruction instructionRun tail tailRoute ih =>
    intro h_eq hFS pc sub hb included
    rcases Func.noPushBefore_next sub hb with ⟨hb', sub'⟩
    rcases of_subcode sub with ⟨cd, h_eq', h_slice⟩
    rcases of_bind_eq_some h_eq' with ⟨cd', h_eq'', h_rw⟩
    rw [← of_pure_eq_some h_rw] at h_slice
    have h_at : Ninst.At sevm.code pc instr :=
      Ninst.at_of_slice (List.slice_prefix h_slice)
    obtain ⟨excTail, occurrence, site, hpath, hmem, hpc, hinstr, hsite⟩ :=
      ih h_eq hFS (pc + instr.size) sub' hb'
        (fun site member => included site
          (by simp [Func.sourceSites, member]))
    rcases instructionRun with ⟨xl, h_filled, h_step⟩
    obtain ⟨exc, hsub⟩ :=
      Ninst.exec_of_stepRun_extend h_at h_filled (h_step pc) excTail
    exact ⟨exc, ⟨occurrence.node, occurrence.instruction, occurrence.slot,
      occurrence.stepResult, hsub _ occurrence.reached, occurrence.decoded,
      occurrence.filled, occurrence.stepRun⟩, site, hpath, hmem, hpc, hinstr,
      hsite⟩
  | @branchLeft pre post leftArm rightArm out functionIndex steps
      target targetInstruction room pop tail armRoute ih =>
    intro h_eq hFS pc sub hb included
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp,
        h_subq, h_bq⟩
    rcases Evm.branch_zero_steps h_push h_jumpi h_loc room pop with ⟨h1, h2⟩
    obtain ⟨excf, occurrence, site, hpath, hmem, hpc, hinstr⟩ :=
      ih h_eq hFS (pc + 4) h_subp h_bp
        (fun site member => included site (by
          simp only [Func.sourceSites, List.mem_append]
          exact Or.inl member))
    refine ⟨.cont h1 (.cont h2 excf),
      ⟨occurrence.node, occurrence.instruction, occurrence.slot,
        occurrence.stepResult, ?_, occurrence.decoded, occurrence.filled,
        occurrence.stepRun⟩, site, hpath, hmem, hpc, hinstr⟩
    exact Exec.mem_rawNodes_cont h1 _
      (Exec.mem_rawNodes_cont h2 _ occurrence.reached)
  | @branchRight pre post leftArm rightArm out functionIndex steps
      target targetInstruction word nonzero room pop tail armRoute ih =>
    intro h_eq hFS pc sub hb included
    rcases subcode_compile_branch_jumpable sub hb with
      ⟨loc, h_loc_eq, h_loc, h_push, h_jumpi, h_subp, h_bp, h_jd, h_jp,
        h_subq, h_bq⟩
    rcases Evm.branch_succ_steps h_push h_jumpi h_jd h_jp h_loc nonzero
      room pop with ⟨h1, h2, h3⟩
    obtain ⟨excg, occurrence, site, hpath, hmem, hpc, hinstr⟩ :=
      ih h_eq hFS (loc + 1) h_subq h_bq
        (fun site member => included site (by
          simp only [Func.sourceSites, List.mem_append]
          refine Or.inr ?_
          have hpcEq : loc + 1 = pc + compsize leftArm + 5 := by omega
          rw [← hpcEq]
          exact member))
    refine ⟨.cont h1 (.cont h2 (.cont h3 excg)),
      ⟨occurrence.node, occurrence.instruction, occurrence.slot,
        occurrence.stepResult, ?_, occurrence.decoded, occurrence.filled,
        occurrence.stepRun⟩, site, hpath, hmem, hpc, hinstr⟩
    exact Exec.mem_rawNodes_cont h1 _ (Exec.mem_rawNodes_cont h2 _
      (Exec.mem_rawNodes_cont h3 _ occurrence.reached))
  | @call pre post index body out current target targetInstruction
      lookup room burn tail bodyRoute ih =>
    intro h_eq hFS pc sub hb included
    subst hFS
    rcases subcode_compile_call sub with
      ⟨loc, p₁, h_get_tab, h_loc, h_pushAt, h_jump⟩
    have h_pf := (Prog.get?_table (m := 0)).symm.trans
      (congrArg (Prod.snd <$> ·) h_get_tab)
    rw [lookup] at h_pf
    simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at h_pf
    subst h_pf
    rcases subcode_of_get?_eq_some h_eq h_get_tab with ⟨h_jd, h_subf⟩
    have h_jpb := Prog.jumpable_of_get?_table h_eq h_get_tab
    rcases h_pushAt with ⟨le, h_push⟩
    rcases Evm.call_steps (le := le) h_push h_jump h_jd h_jpb.1 h_loc
      room burn with ⟨h1, h2, h3⟩
    obtain ⟨excf, occurrence, site, hpath, hmem, hpc, hinstr⟩ :=
      ih h_eq rfl (loc + 1) h_subf h_jpb.2
        (fun site member => by
          simp only [Prog.sourceSites, List.mem_flatMap]
          refine ⟨index, ?_, ?_⟩
          · exact List.mem_range.mpr
              (List.getElem?_eq_some_iff.mp lookup).choose
          · simpa only [h_get_tab] using member)
    refine ⟨.cont h1 (.cont h2 (.cont h3 excf)),
      ⟨occurrence.node, occurrence.instruction, occurrence.slot,
        occurrence.stepResult, ?_, occurrence.decoded, occurrence.filled,
        occurrence.stepRun⟩, site, hpath, hmem, hpc, hinstr⟩
    exact Exec.mem_rawNodes_cont h1 _ (Exec.mem_rawNodes_cont h2 _
      (Exec.mem_rawNodes_cont h3 _ occurrence.reached))

/-! ## Entry wrappers

The program entry crosses `Table.compile`'s leading `JUMPDEST`, mirroring
`Prog.exec_of_runCompiledTo`; the `.ok` entry embeds a `Func.RunCompiled`
derivation through `Func.RunCompiledTo.of_runCompiled` and delegates. -/

/-- The program-level bridge: a routed walk entered at pc 0 yields an
occurrence at a site of the program's own inventory. -/
theorem Prog.exec_of_runCompiledTo_routeTo {sevm : Sevm} {pre mid : Devm}
    {p : Prog} {ex : Execution}
    {h_run : Func.RunCompiledTo (p.main :: p.aux) sevm mid p.main ex}
    {target : Prog.SourcePath} {instruction : Ninst}
    (h_burn : Devm.BurnBy gJumpdest pre mid)
    (h_route : Func.RunCompiledTo.RouteTo ⟨0, []⟩ h_run target instruction)
    (h_eq : some sevm.code.toList = p.compile) :
    ∃ exc : Exec 0 sevm pre ex,
      ∃ occurrence : Exec.NinstOccurrence ⟨0, sevm, pre, ex, exc⟩,
        ∃ site : Prog.SourceSite,
          site.path = target ∧
          site ∈ p.sourceSites ∧
          occurrence.node.pc = site.pc ∧
          occurrence.instruction = site.instruction ∧
          site.instruction = instruction := by
  have h_eq' : some sevm.code.toList = Prog.compile ⟨p.main, p.aux⟩ := h_eq
  have h_get : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some h_eq' h_get with ⟨h_jd, h_sub⟩
  have h_npb : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table h_eq' h_get).2
  have h1 : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont h_jd h_burn
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget⟩ :=
    Func.exec_of_runCompiledTo_routeTo_core h_route h_eq' rfl 1 h_sub h_npb
      (fun site member => by
        simp only [Prog.sourceSites, List.mem_flatMap]
        refine ⟨0, by simp, ?_⟩
        simpa only [h_get] using member)
  exact ⟨.cont h1 exc,
    ⟨occurrence.node, occurrence.instruction, occurrence.slot,
      occurrence.stepResult,
      Exec.mem_rawNodes_cont h1 _ occurrence.reached,
      occurrence.decoded, occurrence.filled, occurrence.stepRun⟩,
    site, hpath, hmem, hpc, hinstr, hinstrTarget⟩

/-- The `.ok` embedding: a routed `Func.RunCompiled` walk, decorated through
`Func.RunCompiledTo.of_runCompiled`, yields the same package with the outcome
pinned to `.ok`. -/
theorem Func.exec_of_runCompiled_routeTo_core {f₀ : Func} {fs' : List Func}
    {sevm : Sevm} {FS : List Func} {devm devm' : Devm} {p : Func}
    {path target : Prog.SourcePath} {instruction : Ninst}
    {h_run : Func.RunCompiled FS sevm devm p devm'}
    (h_route : Func.RunCompiledTo.RouteTo path
      (Func.RunCompiledTo.of_runCompiled h_run) target instruction)
    (h_eq : some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩)
    (hFS : FS = f₀ :: fs') :
    ∀ pc,
      subcode sevm.code.toList pc
        (Func.compile (table 0 (f₀ :: fs')) pc p) →
      noPushBefore sevm.code pc 32 = true →
      (∀ site ∈ Func.sourceSites path.functionIndex path.steps pc p,
        site ∈ Prog.sourceSites ⟨f₀, fs'⟩) →
      ∃ exc : Exec pc sevm devm (.ok devm'),
        ∃ occurrence : Exec.NinstOccurrence ⟨pc, sevm, devm, .ok devm', exc⟩,
          ∃ site : Prog.SourceSite,
            site.path = target ∧
            site ∈ Prog.sourceSites ⟨f₀, fs'⟩ ∧
            occurrence.node.pc = site.pc ∧
            occurrence.instruction = site.instruction ∧
            site.instruction = instruction :=
  Func.exec_of_runCompiledTo_routeTo_core h_route h_eq hFS

/-! ## Same-frame packaging

`Prog.exec_of_runCompiledTo_routeTo` hands back an occurrence whose only tie
to the root is `reached` — raw-chronology membership.  Every same-frame
attribution theorem downstream instead takes
`Exec.Deriv.ParentPrefix frameRoot occurrence.node`, so a consumer that stops
at `reached` has to re-derive the same glue.  The wrappers below do it once.

The bridge is frame-entry freedom: a derivation that never decodes an `Xinst`
spawns no child frame, so its raw frame traversal is the singleton outer root
and its raw chronology *is* that root's same-frame prefix.  The exclusion
covers the whole `Xinst` family — `create`, `call`, `callcode`, `delcall`,
`create2`, `statcall` — because any one alone produces a descendant;
narrowing it to the constructors a given program happens to avoid would make
the certificate unsound.

**The certificate is supplied last, not first.**  The routed bridge builds its
derivation, so no consumer can name that derivation before the bridge runs.
Rather than force the certificate to be proved for *every* derivation of the
walk's type — a real strengthening, since a frame-entry-freedom fact is
normally established about one derivation in hand — the routed wrapper hands
the certificate obligation back *inside* the existential.  A consumer
destructs first, so the concrete derivation is in context, and only then
discharges it.  The transport itself is factored out below so that a consumer
that built its own derivation (rather than routing to one) can use it
directly. -/

/-- A same-frame prefix node of a derivation is one of its raw nodes.  The
converse direction of frame-entry freedom, and the glue that lets a
`ParentPrefix`-shaped certificate stand in for a reached-node one. -/
theorem Exec.mem_rawNodes_of_parentPrefix_root {pc : Nat} {sevm : Sevm}
    {pre : Devm} {out : Execution} {run : Exec pc sevm pre out}
    {node : Exec.Deriv}
    (prefixed :
      Exec.Deriv.ParentPrefix (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) node) :
    node ∈ Exec.rawNodes run :=
  (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run node).mpr
    ⟨_, Exec.mem_rawFrameRoots_self run, prefixed⟩

/-- The transport, on a derivation in hand: a frame-entry-free root has an
empty descendant list, is the whole of its raw frame traversal, and is a
same-frame ancestor of each of its occurrences.

`parentPrefix` is exactly the `sameFrame` premise of
`Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot` and its relatives,
and `frameRoots` discharges their `frameRoot ∈ Exec.rawFrameRoots …` premise at
the root itself. -/
theorem Exec.NinstOccurrence.parentPrefix_of_no_sameFrame_xinstAt
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (occurrence : Exec.NinstOccurrence (⟨pc, sevm, pre, out, run⟩ :
      Exec.Deriv))
    (childless : ∀ node : Exec.Deriv,
      Exec.Deriv.ParentPrefix (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) node →
        ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    Exec.rawFrameDescendants run = [] ∧
      Exec.rawFrameRoots run = [⟨pc, sevm, pre, out, run⟩] ∧
      Exec.Deriv.ParentPrefix (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv)
        occurrence.node := by
  have descendants : Exec.rawFrameDescendants run = [] :=
    Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt run childless
  exact ⟨descendants, by rw [Exec.rawFrameRoots, descendants],
    Exec.Deriv.parentPrefix_of_mem_rawNodes_of_rawFrameDescendants_eq_nil
      descendants occurrence.reached⟩

/-- The same transport from the occurrence-shaped certificate: no occurrence
of the root decodes a frame-entering instruction.  This is the stronger
hypothesis — it ranges over every reached node, not only over the root frame's
own prefix — so prefer `parentPrefix_of_no_sameFrame_xinstAt` where a
same-frame fact is what is available. -/
theorem Exec.NinstOccurrence.parentPrefix_of_no_execOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (occurrence : Exec.NinstOccurrence (⟨pc, sevm, pre, out, run⟩ :
      Exec.Deriv))
    (childless : ∀ other : Exec.NinstOccurrence
        (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv),
      ∀ x : Xinst, other.instruction ≠ .exec x) :
    Exec.rawFrameDescendants run = [] ∧
      Exec.rawFrameRoots run = [⟨pc, sevm, pre, out, run⟩] ∧
      Exec.Deriv.ParentPrefix (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv)
        occurrence.node :=
  occurrence.parentPrefix_of_no_sameFrame_xinstAt
    fun node prefixed x decoded => by
      rcases Exec.exists_ninstOccurrence_of_mem_rawNodes
          (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
          (Exec.mem_rawNodes_of_parentPrefix_root prefixed) decoded with
        ⟨other, -, instructionEq⟩
      exact childless other x instructionEq

/-- `Prog.exec_of_runCompiledTo_routeTo` with the same-frame package attached:
the site identity exactly as before, plus — under a frame-entry-freedom
certificate for the derivation the bridge just built — the `ParentPrefix` and
`rawFrameRoots` facts that same-frame attribution theorems consume.

The certificate is an obligation *inside* the existential on purpose; see this
section's note.  A consumer writes

    obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
      package⟩ := …
    obtain ⟨descendants, frameRoots, sameFrame⟩ := package (by …)

so that the `by …` runs with `exc` already in context. -/
theorem Prog.exec_of_runCompiledTo_routeTo_parentPrefix {sevm : Sevm}
    {pre mid : Devm} {p : Prog} {ex : Execution}
    {h_run : Func.RunCompiledTo (p.main :: p.aux) sevm mid p.main ex}
    {target : Prog.SourcePath} {instruction : Ninst}
    (h_burn : Devm.BurnBy gJumpdest pre mid)
    (h_route : Func.RunCompiledTo.RouteTo ⟨0, []⟩ h_run target instruction)
    (h_eq : some sevm.code.toList = p.compile) :
    ∃ exc : Exec 0 sevm pre ex,
      ∃ occurrence : Exec.NinstOccurrence ⟨0, sevm, pre, ex, exc⟩,
        ∃ site : Prog.SourceSite,
          site.path = target ∧
          site ∈ p.sourceSites ∧
          occurrence.node.pc = site.pc ∧
          occurrence.instruction = site.instruction ∧
          site.instruction = instruction ∧
          ((∀ node : Exec.Deriv,
              Exec.Deriv.ParentPrefix (⟨0, sevm, pre, ex, exc⟩ : Exec.Deriv)
                node →
                ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x)) →
            Exec.rawFrameDescendants exc = [] ∧
              Exec.rawFrameRoots exc = [⟨0, sevm, pre, ex, exc⟩] ∧
              Exec.Deriv.ParentPrefix (⟨0, sevm, pre, ex, exc⟩ : Exec.Deriv)
                occurrence.node) := by
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget⟩ :=
    Prog.exec_of_runCompiledTo_routeTo h_burn h_route h_eq
  exact ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr, hinstrTarget,
    occurrence.parentPrefix_of_no_sameFrame_xinstAt⟩

end Blanc
