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
`program.sourceSites` that a consumer settles by `decide`. -/

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
              occurrence.instruction = site.instruction := by
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
      included _ (by simp [Func.sourceSites]), ?_, hinstr⟩
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
    obtain ⟨excTail, occurrence, site, hpath, hmem, hpc, hinstr⟩ :=
      ih h_eq hFS (pc + instr.size) sub' hb'
        (fun site member => included site
          (by simp [Func.sourceSites, member]))
    rcases instructionRun with ⟨xl, h_filled, h_step⟩
    obtain ⟨exc, hsub⟩ :=
      Ninst.exec_of_stepRun_extend h_at h_filled (h_step pc) excTail
    exact ⟨exc, ⟨occurrence.node, occurrence.instruction, occurrence.slot,
      occurrence.stepResult, hsub _ occurrence.reached, occurrence.decoded,
      occurrence.filled, occurrence.stepRun⟩, site, hpath, hmem, hpc, hinstr⟩
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
          occurrence.instruction = site.instruction := by
  have h_eq' : some sevm.code.toList = Prog.compile ⟨p.main, p.aux⟩ := h_eq
  have h_get : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some h_eq' h_get with ⟨h_jd, h_sub⟩
  have h_npb : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table h_eq' h_get).2
  have h1 : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont h_jd h_burn
  obtain ⟨exc, occurrence, site, hpath, hmem, hpc, hinstr⟩ :=
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
    site, hpath, hmem, hpc, hinstr⟩

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
            occurrence.instruction = site.instruction :=
  Func.exec_of_runCompiledTo_routeTo_core h_route h_eq hFS

end Blanc
