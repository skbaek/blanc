import Blanc.ExecutionOccurrence
import Blanc.Compiled
import Blanc.RunPrefix
import Blanc.GasErasure

/-!
Contract-neutral prefix transport: replay a loose gas-free `Func.RunPrefix`
onto the actual execution cursor.

The target-directed `Exec.Deriv.SourceCursor` API (`mainToward`,
`nextOfParentStep`, `branchFlagToward`, `callToward`) crosses compiler glue only
toward an already-reached target. The forward duals here need no target: under
`root.exn = .ok post` every same-frame instruction of a successful frame has a
continuation edge, so the cursor advances from the current derivation alone.

`Exec.Deriv.SourceCursor.ofRunPrefix` then walks a loose prefix and the actual
cursor in lockstep, maintaining `Devm.EqModGas` per step, and lands on the
actual node reached by the prefix's target with a same-frame `ParentPrefix`.

Caveat (design R6, inherited from `Ninst.run_eqModGas`): the identity is modulo
exactly the columns outside `Devm.Rels` as pinned; revisit at a Jaune pin bump
that adds columns outside `Devm.Rels`.
-/

namespace Blanc

open Jaune

/-! ## Forward same-frame edges of a successful frame -/

/-- A successful frame continues past every source instruction it reaches:
an `Ninst` never halts successfully, and an error would be the frame's
outcome. -/
theorem Exec.Deriv.ParentStep.exists_of_ninstAt_ok
    {start : Exec.Deriv} {instruction : Ninst} {post : Devm}
    (ok : start.exn = .ok post)
    (instructionAt : Ninst.At start.sevm.code start.pc instruction) :
    ∃ next : Exec.Deriv, Exec.Deriv.ParentStep next start := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  dsimp at ok instructionAt
  subst ok
  have hstatic :
      Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ instruction :=
    Evm.step_next instructionAt
  cases run with
  | halt h => cases Ninst.step_ne_halt_ok (hstatic.symm.trans h)
  | cont h next => exact ⟨_, .cont h next⟩
  | doneOk h henter hresume next => exact ⟨_, .doneOk h henter hresume next⟩
  | runOk h henter child hresume next =>
      exact ⟨_, .runOk h henter child hresume next⟩

/-- A successful frame crosses a compiler `PUSH` by a childless continuation
that pushes exactly the immediate word. -/
theorem Exec.Deriv.ParentStep.exists_of_pushAt_ok
    {start : Exec.Deriv} {xs : Bytes} {post : Devm}
    (ok : start.exn = .ok post)
    (pushAt : PushAt start.sevm.code start.pc xs)
    (hne : xs ≠ []) :
    ∃ (inter : Devm)
      (next : Exec (start.pc + xs.length + 1) start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ start ∧
      Devm.PushBurn [xs.toB256] start.devm inter := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  dsimp at ok pushAt ⊢
  subst ok
  rcases pushAt with ⟨le, pushAt⟩
  have hstatic :
      Evm.step ⟨pc, sevm, pre⟩ = Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
    Evm.step_next pushAt
  cases run with
  | halt h => cases Ninst.step_ne_halt_ok (hstatic.symm.trans h)
  | cont h next =>
      have sourceStep := hstatic.symm.trans h
      rw [Ninst.step_push, if_neg hne] at sourceStep
      obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont sourceStep
      cases hpc
      exact ⟨_, next, .cont h next, Devm.pushBurn_of_run hrun⟩
  | doneOk h henter hresume next =>
      exact (Step.ofExecution_ne_spawn (hstatic.symm.trans h)).elim
  | runOk h henter child hresume next =>
      exact (Step.ofExecution_ne_spawn (hstatic.symm.trans h)).elim

/-- A successful frame crosses a compiler jump instruction by a childless
continuation carrying the exact `Jinst.Run`. -/
theorem Exec.Deriv.ParentStep.exists_of_jinstAt_ok
    {start : Exec.Deriv} {instruction : Jinst} {post : Devm}
    (ok : start.exn = .ok post)
    (jumpAt : Jinst.At start.sevm.code start.pc instruction) :
    ∃ (nextPc : Nat) (inter : Devm)
      (next : Exec nextPc start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ start ∧
      Jinst.Run ⟨start.pc, start.sevm, start.devm⟩ instruction
        (.ok ⟨nextPc, inter⟩) := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  dsimp at ok jumpAt ⊢
  subst ok
  have hstatic :
      Evm.step ⟨pc, sevm, pre⟩ =
        Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
    Evm.step_jump jumpAt
  cases run with
  | halt h => cases Step.ofJump_ne_halt_ok (hstatic.symm.trans h)
  | cont h next =>
      exact ⟨_, _, next, .cont h next,
        Step.ofJump_cont (hstatic.symm.trans h)⟩
  | doneOk h henter hresume next =>
      exact (Step.ofJump_ne_spawn (hstatic.symm.trans h)).elim
  | runOk h henter child hresume next =>
      exact (Step.ofJump_ne_spawn (hstatic.symm.trans h)).elim

/-! ## Forward cursor duals -/

/-- Forward dual of `mainToward`: a successful exact compiled root crosses the
compiler's leading `JUMPDEST` into the main body. -/
theorem Exec.Deriv.SourceCursor.mainForward
    {root : Exec.Deriv} {program : Prog}
    {storageTarget codeAddress : Adr} {post : Devm}
    (invocation : root.exactInvocation program storageTarget codeAddress)
    (ok : root.exn = .ok post) :
    ∃ cursor : Exec.Deriv.SourceCursor root program ⟨0, []⟩ program.main,
      Exec.Deriv.ParentPrefix root cursor.node ∧
      Devm.Burn root.devm cursor.pre := by
  rcases invocation with ⟨hpc, -, -, hcode⟩
  have hget :
      (table 0 (program.main :: program.aux))[0]? =
        some (0, program.main) := rfl
  rcases subcode_of_get?_eq_some hcode hget with ⟨jumpdestAt, sourceSlice⟩
  have sourceBoundary : noPushBefore root.sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table hcode hget).2
  rw [← hpc] at jumpdestAt
  rcases Exec.Deriv.ParentStep.exists_of_jinstAt_ok ok jumpdestAt with
    ⟨bodyPc, bodyPre, bodyExec, edge, jumpdestRun⟩
  rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, burn⟩
  rw [hpc] at bodyPcEq
  subst bodyPc
  have parentPrefix : Exec.Deriv.ParentPrefix root
      ⟨0 + 1, root.sevm, bodyPre, root.exn, bodyExec⟩ :=
    .step edge (.refl _)
  exact ⟨⟨0 + 1, bodyPre, bodyExec, parentPrefix, sourceSlice,
    sourceBoundary, by
      intro site member
      simp only [Prog.sourceSites, List.mem_flatMap]
      refine ⟨0, by simp, ?_⟩
      simpa only [hget] using member⟩, parentPrefix, burn⟩

/-- Forward dual of `nextOfParentStep`: a successful frame crosses the current
source instruction, and the crossing is the exact `Ninst.Run`. -/
theorem Exec.Deriv.SourceCursor.nextForward
    {root : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {instruction : Ninst} {tail : Func} {post : Devm}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail))
    (ok : root.exn = .ok post) :
    ∃ tailCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.rest]⟩ tail,
      Exec.Deriv.ParentStep tailCursor.node cursor.node ∧
      Ninst.Run root.sevm cursor.pre instruction tailCursor.pre := by
  have sourceAt : Ninst.At root.sevm.code cursor.pc instruction :=
    Func.sourceSites_sound cursor.codeSlice cursor.codeBoundary
      (functionIndex := path.functionIndex) (steps := path.steps)
      (site := { path := path, pc := cursor.pc, instruction := instruction })
      (by rcases path with ⟨functionIndex, steps⟩
          simp [Func.sourceSites])
  rcases Exec.Deriv.ParentStep.exists_of_ninstAt_ok
      (start := cursor.node) ok sourceAt with ⟨nextNode, edge⟩
  rcases cursor.nextOfParentStep edge with ⟨tailCursor, nodeEq⟩
  rw [← nodeEq] at edge
  exact ⟨tailCursor, edge, cursor.ninstRun_of_nextEdge edge⟩

/-- Forward dual of `branchFlagToward`: a successful frame takes exactly the
arm selected by the actual flag, with the loose `Func.Run` branch rule's state
relation. -/
theorem Exec.Deriv.SourceCursor.branchForward
    {root : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {left right : Func} {post : Devm}
    (cursor : Exec.Deriv.SourceCursor root program path (.branch left right))
    (ok : root.exn = .ok post) :
    (∃ arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.ParentPrefix cursor.node arm.node ∧
        Devm.PopBurn [(0 : B256)] cursor.pre arm.pre) ∨
    (∃ flag : B256, flag ≠ 0 ∧
      ∃ arm : Exec.Deriv.SourceCursor root program
          ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
        Exec.Deriv.ParentPrefix cursor.node arm.node ∧
          Devm.PopBurn [flag] cursor.pre arm.pre) := by
  rcases subcode_compile_branch_jumpable cursor.codeSlice
      cursor.codeBoundary with
    ⟨loc, hlocEq, hloc, pushAt, jumpiAt, leftSlice, leftBoundary,
      jumpdestAt, jumpable, rightSlice, rightBoundary⟩
  rcases Exec.Deriv.ParentStep.exists_of_pushAt_ok (start := cursor.node)
      ok ⟨_, pushAt⟩ (by simp) with
    ⟨afterPushPre, afterPush, pushEdge, pushBurn⟩
  rw [List.toB256_pair _ hloc] at pushBurn
  rcases Exec.Deriv.ParentStep.exists_of_jinstAt_ok
      (start := ⟨_, root.sevm, afterPushPre, root.exn, afterPush⟩)
      ok jumpiAt with
    ⟨nextPc, armPre, armExec, jumpEdge, jumpRun⟩
  rcases of_jumpi_run jumpRun with
    ⟨x, nextPcEq, popBurn⟩ | ⟨x, flag, nextPcEq, popBurn,
      actualJumpable, nonzero⟩
  · cases nextPcEq
    let armCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left :=
      ⟨_, _, armExec, cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge,
        leftSlice, leftBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          exact Or.inl member⟩
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have zeroPop : Devm.PopBurn [(0 : B256)] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    exact Or.inl ⟨armCursor,
      .step pushEdge (.step jumpEdge (.refl _)), zeroPop⟩
  · have hloc256 : loc < 2 ^ 256 := by
      apply Nat.lt_trans hloc
      rw [Nat.pow_lt_pow_iff_right] <;> omega
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have hxeq : loc = x.toNat := by
      have hlocToNat : loc.toB256.toNat = loc :=
        B256.toNat_toB256_of_lt hloc256
      rw [← congrArg B256.toNat hx, hlocToNat]
    have nextPcLoc : nextPc = loc := nextPcEq.trans hxeq.symm
    cases nextPcLoc
    rcases Exec.Deriv.ParentStep.exists_of_jinstAt_ok
        (start := ⟨_, root.sevm, armPre, root.exn, armExec⟩)
        ok jumpdestAt with
      ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, jumpdestRun⟩
    rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
    subst bodyPc
    let armCursor : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right :=
      ⟨_, _, bodyExec,
        cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
          |>.snoc jumpdestEdge,
        rightSlice, rightBoundary, by
          intro site member
          apply cursor.sourceIncluded
          simp only [Func.sourceSites, List.mem_append]
          apply Or.inr
          have hrightPc : loc + 1 = cursor.pc + compsize left + 5 := by
            omega
          rw [← hrightPc]
          exact member⟩
    have flagPop : Devm.PopBurn [flag] cursor.pre armPre :=
      Devm.popBurn_of_burn_of_popBurn
        (Devm.burn_of_pushBurn_nil pushBurn') popBurn'
    have bodyPop : Devm.PopBurn [flag] cursor.pre bodyPre :=
      Devm.popBurn_of_popBurn_of_pop flagPop jumpdestBurn
    exact Or.inr ⟨flag, nonzero, armCursor,
      .step pushEdge (.step jumpEdge (.step jumpdestEdge (.refl _))),
      bodyPop⟩

/-- Forward dual of `callToward`: a successful frame enters the called source
body through the compiler's `PUSH`/`JUMP`/`JUMPDEST` glue, which only burns
gas. -/
theorem Exec.Deriv.SourceCursor.callForward
    {root : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {index : Nat} {post : Devm}
    (cursor : Exec.Deriv.SourceCursor root program path (.call index))
    (compiled : some root.sevm.code.toList = program.compile)
    (ok : root.exn = .ok post) :
    ∃ body, (program.main :: program.aux)[index]? = some body ∧
      ∃ bodyCursor : Exec.Deriv.SourceCursor root program ⟨index, []⟩ body,
        Exec.Deriv.ParentPrefix cursor.node bodyCursor.node ∧
        Devm.Burn cursor.pre bodyCursor.pre := by
  rcases subcode_compile_call cursor.codeSlice with
    ⟨loc, body, hgetTable, hloc, pushAt, jumpAt⟩
  have hgetBody : (program.main :: program.aux)[index]? = some body := by
    have h := @Prog.get?_table 0 index (program.main :: program.aux)
    rw [hgetTable] at h
    simpa using h.symm
  rcases Exec.Deriv.ParentStep.exists_of_pushAt_ok (start := cursor.node)
      ok pushAt (by simp) with
    ⟨afterPushPre, afterPush, pushEdge, pushBurn⟩
  rw [List.toB256_pair _ hloc] at pushBurn
  rcases Exec.Deriv.ParentStep.exists_of_jinstAt_ok
      (start := ⟨_, root.sevm, afterPushPre, root.exn, afterPush⟩)
      ok jumpAt with
    ⟨nextPc, beforeJumpdestPre, beforeJumpdest, jumpEdge, jumpRun⟩
  rcases of_jump_run jumpRun with ⟨x, nextPcEq, popBurn, actualJumpable⟩
  have hloc256 : loc < 2 ^ 256 := by
    apply Nat.lt_trans hloc
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
    ⟨hx, stack, pushBurn', popBurn'⟩
  have hxeq : loc = x.toNat := by
    have hlocToNat : loc.toB256.toNat = loc :=
      B256.toNat_toB256_of_lt hloc256
    rw [← congrArg B256.toNat hx, hlocToNat]
  have nextPcLoc : nextPc = loc := nextPcEq.trans hxeq.symm
  cases nextPcLoc
  rcases subcode_of_get?_eq_some compiled hgetTable with
    ⟨jumpdestAt, bodySlice⟩
  have bodyBoundary := Prog.jumpable_of_get?_table compiled hgetTable
  rcases Exec.Deriv.ParentStep.exists_of_jinstAt_ok
      (start := ⟨_, root.sevm, beforeJumpdestPre, root.exn, beforeJumpdest⟩)
      ok jumpdestAt with
    ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, jumpdestRun⟩
  rcases of_jumpdest_run jumpdestRun with ⟨bodyPcEq, jumpdestBurn⟩
  subst bodyPc
  let bodyCursor : Exec.Deriv.SourceCursor root program ⟨index, []⟩ body :=
    ⟨_, _, bodyExec,
      cursor.parentPrefix.snoc pushEdge |>.snoc jumpEdge
        |>.snoc jumpdestEdge,
      bodySlice, bodyBoundary.2, by
        intro site member
        simp only [Prog.sourceSites, List.mem_flatMap]
        refine ⟨index, ?_, ?_⟩
        · exact List.mem_range.mpr
            (List.getElem?_eq_some_iff.mp hgetBody).choose
        · simpa only [hgetTable] using member⟩
  refine ⟨body, hgetBody, bodyCursor,
    .step pushEdge (.step jumpEdge (.step jumpdestEdge (.refl _))), ?_⟩
  exact Devm.burn_trans
    (Devm.burn_trans (Devm.burn_of_pushBurn_nil pushBurn')
      (Devm.burn_of_popBurn_nil popBurn'))
    jumpdestBurn

/-! ## Headline transport -/

/-- Replay a loose gas-free prefix against the actual execution: starting from
a cursor whose state agrees with the loose start modulo gas, the prefix's target
is an actual same-frame node of the selected root, again agreeing modulo gas.

`ok` is what makes every crossed instruction continue; `agree` is the seed,
and each `.next` step's `Ninst.gasFree` certificate licenses the per-step
congruence. The identity is modulo exactly the columns outside `Devm.Rels`
(see `Ninst.run_eqModGas`). -/
theorem Exec.Deriv.SourceCursor.ofRunPrefix
    {root : Exec.Deriv} {program : Prog} {post : Devm}
    {current : Prog.SourcePath} {body : Func}
    (cursor : Exec.Deriv.SourceCursor root program current body)
    (compiled : some root.sevm.code.toList = program.compile)
    (ok : root.exn = .ok post)
    {s t : Devm} {target : Prog.SourcePath} {rest : Func}
    (walk : Func.RunPrefix (program.main :: program.aux) root.sevm
      current s body target t rest)
    (agree : Devm.EqModGas s cursor.pre) :
    ∃ cursor' : Exec.Deriv.SourceCursor root program target rest,
      Devm.EqModGas t cursor'.pre ∧
      Exec.Deriv.ParentPrefix cursor.node cursor'.node := by
  induction walk with
  | refl => exact ⟨cursor, agree, .refl _⟩
  | next gasFree looseRun _ ih =>
      rcases cursor.nextForward ok with ⟨tailCursor, edge, actualRun⟩
      rcases ih tailCursor
          (Ninst.run_eqModGas gasFree looseRun actualRun agree) with
        ⟨cursor', agree', reached⟩
      exact ⟨cursor', agree', .step edge reached⟩
  | zero loosePop _ ih =>
      rcases cursor.branchForward ok with
        ⟨arm, armReached, actualPop⟩ |
        ⟨flag, nonzero, arm, armReached, actualPop⟩
      · rcases ih arm (agree.of_popBurn loosePop actualPop).2 with
          ⟨cursor', agree', reached⟩
        exact ⟨cursor', agree', armReached.trans reached⟩
      · exact (nonzero (agree.of_popBurn loosePop actualPop).1.symm).elim
  | succ looseNonzero loosePop looseBurn _ ih =>
      have loosePop' := Devm.popBurn_of_popBurn_of_pop loosePop looseBurn
      rcases cursor.branchForward ok with
        ⟨arm, armReached, actualPop⟩ |
        ⟨flag, nonzero, arm, armReached, actualPop⟩
      · exact (looseNonzero
          (agree.of_popBurn loosePop' actualPop).1).elim
      · rcases ih arm (agree.of_popBurn loosePop' actualPop).2 with
          ⟨cursor', agree', reached⟩
        exact ⟨cursor', agree', armReached.trans reached⟩
  | call lookup looseBurn _ ih =>
      rcases cursor.callForward compiled ok with
        ⟨actualBody, actualLookup, bodyCursor, bodyReached, actualBurn⟩
      cases lookup.symm.trans actualLookup
      rcases ih bodyCursor (agree.of_burn looseBurn actualBurn) with
        ⟨cursor', agree', reached⟩
      exact ⟨cursor', agree', bodyReached.trans reached⟩

end Blanc
