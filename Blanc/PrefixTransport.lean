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

/-! ## Frame-entry-free same-frame spans -/

/-- `ExecFreeUntil start stop`: `stop` is a same-frame successor of `start`,
and every same-frame node reached from `start` either lies at or after `stop`
or decodes no frame-entering instruction. Only an `Xinst` can spawn a child
frame (`Evm.step_spawn_inv`), so such a span enters no frame before `stop`. -/
def Exec.Deriv.ExecFreeUntil (start stop : Exec.Deriv) : Prop :=
  Exec.Deriv.ParentPrefix start stop ∧
    ∀ node, Exec.Deriv.ParentPrefix start node →
      Exec.Deriv.ParentPrefix stop node ∨
        ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x)

theorem Exec.Deriv.ExecFreeUntil.refl (node : Exec.Deriv) :
    Exec.Deriv.ExecFreeUntil node node :=
  ⟨.refl _, fun _ reached => Or.inl reached⟩

theorem Exec.Deriv.ExecFreeUntil.trans {start middle stop : Exec.Deriv}
    (left : Exec.Deriv.ExecFreeUntil start middle)
    (right : Exec.Deriv.ExecFreeUntil middle stop) :
    Exec.Deriv.ExecFreeUntil start stop :=
  ⟨left.1.trans right.1, fun node reached =>
    (left.2 node reached).elim (right.2 node) Or.inr⟩

/-- One same-frame edge out of a node that decodes no frame-entering
instruction. -/
theorem Exec.Deriv.ExecFreeUntil.ofStep {start next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next start)
    (free : ∀ x : Xinst, ¬ Ninst.At start.sevm.code start.pc (.exec x)) :
    Exec.Deriv.ExecFreeUntil start next := by
  refine ⟨.step edge (.refl _), fun node reached => ?_⟩
  rcases edge.parentPrefix_iff.mp reached with rfl | later
  · exact Or.inr free
  · exact Or.inl later

theorem Jinst.At.not_exec {code : ByteArray} {pc : Nat} {j : Jinst}
    (jumpAt : Jinst.At code pc j) (x : Xinst) :
    ¬ Ninst.At code pc (.exec x) := by
  intro execAt
  unfold Ninst.At at execAt
  unfold Jinst.At at jumpAt
  rw [execAt] at jumpAt
  cases jumpAt

theorem PushAt.not_exec {code : ByteArray} {pc : Nat} {xs : Bytes}
    (pushAt : PushAt code pc xs) (x : Xinst) :
    ¬ Ninst.At code pc (.exec x) := by
  intro execAt
  rcases pushAt with ⟨_, pushAt⟩
  unfold Ninst.At at execAt
  rw [execAt] at pushAt
  cases pushAt

theorem Ninst.At.not_exec_of_gasFree {code : ByteArray} {pc : Nat}
    {instruction : Ninst} (instructionAt : Ninst.At code pc instruction)
    (gasFree : Ninst.gasFree instruction = true) (x : Xinst) :
    ¬ Ninst.At code pc (.exec x) := by
  intro execAt
  unfold Ninst.At at execAt instructionAt
  rw [execAt] at instructionAt
  cases instructionAt
  cases gasFree

/-- A terminal instruction ends its frame's same-frame chain. -/
theorem Exec.Deriv.ParentPrefix.eq_of_linstAt {root tail : Exec.Deriv}
    {instruction : Linst}
    (reached : Exec.Deriv.ParentPrefix root tail)
    (lastAt : Linst.At root.sevm.code root.pc instruction) : tail = root := by
  cases reached with
  | refl => rfl
  | step edge _ => exact (edge.false_of_linstAt lastAt).elim

/-! ## Forward cursor duals -/

/-- Frame-entry-free twin of `mainForward`: the only node crossed is the
compiler's leading `JUMPDEST`. -/
theorem Exec.Deriv.SourceCursor.mainForwardFree
    {root : Exec.Deriv} {program : Prog} {post : Devm}
    (hpc : root.pc = 0)
    (hcode : some root.sevm.code.toList = program.compile)
    (ok : root.exn = .ok post) :
    ∃ cursor : Exec.Deriv.SourceCursor root program ⟨0, []⟩ program.main,
      Exec.Deriv.ExecFreeUntil root cursor.node ∧
      Devm.Burn root.devm cursor.pre := by
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
      simpa only [hget] using member⟩,
    Exec.Deriv.ExecFreeUntil.ofStep edge jumpdestAt.not_exec, burn⟩

/-- Forward dual of `mainToward`: a successful compiled root at the entry
counter crosses the compiler's leading `JUMPDEST` into the main body. Only the
entry counter and the compiled bytes are consumed, so no storage-target or
code-address identity is demanded. -/
theorem Exec.Deriv.SourceCursor.mainForward
    {root : Exec.Deriv} {program : Prog} {post : Devm}
    (hpc : root.pc = 0)
    (hcode : some root.sevm.code.toList = program.compile)
    (ok : root.exn = .ok post) :
    ∃ cursor : Exec.Deriv.SourceCursor root program ⟨0, []⟩ program.main,
      Exec.Deriv.ParentPrefix root cursor.node ∧
      Devm.Burn root.devm cursor.pre := by
  rcases Exec.Deriv.SourceCursor.mainForwardFree hpc hcode ok with
    ⟨cursor, free, burn⟩
  exact ⟨cursor, free.1, burn⟩

/-- The source instruction under a `.next` cursor decodes at the cursor's
counter in the executing code. -/
theorem Exec.Deriv.SourceCursor.ninstAt
    {root : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {instruction : Ninst} {tail : Func}
    (cursor : Exec.Deriv.SourceCursor root program path
      (.next instruction tail)) :
    Ninst.At root.sevm.code cursor.pc instruction :=
  Func.sourceSites_sound cursor.codeSlice cursor.codeBoundary
    (functionIndex := path.functionIndex) (steps := path.steps)
    (site := { path := path, pc := cursor.pc, instruction := instruction })
    (by rcases path with ⟨functionIndex, steps⟩
        simp [Func.sourceSites])

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
  rcases Exec.Deriv.ParentStep.exists_of_ninstAt_ok
      (start := cursor.node) ok cursor.ninstAt with ⟨nextNode, edge⟩
  rcases cursor.nextOfParentStep edge with ⟨tailCursor, nodeEq⟩
  rw [← nodeEq] at edge
  exact ⟨tailCursor, edge, cursor.ninstRun_of_nextEdge edge⟩

/-- Frame-entry-free twin of `branchForward`: the crossed compiler glue is a
`PUSH`, a `JUMPI` and, on the right arm, a `JUMPDEST`. -/
theorem Exec.Deriv.SourceCursor.branchForwardFree
    {root : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {left right : Func} {post : Devm}
    (cursor : Exec.Deriv.SourceCursor root program path (.branch left right))
    (ok : root.exn = .ok post) :
    (∃ arm : Exec.Deriv.SourceCursor root program
        ⟨path.functionIndex, path.steps ++ [.branchLeft]⟩ left,
      Exec.Deriv.ExecFreeUntil cursor.node arm.node ∧
        Devm.PopBurn [(0 : B256)] cursor.pre arm.pre) ∨
    (∃ flag : B256, flag ≠ 0 ∧
      ∃ arm : Exec.Deriv.SourceCursor root program
          ⟨path.functionIndex, path.steps ++ [.branchRight]⟩ right,
        Exec.Deriv.ExecFreeUntil cursor.node arm.node ∧
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
      (Exec.Deriv.ExecFreeUntil.ofStep pushEdge
        (PushAt.not_exec ⟨_, pushAt⟩)).trans
        (Exec.Deriv.ExecFreeUntil.ofStep jumpEdge jumpiAt.not_exec),
      zeroPop⟩
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
      ((Exec.Deriv.ExecFreeUntil.ofStep pushEdge
        (PushAt.not_exec ⟨_, pushAt⟩)).trans
        (Exec.Deriv.ExecFreeUntil.ofStep jumpEdge jumpiAt.not_exec)).trans
        (Exec.Deriv.ExecFreeUntil.ofStep jumpdestEdge jumpdestAt.not_exec),
      bodyPop⟩


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
  rcases cursor.branchForwardFree ok with
    ⟨arm, free, pop⟩ | ⟨flag, nonzero, arm, free, pop⟩
  · exact Or.inl ⟨arm, free.1, pop⟩
  · exact Or.inr ⟨flag, nonzero, arm, free.1, pop⟩

/-- Frame-entry-free twin of `callForward`: the crossed compiler glue is a
`PUSH`, a `JUMP` and a `JUMPDEST`. -/
theorem Exec.Deriv.SourceCursor.callForwardFree
    {root : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {index : Nat} {post : Devm}
    (cursor : Exec.Deriv.SourceCursor root program path (.call index))
    (compiled : some root.sevm.code.toList = program.compile)
    (ok : root.exn = .ok post) :
    ∃ body, (program.main :: program.aux)[index]? = some body ∧
      ∃ bodyCursor : Exec.Deriv.SourceCursor root program ⟨index, []⟩ body,
        Exec.Deriv.ExecFreeUntil cursor.node bodyCursor.node ∧
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
    ((Exec.Deriv.ExecFreeUntil.ofStep pushEdge pushAt.not_exec).trans
      (Exec.Deriv.ExecFreeUntil.ofStep jumpEdge jumpAt.not_exec)).trans
      (Exec.Deriv.ExecFreeUntil.ofStep jumpdestEdge jumpdestAt.not_exec), ?_⟩
  exact Devm.burn_trans
    (Devm.burn_trans (Devm.burn_of_pushBurn_nil pushBurn')
      (Devm.burn_of_popBurn_nil popBurn'))
    jumpdestBurn


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
  rcases cursor.callForwardFree compiled ok with
    ⟨body, lookup, bodyCursor, free, burn⟩
  exact ⟨body, lookup, bodyCursor, free.1, burn⟩

/-! ## Headline transport -/

/-- **Spine lemma.** Frame-entry-free twin of `ofRunPrefix`: every
same-frame node between the two cursors decodes a gas-free source instruction
or compiler glue, never a frame-entering `Xinst`. With
`Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt` this is what shows a
gas-free walk spawns no child frame. -/
theorem Exec.Deriv.SourceCursor.ofRunPrefix_sameFrame_gasFree
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
      Exec.Deriv.ExecFreeUntil cursor.node cursor'.node := by
  induction walk with
  | refl => exact ⟨cursor, agree, Exec.Deriv.ExecFreeUntil.refl _⟩
  | next gasFree looseRun _ ih =>
      rcases cursor.nextForward ok with ⟨tailCursor, edge, actualRun⟩
      rcases ih tailCursor
          (Ninst.run_eqModGas gasFree looseRun actualRun agree) with
        ⟨cursor', agree', reached⟩
      exact ⟨cursor', agree', (Exec.Deriv.ExecFreeUntil.ofStep edge
        (cursor.ninstAt.not_exec_of_gasFree gasFree)).trans reached⟩
  | zero loosePop _ ih =>
      rcases cursor.branchForwardFree ok with
        ⟨arm, armReached, actualPop⟩ |
        ⟨flag, nonzero, arm, armReached, actualPop⟩
      · rcases ih arm (agree.of_popBurn loosePop actualPop).2 with
          ⟨cursor', agree', reached⟩
        exact ⟨cursor', agree', armReached.trans reached⟩
      · exact (nonzero (agree.of_popBurn loosePop actualPop).1.symm).elim
  | succ looseNonzero loosePop looseBurn _ ih =>
      have loosePop' := Devm.popBurn_of_popBurn_of_pop loosePop looseBurn
      rcases cursor.branchForwardFree ok with
        ⟨arm, armReached, actualPop⟩ |
        ⟨flag, nonzero, arm, armReached, actualPop⟩
      · exact (looseNonzero
          (agree.of_popBurn loosePop' actualPop).1).elim
      · rcases ih arm (agree.of_popBurn loosePop' actualPop).2 with
          ⟨cursor', agree', reached⟩
        exact ⟨cursor', agree', armReached.trans reached⟩
  | call lookup looseBurn _ ih =>
      rcases cursor.callForwardFree compiled ok with
        ⟨actualBody, actualLookup, bodyCursor, bodyReached, actualBurn⟩
      cases lookup.symm.trans actualLookup
      rcases ih bodyCursor (agree.of_burn looseBurn actualBurn) with
        ⟨cursor', agree', reached⟩
      exact ⟨cursor', agree', bodyReached.trans reached⟩


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
  rcases cursor.ofRunPrefix_sameFrame_gasFree compiled ok walk agree with
    ⟨cursor', agree', free⟩
  exact ⟨cursor', agree', free.1⟩

/-! ## Frames that enter no child -/

/-- A frame-entry-free span that ends at a terminal instruction covers the
whole same-frame chain of its start. -/
theorem Exec.Deriv.ExecFreeUntil.noExec_of_linstAt {start stop : Exec.Deriv}
    {instruction : Linst}
    (free : Exec.Deriv.ExecFreeUntil start stop)
    (lastAt : Linst.At stop.sevm.code stop.pc instruction) :
    ∀ node, Exec.Deriv.ParentPrefix start node →
      ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x) := by
  intro node reached x execAt
  rcases free.2 node reached with later | clean
  · have atStop := later.eq_of_linstAt lastAt
    subst atStop
    exact execAt.false_of_linstAt lastAt
  · exact clean x execAt

/-- An execution whose own same-frame chain decodes no frame-entering
instruction retains no descendant frame. -/
theorem Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (childless : ∀ node : Exec.Deriv,
      Exec.Deriv.ParentPrefix (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) node →
        ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x)) :
    Exec.descendantFrames run = [] := by
  have raw := Exec.rawFrameDescendants_eq_nil_of_no_sameFrame_xinstAt run
    childless
  cases frames : Exec.descendantFrames run with
  | nil => rfl
  | cons frame _ =>
      have member := Exec.mem_rawFrameDescendants_of_mem_descendantFrames run
        frame (by rw [frames]; exact List.mem_cons_self)
      rw [raw] at member
      cases member

/-! ## Same-frame spans carry no descendant frame -/

private theorem Exec.Deriv.le_trans' {a b c : Exec.Deriv}
    (left : Exec.Deriv.le a b) (right : Exec.Deriv.le b c) :
    Exec.Deriv.le a c := by
  induction right with
  | refl => exact left
  | step _ prec ih => exact .step ih prec

private theorem Exec.Deriv.ParentPrefix.le' {root tail : Exec.Deriv}
    (reached : Exec.Deriv.ParentPrefix root tail) : Exec.Deriv.le tail root := by
  induction reached with
  | refl => exact .refl _
  | step head _ ih => exact .step ih head.prec

private theorem Exec.Deriv.lt_irrefl' (node : Exec.Deriv) :
    ¬ Exec.Deriv.lt node node := by
  have acc := Exec.Deriv.lt.well_founded.apply node
  induction acc with
  | intro current _ ih => exact fun self => ih current self self

/-- A same-frame chain never returns to a node it has left. -/
theorem Exec.Deriv.ParentStep.not_parentPrefix_back
    {root next node : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root)
    (forward : Exec.Deriv.ParentPrefix next node)
    (back : Exec.Deriv.ParentPrefix node root) : False :=
  Exec.Deriv.lt_irrefl' root
    ⟨next, Exec.Deriv.le_trans' back.le' forward.le', edge.prec⟩

/-- A frame-entry-free span retains no descendant frame of its own: the
descendant frames of its start are those of its end. -/
theorem Exec.Deriv.ExecFreeUntil.descendantFrames_eq {start stop : Exec.Deriv}
    (free : Exec.Deriv.ExecFreeUntil start stop) :
    Exec.descendantFrames start.exc = Exec.descendantFrames stop.exc := by
  rcases free with ⟨reached, clean⟩
  induction reached with
  | refl => rfl
  | @step root next tail edge rest ih =>
      have rootClean : ∀ x : Xinst,
          ¬ Ninst.At root.sevm.code root.pc (.exec x) := by
        rcases clean root (.refl _) with back | rootClean
        · exact (edge.not_parentPrefix_back rest back).elim
        · exact rootClean
      have nextClean : ∀ node, Exec.Deriv.ParentPrefix next node →
          Exec.Deriv.ParentPrefix tail node ∨
            ∀ x : Xinst, ¬ Ninst.At node.sevm.code node.pc (.exec x) :=
        fun node reached => clean node (.step edge reached)
      rw [← ih nextClean]
      cases edge with
      | cont hstep next => simp [Exec.descendantFrames]
      | doneOk hstep henter hresume next =>
          rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
          exact (rootClean x decoded).elim
      | runOk hstep henter child hresume next =>
          rcases Evm.step_spawn_inv hstep with ⟨x, decoded, -, -⟩
          exact (rootClean x decoded).elim

/-! ## Straight-line gas-free functions -/

/-- Every instruction gas-free and no table call. -/
def Func.straightGasFree : Func → Bool
  | .last _ => true
  | .next i f => Ninst.gasFree i && Func.straightGasFree f
  | .branch f g => Func.straightGasFree f && Func.straightGasFree g
  | .call _ => false

/-- A successful run of a straight-line gas-free function is a gas-free prefix
ending at one of its terminal instructions. -/
theorem Func.RunPrefix.toLast_of_run {fs : List Func} {e : Sevm} :
    ∀ {f : Func} {path : Prog.SourcePath} {s r : Devm},
      Func.straightGasFree f = true → Func.Run fs e s f r →
      ∃ target t l, Func.RunPrefix fs e path s f target t (.last l)
  | .last l, path, s, _, _, _ => ⟨path, s, l, .refl⟩
  | .next i f, ⟨k, steps⟩, s, r, free, run => by
      simp only [Func.straightGasFree, Bool.and_eq_true] at free
      cases run with
      | next step rest =>
          rcases Func.RunPrefix.toLast_of_run (path := ⟨k, steps ++ [.rest]⟩)
              free.2 rest with ⟨target, t, l, walk⟩
          exact ⟨target, t, l, .next free.1 step walk⟩
  | .branch f g, ⟨k, steps⟩, s, r, free, run => by
      simp only [Func.straightGasFree, Bool.and_eq_true] at free
      cases run with
      | zero pop rest =>
          rcases Func.RunPrefix.toLast_of_run
              (path := ⟨k, steps ++ [.branchLeft]⟩) free.1 rest with
            ⟨target, t, l, walk⟩
          exact ⟨target, t, l, .zero pop walk⟩
      | succ nonzero pop burn rest =>
          rcases Func.RunPrefix.toLast_of_run
              (path := ⟨k, steps ++ [.branchRight]⟩) free.2 rest with
            ⟨target, t, l, walk⟩
          exact ⟨target, t, l, .succ nonzero pop burn walk⟩
  | .call _, _, _, _, free, _ => by cases free

end Blanc
