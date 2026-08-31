import Blanc.DeploymentCompiled
import Blanc.ExecutionOccurrence

/-!
# Source occurrence attribution for appended deployment code

Creation code commonly executes a compiled `Prog` prefix while retaining an
appended runtime or ABI payload in `Sevm.code`.  The ordinary exact-invocation
source bridge deliberately requires whole-code equality.  This additive layer
repeats only the target-directed pieces that need compiler-table evidence and
uses `DeploymentCompiled`'s prefix lemmas at entry and internal-call targets.

The traversal still follows the finite execution derivation.  In particular,
bytes in the appended suffix are not granted source authority merely because
they decode as an instruction also present in the prefix program.
-/

namespace Blanc

open Jaune

/-- Exact placement of a compiled program at the front of a larger code image.
Both the compiled prefix and the arbitrary suffix are explicit identities. -/
structure Prog.CompiledPrefix
    (program : Prog) (code : ByteArray) (pfxCode sfxData : Bytes) : Prop where
  compile_eq : some pfxCode = program.compile
  code_eq : code.toList = pfxCode ++ sfxData

/-- Entry identity for a compiled prefix running at PC zero.  Storage owner,
code address, commitment, settlement, and deployment provenance remain
separate facts. -/
def Exec.Deriv.exactProgramPrefix
    (program : Prog) (pfxCode sfxData : Bytes) (root : Exec.Deriv) : Prop :=
  root.pc = 0 ∧ program.CompiledPrefix root.sevm.code pfxCode sfxData

/-! ## Appended-code cursor entry -/

/-- Enter the main source body when the compiled program is the exact prefix
of the full code image and the target proves that execution crossed the
leading compiler `JUMPDEST`. -/
theorem Exec.Deriv.SourceCursor.mainToward_appended
    {root target : Exec.Deriv} {program : Prog}
    {pfxCode sfxData : Bytes} {targetInstruction : Ninst}
    (identity : root.exactProgramPrefix program pfxCode sfxData)
    (reached : Exec.Deriv.ParentPrefix root target)
    (instructionAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ cursor : Exec.Deriv.SourceCursor root program ⟨0, []⟩ program.main,
      Exec.Deriv.ParentNonSstorePrefix root cursor.node ∧
      Exec.Deriv.ParentPrefix cursor.node target := by
  rcases root with ⟨pc, sevm, pre, out, run⟩
  rcases identity with ⟨hpc, compiled⟩
  rcases compiled with ⟨hcompile, hcode⟩
  dsimp at hpc hcompile hcode reached instructionAt
  subst pc
  have hget :
      (table 0 (program.main :: program.aux))[0]? =
        some (0, program.main) := rfl
  rcases subcode_of_get?_eq_some_appended hcompile hcode hget with
    ⟨jumpdestAt, sourceSlice⟩
  have sourceBoundary : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table_appended hcompile hcode hget).2
  cases reached with
  | refl =>
      exact (instructionAt.false_of_jinstAt jumpdestAt).elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          have jrun :
              Jinst.Run ⟨0, sevm, pre⟩ .jumpdest (.ok ⟨_, _⟩) :=
            Step.ofJump_cont (hstatic.symm.trans hstep)
          rcases of_jumpdest_run jrun with ⟨eqPc, burn⟩
          cases eqPc
          let nextNode : Exec.Deriv := ⟨1, sevm, _, out, next⟩
          let parentEdge : Exec.Deriv.ParentStep nextNode
              ⟨0, sevm, pre, out, .cont hstep next⟩ :=
            .cont hstep next
          have parentPrefix : Exec.Deriv.ParentPrefix
              ⟨0, sevm, pre, out, .cont hstep next⟩ nextNode :=
            .step parentEdge (.refl _)
          let cursor : Exec.Deriv.SourceCursor
              ⟨0, sevm, pre, out, .cont hstep next⟩ program
              ⟨0, []⟩ program.main :=
            ⟨1, _, next, parentPrefix, sourceSlice, sourceBoundary, by
              intro site member
              simp only [Prog.sourceSites, List.mem_flatMap]
              refine ⟨0, by simp, ?_⟩
              simpa only [hget] using member⟩
          have notStore : ¬ Ninst.At sevm.code 0 (.reg .sstore) := by
            intro storeHere
            exact storeHere.false_of_jinstAt jumpdestAt
          exact ⟨cursor, .step parentEdge notStore (.refl _), rest⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨0, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨0, sevm, pre⟩ .jumpdest) :=
            Evm.step_jump jumpdestAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim

/-! ## Private same-frame glue used by appended internal calls -/

private theorem Exec.Deriv.ParentNonSstorePrefix.toParentPrefix_appended
    {root tail : Exec.Deriv}
    (chain : Exec.Deriv.ParentNonSstorePrefix root tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction chain with
  | refl => exact .refl _
  | step edge notStore rest ih => exact .step edge ih

private theorem Exec.Deriv.ParentPrefix.trans_appended
    {root middle tail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root middle)
    (right : Exec.Deriv.ParentPrefix middle tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction right generalizing root with
  | refl => exact left
  | step head rest ih => exact ih (left.snoc head)

private theorem Exec.Deriv.ParentPrefix.advancePushToward_appended
    {start target : Exec.Deriv} {xs : Bytes} {targetInstruction : Ninst}
    (reached : Exec.Deriv.ParentPrefix start target)
    (pushAt : PushAt start.sevm.code start.pc xs)
    (hne : xs ≠ [])
    (targetNonPush : NinstNonPush targetInstruction)
    (instructionAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ (inter : Devm)
      (next : Exec (start.pc + xs.length + 1) start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨start.pc + xs.length + 1, start.sevm, inter, start.exn, next⟩ target ∧
      Devm.PushBurn [xs.toB256] start.devm inter := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  rcases pushAt with ⟨le, pushAt⟩
  cases reached with
  | refl =>
      have impossible := Ninst.at_unique instructionAt pushAt
      subst targetInstruction
      exact targetNonPush.elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          have sourceStep := hstatic.symm.trans hstep
          rw [Ninst.step_push, if_neg hne] at sourceStep
          obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont sourceStep
          cases hpc
          exact ⟨_, next, .cont hstep next, rest,
            Devm.pushBurn_of_run hrun⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Ninst.step ⟨pc, sevm, pre⟩ (.push xs le) :=
            Evm.step_next pushAt
          exact (Step.ofExecution_ne_spawn (hstatic.symm.trans hstep)).elim

private theorem Exec.Deriv.ParentPrefix.advanceJumpToward_appended
    {start target : Exec.Deriv} {instruction : Jinst}
    {targetInstruction : Ninst}
    (reached : Exec.Deriv.ParentPrefix start target)
    (jumpAt : Jinst.At start.sevm.code start.pc instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ (nextPc : Nat) (inter : Devm)
      (next : Exec nextPc start.sevm inter start.exn),
      Exec.Deriv.ParentStep
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ start ∧
      Exec.Deriv.ParentPrefix
        ⟨nextPc, start.sevm, inter, start.exn, next⟩ target ∧
      Jinst.Run ⟨start.pc, start.sevm, start.devm⟩ instruction
        (.ok ⟨nextPc, inter⟩) := by
  rcases start with ⟨pc, sevm, pre, out, run⟩
  dsimp at reached instructionAt jumpAt
  cases reached with
  | refl => exact (instructionAt.false_of_jinstAt jumpAt).elim
  | step edge rest =>
      cases edge with
      | cont hstep next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact ⟨_, _, next, .cont hstep next, rest,
            Step.ofJump_cont (hstatic.symm.trans hstep)⟩
      | doneOk hstep henter hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim
      | runOk hstep henter child hresume next =>
          have hstatic :
              Evm.step ⟨pc, sevm, pre⟩ =
                Step.ofJump (Jinst.run ⟨pc, sevm, pre⟩ instruction) :=
            Evm.step_jump jumpAt
          exact (Step.ofJump_ne_spawn (hstatic.symm.trans hstep)).elim

/-! ## Appended internal-call traversal -/

/-- Follow an actually executed internal source call when the compiler table
occupies only the exact prefix of the full code image. -/
theorem Exec.Deriv.SourceCursor.callToward_appended
    {root target : Exec.Deriv} {program : Prog} {path : Prog.SourcePath}
    {index : Nat} {targetInstruction : Ninst} {pfxCode sfxData : Bytes}
    (cursor : Exec.Deriv.SourceCursor root program path (.call index))
    (compiled : program.CompiledPrefix root.sevm.code pfxCode sfxData)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (targetNonPush : NinstNonPush targetInstruction)
    (instructionAt : Ninst.At target.sevm.code target.pc targetInstruction) :
    ∃ body, (program.main :: program.aux)[index]? = some body ∧
      ∃ bodyCursor : Exec.Deriv.SourceCursor root program ⟨index, []⟩ body,
        Exec.Deriv.ParentNonSstorePrefix cursor.node bodyCursor.node ∧
        Exec.Deriv.ParentPrefix bodyCursor.node target ∧
        Exec.Deriv.lt bodyCursor.node cursor.node := by
  rcases subcode_compile_call cursor.codeSlice with
    ⟨loc, body, hgetTable, hloc, pushAt, jumpAt⟩
  rcases pushAt with ⟨pushLe, pushAt⟩
  have hgetBody : (program.main :: program.aux)[index]? = some body := by
    have h := @Prog.get?_table 0 index (program.main :: program.aux)
    rw [hgetTable] at h
    simpa using h.symm
  rcases reached.advancePushToward_appended ⟨pushLe, pushAt⟩ (by simp)
      targetNonPush instructionAt with
    ⟨afterPushPre, afterPush, pushEdge, afterPushReached, pushBurn⟩
  rw [List.toB256_pair _ hloc] at pushBurn
  rcases afterPushReached.advanceJumpToward_appended jumpAt instructionAt with
    ⟨nextPc, beforeJumpdestPre, beforeJumpdest, jumpEdge,
      beforeJumpdestReached, jumpRun⟩
  rcases of_jump_run jumpRun with
    ⟨x, nextPcEq, popBurn, actualJumpable⟩
  have hloc256 : loc < 2 ^ 256 := by
    apply Nat.lt_trans hloc
    rw [Nat.pow_lt_pow_iff_right] <;> omega
  have hxeq : loc = x.toNat := by
    rcases Devm.pushBurn_cons_popBurn_cons pushBurn popBurn with
      ⟨hx, stack, pushBurn', popBurn'⟩
    have hlocToNat : loc.toB256.toNat = loc :=
      B256.toNat_toB256_of_lt hloc256
    rw [← congrArg B256.toNat hx, hlocToNat]
  have nextPcLoc : nextPc = loc := nextPcEq.trans hxeq.symm
  cases nextPcLoc
  rcases subcode_of_get?_eq_some_appended compiled.compile_eq
      compiled.code_eq hgetTable with
    ⟨jumpdestAt, bodySlice⟩
  have bodyBoundary := Prog.jumpable_of_get?_table_appended
    compiled.compile_eq compiled.code_eq hgetTable
  rcases beforeJumpdestReached.advanceJumpToward_appended jumpdestAt
      instructionAt with
    ⟨bodyPc, bodyPre, bodyExec, jumpdestEdge, bodyReached,
      jumpdestRun⟩
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
  have pushNotStore : ¬ Ninst.At root.sevm.code cursor.pc
      (.reg .sstore) := by
    intro storeAt
    have impossible := Ninst.at_unique storeAt pushAt
    cases impossible
  have jumpNotStore : ¬ Ninst.At root.sevm.code (cursor.pc + 3)
      (.reg .sstore) := by
    intro storeAt
    exact storeAt.false_of_jinstAt jumpAt
  have jumpdestNotStore : ¬ Ninst.At root.sevm.code loc
      (.reg .sstore) := by
    intro storeAt
    exact storeAt.false_of_jinstAt jumpdestAt
  let compilerPrefix : Exec.Deriv.ParentNonSstorePrefix
      cursor.node bodyCursor.node :=
    .step pushEdge pushNotStore
      (.step jumpEdge jumpNotStore
        (.step jumpdestEdge jumpdestNotStore (.refl _)))
  refine ⟨body, hgetBody, bodyCursor, compilerPrefix, bodyReached, ?_⟩
  exact Exec.Deriv.ParentNonSstorePrefix.lt_of_step
    pushEdge pushNotStore
    (.step jumpEdge jumpNotStore
      (.step jumpdestEdge jumpdestNotStore (.refl _)))

/-! ## Finite appended-code source traversal -/

/-- The target-directed source traversal for a program compiled as an exact
prefix.  Recursion is over the finite execution proof, not the source call
graph, so recursive constructor loops remain admissible. -/
private theorem Exec.Deriv.SourceCursor.toward_appended_core :
    ∀ current : Exec.Deriv,
      ∀ {root : Exec.Deriv} {program : Prog}
        {pfxCode sfxData : Bytes}
        {initialPath path : Prog.SourcePath}
        {initialSource source : Func}
        {targetInstruction : Ninst} {target : Exec.Deriv}
        (initial : Exec.Deriv.SourceCursor root program
          initialPath initialSource)
        (cursor : Exec.Deriv.SourceCursor root program path source),
        cursor.node = current →
        program.CompiledPrefix root.sevm.code pfxCode sfxData →
        Exec.Deriv.SourceCursor.Chronology initial cursor target →
        NinstNonPush targetInstruction →
        Ninst.At target.sevm.code target.pc targetInstruction →
        Exec.Deriv.SourceCursor.Toward
          initial target targetInstruction cursor := by
  let property : Exec.Deriv.Pred := fun current =>
    ∀ {root : Exec.Deriv} {program : Prog}
      {pfxCode sfxData : Bytes}
      {initialPath path : Prog.SourcePath}
      {initialSource source : Func}
      {targetInstruction : Ninst} {target : Exec.Deriv}
      (initial : Exec.Deriv.SourceCursor root program
        initialPath initialSource)
      (cursor : Exec.Deriv.SourceCursor root program path source),
      cursor.node = current →
      program.CompiledPrefix root.sevm.code pfxCode sfxData →
      Exec.Deriv.SourceCursor.Chronology initial cursor target →
      NinstNonPush targetInstruction →
      Ninst.At target.sevm.code target.pc targetInstruction →
      Exec.Deriv.SourceCursor.Toward
        initial target targetInstruction cursor
  apply Exec.Deriv.strongRec property
  intro current ih root program pfxCode sfxData initialPath path
    initialSource source targetInstruction target initial cursor hcurrent
    compiled chronology targetNonPush instructionAt
  subst current
  cases source with
  | last outcome =>
      have lastAt : Linst.At root.sevm.code cursor.pc outcome :=
        Linst.at_of_slice cursor.codeSlice
      cases chronology.cursorToTarget with
      | refl => exact (instructionAt.false_of_linstAt lastAt).elim
      | step edge suffix => exact (edge.false_of_linstAt lastAt).elim
  | next instruction tail =>
      cases chronology.cursorToTarget with
      | refl =>
          let site : Prog.SourceSite :=
            { path := path, pc := cursor.pc, instruction := instruction }
          have localMember : site ∈
              Func.sourceSites path.functionIndex path.steps cursor.pc
                (.next instruction tail) := by
            rcases path with ⟨functionIndex, steps⟩
            simp [site, Func.sourceSites]
          have sourceAt : Ninst.At root.sevm.code cursor.pc instruction :=
            Func.sourceSites_sound cursor.codeSlice cursor.codeBoundary
              localMember
          have instructionEq := Ninst.at_unique sourceAt instructionAt
          exact .atTarget cursor chronology site rfl
            (cursor.sourceIncluded localMember) rfl instructionEq
      | step occurrenceEdge suffix =>
          rcases cursor.nextOfParentStep occurrenceEdge with
            ⟨tailCursor, tailNodeEq⟩
          have tailEdge : Exec.Deriv.ParentStep
              tailCursor.node cursor.node := by
            rw [tailNodeEq]
            exact occurrenceEdge
          have tailReached :
              Exec.Deriv.ParentPrefix tailCursor.node target := by
            rw [tailNodeEq]
            exact suffix
          let tailChronology :
              Exec.Deriv.SourceCursor.Chronology
                initial tailCursor target :=
            ⟨chronology.initialToCursor.trans_appended
                (.step tailEdge (.refl _)),
              tailReached⟩
          have rest := ih tailCursor.node tailEdge.lt initial tailCursor rfl
            compiled tailChronology targetNonPush instructionAt
          exact .next cursor chronology tailCursor tailEdge rest
  | branch left right =>
      rcases cursor.branchToward chronology.cursorToTarget
          targetNonPush instructionAt with
        ⟨arm, compilerPrefix, armReached, decrease⟩ |
        ⟨arm, compilerPrefix, armReached, decrease⟩
      · let armChronology :
            Exec.Deriv.SourceCursor.Chronology initial arm target :=
          ⟨chronology.initialToCursor.trans_appended
              compilerPrefix.toParentPrefix_appended,
            armReached⟩
        have rest := ih arm.node decrease initial arm rfl compiled
          armChronology targetNonPush instructionAt
        exact .branchLeft cursor chronology arm compilerPrefix rest
      · let armChronology :
            Exec.Deriv.SourceCursor.Chronology initial arm target :=
          ⟨chronology.initialToCursor.trans_appended
              compilerPrefix.toParentPrefix_appended,
            armReached⟩
        have rest := ih arm.node decrease initial arm rfl compiled
          armChronology targetNonPush instructionAt
        exact .branchRight cursor chronology arm compilerPrefix rest
  | call index =>
      rcases cursor.callToward_appended compiled chronology.cursorToTarget
          targetNonPush instructionAt with
        ⟨body, lookup, bodyCursor, compilerPrefix, bodyReached, decrease⟩
      let bodyChronology :
          Exec.Deriv.SourceCursor.Chronology initial bodyCursor target :=
        ⟨chronology.initialToCursor.trans_appended
            compilerPrefix.toParentPrefix_appended,
          bodyReached⟩
      have rest := ih bodyCursor.node decrease initial bodyCursor rfl compiled
        bodyChronology targetNonPush instructionAt
      exact .call cursor chronology lookup bodyCursor compilerPrefix rest

/-- Public finite source route for a reached non-PUSH instruction when the
compiled program occupies an exact code prefix. -/
theorem Exec.Deriv.SourceCursor.toward_appended
    {root target : Exec.Deriv} {program : Prog}
    {pfxCode sfxData : Bytes}
    {path : Prog.SourcePath} {source : Func} {instruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : program.CompiledPrefix root.sevm.code pfxCode sfxData)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    Exec.Deriv.SourceCursor.Toward cursor target instruction cursor := by
  let chronology : Exec.Deriv.SourceCursor.Chronology cursor cursor target :=
    ⟨.refl _, reached⟩
  exact Exec.Deriv.SourceCursor.toward_appended_core cursor.node cursor cursor
    rfl compiled chronology nonPush instructionAt

/-- Source-site completeness for a reached non-PUSH instruction in an exact
compiled prefix. -/
theorem Exec.Deriv.SourceCursor.sourceSite_appended
    {root target : Exec.Deriv} {program : Prog}
    {pfxCode sfxData : Bytes}
    {path : Prog.SourcePath} {source : Func} {instruction : Ninst}
    (cursor : Exec.Deriv.SourceCursor root program path source)
    (compiled : program.CompiledPrefix root.sevm.code pfxCode sfxData)
    (reached : Exec.Deriv.ParentPrefix cursor.node target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = instruction := by
  exact (cursor.toward_appended compiled reached nonPush instructionAt).sourceSiteResult

/-! ## Root specializations -/

/-- Every reached same-frame non-PUSH instruction of an exact compiled prefix
has a structural site in the prefix program. -/
theorem Exec.Deriv.nonPush_sourceSite_appended
    {root target : Exec.Deriv} {program : Prog}
    {pfxCode sfxData : Bytes} {instruction : Ninst}
    (identity : root.exactProgramPrefix program pfxCode sfxData)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (nonPush : NinstNonPush instruction)
    (instructionAt : Ninst.At target.sevm.code target.pc instruction) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = instruction := by
  rcases Exec.Deriv.SourceCursor.mainToward_appended identity sameFrame
      instructionAt with
    ⟨mainCursor, compilerPrefix, reached⟩
  exact mainCursor.sourceSite_appended identity.2 reached nonPush instructionAt

/-- Every reached same-frame SSTORE of an exact compiled prefix has a source
site in the prefix program, independently of the root outcome. -/
theorem Exec.Deriv.sstore_sourceSite_appended
    {root target : Exec.Deriv} {program : Prog}
    {pfxCode sfxData : Bytes}
    (identity : root.exactProgramPrefix program pfxCode sfxData)
    (sameFrame : Exec.Deriv.ParentPrefix root target)
    (storeAt : Ninst.At target.sevm.code target.pc (.reg .sstore)) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = target.pc ∧
      site.instruction = .reg .sstore := by
  exact root.nonPush_sourceSite_appended identity sameFrame (by trivial) storeAt

/-- Successful-SSTORE specialization for an arbitrary-outcome root whose
compiled program occupies an exact prefix of the full code image. -/
theorem Exec.Deriv.successfulSstore_sourceSite_appended
    {root : Exec.Deriv} {program : Prog} {pfxCode sfxData : Bytes}
    (identity : root.exactProgramPrefix program pfxCode sfxData)
    (write : Exec.SuccessfulSstoreOccurrence root)
    (sameFrame : Exec.Deriv.ParentPrefix root write.occurrence.node) :
    ∃ site : Prog.SourceSite,
      site ∈ program.sourceSites ∧
      site.pc = write.occurrence.node.pc ∧
      site.instruction = .reg .sstore := by
  have storeAt : Ninst.At write.occurrence.node.sevm.code
      write.occurrence.node.pc (.reg .sstore) := by
    rw [← write.instruction_eq]
    exact write.occurrence.decoded
  exact root.sstore_sourceSite_appended identity sameFrame storeAt

end Blanc
