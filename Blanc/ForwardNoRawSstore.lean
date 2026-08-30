import Blanc.CycleWriteFree
import Blanc.RevertPayload
import Blanc.RootedExecution

/-!
Contract-neutral construction-direction certificates for proving that a
selected compiled execution contains no raw `SSTORE` occurrence.

The path certificate follows only the branch and internal source call selected
by a `Func.RunCompiledTo` witness.  External instructions are admitted only
when their compiled step is proved childless, so a synchronously resolved
precompile call contributes its parent instruction but no entered child trace.
-/

namespace Blanc

open Jaune

/-- No reached raw execution node decodes as `SSTORE`.  This deliberately uses
`Exec.rawNodes`, not the settlement-retained chronology: reverted and failed
subtrees remain in scope. -/
def Exec.NoRawSstore {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : Prop :=
  ∀ node : Exec.Deriv,
    node ∈ Exec.rawNodes run →
    ¬ Ninst.At node.sevm.code node.pc (.reg .sstore)

namespace Exec.NoRawSstore

/-- A halting execution is raw-SSTORE-free when its root is not `SSTORE`. -/
theorem halt {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {step : Evm.step ⟨pc, sevm, pre⟩ = .halt out}
    (root : ¬ Ninst.At sevm.code pc (.reg .sstore)) :
    Exec.NoRawSstore (.halt step) := by
  intro node reached storeAt
  simp only [Exec.rawNodes, List.mem_singleton] at reached
  subst node
  exact root storeAt

/-- Prepending a non-SSTORE same-frame step preserves raw-SSTORE freedom. -/
theorem cont {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {out : Execution}
    {step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post}
    {next : Exec pc' sevm post out}
    (root : ¬ Ninst.At sevm.code pc (.reg .sstore))
    (tail : Exec.NoRawSstore next) :
    Exec.NoRawSstore (.cont step next) := by
  intro node reached storeAt
  simp only [Exec.rawNodes, List.mem_cons] at reached
  rcases reached with rfl | reached
  · exact root storeAt
  · exact tail node reached storeAt

/-- A synchronously resolved childless frame contributes only its parent root
before execution resumes. -/
theorem doneOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {settled : Except (EvmError × State × AdrSet × Tra) Devm}
    {out : Execution}
    {step : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc'}
    {enter : frame.enter = .done settled}
    {resumeOk : resume.run settled = .ok post}
    {next : Exec pc' sevm post out}
    (root : ¬ Ninst.At sevm.code pc (.reg .sstore))
    (tail : Exec.NoRawSstore next) :
    Exec.NoRawSstore (.doneOk step enter resumeOk next) := by
  intro node reached storeAt
  simp only [Exec.rawNodes, List.mem_cons] at reached
  rcases reached with rfl | reached
  · exact root storeAt
  · exact tail node reached storeAt

end Exec.NoRawSstore

/-- A raw-SSTORE-free execution rules out `SSTORE` as the instruction decoded
at every exact nonterminal occurrence in its chronology. -/
theorem Exec.NoRawSstore.instruction_ne_sstore
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (safe : Exec.NoRawSstore run)
    (occurrence : Exec.NinstOccurrence
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv)) :
    occurrence.instruction ≠ .reg .sstore := by
  intro instructionEq
  apply safe occurrence.node occurrence.reached
  rw [← instructionEq]
  exact occurrence.decoded

/-- A successful compiled instruction step whose recursive execution slot is
definitionally empty. -/
def Ninst.ChildlessRunCompiled
    (sevm : Sevm) (pre : Devm) (instruction : Ninst) (post : Devm) : Prop :=
  ∀ pc, Ninst.StepRun pc sevm pre instruction .none (.ok post)

/-- Forgetting childlessness yields the ordinary compiled-step witness. -/
theorem Ninst.ChildlessRunCompiled.toRunCompiled
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst}
    (run : Ninst.ChildlessRunCompiled sevm pre instruction post) :
    Ninst.RunCompiled sevm pre instruction post :=
  ⟨.none, trivial, run⟩

/-- A syntactically non-external compiled instruction necessarily uses the
empty recursive slot. -/
theorem Ninst.RunCompiled.childless_of_not_exec
    {sevm : Sevm} {pre post : Devm} {instruction : Ninst}
    (run : Ninst.RunCompiled sevm pre instruction post)
    (notExec : ∀ operation : Xinst, instruction ≠ .exec operation) :
    Ninst.ChildlessRunCompiled sevm pre instruction post := by
  rcases run with ⟨slot, filled, steps⟩
  cases instruction with
  | reg operation =>
      have stepRun := steps 0
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
      rw [stepRun.1] at steps
      exact steps
  | push bytes length =>
      have stepRun := steps 0
      rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at stepRun
      rw [stepRun.1] at steps
      exact steps
  | exec operation => exact (notExec operation rfl).elim

/-- A spawning instruction whose frame resolves synchronously has a childless
compiled-step witness.  Enabled precompiles are the principal consumer. -/
theorem Ninst.childlessRunCompiled_exec_doneFrame
    {sevm : Sevm} {pre post : Devm} {operation : Xinst}
    {frame : Frame} {resume : Resume}
    {settled : Except (EvmError × State × AdrSet × Tra) Devm}
    (step : Xinst.step sevm pre operation = .spawn frame resume)
    (enter : frame.enter = .done settled)
    (resumeOk : resume.run settled = .ok post) :
    Ninst.ChildlessRunCompiled sevm pre (.exec operation) post := by
  intro pc
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm pre operation) _ _
  rw [step]
  exact ⟨settled, RunFrame.of_done enter, resumeOk.symm⟩

/-- A certificate over one selected compiled source path.  Branches and
internal source calls recurse only into the chosen body.  Each explicit
instruction must have both a non-SSTORE decode and a childless compiled step. -/
inductive Func.RunCompiledTo.NoRawSstorePath :
    ∀ {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
      {out : Execution}, Func.RunCompiledTo fs sevm pre body out → Prop
  | zero {fs sevm pre post left right out}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre post}
      {tail : Func.RunCompiledTo fs sevm post left out}
      (tailSafe : Func.RunCompiledTo.NoRawSstorePath tail) :
      Func.RunCompiledTo.NoRawSstorePath
        (.zero (g := right) room pop tail)
  | succ {fs sevm pre post word left right out}
      {nonzero : word ≠ 0}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [word]
        (gVerylow + gHigh + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post right out}
      (tailSafe : Func.RunCompiledTo.NoRawSstorePath tail) :
      Func.RunCompiledTo.NoRawSstorePath
        (.succ (f := left) nonzero room pop tail)
  | last {fs sevm pre terminal out}
      {terminalRun : Linst.Run sevm pre terminal out} :
      Func.RunCompiledTo.NoRawSstorePath
        (Func.RunCompiledTo.last (fs := fs) terminalRun)
  | next {fs sevm pre post instruction body out}
      {instructionRun : Ninst.RunCompiled sevm pre instruction post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (instructionNe : instruction ≠ .reg .sstore)
      (instructionChildless :
        Ninst.ChildlessRunCompiled sevm pre instruction post)
      (tailSafe : Func.RunCompiledTo.NoRawSstorePath tail) :
      Func.RunCompiledTo.NoRawSstorePath (.next instructionRun tail)
  | call {fs sevm pre post index body out}
      {lookup : fs[index]? = some body}
      {room : pre.stack.length < 1024}
      {burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre post}
      {tail : Func.RunCompiledTo fs sevm post body out}
      (tailSafe : Func.RunCompiledTo.NoRawSstorePath tail) :
      Func.RunCompiledTo.NoRawSstorePath (.call lookup room burn tail)

/-- Ergonomic selected-path constructor for ordinary non-external
instructions. -/
theorem Func.RunCompiledTo.NoRawSstorePath.next_of_not_exec
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {instruction : Ninst} {body : Func} {out : Execution}
    {instructionRun : Ninst.RunCompiled sevm pre instruction post}
    {tail : Func.RunCompiledTo fs sevm post body out}
    (instructionNe : instruction ≠ .reg .sstore)
    (notExec : ∀ operation : Xinst, instruction ≠ .exec operation)
    (tailSafe : Func.RunCompiledTo.NoRawSstorePath tail) :
    Func.RunCompiledTo.NoRawSstorePath (.next instructionRun tail) :=
  .next (instructionRun := instructionRun) instructionNe
    (instructionRun.childless_of_not_exec notExec) tailSafe

/-- An execution-free, locally SSTORE-free source body gives a selected-path
raw certificate for any of its compiled walks.  `funcExecFree` excludes both
external instructions and internal calls; `LocalSstoreFree` excludes the
remaining same-frame `SSTORE` heads. -/
theorem Func.RunCompiledTo.NoRawSstorePath.of_execFree
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {body : Func} {out : Execution}
    (run : Func.RunCompiledTo fs sevm pre body out)
    (execFree : funcExecFree body)
    (storeFree : body.LocalSstoreFree) :
    Func.RunCompiledTo.NoRawSstorePath run := by
  induction run with
  | zero room pop tail ih =>
      exact .zero (room := room) (pop := pop)
        (ih execFree.1 storeFree.1)
  | succ nonzero room pop tail ih =>
      exact .succ (nonzero := nonzero) (room := room) (pop := pop)
        (ih execFree.2 storeFree.2)
  | last terminalRun =>
      exact .last (terminalRun := terminalRun)
  | next instructionRun tail ih =>
      rename_i _ instruction _ _ _
      cases instruction with
      | reg operation =>
          exact .next (instructionRun := instructionRun) storeFree.1
            (instructionRun.childless_of_not_exec (by
              intro external impossible
              cases impossible))
            (ih (by simpa [funcExecFree] using execFree) storeFree.2)
      | push bytes size =>
          exact .next (instructionRun := instructionRun) storeFree.1
            (instructionRun.childless_of_not_exec (by
              intro external impossible
              cases impossible))
            (ih (by simpa [funcExecFree] using execFree) storeFree.2)
      | exec operation =>
          simp [funcExecFree] at execFree
  | call lookup room burn tail ih =>
      simp [funcExecFree] at execFree

private theorem prependStoresRev_execFree
    (iws : List (B256 × Nat)) (rest : Func)
    (hrest : funcExecFree rest) :
    funcExecFree (prependStoresRev iws rest) := by
  induction iws generalizing rest with
  | nil => exact hrest
  | cons iw iws ih =>
      apply ih
      simpa [prependStore, Ninst.pushB256, funcExecFree] using hrest

private theorem prependStoresRev_localSstoreFree
    (iws : List (B256 × Nat)) (rest : Func)
    (hrest : rest.LocalSstoreFree) :
    (prependStoresRev iws rest).LocalSstoreFree := by
  induction iws generalizing rest with
  | nil => exact hrest
  | cons iw iws ih =>
      apply ih
      simpa [prependStore, Ninst.pushB256, Func.LocalSstoreFree] using hrest

/-- Every compiled constant `Error(string)` body is raw-SSTORE-free.  The
reason remains symbolic: the proof traverses the reverse-store constructor
rather than reducing the payload's computed word list. -/
theorem Func.RunCompiledTo.NoRawSstorePath.of_revWith
    {fs : List Func} {sevm : Sevm} {pre : Devm}
    {reason : String} {out : Execution}
    (run : Func.RunCompiledTo fs sevm pre (Func.revWith reason) out) :
    Func.RunCompiledTo.NoRawSstorePath run := by
  apply Func.RunCompiledTo.NoRawSstorePath.of_execFree run
  · unfold Func.revWith Func.revData
    apply prependStoresRev_execFree
    simp [Ninst.pushB256, funcExecFree]
  · unfold Func.revWith Func.revData
    apply prependStoresRev_localSstoreFree
    simp [Ninst.pushB256, Func.LocalSstoreFree]

/-- Prepend one decoded childless instruction to a raw-SSTORE-free execution.
The `.exec` case admits synchronous `.done` and synchronously resolved
`.spawn` steps, but rejects an entered child frame by the empty-slot witness. -/
private lemma Ninst.exists_exec_noRawSstore
    {pc : Nat} {sevm : Sevm} {pre post : Devm}
    {instruction : Ninst} {out : Execution}
    (instructionAt : Ninst.At sevm.code pc instruction)
    (instructionRun :
      Ninst.ChildlessRunCompiled sevm pre instruction post)
    (instructionNe : instruction ≠ .reg .sstore)
    {tail : Exec (pc + instruction.size) sevm post out}
    (tailSafe : Exec.NoRawSstore tail) :
    ∃ run : Exec pc sevm pre out, Exec.NoRawSstore run := by
  have rootSafe : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
    intro storeAt
    exact instructionNe (Ninst.at_unique instructionAt storeAt)
  have evmStep : Evm.step ⟨pc, sevm, pre⟩ =
      Ninst.step ⟨pc, sevm, pre⟩ instruction :=
    Evm.step_next instructionAt
  have stepRun := instructionRun pc
  cases instruction with
  | reg operation =>
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
      have step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) post := by
        rw [evmStep, Ninst.step_reg, ← stepRun.2]
        rfl
      exact ⟨.cont step tail, .cont rootSafe tailSafe⟩
  | push bytes length =>
      rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at stepRun
      have step : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + Ninst.size (.push bytes length)) post := by
        rw [evmStep, Ninst.step_push, ← stepRun.2]
        rfl
      exact ⟨.cont step tail, .cont rootSafe tailSafe⟩
  | exec operation =>
      rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at stepRun
      cases operationStep : Xinst.step sevm pre operation with
      | done result =>
          rw [operationStep] at stepRun
          simp only [XStep.Run] at stepRun
          have step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) post := by
            rw [evmStep, Ninst.step_exec, operationStep, ← stepRun.2]
            rfl
          exact ⟨.cont step tail, .cont rootSafe tailSafe⟩
      | spawn frame resume =>
          rw [operationStep] at stepRun
          rcases stepRun with ⟨settled, frameRun, resultEq⟩
          have step : Evm.step ⟨pc, sevm, pre⟩ =
              .spawn frame resume (pc + 1) := by
            rw [evmStep, Ninst.step_exec, operationStep]
            rfl
          unfold RunFrame at frameRun
          rcases entered : frame.enter with settled' | childEvm <;>
            simp only [entered] at frameRun
          · have resumeOk : resume.run settled' = .ok post :=
              frameRun.2 ▸ resultEq.symm
            exact ⟨.doneOk step entered resumeOk tail,
              .doneOk rootSafe tailSafe⟩
          · rcases frameRun with ⟨raw, slotEq, settledEq⟩
            cases slotEq

/-- Construction-direction compiler bridge for a selected path certificate.
It returns the exact finite execution derivation together with raw chronology
freedom; it is not an inversion or an exhaustiveness theorem. -/
theorem Func.RunCompiledTo.exists_exec_noRawSstore_core :
    ∀ {main : Func} {aux : List Func} {sevm : Sevm} {fs : List Func}
      {pre : Devm} {body : Func} {out : Execution}
      (run : Func.RunCompiledTo fs sevm pre body out),
      Func.RunCompiledTo.NoRawSstorePath run →
      some sevm.code.toList = Prog.compile ⟨main, aux⟩ →
      fs = main :: aux →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (main :: aux)) pc body) →
        noPushBefore sevm.code pc 32 = true →
        ∃ execution : Exec pc sevm pre out,
          Exec.NoRawSstore execution := by
  intro main aux sevm fs pre body out run safe
  induction safe with
  | @zero certPre certPost left right certOut
      room pop tail tailSafe ih =>
      intro compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpiAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_zero_steps pushAt jumpiAt locAt room pop with
        ⟨pushStep, jumpStep⟩
      rcases ih compiled tableEq (pc + 4) leftSub leftNoPush with
        ⟨leftRun, leftSafe⟩
      have pushSafe : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.at_unique pushAt storeAt
        cases impossible
      have jumpSafe : ¬ Ninst.At sevm.code (pc + 3) (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpiAt
      exact ⟨.cont pushStep (.cont jumpStep leftRun),
        .cont pushSafe (.cont jumpSafe leftSafe)⟩
  | @succ certPre certPost word left right certOut
      nonzero room pop tail tailSafe ih =>
      intro compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpiAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_succ_steps pushAt jumpiAt jumpdestAt jumpable
        locAt nonzero room pop with
        ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih compiled tableEq (loc + 1) rightSub rightNoPush with
        ⟨rightRun, rightSafe⟩
      have pushSafe : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.at_unique pushAt storeAt
        cases impossible
      have jumpSafe : ¬ Ninst.At sevm.code (pc + 3) (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpiAt
      have jumpdestSafe : ¬ Ninst.At sevm.code loc (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpdestAt
      exact ⟨.cont pushStep (.cont jumpStep
          (.cont jumpdestStep rightRun)),
        .cont pushSafe (.cont jumpSafe
          (.cont jumpdestSafe rightSafe))⟩
  | @last certPre terminal certOut terminalRun =>
      intro compiled tableEq pc sub noPush
      have terminalAt := Linst.at_of_slice sub
      have step : Evm.step ⟨pc, sevm, certPre⟩ = .halt certOut := by
        rw [Evm.step_last terminalAt]
        exact congrArg Step.halt terminalRun
      have terminalSafe : ¬ Ninst.At sevm.code pc (.reg .sstore) :=
        fun storeAt => storeAt.false_of_linstAt terminalAt
      exact ⟨.halt step, .halt terminalSafe⟩
  | @next certPre certPost instruction certBody certOut
      instructionRun tail instructionNe instructionChildless tailSafe ih =>
      intro compiled tableEq pc sub noPush
      rcases Func.noPushBefore_next sub noPush with
        ⟨tailNoPush, tailSub⟩
      rcases of_subcode sub with ⟨code, compileEq, slice⟩
      rcases of_bind_eq_some compileEq with
        ⟨tailCode, tailCompileEq, codeEq⟩
      simp [pure] at codeEq
      rw [← codeEq] at slice
      have instructionAt : Ninst.At sevm.code pc _ :=
        Ninst.at_of_slice (List.slice_prefix slice)
      rcases ih compiled tableEq _ tailSub tailNoPush with
        ⟨tailRun, tailExecutionSafe⟩
      exact Ninst.exists_exec_noRawSstore instructionAt
        instructionChildless instructionNe tailExecutionSafe
  | @call certPre certPost index certBody certOut
      lookup room burn tail tailSafe ih =>
      intro compiled tableEq pc sub noPush
      subst tableEq
      rcases subcode_compile_call sub with
        ⟨loc, compiledBody, tableLookup, locBound, pushAt, jumpAt⟩
      have selected := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) tableLookup)
      rw [lookup] at selected
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at selected
      subst selected
      rcases subcode_of_get?_eq_some compiled tableLookup with
        ⟨jumpdestAt, bodySub⟩
      have bodyJumpable := Prog.jumpable_of_get?_table compiled tableLookup
      rcases pushAt with ⟨length, pushAt⟩
      rcases Evm.call_steps (le := length) pushAt jumpAt jumpdestAt
        bodyJumpable.1 locBound room burn with
        ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih compiled rfl (loc + 1) bodySub bodyJumpable.2 with
        ⟨bodyRun, bodySafe⟩
      have pushSafe : ¬ Ninst.At sevm.code pc (.reg .sstore) := by
        intro storeAt
        have impossible := Ninst.at_unique pushAt storeAt
        cases impossible
      have jumpSafe : ¬ Ninst.At sevm.code (pc + 3) (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpAt
      have jumpdestSafe : ¬ Ninst.At sevm.code loc (.reg .sstore) :=
        fun storeAt => storeAt.false_of_jinstAt jumpdestAt
      exact ⟨.cont pushStep (.cont jumpStep
          (.cont jumpdestStep bodyRun)),
        .cont pushSafe (.cont jumpSafe
          (.cont jumpdestSafe bodySafe))⟩

/-- Whole-program entry bridge.  The explicit components are exactly the
witnesses hidden by `Prog.RunCompiledTo`; keeping the selected-path certificate
indexed by `mainRun` avoids any proof-identity seam through that existential. -/
theorem Prog.exists_exec_noRawSstore
    {sevm : Sevm} {pre mid : Devm} {program : Prog} {out : Execution}
    (entryBurn : Devm.BurnBy gJumpdest pre mid)
    (mainRun : Func.RunCompiledTo (program.main :: program.aux)
      sevm mid program.main out)
    (mainSafe : Func.RunCompiledTo.NoRawSstorePath mainRun)
    (compiled : some sevm.code.toList = program.compile) :
    ∃ execution : Exec 0 sevm pre out, Exec.NoRawSstore execution := by
  have compiled' : some sevm.code.toList =
      Prog.compile ⟨program.main, program.aux⟩ := compiled
  have entryLookup :
      (table 0 (program.main :: program.aux))[0]? =
        some (0, program.main) := rfl
  rcases subcode_of_get?_eq_some compiled' entryLookup with
    ⟨jumpdestAt, mainSub⟩
  have mainNoPush : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table compiled' entryLookup).2
  have entryStep : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont jumpdestAt entryBurn
  rcases mainRun.exists_exec_noRawSstore_core mainSafe compiled' rfl
      1 mainSub mainNoPush with
    ⟨mainExecution, mainExecutionSafe⟩
  have entrySafe : ¬ Ninst.At sevm.code 0 (.reg .sstore) :=
    fun storeAt => storeAt.false_of_jinstAt jumpdestAt
  exact ⟨.cont entryStep mainExecution,
    .cont entrySafe mainExecutionSafe⟩

/-- Raw-SSTORE freedom excludes every successful SSTORE occurrence in the
same exact execution derivation. -/
theorem Exec.NoRawSstore.no_successfulSstoreOccurrence
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (safe : Exec.NoRawSstore run) :
    ¬ Nonempty (Exec.SuccessfulSstoreOccurrence
      (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv)) := by
  rintro ⟨write⟩
  exact safe.instruction_ne_sstore
    write.occurrence write.instruction_eq

/-- In particular, a raw-SSTORE-free execution has an empty retained write
chronology. -/
theorem Exec.NoRawSstore.retainedStorageWrites_eq_nil
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    {run : Exec pc sevm pre out}
    (safe : Exec.NoRawSstore run) :
    Exec.retainedStorageWrites run = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro event member
  rcases Exec.exists_successfulSstore_of_mem_retainedStorageWrites
      (root := (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv))
      (event := event) member with ⟨write, -, -⟩
  exact safe.no_successfulSstoreOccurrence ⟨write⟩

end Blanc
