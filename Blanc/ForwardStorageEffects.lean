import Blanc.ForwardNoRawSstore

/-!
# Exact selected-path storage effects

Construction-direction certificates for the complete retained SSTORE
chronology of one successful compiled path.  Branches and internal calls follow
the witness selected by `Func.RunCompiled`; external steps must be childless,
so a synchronously resolved precompile contributes no hidden child-frame
writes.  A successful no-op SSTORE is retained intentionally.
-/

namespace Blanc

open Jaune

/-- The proof-free storage effect of one successful childless instruction
step, if that instruction is SSTORE and its two stack operands are present. -/
def Ninst.storageEffectTriple?
    (sevm : Sevm) (pre : Devm) (instruction : Ninst) :
    Option (Adr × B256 × B256) :=
  match instruction, pre.stack with
  | .reg .sstore, key :: value :: _ =>
      some (sevm.currentTarget, key, value)
  | _, _ => none

private theorem Ninst.successfulSstore_effectTriples
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {out : Execution} {instruction : Ninst}
    {step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post}
    (tail : Exec pc' sevm post out)
    (instructionAt : Ninst.At sevm.code pc instruction) :
    (Exec.Deriv.successfulSstore?
      (⟨pc, sevm, pre, out, Exec.cont step tail⟩ : Exec.Deriv)).toList.map
        Exec.StorageWrite.effectTriple =
      (Ninst.storageEffectTriple? sevm pre instruction).toList := by
  have decoded : Evm.getInst ⟨pc, sevm, pre⟩ =
      some (.next instruction) := instructionAt
  cases instruction with
  | push bytes bound =>
      simp [Exec.Deriv.successfulSstore?, Ninst.storageEffectTriple?, decoded]
  | exec operation =>
      simp [Exec.Deriv.successfulSstore?, Ninst.storageEffectTriple?, decoded]
  | reg operation =>
      cases operation <;>
        simp [Exec.Deriv.successfulSstore?, Ninst.storageEffectTriple?, decoded]
      case sstore =>
        cases stackEq : pre.stack with
        | nil =>
            simp
        | cons key rest =>
            cases rest with
            | nil =>
                simp
            | cons value tail =>
                simp [Exec.StorageWrite.effectTriple]

private theorem Jinst.successfulSstore_effectTriples
    {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
    {out : Execution} {instruction : Jinst}
    {step : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post}
    (tail : Exec pc' sevm post out)
    (instructionAt : Jinst.At sevm.code pc instruction) :
    (Exec.Deriv.successfulSstore?
      (⟨pc, sevm, pre, out, Exec.cont step tail⟩ : Exec.Deriv)).toList.map
        Exec.StorageWrite.effectTriple = [] := by
  have decoded : Evm.getInst ⟨pc, sevm, pre⟩ =
      some (.jump instruction) := instructionAt
  simp [Exec.Deriv.successfulSstore?, decoded]

/-- Exact retained storage-effect annotation for a selected successful source
walk.  Its list is in execution order. -/
inductive Func.RunCompiled.StorageEffectPath :
    ∀ {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
      {post : Devm}, Func.RunCompiled fs sevm pre body post →
        List (Adr × B256 × B256) → Prop
  | zero {fs sevm pre branchPre left right post effects}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre branchPre}
      {tail : Func.RunCompiled fs sevm branchPre left post}
      (tailEffects : Func.RunCompiled.StorageEffectPath tail effects) :
      Func.RunCompiled.StorageEffectPath
        (.zero (g := right) room pop tail) effects
  | succ {fs sevm pre branchPre word left right post effects}
      {nonzero : word ≠ 0}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [word]
        (gVerylow + gHigh + gJumpdest) pre branchPre}
      {tail : Func.RunCompiled fs sevm branchPre right post}
      (tailEffects : Func.RunCompiled.StorageEffectPath tail effects) :
      Func.RunCompiled.StorageEffectPath
        (.succ (f := left) nonzero room pop tail) effects
  | last {fs sevm pre terminal post}
      {terminalRun : Linst.Run sevm pre terminal (.ok post)} :
      Func.RunCompiled.StorageEffectPath
        (Func.RunCompiled.last (fs := fs) terminalRun) []
  | next {fs sevm pre nextPre instruction body post effects}
      {instructionRun : Ninst.RunCompiled sevm pre instruction nextPre}
      {tail : Func.RunCompiled fs sevm nextPre body post}
      (instructionChildless :
        Ninst.ChildlessRunCompiled sevm pre instruction nextPre)
      (tailEffects : Func.RunCompiled.StorageEffectPath tail effects) :
      Func.RunCompiled.StorageEffectPath (.next instructionRun tail)
        ((Ninst.storageEffectTriple? sevm pre instruction).toList ++ effects)
  | call {fs sevm pre callPre index body post effects}
      {lookup : fs[index]? = some body}
      {room : pre.stack.length < 1024}
      {burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre callPre}
      {tail : Func.RunCompiled fs sevm callPre body post}
      (tailEffects : Func.RunCompiled.StorageEffectPath tail effects) :
      Func.RunCompiled.StorageEffectPath (.call lookup room burn tail) effects

/-- Ordinary non-external instructions are childless automatically. -/
theorem Func.RunCompiled.StorageEffectPath.next_of_not_exec
    {fs : List Func} {sevm : Sevm} {pre nextPre : Devm}
    {instruction : Ninst} {body : Func} {post : Devm}
    {instructionRun : Ninst.RunCompiled sevm pre instruction nextPre}
    {tail : Func.RunCompiled fs sevm nextPre body post}
    {effects : List (Adr × B256 × B256)}
    (notExec : ∀ operation : Xinst, instruction ≠ .exec operation)
    (tailEffects : Func.RunCompiled.StorageEffectPath tail effects) :
    Func.RunCompiled.StorageEffectPath (.next instructionRun tail)
      ((Ninst.storageEffectTriple? sevm pre instruction).toList ++ effects) :=
  .next (instructionRun := instructionRun)
    (instructionRun.childless_of_not_exec notExec) tailEffects

private theorem Ninst.exists_exec_storageEffects
    {pc : Nat} {sevm : Sevm} {pre nextPre post : Devm}
    {instruction : Ninst} {effects : List (Adr × B256 × B256)}
    (instructionAt : Ninst.At sevm.code pc instruction)
    (instructionRun :
      Ninst.ChildlessRunCompiled sevm pre instruction nextPre)
    {tail : Exec (pc + instruction.size) sevm nextPre (.ok post)}
    (committed : Execution.commits (.ok post) = true)
    (tailEffects : Exec.retainedStorageEffectTriples tail =
      effects) :
    ∃ run : Exec pc sevm pre (.ok post),
      Exec.retainedStorageEffectTriples run =
        (Ninst.storageEffectTriple? sevm pre instruction).toList ++ effects := by
  have evmStep : Evm.step ⟨pc, sevm, pre⟩ =
      Ninst.step ⟨pc, sevm, pre⟩ instruction :=
    Evm.step_next instructionAt
  have stepRun := instructionRun pc
  cases instruction with
  | reg operation =>
    rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at stepRun
    have step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) nextPre := by
      rw [evmStep, Ninst.step_reg, ← stepRun.2]
      rfl
    have step' : Evm.step ⟨pc, sevm, pre⟩ =
        .cont (pc + Ninst.size (.reg operation)) nextPre := by
      simpa only [Ninst.size] using step
    refine ⟨.cont step' tail, ?_⟩
    rw [Exec.retainedStorageEffectTriples_cont tail committed,
      Ninst.successfulSstore_effectTriples tail instructionAt,
      tailEffects]
  | push bytes bound =>
      rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at stepRun
      have step : Evm.step ⟨pc, sevm, pre⟩ =
          .cont (pc + Ninst.size (.push bytes bound)) nextPre := by
        rw [evmStep, Ninst.step_push, ← stepRun.2]
        rfl
      refine ⟨.cont step tail, ?_⟩
      rw [Exec.retainedStorageEffectTriples_cont tail committed,
        Ninst.successfulSstore_effectTriples tail instructionAt,
        tailEffects]
  | exec operation =>
      rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at stepRun
      cases operationStep : Xinst.step sevm pre operation with
      | done result =>
          rw [operationStep] at stepRun
          simp only [XStep.Run] at stepRun
          have step : Evm.step ⟨pc, sevm, pre⟩ = .cont (pc + 1) nextPre := by
            rw [evmStep, Ninst.step_exec, operationStep, ← stepRun.2]
            rfl
          have step' : Evm.step ⟨pc, sevm, pre⟩ =
              .cont (pc + Ninst.size (.exec operation)) nextPre := by
            simpa only [Ninst.size] using step
          refine ⟨.cont step' tail, ?_⟩
          rw [Exec.retainedStorageEffectTriples_cont tail committed,
            Ninst.successfulSstore_effectTriples tail instructionAt,
            tailEffects]
      | spawn frame resume =>
          rw [operationStep] at stepRun
          rcases stepRun with ⟨settled, frameRun, resultEq⟩
          have step : Evm.step ⟨pc, sevm, pre⟩ =
              .spawn frame resume (pc + 1) := by
            rw [evmStep, Ninst.step_exec, operationStep]
            rfl
          have step' : Evm.step ⟨pc, sevm, pre⟩ =
              .spawn frame resume (pc + Ninst.size (.exec operation)) := by
            simpa only [Ninst.size] using step
          unfold RunFrame at frameRun
          rcases entered : frame.enter with settled' | childEvm <;>
            simp only [entered] at frameRun
          · have resumeOk : resume.run settled' = .ok nextPre :=
              frameRun.2 ▸ resultEq.symm
            refine ⟨.doneOk step' entered resumeOk tail, ?_⟩
            rw [Exec.retainedStorageEffectTriples_doneOk tail committed,
              tailEffects]
            rfl
          · rcases frameRun with ⟨raw, slotEq, settledEq⟩
            cases slotEq

private theorem Func.RunCompiled.StorageEffectPath.exists_exec_core :
    ∀ {main : Func} {aux : List Func} {sevm : Sevm} {fs : List Func}
      {pre : Devm} {body : Func} {post : Devm}
      {run : Func.RunCompiled fs sevm pre body post}
      {effects : List (Adr × B256 × B256)},
      Func.RunCompiled.StorageEffectPath run effects →
      Execution.commits (.ok post) = true →
      some sevm.code.toList = Prog.compile ⟨main, aux⟩ →
      fs = main :: aux →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (main :: aux)) pc body) →
        noPushBefore sevm.code pc 32 = true →
        ∃ execution : Exec pc sevm pre (.ok post),
          Exec.retainedStorageEffectTriples execution = effects := by
  intro main aux sevm fs pre body post run effects certified
  induction certified with
  | @zero certPre branchPre left right certPost certEffects
      room pop tail tailEffects ih =>
      intro committed compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_zero_steps pushAt jumpAt locAt room pop with
        ⟨pushStep, jumpStep⟩
      rcases ih committed compiled tableEq (pc + 4) leftSub leftNoPush with
        ⟨leftRun, leftEffects⟩
      refine ⟨.cont pushStep (.cont jumpStep leftRun), ?_⟩
      rw [Exec.retainedStorageEffectTriples_cont _ committed,
        Exec.retainedStorageEffectTriples_cont leftRun committed,
        Ninst.successfulSstore_effectTriples _ pushAt,
        Jinst.successfulSstore_effectTriples leftRun jumpAt,
        leftEffects]
      rfl
  | @succ certPre branchPre word left right certPost certEffects
      nonzero room pop tail tailEffects ih =>
      intro committed compiled tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_succ_steps pushAt jumpAt jumpdestAt jumpable
        locAt nonzero room pop with ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih committed compiled tableEq (loc + 1) rightSub rightNoPush with
        ⟨rightRun, rightEffects⟩
      refine ⟨.cont pushStep (.cont jumpStep
        (.cont jumpdestStep rightRun)), ?_⟩
      rw [Exec.retainedStorageEffectTriples_cont _ committed,
        Exec.retainedStorageEffectTriples_cont _ committed,
        Exec.retainedStorageEffectTriples_cont rightRun committed,
        Ninst.successfulSstore_effectTriples _ pushAt,
        Jinst.successfulSstore_effectTriples _ jumpAt,
        Jinst.successfulSstore_effectTriples rightRun jumpdestAt,
        rightEffects]
      rfl
  | @last certPre terminal certPost terminalRun =>
      intro committed compiled tableEq pc sub noPush
      have terminalAt := Linst.at_of_slice sub
      have step : Evm.step ⟨pc, sevm, certPre⟩ = .halt (.ok certPost) := by
        rw [Evm.step_last terminalAt]
        exact congrArg Step.halt terminalRun
      refine ⟨.halt step, ?_⟩
      exact Exec.retainedStorageEffectTriples_halt committed
  | @next certPre nextPre instruction certBody certPost certEffects
      instructionRun tail instructionChildless tailEffects ih =>
      intro committed compiled tableEq pc sub noPush
      rcases Func.noPushBefore_next sub noPush with
        ⟨tailNoPush, tailSub⟩
      rcases of_subcode sub with ⟨compiledTail, compileEq, slice⟩
      rcases of_bind_eq_some compileEq with
        ⟨tailCode, tailCompileEq, codeEq⟩
      simp [pure] at codeEq
      rw [← codeEq] at slice
      have instructionAt : Ninst.At sevm.code pc instruction :=
        Ninst.at_of_slice (List.slice_prefix slice)
      rcases ih committed compiled tableEq _ tailSub tailNoPush with
        ⟨tailRun, tailEffectEq⟩
      rcases Ninst.exists_exec_storageEffects instructionAt
          instructionChildless (tail := tailRun) committed tailEffectEq with
        ⟨execution, headEffect⟩
      exact ⟨execution, headEffect⟩
  | @call certPre callPre index certBody certPost certEffects
      lookup room burn tail tailEffects ih =>
      intro committed compiled tableEq pc sub noPush
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
      rcases ih committed compiled rfl (loc + 1) bodySub bodyJumpable.2 with
        ⟨bodyRun, bodyEffects⟩
      refine ⟨.cont pushStep (.cont jumpStep
        (.cont jumpdestStep bodyRun)), ?_⟩
      rw [Exec.retainedStorageEffectTriples_cont _ committed,
        Exec.retainedStorageEffectTriples_cont _ committed,
        Exec.retainedStorageEffectTriples_cont bodyRun committed,
        Ninst.successfulSstore_effectTriples _ pushAt,
        Jinst.successfulSstore_effectTriples _ jumpAt,
        Jinst.successfulSstore_effectTriples bodyRun jumpdestAt,
        bodyEffects]
      rfl

/-- Whole-program successful execution bridge with exact retained storage
effect chronology. -/
theorem Prog.exists_exec_retainedStorageEffectTriples
    {sevm : Sevm} {pre mid post : Devm} {program : Prog}
    {mainRun : Func.RunCompiled (program.main :: program.aux)
      sevm mid program.main post}
    {effects : List (Adr × B256 × B256)}
    (entryBurn : Devm.BurnBy gJumpdest pre mid)
    (mainEffects : Func.RunCompiled.StorageEffectPath mainRun effects)
    (committed : Execution.commits (.ok post) = true)
    (compiled : some sevm.code.toList = program.compile) :
    ∃ execution : Exec 0 sevm pre (.ok post),
      Exec.retainedStorageEffectTriples execution = effects := by
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
  rcases Func.RunCompiled.StorageEffectPath.exists_exec_core mainEffects
      committed compiled' rfl 1 mainSub mainNoPush with
    ⟨execution, effectEq⟩
  refine ⟨.cont entryStep execution, ?_⟩
  rw [Exec.retainedStorageEffectTriples_cont execution committed,
    Jinst.successfulSstore_effectTriples execution jumpdestAt,
    effectEq]
  rfl

end Blanc
