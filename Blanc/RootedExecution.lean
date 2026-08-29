import Blanc.ExecutionOccurrence
import Blanc.Reverts

/-!
# Frame-root predicates carried through compiled execution

This module strengthens the ordinary compiled-walk bridge with a predicate on
every child frame root selected by an execution slot.  It is contract-neutral:
callers choose the predicate, prove it for spawning instructions, and recover
an `Exec` derivation whose raw frame descendants all satisfy that predicate.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- A predicate holds for every root in a filled execution slot. -/
def rawFrameRootsSatisfy (P : Exec.Deriv → Prop) : Xlot → Prop
  | .none => True
  | .some ⟨evm, out⟩ =>
      ∀ run : Exec evm.pc evm.sta evm.dyna out,
        ∀ root ∈ Exec.rawFrameRoots run, P root

/-- Every child root selected by one compiled instruction satisfies `P`. -/
def ninstAllChildRoots
    (P : Exec.Deriv → Prop) {sevm : Sevm} {devm : Devm}
    {n : Ninst} {devm' : Devm} : Prop :=
  ∀ (xl : Xlot) (_filled : xl.Filled),
    (∀ pc, Ninst.StepRun pc sevm devm n xl (.ok devm')) →
      rawFrameRootsSatisfy P xl

/-- A compiled function walk together with a predicate on every child frame
root selected along the walk. -/
inductive rootedRunCompiledTo (P : Exec.Deriv → Prop) :
    {FS : List Func} → {sevm : Sevm} → {devm : Devm} →
      {f : Func} → {ex : Execution} →
      (run : Func.RunCompiledTo FS sevm devm f ex) → Prop
  | zero {FS : List Func} {sevm : Sevm} {devm devm' : Devm}
      {f g : Func} {ex : Execution}
      {room : devm.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) devm devm'}
      {tail : Func.RunCompiledTo FS sevm devm' f ex} :
      rootedRunCompiledTo P tail →
        rootedRunCompiledTo P (.zero room pop tail)
  | succ {FS : List Func} {sevm : Sevm} {devm devm' : Devm}
      {w : B256} {f g : Func} {ex : Execution}
      {hne : w ≠ 0} {room : devm.stack.length < 1024}
      {pop : Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm devm'}
      {tail : Func.RunCompiledTo FS sevm devm' g ex} :
      rootedRunCompiledTo P tail →
        rootedRunCompiledTo P (.succ hne room pop tail)
  | last {FS : List Func} {sevm : Sevm} {devm : Devm}
      {i : Linst} {ex : Execution} {run : Linst.Run sevm devm i ex} :
      rootedRunCompiledTo P (.last run)
  | next {FS : List Func} {sevm : Sevm} {devm devm' : Devm}
      {i : Ninst} {f : Func} {ex : Execution}
      {step : Ninst.RunCompiled sevm devm i devm'}
      {tail : Func.RunCompiledTo FS sevm devm' f ex} :
      ninstAllChildRoots P
        (sevm := sevm) (devm := devm) (n := i) (devm' := devm') →
      rootedRunCompiledTo P tail →
        rootedRunCompiledTo P (.next step tail)
  | call {FS : List Func} {sevm : Sevm} {devm devm' : Devm}
      {k : Nat} {f : Func} {ex : Execution}
      {found : FS[k]? = some f}
      {room : devm.stack.length < 1024}
      {burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) devm devm'}
      {tail : Func.RunCompiledTo FS sevm devm' f ex} :
      rootedRunCompiledTo P tail →
        rootedRunCompiledTo P (.call found room burn tail)

/-- A non-execution instruction selects no child frame roots. -/
theorem ninstAllChildRoots_of_not_exec
    {P : Exec.Deriv → Prop} {sevm : Sevm} {devm devm' : Devm}
    {n : Ninst} (notExec : ∀ x : Xinst, n ≠ .exec x) :
    ninstAllChildRoots P
      (sevm := sevm) (devm := devm) (n := n) (devm' := devm') := by
  intro slot _filled stepRun
  cases slot with
  | none => trivial
  | some child =>
      have step := stepRun 0
      cases n with
      | reg r =>
          simp only [Ninst.StepRun, Ninst.step_reg,
            Step.run_ofExecution] at step
          cases step.1
      | push xs le =>
          simp only [Ninst.StepRun, Ninst.step_push,
            Step.run_ofExecution] at step
          cases step.1
      | exec x =>
          exact (notExec x rfl).elim

/-- Structural execution-freedom for a function body, including the absence
of internal `.call` edges. -/
def funcExecFree : Func → Prop
  | .branch f g => funcExecFree f ∧ funcExecFree g
  | .last _ => True
  | .next (.exec _) _ => False
  | .next _ f => funcExecFree f
  | .call _ => False

/-- An execution-free compiled walk cannot add a child frame, so it can carry
any already-selected frame-root predicate. -/
theorem rootedRunCompiledTo_of_execFree
    {P : Exec.Deriv → Prop}
    {FS : List Func} {sevm : Sevm} {devm : Devm}
    {f : Func} {ex : Execution}
    {run : Func.RunCompiledTo FS sevm devm f ex}
    (free : funcExecFree f) :
    rootedRunCompiledTo P run := by
  induction run with
  | zero room pop tail ih =>
      rename_i _ _ _ other _
      exact rootedRunCompiledTo.zero
        (g := other) (room := room) (pop := pop) (tail := tail) (ih free.1)
  | succ hne room pop tail ih =>
      rename_i _ _ _ other _ _
      exact rootedRunCompiledTo.succ
        (f := other) (hne := hne) (room := room) (pop := pop) (tail := tail)
        (ih free.2)
  | last lastRun =>
      exact rootedRunCompiledTo.last (FS := FS) (run := lastRun)
  | next step tail ih =>
      rename_i _ instruction _ _ _
      cases instruction with
      | reg r =>
          refine rootedRunCompiledTo.next (step := step) (tail := tail)
            (ninstAllChildRoots_of_not_exec ?_) (ih ?_)
          · intro x h
            cases h
          · simpa [funcExecFree] using free
      | push bytes size =>
          refine rootedRunCompiledTo.next (step := step) (tail := tail)
            (ninstAllChildRoots_of_not_exec ?_) (ih ?_)
          · intro x h
            cases h
          · simpa [funcExecFree] using free
      | exec x =>
          simp [funcExecFree] at free
  | call found room burn tail ih =>
      simp [funcExecFree] at free

/-- A spawning instruction carries a predicate proved for all roots of the
entered child execution. -/
theorem ninstAllChildRoots_of_exec_spawn
    {P : Exec.Deriv → Prop} {sevm : Sevm} {devm devm' : Devm}
    {x : Xinst} {frame : Frame} {resume : Resume} {childEvm : Evm}
    (spawn : Xinst.step sevm devm x = .spawn frame resume)
    (enters : frame.enter = .run childEvm)
    (childRoots :
      ∀ {raw : Execution}
        (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw),
        ∀ root ∈ Exec.rawFrameRoots child, P root) :
    ninstAllChildRoots P
      (sevm := sevm) (devm := devm) (n := .exec x) (devm' := devm') := by
  intro slot _filled stepRun
  have step := stepRun 0
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, spawn] at step
  rcases step with ⟨result, frameRun, _⟩
  unfold RunFrame at frameRun
  rw [enters] at frameRun
  rcases frameRun with ⟨raw, slotEq, _⟩
  subst slot
  exact childRoots

/-- Lift one instruction step and a rooted continuation into an `Exec`
derivation while preserving all raw child-frame roots. -/
theorem Ninst.exec_of_stepRun_with_frameRoots
    {P : Exec.Deriv → Prop}
    {pc : Nat} {sevm : Sevm} {devm devmMid : Devm}
    {n : Ninst} {xl : Xlot} {exn : Execution}
    (h_at : Ninst.At sevm.code pc n)
    (h_filled : xl.Filled)
    (h_roots : rawFrameRootsSatisfy P xl)
    (h_step : Ninst.StepRun pc sevm devm n xl (.ok devmMid))
    (h_next :
      ∃ next : Exec (pc + n.size) sevm devmMid exn,
        ∀ root ∈ Exec.rawFrameDescendants next, P root) :
    ∃ run : Exec pc sevm devm exn,
      ∀ root ∈ Exec.rawFrameDescendants run, P root := by
  rcases h_next with ⟨next, nextRoots⟩
  have hstep : Evm.step ⟨pc, sevm, devm⟩ =
      Ninst.step ⟨pc, sevm, devm⟩ n :=
    Evm.step_next h_at
  cases n with
  | reg r =>
      rw [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at h_step
      refine ⟨Exec.cont ?_ next, ?_⟩
      · rw [hstep, Ninst.step_reg, ← h_step.2]
        rfl
      · simpa [Exec.rawFrameDescendants] using nextRoots
  | push xs le =>
      rw [Ninst.StepRun, Ninst.step_push, Step.run_ofExecution] at h_step
      refine ⟨Exec.cont ?_ next, ?_⟩
      · rw [hstep, Ninst.step_push, ← h_step.2]
        rfl
      · simpa [Exec.rawFrameDescendants] using nextRoots
  | exec x =>
      rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at h_step
      cases hx : Xinst.step sevm devm x with
      | done e =>
          rw [hx] at h_step
          simp only [XStep.Run] at h_step
          refine ⟨Exec.cont ?_ next, ?_⟩
          · rw [hstep, Ninst.step_exec, hx, ← h_step.2]
            rfl
          · simpa [Exec.rawFrameDescendants] using nextRoots
      | spawn frame resume =>
          rw [hx] at h_step
          rcases h_step with ⟨result, frameRun, resultEq⟩
          have hspawn : Evm.step ⟨pc, sevm, devm⟩ =
              .spawn frame resume (pc + 1) := by
            rw [hstep, Ninst.step_exec, hx]
            rfl
          unfold RunFrame at frameRun
          rcases henter : frame.enter with done | childEvm <;>
              simp only [henter] at frameRun
          · refine ⟨Exec.doneOk hspawn henter (frameRun.2 ▸ resultEq.symm)
                next, ?_⟩
            simpa only [Exec.rawFrameDescendants]
          · rcases frameRun with ⟨raw, slotEq, settleEq⟩
            subst slotEq
            obtain ⟨child⟩ :
                Nonempty (Exec childEvm.pc childEvm.sta childEvm.dyna raw) :=
              h_filled
            have resumeOk :
                resume.run (frame.settle raw) = .ok devmMid := by
              rw [← settleEq]
              exact resultEq.symm
            let run : Exec pc sevm devm exn :=
              Exec.runOk hspawn henter child resumeOk next
            refine ⟨run, ?_⟩
            intro root member
            simp only [run, Exec.rawFrameDescendants, List.mem_cons,
              List.mem_append] at member
            rcases member with rfl | member
            · exact h_roots child _ (Exec.mem_rawFrameRoots_self child)
            · rcases member with childMember | nextMember
              · exact h_roots child root (by
                  simp only [Exec.rawFrameRoots, List.mem_cons]
                  exact Or.inr childMember)
              · exact nextRoots root nextMember

/-- Core compiler bridge for a rooted compiled function walk. -/
theorem Func.exec_of_rootedRunCompiledTo_core
    {P : Exec.Deriv → Prop}
    {f₀ : Func} {fs' : List Func} {sevm : Sevm} {FS : List Func}
    {devm : Devm} {p : Func} {ex : Execution}
    {run : Func.RunCompiledTo FS sevm devm p ex}
    (rooted : rootedRunCompiledTo P run)
    (compiled : some sevm.code.toList = Prog.compile ⟨f₀, fs'⟩)
    (hFS : FS = f₀ :: fs')
    (pc : Nat)
    (sub : subcode sevm.code.toList pc
      (Func.compile (table 0 (f₀ :: fs')) pc p))
    (boundary : noPushBefore sevm.code pc 32 = true) :
    ∃ execution : Exec pc sevm devm ex,
      ∀ root ∈ Exec.rawFrameDescendants execution, P root := by
  induction rooted generalizing f₀ fs' pc with
  | zero tailRooted ih =>
      rename_i _ _ _ _ _ _ _ _ hroom hpop _
      rcases subcode_compile_branch_jumpable sub boundary with
        ⟨loc, _, hloc, hpush, hjumpi, hsubp, hbp, _, _, _, _⟩
      rcases Evm.branch_zero_steps hpush hjumpi hloc hroom hpop with
        ⟨step₁, step₂⟩
      obtain ⟨tailExec, tailRoots⟩ :=
        ih compiled hFS (pc + 4) hsubp hbp
      refine ⟨Exec.cont step₁ (Exec.cont step₂ tailExec), ?_⟩
      simpa [Exec.rawFrameDescendants] using tailRoots
  | succ tailRooted ih =>
      rename_i _ _ _ _ _ _ _ _ _ hne hroom hpop _
      rcases subcode_compile_branch_jumpable sub boundary with
        ⟨loc, _, hloc, hpush, hjumpi, _, _, hjumpdest, hjumpable,
          hsubq, hbq⟩
      rcases Evm.branch_succ_steps hpush hjumpi hjumpdest hjumpable hloc
          hne hroom hpop with ⟨step₁, step₂, step₃⟩
      obtain ⟨tailExec, tailRoots⟩ :=
        ih compiled hFS (loc + 1) hsubq hbq
      refine ⟨Exec.cont step₁ (Exec.cont step₂
        (Exec.cont step₃ tailExec)), ?_⟩
      simpa [Exec.rawFrameDescendants] using tailRoots
  | last =>
      rename_i _ _ _ _ _ _ hlast
      refine ⟨Exec.halt ?_, ?_⟩
      · rw [Evm.step_last (Linst.at_of_slice sub)]
        exact congrArg Step.halt hlast
      · simp [Exec.rawFrameDescendants]
  | next stepRoots tailRooted ih =>
      rename_i _ _ _ _ _ _ _ hstep _
      rcases Func.noPushBefore_next sub boundary with ⟨boundary', sub'⟩
      rcases of_subcode sub with ⟨code, compiledHead, slice⟩
      rcases of_bind_eq_some compiledHead with
        ⟨tailCode, compiledTail, headEq⟩
      simp [pure] at headEq
      rw [← headEq] at slice
      rcases hstep with ⟨slot, filled, stepRun⟩
      exact Ninst.exec_of_stepRun_with_frameRoots
        (Ninst.at_of_slice (List.slice_prefix slice))
        filled (stepRoots slot filled stepRun) (stepRun pc)
        (ih compiled hFS _ sub' boundary')
  | call tailRooted ih =>
      rename_i _ _ _ _ _ _ _ hfound hroom hburn _
      subst hFS
      rcases subcode_compile_call sub with
        ⟨loc, body, htable, hloc, hpushAt, hjump⟩
      have bodyEq := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) htable)
      rw [hfound] at bodyEq
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at bodyEq
      subst bodyEq
      rcases subcode_of_get?_eq_some compiled htable with
        ⟨hjumpdest, hsubbody⟩
      have hjumpable := Prog.jumpable_of_get?_table compiled htable
      rcases hpushAt with ⟨le, hpush⟩
      rcases Evm.call_steps (le := le) hpush hjump hjumpdest
          hjumpable.1 hloc hroom hburn with ⟨step₁, step₂, step₃⟩
      obtain ⟨bodyExec, bodyRoots⟩ :=
        ih compiled rfl (loc + 1) hsubbody hjumpable.2
      refine ⟨Exec.cont step₁ (Exec.cont step₂
        (Exec.cont step₃ bodyExec)), ?_⟩
      simpa [Exec.rawFrameDescendants] using bodyRoots

/-- Lift a rooted compiled main-function walk through the program entry
`JUMPDEST` into an `Exec` derivation. -/
theorem Prog.exec_of_rootedRunCompiledTo
    {P : Exec.Deriv → Prop} {sevm : Sevm} {pre mid : Devm}
    {p : Prog} {ex : Execution}
    {run : Func.RunCompiledTo (p.main :: p.aux) sevm mid p.main ex}
    (burn : Devm.BurnBy gJumpdest pre mid)
    (rooted : rootedRunCompiledTo P run)
    (compiled : some sevm.code.toList = p.compile) :
    ∃ execution : Exec 0 sevm pre ex,
      ∀ root ∈ Exec.rawFrameDescendants execution, P root := by
  have compiled' :
      some sevm.code.toList = Prog.compile ⟨p.main, p.aux⟩ := compiled
  have entry : (table 0 (p.main :: p.aux))[0]? = some (0, p.main) := rfl
  rcases subcode_of_get?_eq_some compiled' entry with ⟨jumpdest, sub⟩
  have boundary : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table compiled' entry).2
  have first : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont jumpdest burn
  obtain ⟨body, bodyRoots⟩ :=
    Func.exec_of_rootedRunCompiledTo_core rooted compiled' rfl 1 sub boundary
  refine ⟨Exec.cont first body, ?_⟩
  simpa [Exec.rawFrameDescendants] using bodyRoots

/-- An instruction known structurally not to be an execution instruction. -/
class NonExecInstruction (instruction : Ninst) : Prop where
  notExec : ∀ x : Xinst, instruction ≠ .exec x

instance (instruction : Rinst) : NonExecInstruction (.reg instruction) :=
  ⟨by intro x h; cases h⟩

instance (word : B256) : NonExecInstruction (pushB256 word) :=
  ⟨by
    intro x h
    simp only [Ninst.pushB256] at h
    cases h⟩

end Blanc
