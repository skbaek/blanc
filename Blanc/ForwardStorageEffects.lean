import Blanc.DeploymentCompiled
import Blanc.ForwardNoRawSstore

/-!
# Exact selected-path storage effects

Construction-direction certificates for the complete retained SSTORE
chronology of one committing compiled path.  Branches and internal calls follow
the witness selected by `Func.RunCompiledTo`; external steps must be childless,
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

/-- Exact retained storage-effect annotation for a selected committing source
walk.  Its list is in execution order. -/
inductive Func.RunCompiledTo.StorageEffectPath :
    ∀ {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
      {out : Execution}, Func.RunCompiledTo fs sevm pre body out →
        List (Adr × B256 × B256) → Prop
  | zero {fs sevm pre branchPre left right out effects}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre branchPre}
      {tail : Func.RunCompiledTo fs sevm branchPre left out}
      (tailEffects : Func.RunCompiledTo.StorageEffectPath tail effects) :
      Func.RunCompiledTo.StorageEffectPath
        (.zero (g := right) room pop tail) effects
  | succ {fs sevm pre branchPre word left right out effects}
      {nonzero : word ≠ 0}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [word]
        (gVerylow + gHigh + gJumpdest) pre branchPre}
      {tail : Func.RunCompiledTo fs sevm branchPre right out}
      (tailEffects : Func.RunCompiledTo.StorageEffectPath tail effects) :
      Func.RunCompiledTo.StorageEffectPath
        (.succ (f := left) nonzero room pop tail) effects
  | last {fs sevm pre terminal out}
      {terminalRun : Linst.Run sevm pre terminal out} :
      Func.RunCompiledTo.StorageEffectPath
        (Func.RunCompiledTo.last (fs := fs) terminalRun) []
  | next {fs sevm pre nextPre instruction body out effects}
      {instructionRun : Ninst.RunCompiled sevm pre instruction nextPre}
      {tail : Func.RunCompiledTo fs sevm nextPre body out}
      (instructionChildless :
        Ninst.ChildlessRunCompiled sevm pre instruction nextPre)
      (tailEffects : Func.RunCompiledTo.StorageEffectPath tail effects) :
      Func.RunCompiledTo.StorageEffectPath (.next instructionRun tail)
        ((Ninst.storageEffectTriple? sevm pre instruction).toList ++ effects)
  | call {fs sevm pre callPre index body out effects}
      {lookup : fs[index]? = some body}
      {room : pre.stack.length < 1024}
      {burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre callPre}
      {tail : Func.RunCompiledTo fs sevm callPre body out}
      (tailEffects : Func.RunCompiledTo.StorageEffectPath tail effects) :
      Func.RunCompiledTo.StorageEffectPath (.call lookup room burn tail) effects

/-- Ordinary non-external instructions are childless automatically. -/
theorem Func.RunCompiledTo.StorageEffectPath.next_of_not_exec
    {fs : List Func} {sevm : Sevm} {pre nextPre : Devm}
    {instruction : Ninst} {body : Func} {out : Execution}
    {instructionRun : Ninst.RunCompiled sevm pre instruction nextPre}
    {tail : Func.RunCompiledTo fs sevm nextPre body out}
    {effects : List (Adr × B256 × B256)}
    (notExec : ∀ operation : Xinst, instruction ≠ .exec operation)
    (tailEffects : Func.RunCompiledTo.StorageEffectPath tail effects) :
    Func.RunCompiledTo.StorageEffectPath (.next instructionRun tail)
      ((Ninst.storageEffectTriple? sevm pre instruction).toList ++ effects) :=
  .next (instructionRun := instructionRun)
    (instructionRun.childless_of_not_exec notExec) tailEffects

/-- Raw-SSTORE freedom is the empty exact storage-effect annotation for the
same selected path. -/
theorem Func.RunCompiledTo.StorageEffectPath.of_noRawSstorePath
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {out : Execution} {run : Func.RunCompiledTo fs sevm pre body out}
    (safe : Func.RunCompiledTo.NoRawSstorePath run) :
    Func.RunCompiledTo.StorageEffectPath run [] := by
  induction safe with
  | @zero pre post left right out room pop tail tailSafe ih =>
      exact .zero (room := room) (pop := pop) ih
  | @succ pre post word left right out nonzero room pop tail tailSafe ih =>
      exact .succ (nonzero := nonzero) (room := room) (pop := pop) ih
  | @last pre terminal out terminalRun =>
      exact .last (terminalRun := terminalRun)
  | @next certPre certPost instruction certBody certOut
      instructionRun tail instructionNe instructionChildless tailSafe ih =>
      have none :
          Ninst.storageEffectTriple? sevm certPre instruction = none := by
        cases instruction with
        | push bytes bound => rfl
        | exec operation => rfl
        | reg operation =>
            cases operation <;>
              simp [Ninst.storageEffectTriple?] at instructionNe ⊢
      simpa only [none, Option.toList_none, List.nil_append] using
        (Func.RunCompiledTo.StorageEffectPath.next
          (instructionRun := instructionRun)
          instructionChildless ih)
  | @call pre post index body out lookup room burn tail tailSafe ih =>
      exact .call (lookup := lookup) (room := room) (burn := burn) ih

/-- Package a selected compiled run with its exact retained storage-effect
annotation so construction lemmas can thread both proofs together. -/
structure Func.StorageEffectRun
    (fs : List Func) (sevm : Sevm) (pre : Devm) (body : Func)
    (out : Execution) (effects : List (Adr × B256 × B256)) : Prop where
  run : Func.RunCompiledTo fs sevm pre body out
  path : Func.RunCompiledTo.StorageEffectPath run effects

/-- Package an existing selected raw-SSTORE-free run as the exact empty
retained-effect carrier. -/
theorem Func.StorageEffectRun.of_noRawSstorePath
    {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {out : Execution} {run : Func.RunCompiledTo fs sevm pre body out}
    (safe : Func.RunCompiledTo.NoRawSstorePath run) :
    Func.StorageEffectRun fs sevm pre body out [] :=
  ⟨run, Func.RunCompiledTo.StorageEffectPath.of_noRawSstorePath safe⟩

theorem Func.StorageEffectRun.last
    {fs : List Func} {sevm : Sevm} {pre : Devm} {terminal : Linst}
    {out : Execution} (terminalRun : Linst.Run sevm pre terminal out) :
    Func.StorageEffectRun fs sevm pre (.last terminal) out [] :=
  ⟨.last terminalRun, .last (terminalRun := terminalRun)⟩

theorem Func.StorageEffectRun.next
    {fs : List Func} {sevm : Sevm} {pre nextPre : Devm}
    {instruction : Ninst} {body : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)}
    (instructionRun :
      Ninst.ChildlessRunCompiled sevm pre instruction nextPre)
    (tail : Func.StorageEffectRun fs sevm nextPre body out effects) :
    Func.StorageEffectRun fs sevm pre (.next instruction body) out
      ((Ninst.storageEffectTriple? sevm pre instruction).toList ++ effects) :=
  ⟨.next instructionRun.toRunCompiled tail.run,
    .next (instructionRun := instructionRun.toRunCompiled)
      instructionRun tail.path⟩

theorem Func.StorageEffectRun.next_of_not_exec
    {fs : List Func} {sevm : Sevm} {pre nextPre : Devm}
    {instruction : Ninst} {body : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)}
    (instructionRun : Ninst.RunCompiled sevm pre instruction nextPre)
    (notExec : ∀ operation : Xinst, instruction ≠ .exec operation)
    (tail : Func.StorageEffectRun fs sevm nextPre body out effects) :
    Func.StorageEffectRun fs sevm pre (.next instruction body) out
      ((Ninst.storageEffectTriple? sevm pre instruction).toList ++ effects) :=
  ⟨.next instructionRun tail.run,
    .next_of_not_exec (instructionRun := instructionRun)
      notExec tail.path⟩

/-- An ordinary non-SSTORE instruction preserves the tail's exact effect
list definitionally after its absent effect annotation is discharged. -/
theorem Func.StorageEffectRun.next_effectNeutral
    {fs : List Func} {sevm : Sevm} {pre nextPre : Devm}
    {instruction : Ninst} {body : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)}
    (instructionRun : Ninst.RunCompiled sevm pre instruction nextPre)
    (notSstore : instruction ≠ .reg .sstore)
    (notExec : ∀ operation : Xinst, instruction ≠ .exec operation)
    (tail : Func.StorageEffectRun fs sevm nextPre body out effects) :
    Func.StorageEffectRun fs sevm pre (.next instruction body) out effects := by
  have none : Ninst.storageEffectTriple? sevm pre instruction = none := by
    cases instruction with
    | push bytes bound => rfl
    | exec operation => rfl
    | reg operation =>
        cases operation <;>
          simp [Ninst.storageEffectTriple?] at notSstore ⊢
  simpa only [none, Option.toList_none, List.nil_append] using
    Func.StorageEffectRun.next_of_not_exec instructionRun notExec tail

theorem Func.StorageEffectRun.zero
    {fs : List Func} {sevm : Sevm} {pre branchPre : Devm}
    {left right : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)}
    (room : pre.stack.length < 1024)
    (pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre branchPre)
    (tail : Func.StorageEffectRun fs sevm branchPre left out effects) :
    Func.StorageEffectRun fs sevm pre (.branch left right) out effects :=
  ⟨.zero room pop tail.run,
    .zero (room := room) (pop := pop) tail.path⟩

theorem Func.StorageEffectRun.succ
    {fs : List Func} {sevm : Sevm} {pre branchPre : Devm} {word : B256}
    {left right : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)}
    (nonzero : word ≠ 0) (room : pre.stack.length < 1024)
    (pop : Devm.PopBurnBy [word]
      (gVerylow + gHigh + gJumpdest) pre branchPre)
    (tail : Func.StorageEffectRun fs sevm branchPre right out effects) :
    Func.StorageEffectRun fs sevm pre (.branch left right) out effects :=
  ⟨.succ nonzero room pop tail.run,
    .succ (nonzero := nonzero) (room := room) (pop := pop) tail.path⟩

theorem Func.StorageEffectRun.call
    {fs : List Func} {sevm : Sevm} {pre callPre : Devm} {index : Nat}
    {body : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)}
    (lookup : fs[index]? = some body) (room : pre.stack.length < 1024)
    (burn : Devm.BurnBy (gVerylow + gMid + gJumpdest) pre callPre)
    (tail : Func.StorageEffectRun fs sevm callPre body out effects) :
    Func.StorageEffectRun fs sevm pre (.call index) out effects :=
  ⟨.call lookup room burn tail.run,
    .call (lookup := lookup) (room := room) (burn := burn) tail.path⟩

/-- Tactic-facing zero-branch wrapper for `StorageEffectRun`. -/
lemma Func.storageEffectRun_branch_zero
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {effects : List (Adr × B256 × B256)}
    {s : List B256} {G : Nat}
    (h_stk : devm.stack = 0 :: s) (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh))
    (h_arm : Func.StorageEffectRun fs sevm
      (devm.setMach ⟨s, devm.memory, G⟩) f ex effects) :
    Func.StorageEffectRun fs sevm devm (.branch f g) ex effects :=
  .zero h_room (Devm.popBurnBy_setMach h_stk h_gas) h_arm

/-- Tactic-facing nonzero-branch wrapper for `StorageEffectRun`. -/
lemma Func.storageEffectRun_branch_succ
    {fs : List Func} {sevm : Sevm} {devm : Devm}
    {f g : Func} {ex : Execution} {effects : List (Adr × B256 × B256)}
    {w : B256} {s : List B256} {G : Nat}
    (h_ne : w ≠ 0) (h_stk : devm.stack = w :: s)
    (h_room : devm.stack.length < 1024)
    (h_gas : devm.gasLeft = G + (gVerylow + gHigh + gJumpdest))
    (h_arm : Func.StorageEffectRun fs sevm
      (devm.setMach ⟨s, devm.memory, G⟩) g ex effects) :
    Func.StorageEffectRun fs sevm devm (.branch f g) ex effects :=
  .succ h_ne h_room (Devm.popBurnBy_setMach h_stk h_gas) h_arm

/-! ## `storage_effect_run` — exact-effect neutral walk -/

section StorageEffectTactic

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic

namespace Forward

/-- Retarget a six-argument exact-effect relation after a structural rule has
named its successor state. -/
def retargetStorageEffect (g : MVarId) (state : Expr) : MetaM MVarId := do
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (``Blanc.Func.StorageEffectRun, #[fs, sevm, _, f, post, effects]) =>
      g.change (mkAppN (mkConst ``Blanc.Func.StorageEffectRun)
        #[fs, sevm, state, f, post, effects])
  | _ => return g

/-- Exact-effect analogue of `funcWalk` for neutral prefixes.  It shares the
instruction evaluator, hints, gas accounting, and resource profiling with
`func_run`; an external instruction or SSTORE is deliberately handed back to
the caller as the residual exact-effect goal. -/
partial def storageEffectWalk (g : MVarId) : ForwardM Unit := g.withContext do
  if let some b := (← get).budget then
    if (← get).step ≥ b then
      modify fun c => { c with side := c.side.push g }
      return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  match t.getAppFnArgs with
  | (``Blanc.Func.StorageEffectRun, #[fs, sevm, d, f, post, effects]) => do
    let f' ← whnf f
    let g ← g.change (mkAppN (mkConst ``Blanc.Func.StorageEffectRun)
      #[fs, sevm, d, f', post, effects])
    let (base, stk, mem, gas) ← parseState d
    let (gb, goff) ← parseGas gas
    match f'.getAppFnArgs with
    | (``Blanc.Func.next, #[instruction, rest]) => do
      let instruction' ← whnfR instruction
      let isExec := instruction'.getAppFn.constName? == some ``Jaune.Ninst.exec
      let isSstore := match instruction'.getAppFnArgs with
        | (``Jaune.Ninst.reg, #[operation]) =>
            operation.getAppFn.constName? == some ``Jaune.Rinst.sstore
        | _ => false
      if isExec || isSstore then
        modify fun c => { c with side := c.side.push g, step := c.step + 1 }
        return
      let gs ← applyLemma g ``Func.StorageEffectRun.next_effectNeutral
        [(0, fs), (1, sevm), (2, d), (4, instruction), (5, rest),
          (6, post), (7, effects)] [8, 9, 10, 11]
      match gs with
      | [instructionGoal, notStore, notExec, tailGoal] =>
          ninstStep instructionGoal
          let neStore ← `(tactic| (rintro impossible; cases impossible))
          let neStore' ← `(tactic| decide)
          let neExec ← `(tactic|
            (intro operation impossible; cases impossible))
          discharge notStore [neStore, neStore']
          discharge notExec [neExec]
          storageEffectWalk tailGoal
      | _ =>
          throwError
            "storage_effect_run: `.next` left an unexpected obligation set"
    | (``Blanc.Func.branch, #[left, right]) => do
      modify fun c => { c with step := c.step + 1 }
      let ([word], stackTail) ← popStack 1 stk
        | throwError "storage_effect_run: BRANCH"
      let takesZero ←
        if word.nat? == some 0 then pure true
        else if (word.nat?).isSome then pure false
        else pure false
      if takesZero then
        let gas' ← mkGas gb goff 13
        let successor ← mkState base stackTail mem gas'
        let gs ← applyLemma g ``Func.storageEffectRun_branch_zero
          [(0, fs), (1, sevm), (2, d), (3, left), (4, right),
            (5, post), (6, effects), (7, stackTail), (8, gas')]
          [9, 10, 11, 12]
        match gs with
        | [stackGoal, roomGoal, gasGoal, armGoal] =>
            discharge stackGoal (← rflTacs)
            dischargeProfiled .room roomGoal (← roomTacs)
            dischargeProfiled .gas gasGoal (← gasTacs)
            storageEffectWalk
              (← retargetStorageEffect armGoal successor)
        | _ =>
            throwError
              "storage_effect_run: `.zero` left an unexpected obligation set"
      else
        let gas' ← mkGas gb goff 14
        let successor ← mkState base stackTail mem gas'
        let gs ← applyLemma g ``Func.storageEffectRun_branch_succ
          [(0, fs), (1, sevm), (2, d), (3, left), (4, right),
            (5, post), (6, effects), (7, word), (8, stackTail),
            (9, gas')] [10, 11, 12, 13, 14]
        let dec ← `(tactic| decide)
        let deck ← `(tactic| decide +kernel)
        match gs with
        | [nonzero, stackGoal, roomGoal, gasGoal, armGoal] =>
            unless (← tryTacOn nonzero dec) || (← tryTacOn nonzero deck) do
              throwError m!"storage_effect_run: cannot decide branch word{indentExpr word}"
            discharge stackGoal (← rflTacs)
            dischargeProfiled .room roomGoal (← roomTacs)
            dischargeProfiled .gas gasGoal (← gasTacs)
            storageEffectWalk
              (← retargetStorageEffect armGoal successor)
        | _ =>
            throwError
              "storage_effect_run: `.succ` left an unexpected obligation set"
    | (``Blanc.Func.call, #[_]) =>
        modify fun c => { c with side := c.side.push g, step := c.step + 1 }
    | (``Blanc.Func.last, #[_]) =>
        modify fun c => { c with side := c.side.push g }
    | _ =>
        throwError m!"storage_effect_run: cannot see the shape of{indentExpr f'}"
  | _ =>
      throwError
        "storage_effect_run: goal is not `Func.StorageEffectRun`"

def storageEffectRunMain (hints : List Term) (budget : Option Nat := none) :
    TacticM Unit := do
  let g ← getMainGoal
  let (_, context) ← (storageEffectWalk g).run
    { rel := toSpec, hints := hints, side := #[], step := 0, budget := budget }
  if context.step == 0 then
    throwError "storage_effect_run: applied no rule; nothing was proved"
  unless context.hints.isEmpty do
    throwError "storage_effect_run: unused hint(s)"
  replaceMainGoal context.side.toList

end Forward

/-- Walk a childless, non-SSTORE exact-effect prefix with `func_run`'s state,
gas, hint, and side-condition engine. -/
syntax (name := storageEffectRun)
  "storage_effect_run" (ppSpace "(" num ")")?
  (ppSpace "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| storage_effect_run $[($n)]? $[[$hs,*]]?) =>
    Forward.storageEffectRunMain
      (match hs with
        | some hs => hs.getElems.toList
        | none => [])
      (n.map (·.getNat))

end StorageEffectTactic

/-! ## Splicing a successful neutral prefix -/

/-- Every selected successful terminal of this source-shaped prefix is its
designated `STOP`; the prefix contains no internal-call leaf.  Combined with
the existing local SSTORE/exec-free predicates, this is the reusable static
side of an exact-effect continuation splice. -/
def Func.SuccessStopOnly : Func → Prop
  | .branch left right => left.SuccessStopOnly ∧ right.SuccessStopOnly
  | .last .stop => True
  | .last _ => False
  | .next _ body => body.SuccessStopOnly
  | .call _ => False

/-- A selected compiled path that reaches the designated successful `STOP`,
retaining the childlessness and non-SSTORE facts needed to graft an arbitrary
exact-effect continuation at that boundary. -/
inductive Func.RunCompiledTo.SuccessfulStopPrefix :
    ∀ {fs : List Func} {sevm : Sevm} {pre : Devm} {source : Func}
      {stopPost : Devm},
      Func.RunCompiledTo fs sevm pre source (.ok stopPost) → Prop
  | zero {fs sevm pre branchPre left right stopPost}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [0] (gVerylow + gHigh) pre branchPre}
      {tail : Func.RunCompiledTo fs sevm branchPre left (.ok stopPost)}
      (tailPrefix : Func.RunCompiledTo.SuccessfulStopPrefix tail) :
      Func.RunCompiledTo.SuccessfulStopPrefix
        (.zero (g := right) room pop tail)
  | succ {fs sevm pre branchPre word left right stopPost}
      {nonzero : word ≠ 0}
      {room : pre.stack.length < 1024}
      {pop : Devm.PopBurnBy [word]
        (gVerylow + gHigh + gJumpdest) pre branchPre}
      {tail : Func.RunCompiledTo fs sevm branchPre right (.ok stopPost)}
      (tailPrefix : Func.RunCompiledTo.SuccessfulStopPrefix tail) :
      Func.RunCompiledTo.SuccessfulStopPrefix
        (.succ (f := left) nonzero room pop tail)
  | last {fs sevm pre}
      {terminalRun : Linst.Run sevm pre .stop (.ok pre)} :
      Func.RunCompiledTo.SuccessfulStopPrefix
        (Func.RunCompiledTo.last (fs := fs) terminalRun)
  | next {fs sevm pre nextPre instruction body stopPost}
      {instructionRun : Ninst.RunCompiled sevm pre instruction nextPre}
      {tail : Func.RunCompiledTo fs sevm nextPre body (.ok stopPost)}
      (instructionNe : instruction ≠ .reg .sstore)
      (instructionChildless :
        Ninst.ChildlessRunCompiled sevm pre instruction nextPre)
      (tailPrefix : Func.RunCompiledTo.SuccessfulStopPrefix tail) :
      Func.RunCompiledTo.SuccessfulStopPrefix
        (.next instructionRun tail)

/-- Static executable/local checks plus `SuccessStopOnly` certify any selected
successful walk through a neutral prefix. -/
theorem Func.RunCompiledTo.SuccessfulStopPrefix.of_execFree
    {fs : List Func} {sevm : Sevm} {pre stopPost : Devm}
    {source : Func}
    (run : Func.RunCompiledTo fs sevm pre source (.ok stopPost))
    (execFree : funcExecFree source)
    (storeFree : source.LocalSstoreFree)
    (stopOnly : source.SuccessStopOnly) :
    Func.RunCompiledTo.SuccessfulStopPrefix run := by
  induction source generalizing pre stopPost with
  | branch left right leftIH rightIH =>
      cases run with
      | zero room pop tail =>
          exact .zero (room := room) (pop := pop)
            (leftIH tail execFree.1 storeFree.1 stopOnly.1)
      | succ nonzero room pop tail =>
          exact .succ (nonzero := nonzero) (room := room) (pop := pop)
            (rightIH tail execFree.2 storeFree.2 stopOnly.2)
  | last terminal =>
      cases run with
      | last terminalRun =>
          cases terminal <;> simp [Func.SuccessStopOnly] at stopOnly
          have hpost : stopPost = pre := by
            simpa [Linst.Run, Linst.run] using terminalRun.symm
          subst stopPost
          exact Func.RunCompiledTo.SuccessfulStopPrefix.last
            (terminalRun := terminalRun)
  | next instruction body ih =>
      cases run with
      | next instructionRun tail =>
          cases instruction with
          | reg operation =>
              exact .next (instructionRun := instructionRun) storeFree.1
                (instructionRun.childless_of_not_exec (by
                  intro external impossible
                  cases impossible))
                (ih tail (by simpa [funcExecFree] using execFree)
                  storeFree.2 stopOnly)
          | push bytes size =>
              exact .next (instructionRun := instructionRun) storeFree.1
                (instructionRun.childless_of_not_exec (by
                  intro external impossible
                  cases impossible))
                (ih tail (by simpa [funcExecFree] using execFree)
                  storeFree.2 stopOnly)
          | exec operation =>
              simp [funcExecFree] at execFree
  | call index =>
      simp [Func.SuccessStopOnly] at stopOnly

/-- Replace the designated successful `STOP` reached by a neutral prefix with
an arbitrary exact-effect continuation.  The continuation's effect list is
preserved exactly. -/
theorem Func.RunCompiledTo.SuccessfulStopPrefix.splice
    {fs : List Func} {sevm : Sevm} {pre stopPost : Devm}
    {source replacement : Func} {out : Execution}
    {effects : List (Adr × B256 × B256)}
    {run : Func.RunCompiledTo fs sevm pre source (.ok stopPost)}
    (certificate : Func.RunCompiledTo.SuccessfulStopPrefix run)
    (tail : Func.StorageEffectRun fs sevm stopPost replacement out effects) :
    Func.StorageEffectRun fs sevm pre
      (source.replaceStopWith replacement) out effects := by
  induction certificate with
  | zero tailPrefix ih =>
      simpa only [Func.replaceStopWith] using
        (Func.StorageEffectRun.zero (by assumption) (by assumption) (ih tail))
  | succ tailPrefix ih =>
      simpa only [Func.replaceStopWith] using
        (Func.StorageEffectRun.succ (by assumption) (by assumption)
          (by assumption) (ih tail))
  | last =>
      simpa only [Func.replaceStopWith] using tail
  | @next prefixPre nextPre instruction body prefixPost
      instructionRun prefixTail instructionNe instructionChildless
      tailPrefix ih =>
      have none :
          Ninst.storageEffectTriple? sevm prefixPre instruction = none := by
        cases instruction with
        | push bytes bound => rfl
        | exec operation => rfl
        | reg operation =>
            cases operation <;>
              simp [Ninst.storageEffectTriple?] at instructionNe ⊢
      simpa only [Func.replaceStopWith, none, Option.toList_none,
          List.nil_append] using
        (Func.StorageEffectRun.next instructionChildless (ih tail))

private theorem Ninst.exists_exec_storageEffects
    {pc : Nat} {sevm : Sevm} {pre nextPre : Devm} {out : Execution}
    {instruction : Ninst} {effects : List (Adr × B256 × B256)}
    (instructionAt : Ninst.At sevm.code pc instruction)
    (instructionRun :
      Ninst.ChildlessRunCompiled sevm pre instruction nextPre)
    {tail : Exec (pc + instruction.size) sevm nextPre out}
    (committed : Execution.commits out = true)
    (tailEffects : Exec.retainedStorageEffectTriples tail =
      effects) :
    ∃ run : Exec pc sevm pre out,
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

private theorem Func.RunCompiledTo.StorageEffectPath.exists_exec_core :
    ∀ {main : Func} {aux : List Func} {sevm : Sevm} {fs : List Func}
      {pre : Devm} {body : Func} {out : Execution}
      {run : Func.RunCompiledTo fs sevm pre body out}
      {effects : List (Adr × B256 × B256)},
      Func.RunCompiledTo.StorageEffectPath run effects →
      Execution.commits out = true →
      some sevm.code.toList = Prog.compile ⟨main, aux⟩ →
      fs = main :: aux →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (main :: aux)) pc body) →
        noPushBefore sevm.code pc 32 = true →
        ∃ execution : Exec pc sevm pre out,
          Exec.retainedStorageEffectTriples execution = effects := by
  intro main aux sevm fs pre body out run effects certified
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
  | @last certPre terminal certOut terminalRun =>
      intro committed compiled tableEq pc sub noPush
      have terminalAt := Linst.at_of_slice sub
      have step : Evm.step ⟨pc, sevm, certPre⟩ = .halt certOut := by
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

/-- Whole-program committing execution bridge with exact retained storage
effect chronology. -/
theorem Prog.exists_exec_retainedStorageEffectTriples
    {sevm : Sevm} {pre mid : Devm} {out : Execution} {program : Prog}
    {mainRun : Func.RunCompiledTo (program.main :: program.aux)
      sevm mid program.main out}
    {effects : List (Adr × B256 × B256)}
    (entryBurn : Devm.BurnBy gJumpdest pre mid)
    (mainEffects : Func.RunCompiledTo.StorageEffectPath mainRun effects)
    (committed : Execution.commits out = true)
    (compiled : some sevm.code.toList = program.compile) :
    ∃ execution : Exec 0 sevm pre out,
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
  rcases Func.RunCompiledTo.StorageEffectPath.exists_exec_core mainEffects
      committed compiled' rfl 1 mainSub mainNoPush with
    ⟨execution, effectEq⟩
  refine ⟨.cont entryStep execution, ?_⟩
  rw [Exec.retainedStorageEffectTriples_cont execution committed,
    Jinst.successfulSstore_effectTriples execution jumpdestAt,
    effectEq]
  rfl

/-! ## Creation-code prefixes -/

/-- Appended-code variant of the exact retained-effect execution bridge.
Compiler-table instructions occupy `pfxCode`; EVM instructions such as
`CODECOPY` continue to observe the full `pfxCode ++ sfxData` image. -/
private theorem Func.RunCompiledTo.StorageEffectPath.exists_exec_appended_core :
    ∀ {main : Func} {aux : List Func} {sevm : Sevm} {fs : List Func}
      {pre : Devm} {body : Func} {out : Execution}
      {run : Func.RunCompiledTo fs sevm pre body out}
      {effects : List (Adr × B256 × B256)} {pfxCode sfxData : Bytes},
      Func.RunCompiledTo.StorageEffectPath run effects →
      Execution.commits out = true →
      some pfxCode = Prog.compile ⟨main, aux⟩ →
      sevm.code.toList = pfxCode ++ sfxData →
      fs = main :: aux →
      ∀ pc,
        subcode sevm.code.toList pc
          (Func.compile (table 0 (main :: aux)) pc body) →
        noPushBefore sevm.code pc 32 = true →
        ∃ execution : Exec pc sevm pre out,
          Exec.retainedStorageEffectTriples execution = effects := by
  intro main aux sevm fs pre body out run effects pfxCode sfxData certified
  induction certified with
  | @zero certPre branchPre left right certPost certEffects
      room pop tail tailEffects ih =>
      intro committed compiled codeEq tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_zero_steps pushAt jumpAt locAt room pop with
        ⟨pushStep, jumpStep⟩
      rcases ih committed compiled codeEq tableEq (pc + 4)
          leftSub leftNoPush with ⟨leftRun, leftEffects⟩
      refine ⟨.cont pushStep (.cont jumpStep leftRun), ?_⟩
      rw [Exec.retainedStorageEffectTriples_cont _ committed,
        Exec.retainedStorageEffectTriples_cont leftRun committed,
        Ninst.successfulSstore_effectTriples _ pushAt,
        Jinst.successfulSstore_effectTriples leftRun jumpAt,
        leftEffects]
      rfl
  | @succ certPre branchPre word left right certPost certEffects
      nonzero room pop tail tailEffects ih =>
      intro committed compiled codeEq tableEq pc sub noPush
      rcases subcode_compile_branch_jumpable sub noPush with
        ⟨loc, locBound, locAt, pushAt, jumpAt, leftSub,
          leftNoPush, jumpdestAt, jumpable, rightSub, rightNoPush⟩
      rcases Evm.branch_succ_steps pushAt jumpAt jumpdestAt jumpable
        locAt nonzero room pop with ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih committed compiled codeEq tableEq (loc + 1)
          rightSub rightNoPush with ⟨rightRun, rightEffects⟩
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
  | @last certPre terminal certOut terminalRun =>
      intro committed compiled codeEq tableEq pc sub noPush
      have terminalAt := Linst.at_of_slice sub
      have step : Evm.step ⟨pc, sevm, certPre⟩ = .halt certOut := by
        rw [Evm.step_last terminalAt]
        exact congrArg Step.halt terminalRun
      refine ⟨.halt step, ?_⟩
      exact Exec.retainedStorageEffectTriples_halt committed
  | @next certPre nextPre instruction certBody certPost certEffects
      instructionRun tail instructionChildless tailEffects ih =>
      intro committed compiled codeEq tableEq pc sub noPush
      rcases Func.noPushBefore_next sub noPush with
        ⟨tailNoPush, tailSub⟩
      rcases of_subcode sub with ⟨compiledTail, compileEq, slice⟩
      rcases of_bind_eq_some compileEq with
        ⟨tailCode, tailCompileEq, codeEq'⟩
      simp [pure] at codeEq'
      rw [← codeEq'] at slice
      have instructionAt : Ninst.At sevm.code pc instruction :=
        Ninst.at_of_slice (List.slice_prefix slice)
      rcases ih committed compiled codeEq tableEq _ tailSub tailNoPush with
        ⟨tailRun, tailEffectEq⟩
      rcases Ninst.exists_exec_storageEffects instructionAt
          instructionChildless (tail := tailRun) committed tailEffectEq with
        ⟨execution, headEffect⟩
      exact ⟨execution, headEffect⟩
  | @call certPre callPre index certBody certPost certEffects
      lookup room burn tail tailEffects ih =>
      intro committed compiled codeEq tableEq pc sub noPush
      subst tableEq
      rcases subcode_compile_call sub with
        ⟨loc, compiledBody, tableLookup, locBound, pushAt, jumpAt⟩
      have selected := (Prog.get?_table (m := 0)).symm.trans
        (congrArg (Prod.snd <$> ·) tableLookup)
      rw [lookup] at selected
      simp only [Option.map_eq_map, Option.map_some,
        Option.some.injEq] at selected
      subst selected
      rcases subcode_of_get?_eq_some_appended compiled codeEq tableLookup with
        ⟨jumpdestAt, bodySub⟩
      have bodyJumpable :=
        Prog.jumpable_of_get?_table_appended compiled codeEq tableLookup
      rcases pushAt with ⟨length, pushAt⟩
      rcases Evm.call_steps (le := length) pushAt jumpAt jumpdestAt
        bodyJumpable.1 locBound room burn with
        ⟨pushStep, jumpStep, jumpdestStep⟩
      rcases ih committed compiled codeEq rfl (loc + 1)
          bodySub bodyJumpable.2 with ⟨bodyRun, bodyEffects⟩
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

/-- Whole-program committing execution bridge with exact retained storage
chronology when the compiled program is the prefix of a larger code image. -/
theorem Prog.exists_exec_retainedStorageEffectTriples_appended
    {sevm : Sevm} {pre mid : Devm} {out : Execution} {program : Prog}
    {mainRun : Func.RunCompiledTo (program.main :: program.aux)
      sevm mid program.main out}
    {effects : List (Adr × B256 × B256)} {pfxCode sfxData : Bytes}
    (entryBurn : Devm.BurnBy gJumpdest pre mid)
    (mainEffects : Func.RunCompiledTo.StorageEffectPath mainRun effects)
    (committed : Execution.commits out = true)
    (compiled : some pfxCode = program.compile)
    (codeEq : sevm.code.toList = pfxCode ++ sfxData) :
    ∃ execution : Exec 0 sevm pre out,
      Exec.retainedStorageEffectTriples execution = effects := by
  have compiled' : some pfxCode =
      Prog.compile ⟨program.main, program.aux⟩ := compiled
  have entryLookup :
      (table 0 (program.main :: program.aux))[0]? =
        some (0, program.main) := rfl
  rcases subcode_of_get?_eq_some_appended compiled' codeEq entryLookup with
    ⟨jumpdestAt, mainSub⟩
  have mainNoPush : noPushBefore sevm.code 1 32 = true :=
    (Prog.jumpable_of_get?_table_appended compiled' codeEq entryLookup).2
  have entryStep : Evm.step ⟨0, sevm, pre⟩ = .cont 1 mid :=
    Evm.jumpdest_cont jumpdestAt entryBurn
  rcases Func.RunCompiledTo.StorageEffectPath.exists_exec_appended_core
      mainEffects committed compiled' codeEq rfl 1 mainSub mainNoPush with
    ⟨execution, effectEq⟩
  refine ⟨.cont entryStep execution, ?_⟩
  rw [Exec.retainedStorageEffectTriples_cont execution committed,
    Jinst.successfulSstore_effectTriples execution jumpdestAt,
    effectEq]
  rfl

end Blanc
