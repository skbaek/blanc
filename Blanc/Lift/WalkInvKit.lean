import Blanc.Lift.Loop

/-!
# The inversion walk kit: straight-line steps of a cut run read off its tree

An inversion walk takes a successful cut run `h : SFunc.RunCut fs sevm C (St b S M G) f r` (or
its relation-carrying `SFunc.RunCutP P …`) apart one node of `f` at a time, two tactic lines per
instruction:

    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd

The inversion lemma is determined by the node, so the line is written out once per byte of code.
This kit reads it off the tree instead (the inverse twin of `Blanc/Lift/WalkKit.lean`'s `wrun`).

* `winv n` inverts exactly `n` straight-line nodes of the run, failing if fewer are; bare `winv`
  inverts up to the first node that is not straight-line (a branch, a jump, a storage or call
  instruction, a leaf), which is left to the author. Each step runs the hand-written pair:
  `obtain ⟨_, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := L hd` with `L` one of `ri_push`,
  `ri_dup rfl`, `ri_swap rfl`, `ri_pop`, `ri_<op>` for a register instruction whose inversion
  states the next `St` (`ri_add`, `ri_iszero`, `ri_calldataload`, `ri_mload`, `ri_mstore`, …),
  `ri_keccak` and `ri_log1`–`ri_log4`; a `.dest` node runs `obtain ⟨_, h⟩ := ric_dest h`.
* On a `SFunc.RunCutP P …` run it uses `ric_nextP`/`ric_destP`; `using e` names the projection
  from `P` to `Ninst.Run` (`winv 7 using project`, `winv 3 using StepIn.toRun`), applied as
  `L (e hd)`.
* `at h` names the run; without it the kit walks the most recent cut-run hypothesis. The run keeps
  its name, so the author's next line refers to it as before.
* `wskip n [at h]` steps over `n` nodes of any instruction, forgetting the state
  (`obtain ⟨_, _, h⟩ := ric_next h`), as walks do that only need to reach a later node.

The lemma names are resolved at the call site, as the hand walk resolves them. No hypothesis of the
caller is named by the kit's own syntax (the run's name is the caller's), so nothing here needs
`hygiene false`, and the proof term is the hand walk's.
-/

namespace Blanc.Lift.WalkKit

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta

/-- Register instructions whose inversion `ri_<name> hd` states the next `St` outright. -/
private def invOps : List String :=
  ["add", "mul", "sub", "div", "mod", "exp", "lt", "gt", "eq", "iszero", "and", "or", "xor",
    "not", "byte", "shl", "shr", "address", "caller", "callvalue", "calldataload",
    "calldatasize", "returndatasize", "timestamp", "pop", "mload", "mstore", "mstore8", "tload"]

/-- The inversion lemma for a node instruction, as a term awaiting the step (`none`: not a
straight-line instruction this kit takes). -/
def invStep (n : Expr) : MetaM (Option Term) := do
  let ri (s : String) : Ident := mkIdent (Name.mkSimple ("ri_" ++ s))
  let n ← whnfR n
  match n.getAppFnArgs with
  | (``Jaune.Ninst.push, _) => return some (← `($(ri "push")))
  | (``Jaune.Ninst.reg, #[r]) =>
    let r ← whnfR r
    let some rc := r.getAppFn.constName? | return none
    match rc.componentsRev.head!.toString with
    | "dup" => return some (← `($(ri "dup") rfl))
    | "swap" => return some (← `($(ri "swap") rfl))
    | "keccak256" => return some (← `($(ri "keccak")))
    | "log" =>
      let k := (← whnf (← mkAppM ``Fin.val #[r.appArg!])).rawNatLit?
      match k with
      | some k => if 1 ≤ k ∧ k ≤ 4 then return some (← `($(ri s!"log{k}"))) else return none
      | none => return none
    | o => if invOps.contains o then return some (← `($(ri o))) else return none
  | _ => return none

/-- The tree of a cut run's type and whether it carries a relation other than `Ninst.Run` (a
`RunCutP` over `Ninst.Run` itself, as `cases` leaves a `RunCut`, is stepped by `ric_next`). -/
private def cutTree? (ty : Expr) : Option (Expr × Bool) :=
  let (c, args) := ty.getAppFnArgs
  if c == ``Blanc.Lift.SFunc.RunCut && args.size == 6 then some (args[4]!, false)
  else if c == ``Blanc.Lift.SFunc.RunCutP && args.size == 7 then
    some (args[5]!, !args[0]!.cleanupAnnotations.isConstOf ``Jaune.Ninst.Run)
  else none

/-- The walked run: the named hypothesis, or the most recent cut run. -/
private def walkedRun (hyp : Option Ident) : TacticM (Option (LocalDecl × Expr × Bool)) := do
  let check (ld : LocalDecl) : MetaM (Option (LocalDecl × Expr × Bool)) := do
    let ty := (← instantiateMVars ld.type).cleanupAnnotations
    return (cutTree? ty).map fun (f, p) => (ld, f, p)
  match hyp with
  | some i => check (← getLocalDeclFromUserName i.getId)
  | none =>
    for ld in (← getLCtx).decls.toArray.reverse do
      let some ld := ld | continue
      if ld.isImplementationDetail then continue
      if let some r ← check ld then return some r
    return none

/-- One step of the walked run; `skip` forgets the state. `false` if the node is not one the
kit takes. -/
def invStepTac (hyp : Option Ident) (via : Option Term) (skip : Bool) : TacticM Bool :=
  withMainContext do withFreshMacroScope do
  let some (ld, f, rel) ← walkedRun hyp | return false
  let h := mkIdent ld.userName
  let f ← whnfD f
  let ricNext := mkIdent (if rel then `ric_nextP else `ric_next)
  match f.getAppFnArgs with
  | (``Blanc.Lift.SFunc.dest, _) =>
    if skip then return false
    let ricDest := mkIdent (if rel then `ric_destP else `ric_dest)
    evalTactic (← `(tactic| obtain ⟨_, $h:ident⟩ := $ricDest $h))
    return true
  | (``Blanc.Lift.SFunc.next, #[n, _]) =>
    if skip then
      evalTactic (← `(tactic| obtain ⟨_, _, $h:ident⟩ := $ricNext $h))
      return true
    let some lem ← invStep n | return false
    let arg ← match via with
      | some e => `(($e hd))
      | none => `(hd)
    -- `rfl` is rcases' substitution pattern only unhygienic (a scoped name binds a hypothesis).
    let rflPat := mkIdent `rfl
    evalTactic (← `(tactic| (obtain ⟨_, hd, $h:ident⟩ := $ricNext $h
                             obtain ⟨_, $rflPat:ident⟩ := $lem $arg)))
    return true
  | _ => return false

/-- **`n` inversion steps of a cut run** (or, without `n`, every straight-line one); see the
module docstring. -/
syntax (name := winvStx) "winv" (ppSpace num)? (" at " ident)? (" using " term)? : tactic

/-- **`n` forgetful inversion steps** of a cut run, over any instruction. -/
syntax (name := wskipStx) "wskip" ppSpace num (" at " ident)? : tactic

@[tactic winvStx] def evalWinv : Tactic := fun stx => do
  let hyp : Option Ident := if stx[2].isNone then none else some ⟨stx[2][1]⟩
  let via : Option Term := if stx[3].isNone then none else some ⟨stx[3][1]⟩
  match (if stx[1].isNone then none else stx[1][0].isNatLit?) with
  | some n =>
    for i in [0:n] do
      unless ← invStepTac hyp via false do
        throwError "winv {n}: step {i + 1} is not a straight-line node"
  | none =>
    let mut i := 0
    while i < 100000 do
      unless ← invStepTac hyp via false do break
      i := i + 1

@[tactic wskipStx] def evalWskip : Tactic := fun stx => do
  let hyp : Option Ident := if stx[2].isNone then none else some ⟨stx[2][1]⟩
  let some n := stx[1].isNatLit? | throwError "wskip: expected a step count"
  for i in [0:n] do
    unless ← invStepTac hyp none true do
      throwError "wskip {n}: step {i + 1} is not a `.next` node"

end Blanc.Lift.WalkKit
