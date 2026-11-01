import Blanc.Lift.Exact

/-!
# The walk-step kit: forward straight-line steps read off the tree

A forward walk proves `SFunc.RunExact fs sevm d f o` (or its some-outcome closure
`SFunc.RunEx fs sevm d f Q`, `Blanc/Lift/RunEx.lean`) by one step lemma per instruction of the tree
`f`. For a straight-line instruction the lemma and its arguments are determined by the
instruction, so writing them out (`xr (rx_push rfl (by hr) ·)`) is one line per byte of code.

* `wstep` reads the head of the goal's tree (unfolding a tree constant) and applies the matching
  forward step, the same term an author writes by hand: `rx_push rfl R`, `rx_dup rfl R`,
  `rx_swap1` (`SWAP1`) or `rx_swap rfl`, `rx_pop`, `rx_dest`, `rx_add R`, `rx_sub R`,
  `rx_<op> rfl R` for the other value-computing register instructions and `rx_<op> R` for the
  environment pushes, where `R` is the stack-room side condition `(by wroom)`.
* `wrun n` runs exactly `n` such steps, failing if fewer apply; `wrun` runs until the head is not a
  straight-line instruction (a branch, a jump, a memory, storage or call instruction, a leaf), which
  is left to the author.
* `wrun! n` (or `wrun!`) states each pushed word as its numeral (`rx_push (w := 64) rfl R`) and
  steps `SWAP2`–`SWAP4` by the explicit-shape `rx_swap2`–`rx_swap4`, the convention of walks
  whose statements name stack words as numbers (the Uniswap V2 pair's).
* `using tac` (on either) replaces the room tactic, e.g. `wrun 12 using hrs` where the stack holds
  saved frame words whose length lemma `hr` does not know.

The lemma names are resolved at the call site (`rx_<op>`), so a family that adds its own step
(Curve 3pool's `rx_sgt`) is picked up where it is in scope. No hypothesis of the caller is named,
so nothing here needs `hygiene false`.
-/

namespace Blanc.Lift.WalkKit

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta

/-- The default stack-room side condition over a literal stack (Curve 3pool's `hr`). -/
macro "wroom" : tactic => `(tactic| first
  | omega
  | (simp only [List.length_cons, List.length_nil, List.length_set]; omega)
  | decide)

/-- The `Fin 16` index of a `DUP`/`SWAP`, as a number, if it is a literal. -/
private def finLit? (i : Expr) : MetaM (Option Nat) := do
  let v ← whnf (← mkAppM ``Fin.val #[i])
  return v.rawNatLit?

/-- Register instructions whose step takes the value equation by `rfl` and the room. -/
private def valOps : List String :=
  ["mul", "div", "mod", "lt", "gt", "slt", "sgt", "eq", "iszero", "and", "or", "xor", "not", "byte"]

/-- Environment pushes, whose step takes only the room. -/
private def envOps : List String :=
  ["calldataload", "callvalue", "calldatasize", "caller", "gas", "timestamp", "number", "codesize",
    "returndatasize"]

/-- The number a literal byte list denotes, big-endian (`none` unless every byte is a literal). -/
private def pushWord? (bs : Expr) : MetaM (Option Nat) := do
  let mut acc := 0
  let mut l ← whnfR bs
  for _ in [0:33] do
    match l.getAppFnArgs with
    | (``List.nil, _) => return some acc
    | (``List.cons, #[_, x, t]) =>
      let some v := (← instantiateMVars x).getAppArgs[1]?.bind (·.rawNatLit?) | return none
      acc := acc * 256 + v
      l ← whnfR t
    | _ => return none
  return none

/-- The forward step for a tree head, as a term awaiting the continuation (`none`: not a
straight-line instruction). `room` is the stack-room argument. -/
def fwdStep (f : Expr) (room : Term) (lit : Bool := false) : MetaM (Option Term) := do
  let rx (s : String) : Ident := mkIdent (Name.mkSimple ("rx_" ++ s))
  match f.getAppFnArgs with
  | (``Blanc.Lift.SFunc.dest, _) => return some (← `($(rx "dest")))
  | (``Blanc.Lift.SFunc.next, #[n, _]) =>
    let n ← whnfR n
    match n.getAppFnArgs with
    | (``Jaune.Ninst.push, #[bs, _]) =>
      if lit then
        let some w ← pushWord? bs | return none
        return some (← `($(rx "push") (w := $(Syntax.mkNumLit (toString w))) rfl $room))
      return some (← `($(rx "push") rfl $room))
    | (``Jaune.Ninst.reg, #[r]) =>
      let r ← whnfR r
      let some rc := r.getAppFn.constName? | return none
      match rc.componentsRev.head!.toString with
      | "dup" => return some (← `($(rx "dup") rfl $room))
      | "swap" =>
        let i ← finLit? r.appArg!
        if i == some 0 then return some (← `($(rx "swap1")))
        else if lit && i.any (· ≤ 3) then
          return some (← `($(rx s!"swap{i.getD 0 + 1}")))
        else return some (← `($(rx "swap") rfl))
      | "pop" => return some (← `($(rx "pop")))
      | o =>
        if o == "add" || o == "sub" then return some (← `($(rx o) $room))
        else if valOps.contains o then return some (← `($(rx o) rfl $room))
        else if envOps.contains o then return some (← `($(rx o) $room))
        else return none
    | _ => return none
  | _ => return none

/-- One forward step on the main goal, if its tree head is straight-line; `false` otherwise. -/
def fwdStepTac (room : Term) (lit : Bool := false) : TacticM Bool := withMainContext do
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let (c, args) := tgt.getAppFnArgs
  unless (c == ``Blanc.Lift.SFunc.RunExact || c == `Blanc.Lift.SFunc.RunEx) && args.size == 5 do
    return false
  let some lem ← fwdStep (← whnfD args[3]!) room lit | return false
  if c == ``Blanc.Lift.SFunc.RunExact then
    evalTactic (← `(tactic| refine $lem ?_))
  else
    let ofI := mkIdent `Blanc.Lift.SFunc.RunEx.of
    evalTactic (← `(tactic| refine $ofI (fun _ k => $lem k) ?_))
  return true

/-- The room argument of a `using` clause, or `(by wroom)`. -/
def roomOf (tac : Option (TSyntax `tactic)) : TacticM Term :=
  match tac with
  | some t => `((by $t:tactic))
  | none => `((by wroom))

/-- **One forward straight-line step**, read off the goal's tree (see the module docstring). -/
syntax (name := wstepStx) "wstep" (" using " tactic)? : tactic

/-- **`n` forward straight-line steps** (or, without `n`, every one up to the next instruction
that is not straight-line). -/
syntax (name := wrunStx) "wrun" (ppSpace num)? (" using " tactic)? : tactic

/-- As `wrun`, stating pushed words as numerals and `SWAP2`–`SWAP4` by their explicit-shape
lemmas. -/
syntax (name := wrunLitStx) "wrun!" (ppSpace num)? (" using " tactic)? : tactic

@[tactic wstepStx] def evalWstep : Tactic := fun stx => do
  let tac := if stx[1].isNone then none else some ⟨stx[1][1]⟩
  unless ← fwdStepTac (← roomOf tac) do throwError "wstep: the tree head is not straight-line"

/-- `wrun`/`wrun!` over the syntax `stx`. -/
def runSteps (lit : Bool) (stx : Syntax) : TacticM Unit := do
  let tac := if stx[2].isNone then none else some ⟨stx[2][1]⟩
  let room ← roomOf tac
  match (if stx[1].isNone then none else stx[1][0].isNatLit?) with
  | some n =>
    for i in [0:n] do
      unless ← fwdStepTac room lit do
        throwError "wrun {n}: step {i + 1} is not straight-line"
  | none =>
    let mut i := 0
    while i < 100000 do
      unless ← fwdStepTac room lit do break
      i := i + 1

@[tactic wrunStx] def evalWrun : Tactic := runSteps false

@[tactic wrunLitStx] def evalWrunLit : Tactic := runSteps true

end Blanc.Lift.WalkKit
