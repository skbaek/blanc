import Blanc.Lift.Curve3Pool.Walk.Kit

/-!
# Backward walk steps read off the code

A backward walk of the pool's frame steps `h : XAt sevm post pc d L` one instruction at a time
with the `Kit` macros, each naming the instruction and the next pc (`xs 0x2234 (.push [0x01,
0x40] (by decide)) ri_push`), both of which the code at `pc` determines. `xa n` reads `pc` off
`h`, reads the instruction's bytes from the runtime's byte trie (`codeTries.bytes`, by walking
the trie's constructors at elaboration time; nothing is evaluated), and runs the macro an author
writes by hand for it: `xs` with `ri_push`, `ri_dup (by rfl)`, `ri_swap (by rfl)`, `ri_pop` or
`ri_<op>` for a value-computing register instruction, `xs2` for `SLT`/`SGT`, and `xjd` for a
`JUMPDEST`. It runs exactly `n` steps and fails if one of them is not of these kinds; bare `xa`
runs until such an instruction (a jump, a memory, storage or call instruction, a halt), which is
left to the author. The proof term is the macros' own, so the kernel work is the hand walk's.
-/

namespace Blanc.Lift.Curve3Pool

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta

/-- The byte at `i` of a depth-`d` trie, read off its constructors. -/
def trieByte (t : Expr) (d i : Nat) : MetaM (Option Nat) := do
  let t ← whnfD t
  match d, t.getAppFnArgs with
  | 0, (``Blanc.Lift.LTrie.leaf, #[_, v]) =>
    if i != 0 then return none
    let v ← whnfD v
    match v.getAppFnArgs with
    | (``Option.some, #[_, x]) =>
      let x ← instantiateMVars x
      match x.getAppFnArgs with
      | (``OfNat.ofNat, #[_, n, _]) => return n.rawNatLit?
      | _ => return (← whnf (← mkAppM ``UInt8.toNat #[x])).rawNatLit?
    | _ => return none
  | d + 1, (``Blanc.Lift.LTrie.node, #[_, l, r]) =>
    if i < 2 ^ d then trieByte l d i else trieByte r d (i - 2 ^ d)
  | _, _ => return none

/-- Register instructions stepped by `xs` with `ri_<name>`, by opcode. -/
private def plainOps : List (Nat × String) :=
  [(0x01, "add"), (0x02, "mul"), (0x03, "sub"), (0x04, "div"), (0x10, "lt"), (0x11, "gt"),
    (0x14, "eq"), (0x15, "iszero"), (0x16, "and"), (0x17, "or"), (0x18, "xor"), (0x19, "not"),
    (0x50, "pop"), (0x30, "address"), (0x33, "caller"), (0x34, "callvalue"),
    (0x35, "calldataload"), (0x36, "calldatasize"), (0x3d, "returndatasize"),
    (0x42, "timestamp")]

/-- The hand-written step macro for opcode `b` at `pc` of the trie `t` (`none`: left to the
author). -/
def backStepSyntax (t : Expr) (pc b : Nat) : MetaM (Option (TSyntax `tactic)) := do
  let num (n : Nat) : Term := ⟨Syntax.mkNumLit (toString n)⟩
  let reg (r : Term) : MetaM Term := `(($(mkIdent ``Jaune.Ninst.reg) $r))
  let rinst (o : String) : Term := ⟨mkIdent (`Jaune.Rinst ++ Name.mkSimple o)⟩
  let ri (o : String) : Ident := mkIdent (Name.mkSimple ("ri_" ++ o))
  if 0x60 ≤ b ∧ b ≤ 0x7f then
    let k := b - 0x5f
    let mut bs : Array Term := #[]
    for j in [0:k] do
      let some x ← trieByte t 15 (pc + 1 + j) | return none
      bs := bs.push (num x)
    let n ← `(($(mkIdent ``Jaune.Ninst.push) [$bs,*] (by decide)))
    return some (← `(tactic| xs $(num (pc + 1 + k)) $n ri_push))
  if 0x80 ≤ b ∧ b ≤ 0x8f then
    let n ← reg (← `(($(mkIdent ``Jaune.Rinst.dup) $(num (b - 0x80)))))
    return some (← `(tactic| xs $(num (pc + 1)) $n (ri_dup (by rfl))))
  if 0x90 ≤ b ∧ b ≤ 0x9f then
    let n ← reg (← `(($(mkIdent ``Jaune.Rinst.swap) $(num (b - 0x90)))))
    return some (← `(tactic| xs $(num (pc + 1)) $n (ri_swap (by rfl))))
  if b == 0x5b then return some (← `(tactic| xjd $(num (pc + 1))))
  if b == 0x5a then
    return some (← `(tactic| xs $(num (pc + 1)) $(← reg (rinst "gas")) ri_gas_remaining))
  if b == 0x12 then
    return some (← `(tactic| xs2 $(num (pc + 1)) $(← reg (rinst "slt")) $(ri "slt")))
  if b == 0x13 then
    return some (← `(tactic| xs2 $(num (pc + 1)) $(← reg (rinst "sgt")) $(ri "sgt")))
  match plainOps.find? (·.1 == b) with
  | some (_, o) => return some (← `(tactic| xs $(num (pc + 1)) $(← reg (rinst o)) $(ri o)))
  | none => return none

/-- One backward step of the walk `h`, if the instruction at its pc is one `xa` takes. -/
def backStep (t : Expr) : TacticM Bool := withMainContext do
  let some ld := (← getLCtx).findFromUserName? `h | return false
  let ty ← instantiateMVars ld.type
  unless ty.isAppOf ``Blanc.Lift.XAt do return false
  let args := ty.getAppArgs
  let pcE := args[args.size - 3]!
  let pc ← match ← (evalNat pcE).run with
    | some pc => pure (some pc)
    | none => (evalNat (← reduce pcE)).run
  let some pc := pc | return false
  let some b ← trieByte t 15 pc | return false
  let some tac ← backStepSyntax t pc b | return false
  evalTactic tac
  return true

/-- **`n` backward steps read off the code** (or, without `n`, every one up to the next
instruction `xa` does not take); see the module docstring. -/
syntax (name := xaStx) "xa" (ppSpace num)? : tactic

@[tactic xaStx] def evalXa : Tactic := fun stx => do
  let t ← whnfD (← mkAppM ``Blanc.Lift.CodeTries.bytes #[mkConst ``codeTries])
  match (if stx[1].isNone then none else stx[1][0].isNatLit?) with
  | some n =>
    for i in [0:n] do
      unless ← backStep t do throwError "xa {n}: step {i + 1} is not one `xa` takes"
  | none =>
    let mut i := 0
    while i < 100000 do
      unless ← backStep t do break
      i := i + 1

end Blanc.Lift.Curve3Pool
