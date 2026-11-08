import Blanc.Lift.WalkCost
import Blanc.Lift.GasErasureRun
import Blanc.Lift.CallProfileTransport

/-!
# Closing a forward walk's charge exactly

`xcost` bounds a walk's synthesized charge. `xsum` proves it equal to a stated sum: the summands that
are storage charges or callee charges are abstracted to atoms (a callee charge with a listed equation
gets that equation as a hypothesis), and `omega` closes the linear goal over the atoms, so it never
compares or unfolds a storage charge. The rest are the storage-charge facts a coin's exact cost is
evaluated by: what a read leaves warm, and what a store costs after that read.
-/

namespace Blanc.Lift.AccumulatedWalk

open Jaune Blanc Blanc.Lift

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- A summand's head: the constant applied, or a walk's name under `Subtype.val`. Unifying two summands of
different heads can unfold a walk's whole proof term, so they are told apart here first. -/
private def sumHead (e : Expr) : Name :=
  match e.getAppFnArgs with
  | (``Subtype.val, #[_, _, a]) => a.getAppFn.constName
  | (n, _) => n

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- The same summand, up to reducible unfolding. -/
private def sumSame (x e : Expr) : MetaM Bool := do
  if sumHead x != sumHead e then return false
  withReducible (isDefEq x e)

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- The atoms of a `Nat` sum (not sums, not closed literals), each with the equation of the first listed
lemma whose left side matches it, whose right side's atoms join. -/
private def sumAtoms (ls : Array Expr) : Nat → Expr → Array Expr × Array (Nat × Expr × Expr) →
    MetaM (Array Expr × Array (Nat × Expr × Expr))
  | 0, e, _ => throwError "xsum: sum too deep at {e}"
  | fuel + 1, e, st => do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) => sumAtoms ls fuel c (← sumAtoms ls fuel a st)
  | _ =>
    if e.nat?.isSome then return st
    unless e.hasFVar || e.hasMVar do
      if (← whnf e).rawNatLit?.isSome then return st
    let (atoms, hyps) := st
    for x in atoms do
      if ← sumSame x e then return st
    let i := atoms.size
    let st : Array Expr × Array (Nat × Expr × Expr) := (atoms.push e, hyps)
    for l in ls do
      let (xs, _, ty) ← forallMetaTelescope (← inferType l)
      let some (_, x, y) := ty.eq? | continue
      if ← sumSame x e then
        let y ← instantiateMVars y
        let pf ← instantiateMVars (mkAppN l xs)
        let (as, hs) ← sumAtoms ls fuel y st
        return (as, hs.push (i, y, pf))
    return st

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- A `Nat` sum over the atoms, each replaced by its local variable. -/
private def sumAbstract (atoms xs : Array Expr) : Nat → Expr → MetaM Expr
  | 0, e => throwError "xsum: sum too deep at {e}"
  | fuel + 1, e => do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) =>
    return ← mkAdd (← sumAbstract atoms xs fuel a) (← sumAbstract atoms xs fuel c)
  | _ =>
    if let some n := e.nat? then return mkNatLit n
    unless e.hasFVar || e.hasMVar do
      if let some n := (← whnf e).rawNatLit? then return mkNatLit n
    for x in atoms, v in xs do
      if ← sumSame x e then return v
    throwError "xsum: {e} is not an atom"

theorem sum_step {a na ra c nc rc : Nat} (h1 : a = na + ra) (h2 : c = nc + rc) :
    a + c = (na + nc) + (ra + rc) := by
  omega

theorem sum_stepL {a na c nc rc : Nat} (h1 : a = na + 0) (h2 : c = nc + rc) :
    a + c = (na + nc) + rc := by
  omega

theorem sum_stepR {a na ra c nc : Nat} (h1 : a = na + ra) (h2 : c = nc + 0) :
    a + c = (na + nc) + ra := by
  omega

theorem sum_atom (x : Nat) : x = 0 + x := by omega

theorem sum_close {l n1 r1 R n2 r2 : Nat} (p1 : l = n1 + r1) (g : n1 + r1 = n2 + r2)
    (p2 : R = n2 + r2) : l = R :=
  p1.trans (g.trans p2.symm)

open _root_.Lean _root_.Lean.Meta in
/-- A sum over local variables as `literal + variables`, with its proof: a walk's sum nests hundreds of
literals, too much for `omega` as it stands. -/
private def sumNorm : Nat → Expr → MetaM (Nat × Expr × Expr)
  | 0, e => throwError "xsum: sum too deep at {e}"
  | fuel + 1, e => do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) =>
    let (na, ra, pa) ← sumNorm fuel a
    let (nc, rc, pc) ← sumNorm fuel c
    if ra.nat? == some 0 then
      return (na + nc, rc, mkApp7 (mkConst ``sum_stepL) a (mkNatLit na) c (mkNatLit nc) rc pa pc)
    if rc.nat? == some 0 then
      return (na + nc, ra, mkApp7 (mkConst ``sum_stepR) a (mkNatLit na) ra c (mkNatLit nc) pa pc)
    return (na + nc, mkNatAdd ra rc,
      mkApp8 (mkConst ``sum_step) a (mkNatLit na) ra c (mkNatLit nc) rc pa pc)
  | _ =>
    if let some n := e.nat? then
      return (n, mkNatLit 0, mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) e)
    return (0, e, mkApp (mkConst ``sum_atom) e)

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- **Prove an equation between two charge sums**: abstract the summands that are not literals, give each
one a listed lemma matches its equation as a hypothesis, and call `omega` on the linear residue. -/
elab "xsum " "[" ls:term,* "]" : tactic => withMainContext do
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let some (_, lhs, rhs) := tgt.eq? | throwError "xsum: not an equation"
  let lemmas ← ls.getElems.mapM fun l => Term.withSynthesize (elabTerm l none)
  let st ← sumAtoms lemmas 100000 lhs (#[], #[])
  let (atoms, hyps) ← sumAtoms lemmas 100000 rhs st
  let decls := atoms.mapIdx fun i _ => ((`x).appendIndexAfter i, fun _ => pure (mkConst ``Nat))
  withLocalDeclsD decls fun xs => do
    let hdecls ← hyps.mapM fun (i, y, _) => do
      return (`h, (← mkEq xs[i]! (← sumAbstract atoms xs 100000 y)))
    withLocalDeclsD (hdecls.map fun (n, t) => (n, fun _ => pure t)) fun hs => do
      let lhs' ← sumAbstract atoms xs 100000 lhs
      let rhs' ← sumAbstract atoms xs 100000 rhs
      let (n1, r1, p1) ← sumNorm 100000 lhs'
      let (n2, r2, p2) ← sumNorm 100000 rhs'
      let goal ← mkEq (mkNatAdd (mkNatLit n1) r1) (mkNatAdd (mkNatLit n2) r2)
      let mv ← mkFreshExprMVar goal
      let [] ← Tactic.run mv.mvarId! (evalTactic (← `(tactic| omega)))
        | throwError "xsum: omega left goals"
      let close := mkApp8 (mkConst ``sum_close) lhs' (mkNatLit n1) r1 rhs' (mkNatLit n2) r2 p1
        (← instantiateMVars mv)
      let pf ← mkLambdaFVars (xs ++ hs) (mkApp close p2)
      (← getMainGoal).assign (mkAppN pf (atoms ++ hyps.map fun (_, _, p) => p))
      replaceMainGoal []

section Charges

variable (sevm : Sevm) (b : Devm) (k k' v : B256)

/-- A read warms its slot. -/
theorem mem_afterSload :
    (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ (afterSload sevm b k).accessedStorageKeys := by
  unfold afterSload
  split
  · assumption
  · exact Std.HashSet.mem_insert_self

/-- A second read of a slot is warm. -/
theorem sloadCost_afterSload_self : sloadCost sevm (afterSload sevm b k) k = gasWarmAccess := by
  unfold sloadCost
  rw [ite_eq_left (mem_afterSload sevm b k)]

end Charges

section GasLeft

variable (s : Sevm) (a : Devm) (k v : B256) (G : Nat)

theorem addLog_withGasLeft (l : Log) : (a.withGasLeft G).addLog l = (a.addLog l).withGasLeft G := rfl

theorem getStorVal_withGasLeft (t : Adr) : (a.withGasLeft G).getStorVal t k = a.getStorVal t k := rfl

theorem sloadCost_withGasLeft : sloadCost s (a.withGasLeft G) k = sloadCost s a k := rfl

theorem sstoreCost_withGasLeft : sstoreCost s (a.withGasLeft G) k v = sstoreCost s a k v := rfl

end GasLeft

section Cold

variable {s : Sevm} {b : Devm} {k k' v : B256}

end Cold

section Move

variable {s : Sevm} {a : Devm} {kr kt w u : B256}

theorem getStor_withGasLeft (d : Devm) (G : Nat) (t : Adr) : Devm.getStor (d.withGasLeft G) t = Devm.getStor d t := rfl

end Move

end Blanc.Lift.AccumulatedWalk
