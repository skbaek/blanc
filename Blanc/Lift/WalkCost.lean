import Blanc.Lift.AccumulatedWalk
import Blanc.Lift.MemGlue
import Blanc.StorageAccessGas

/-!
# Closing a forward walk's charge

Forward walks synthesize their charge (`AccumulatedWalk.xs`), a sum of literals, storage charges
and the charges of the callee walks they cross. `xcost` bounds such a sum. Also the mapping-slot
hash of a scratch image written value-word first, which optimized solc emits for a view.
-/

namespace Blanc.Lift.AccumulatedWalk

open Jaune Blanc Blanc.Lift

/-- An `SLOAD`'s charge, as a literal. -/
theorem sloadCost_le_lit (sevm : Sevm) (b : Devm) (k : B256) : sloadCost sevm b k ≤ 2100 :=
  sloadCost_le sevm b k

/-- An `SSTORE`'s charge, as a literal. -/
theorem sstoreCost_le_lit (sevm : Sevm) (d : Devm) (k v : B256) : sstoreCost sevm d k v ≤ 22100 := by
  have h1 := sstoreCost_le_value sevm d k v
  have h2 := sstoreValueCost_le (d.getOrigStorVal sevm sevm.currentTarget k)
    (d.getStorVal sevm.currentTarget k) v
  simp only [gasColdSload, gasStorageSet] at h1 h2
  omega

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- A literal bound of a `Nat` sum and its proof, by recursion on the sum: a summand is a literal, a
closed term that evaluates to one, or the left side of a lemma in `ls`. -/
private def sumBound (ls : Array Expr) : Nat → Expr → MetaM (Nat × Expr)
  | 0, e => throwError "xcost: sum too deep at {e}"
  | fuel + 1, e => do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) =>
    let (na, pa) ← sumBound ls fuel a
    let (nc, pc) ← sumBound ls fuel c
    return (na + nc, mkApp6 (mkConst ``Nat.add_le_add) a (mkNatLit na) c (mkNatLit nc) pa pc)
  | _ =>
    if let some n := e.nat? then return (n, mkApp (mkConst ``Nat.le_refl) e)
    for l in ls do
      let (xs, _, ty) ← forallMetaTelescope (← inferType l)
      let some (_, x, k) := ty.le? | continue
      if ← withReducible (isDefEq x e) then
        let some n := (← instantiateMVars k).nat? | throwError "xcost: bound {k} is not a literal"
        return (n, ← instantiateMVars (mkAppN l xs))
    unless e.hasFVar || e.hasMVar do
      if let some n := (← whnf e).rawNatLit? then
        return (n, mkApp (mkConst ``Nat.le_refl) e)
    throwError "xcost: no bound for {e}"

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- **Bound a synthesized charge**: on a goal `Σ ≤ K` for a literal `K`, bound every storage charge
by its literal ceiling and every other summand by the first listed lemma whose left side matches.
The sum is folded by proof-term recursion, not by `omega`, whose atom comparison unfolds storage
charges and whose recursion depth a long walk exceeds. A summand no lemma bounds is an error naming
it, so a callee's missing bound is not a timeout. -/
elab "xcost " "[" ls:term,* "]" : tactic => withMainContext do
  let tgt := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let some (_, lhs, K) := tgt.le? | throwError "xcost: not a `≤` goal"
  let some k := K.nat? | throwError "xcost: bound {K} is not a literal"
  let lemmas ← ls.getElems.mapM fun l => Term.withSynthesize (elabTerm l none)
  let (n, pf) ← sumBound (#[mkConst ``sloadCost_le_lit, mkConst ``sstoreCost_le_lit] ++ lemmas) 100000 lhs
  unless n ≤ k do throwError "xcost: the charge is at most {n}, above {k}"
  let close := mkApp2 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit n) K
  let close := mkApp close (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true))
  (← getMainGoal).assign (mkApp5 (mkConst ``Nat.le_trans) lhs (mkNatLit n) K pf close)
  replaceMainGoal []

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome} {n : Nat} {fp : B256}

end Steps

end Blanc.Lift.AccumulatedWalk
