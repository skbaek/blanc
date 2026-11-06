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
private partial def sumBound (ls : Array Expr) (e : Expr) : MetaM (Nat × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) =>
    let (na, pa) ← sumBound ls a
    let (nc, pc) ← sumBound ls c
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
  let (n, pf) ← sumBound (#[mkConst ``sloadCost_le_lit, mkConst ``sstoreCost_le_lit] ++ lemmas) lhs
  unless n ≤ k do throwError "xcost: the charge is at most {n}, above {k}"
  let close := mkApp2 (mkConst ``Nat.le_of_ble_eq_true) (mkNatLit n) K
  let close := mkApp close (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true))
  (← getMainGoal).assign (mkApp5 (mkConst ``Nat.le_trans) lhs (mkNatLit n) K pf close)
  replaceMainGoal []

/-- Two scratch words written value first read back in hash order. -/
theorem scratch_read_rev {M0 : Mem} (wf : Mem.Wf M0) (a c : B256) :
    (((M0.write 32 c.toBytes).write 0 a.toBytes).read 0 64).1 = a.toBytes ++ c.toBytes := by
  have w1 : Mem.Wf (M0.write 32 c.toBytes) := wf.write _ _
  rw [Mem.read_split64 _ (s := 0) (t := 32) rfl, Mem.read_write_word_of_wf w1 0 a,
    Mem.read_write_word_disjoint w1 0 a (Or.inl (le_refl _)), Mem.read_write_word_of_wf wf 32 c]

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
  {f : SFunc} {o : Outcome} {n : Nat} {fp : B256}

/-- `KECCAK256` of two scratch words written value first. -/
theorem rx_keccakRev {M0 : Mem} {a c i sz : B256} (wf : Mem.Wf M0)
    (hM0 : M = (M0.write 32 c.toBytes).write 0 a.toBytes) (hM : FpM fp n M) (hi : i.toNat = 0)
    (hsz : sz.toNat = 64) (hroom : S.length < 1024)
    (k : SFunc.RunExact fs sevm (St b (mapSlot a c :: S) M G) f o) :
    SFunc.RunExact fs sevm (St b (i :: sz :: S) M (G + 42)) (.next (.reg .keccak256) f) o := by
  subst hM0
  refine rx_keccak (c := 42) ?_ ?_ ?_ hroom k
  · rw [hi, hsz, hM.extCost (by have := hM.ge; omega)]; decide
  · rw [hi, hsz, scratch_read_rev wf]; rfl
  · rw [hi, hsz]; exact hM.read_self (by have := hM.ge; omega)

end Steps

end Blanc.Lift.AccumulatedWalk
