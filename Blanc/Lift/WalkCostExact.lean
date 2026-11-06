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
private partial def sumAtoms (ls : Array Expr) (e : Expr) (st : Array Expr × Array (Nat × Expr × Expr)) :
    MetaM (Array Expr × Array (Nat × Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) => sumAtoms ls c (← sumAtoms ls a st)
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
        let (as, hs) ← sumAtoms ls y st
        return (as, hs.push (i, y, pf))
    return st

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Tactic _root_.Lean.Meta in
/-- A `Nat` sum over the atoms, each replaced by its local variable. -/
private partial def sumAbstract (atoms xs : Array Expr) (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) =>
    return ← mkAdd (← sumAbstract atoms xs a) (← sumAbstract atoms xs c)
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
private partial def sumNorm (e : Expr) : MetaM (Nat × Expr × Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, c]) =>
    let (na, ra, pa) ← sumNorm a
    let (nc, rc, pc) ← sumNorm c
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
  let st ← sumAtoms lemmas lhs (#[], #[])
  let (atoms, hyps) ← sumAtoms lemmas rhs st
  let decls := atoms.mapIdx fun i _ => ((`x).appendIndexAfter i, fun _ => pure (mkConst ``Nat))
  withLocalDeclsD decls fun xs => do
    let hdecls ← hyps.mapM fun (i, y, _) => do
      return (`h, (← mkEq xs[i]! (← sumAbstract atoms xs y)))
    withLocalDeclsD (hdecls.map fun (n, t) => (n, fun _ => pure t)) fun hs => do
      let lhs' ← sumAbstract atoms xs lhs
      let rhs' ← sumAbstract atoms xs rhs
      let (n1, r1, p1) ← sumNorm lhs'
      let (n2, r2, p2) ← sumNorm rhs'
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

/-- A store just after a read pays only its value's case. -/
theorem sstoreCost_afterSload_self :
    sstoreCost sevm (afterSload sevm b k) k v =
      sstoreValueCost (b.getOrigStorVal sevm sevm.currentTarget k)
        (b.getStorVal sevm.currentTarget k) v := by
  unfold sstoreCost
  rw [ite_eq_left (mem_afterSload sevm b k), Nat.zero_add]
  unfold afterSload
  split <;> rfl

end Charges

section GasLeft

variable (s : Sevm) (a : Devm) (k v : B256) (G : Nat)

theorem afterSload_withGasLeft : afterSload s (a.withGasLeft G) k = (afterSload s a k).withGasLeft G := by
  unfold afterSload
  rw [show (a.withGasLeft G).accessedStorageKeys = a.accessedStorageKeys from rfl]
  by_cases h : (⟨s.currentTarget, k⟩ : Adr × B256) ∈ a.accessedStorageKeys <;>
    simp only [h, ↓reduceIte] <;> rfl

theorem afterSstore_withGasLeft :
    afterSstore s (a.withGasLeft G) k v = (afterSstore s a k v).withGasLeft G := by
  unfold afterSstore
  rw [show (a.withGasLeft G).accessedStorageKeys = a.accessedStorageKeys from rfl]
  by_cases h : (⟨s.currentTarget, k⟩ : Adr × B256) ∈ a.accessedStorageKeys <;>
    simp only [h, ↓reduceIte] <;> rfl

theorem addLog_withGasLeft (l : Log) : (a.withGasLeft G).addLog l = (a.addLog l).withGasLeft G := rfl

theorem getStorVal_withGasLeft (t : Adr) : (a.withGasLeft G).getStorVal t k = a.getStorVal t k := rfl

theorem sloadCost_withGasLeft : sloadCost s (a.withGasLeft G) k = sloadCost s a k := rfl

theorem sstoreCost_withGasLeft : sstoreCost s (a.withGasLeft G) k v = sstoreCost s a k v := rfl

end GasLeft

section Cold

variable {s : Sevm} {b : Devm} {k k' v : B256}

/-- A slot not yet accessed is charged the cold read. -/
theorem sloadCost_cold (h : (⟨s.currentTarget, k⟩ : Adr × B256) ∉ b.accessedStorageKeys) :
    sloadCost s b k = gasColdSload := by
  unfold sloadCost
  rw [ite_eq_right h]

/-- A read of another slot leaves this slot cold. -/
theorem notMem_afterSload (hne : k' ≠ k)
    (h : (⟨s.currentTarget, k⟩ : Adr × B256) ∉ b.accessedStorageKeys) :
    (⟨s.currentTarget, k⟩ : Adr × B256) ∉ (afterSload s b k').accessedStorageKeys := by
  unfold afterSload
  split
  · exact h
  · intro hm
    rcases Std.HashSet.mem_insert.mp hm with e | e
    · have : (⟨s.currentTarget, k'⟩ : Adr × B256) = ⟨s.currentTarget, k⟩ := by simpa using e
      exact hne (Prod.mk.inj this).2
    · exact h e

/-- A store to a warm slot leaves every slot's temperature. -/
theorem accessed_afterSstore_of_warm {k : B256} {v : B256}
    (hw : (⟨s.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys) :
    (afterSstore s b k v).accessedStorageKeys = b.accessedStorageKeys := by
  unfold afterSstore
  rw [ite_eq_left hw]
  rfl

end Cold

/-- A frame's halting state keeps its base's columns: agreement modulo gas, at any residuals. -/
theorem memRet_congr {B B' : Devm} {S : List B256} {M : Mem} {a n : Nat} {w : Bytes} {G H : Nat}
    (h : Devm.EqModGas B B') :
    Devm.EqModGas (((St B S M G).memRead a n).2.withOutput w) (((St B' S M H).memRead a n).2.withOutput w) := by
  apply Devm.EqModGas.of_normalized_eq
  have e := h.withGasLeft_eq 0
  change (((St (B.withGasLeft 0) S M 0).memRead a n).2.withOutput w).withGasLeft 0 =
    (((St (B'.withGasLeft 0) S M 0).memRead a n).2.withOutput w).withGasLeft 0
  rw [e]

/-- `memRet_congr` at a base one gas apart. -/
theorem memRet_canon {B B' : Devm} {S : List B256} {M : Mem} {a n : Nat} {w : Bytes} {F G H : Nat}
    (h : B = B'.withGasLeft F) :
    Devm.EqModGas (((St B S M G).memRead a n).2.withOutput w) (((St B' S M H).memRead a n).2.withOutput w) := by
  subst h
  exact memRet_congr (Devm.EqModGas.withGasLeft B' F).symm

section Move

variable {s : Sevm} {a : Devm} {kr kt w u : B256}

theorem getStor_withGasLeft (d : Devm) (G : Nat) (t : Adr) : Devm.getStor (d.withGasLeft G) t = Devm.getStor d t := rfl

/-- A read keeps every warm slot warm. -/
theorem mem_afterSload_of_mem {k k' : B256} {t : Adr}
    (h : (⟨t, k⟩ : Adr × B256) ∈ a.accessedStorageKeys) :
    (⟨t, k⟩ : Adr × B256) ∈ (afterSload s a k').accessedStorageKeys := by
  unfold afterSload
  split
  · exact h
  · exact Std.HashSet.mem_insert.mpr (Or.inr h)

/-- A read of a warm slot changes nothing. -/
theorem afterSload_of_warm (h : (⟨s.currentTarget, kr⟩ : Adr × B256) ∈ a.accessedStorageKeys) :
    afterSload s a kr = a := by
  unfold afterSload
  rw [ite_eq_left h]

theorem sloadCost_of_warm (h : (⟨s.currentTarget, kr⟩ : Adr × B256) ∈ a.accessedStorageKeys) :
    sloadCost s a kr = gasWarmAccess := by
  unfold sloadCost
  rw [ite_eq_left h]

/-- **A warm debit and a cold credit, at their states.** With `kr` warm and `kt` cold and apart: a read at
`100`, the store's value class, a read at `2100`, and the store's value class, both classes at `a`. -/
theorem move_charges (hw : (⟨s.currentTarget, kr⟩ : Adr × B256) ∈ a.accessedStorageKeys)
    (hc : (⟨s.currentTarget, kt⟩ : Adr × B256) ∉ a.accessedStorageKeys) (hne : kr ≠ kt) :
    sloadCost s a kr + sstoreCost s (afterSload s a kr) kr w +
        sloadCost s (afterSstore s (afterSload s a kr) kr w) kt +
        sstoreCost s (afterSload s (afterSstore s (afterSload s a kr) kr w) kt) kt u =
      2200 + sstoreValueCost (a.getOrigStorVal s s.currentTarget kr) (a.getStorVal s.currentTarget kr) w +
        sstoreValueCost (a.getOrigStorVal s s.currentTarget kt) (a.getStorVal s.currentTarget kt) u := by
  have hk : (afterSstore s a kr w).accessedStorageKeys = a.accessedStorageKeys :=
    accessed_afterSstore_of_warm hw
  have hc' : (⟨s.currentTarget, kt⟩ : Adr × B256) ∉ (afterSstore s a kr w).accessedStorageKeys := by
    rw [hk]; exact hc
  have hco : (afterSstore s a kr w).getOrigStorVal s s.currentTarget kt =
      a.getOrigStorVal s s.currentTarget kt := by
    unfold Devm.getOrigStorVal
    rw [afterSstore_createdAccounts]
  have hcu : (afterSstore s a kr w).getStorVal s.currentTarget kt = a.getStorVal s.currentTarget kt := by
    rw [getStorVal_eq_getStor, getStorVal_eq_getStor, afterSstore_getStor_self]
    exact Stor.get_set_ne _ hne _
  rw [afterSload_of_warm hw, sloadCost_of_warm hw, sstoreCost_afterSload_self, sloadCost_cold hc', hco, hcu]
  have hs : sstoreCost s a kr w = sstoreValueCost (a.getOrigStorVal s s.currentTarget kr)
      (a.getStorVal s.currentTarget kr) w := by
    unfold sstoreCost
    rw [ite_eq_left hw, Nat.zero_add]
  rw [hs]
  simp only [gasWarmAccess, gasColdSload]
  omega

/-- A read keeps a slot's snapshot value. -/
theorem origVal_afterSload (k k' : B256) :
    (afterSload s a k').getOrigStorVal s s.currentTarget k = a.getOrigStorVal s s.currentTarget k := by
  unfold Devm.getOrigStorVal
  rw [afterSload_createdAccounts]

/-- A read keeps a slot's value. -/
theorem curVal_afterSload (k k' : B256) :
    (afterSload s a k').getStorVal s.currentTarget k = a.getStorVal s.currentTarget k := by
  rw [getStorVal_eq_getStor, getStorVal_eq_getStor, afterSload_getStor]

/-- A store keeps a slot's snapshot value. -/
theorem origVal_afterSstore (k k' v : B256) :
    (afterSstore s a k' v).getOrigStorVal s s.currentTarget k = a.getOrigStorVal s s.currentTarget k := by
  unfold Devm.getOrigStorVal
  rw [afterSstore_createdAccounts]

/-- A store keeps another slot's value. -/
theorem curVal_afterSstore_ne {k k' v : B256} (h : k' ≠ k) :
    (afterSstore s a k' v).getStorVal s.currentTarget k = a.getStorVal s.currentTarget k := by
  rw [getStorVal_eq_getStor, getStorVal_eq_getStor, afterSstore_getStor_self]
  exact Stor.get_set_ne _ h _

/-- A store keeps a slot warm. -/
theorem mem_afterSstore_of_mem {k k' v : B256} {t : Adr}
    (h : (⟨t, k⟩ : Adr × B256) ∈ a.accessedStorageKeys) :
    (⟨t, k⟩ : Adr × B256) ∈ (afterSstore s a k' v).accessedStorageKeys := by
  unfold afterSstore
  by_cases hk : (⟨s.currentTarget, k'⟩ : Adr × B256) ∈ a.accessedStorageKeys
  · rw [ite_eq_left hk]; exact h
  · rw [ite_eq_right hk]; exact Std.HashSet.mem_insert.mpr (Or.inr h)

/-- A store to another slot leaves this slot cold. -/
theorem notMem_afterSstore {k k' v : B256} (hne : k' ≠ k)
    (h : (⟨s.currentTarget, k⟩ : Adr × B256) ∉ a.accessedStorageKeys) :
    (⟨s.currentTarget, k⟩ : Adr × B256) ∉ (afterSstore s a k' v).accessedStorageKeys := by
  unfold afterSstore
  by_cases hk : (⟨s.currentTarget, k'⟩ : Adr × B256) ∈ a.accessedStorageKeys
  · rw [ite_eq_left hk]; exact h
  · rw [ite_eq_right hk]
    intro hm
    rcases Std.HashSet.mem_insert.mp hm with e | e
    · have : (⟨s.currentTarget, k'⟩ : Adr × B256) = ⟨s.currentTarget, k⟩ := by simpa using e
      exact hne (Prod.mk.inj this).2
    · exact h e

/-- A store to a warm slot pays its value's class. -/
theorem sstoreCost_warm_eq (hw : (⟨s.currentTarget, kr⟩ : Adr × B256) ∈ a.accessedStorageKeys) :
    sstoreCost s a kr w = sstoreValueCost (a.getOrigStorVal s s.currentTarget kr)
      (a.getStorVal s.currentTarget kr) w := by
  unfold sstoreCost
  rw [ite_eq_left hw, Nat.zero_add]

/-- **A cold debit and a cold credit, at their states**: `4200` and the stores' value classes. -/
theorem move_charges_cold (hr : (⟨s.currentTarget, kr⟩ : Adr × B256) ∉ a.accessedStorageKeys)
    (hc : (⟨s.currentTarget, kt⟩ : Adr × B256) ∉ a.accessedStorageKeys) (hne : kr ≠ kt) :
    sloadCost s a kr + sstoreCost s (afterSload s a kr) kr w +
        sloadCost s (afterSstore s (afterSload s a kr) kr w) kt +
        sstoreCost s (afterSload s (afterSstore s (afterSload s a kr) kr w) kt) kt u =
      4200 + sstoreValueCost (a.getOrigStorVal s s.currentTarget kr) (a.getStorVal s.currentTarget kr) w +
        sstoreValueCost (a.getOrigStorVal s s.currentTarget kt) (a.getStorVal s.currentTarget kt) u := by
  have hc' := notMem_afterSstore (s := s) (a := afterSload s a kr) (v := w) hne (notMem_afterSload hne hc)
  rw [sloadCost_cold hr, sstoreCost_afterSload_self, sloadCost_cold hc', sstoreCost_afterSload_self,
    origVal_afterSstore, origVal_afterSload, curVal_afterSstore_ne hne, curVal_afterSload]
  simp only [gasColdSload]
  omega

end Move

end Blanc.Lift.AccumulatedWalk
