import Blanc.Lift.WriteSite
import Blanc.Lift.MapSlot
import Blanc.AddressSlotProofs

/-! ## W2  `Blanc/Lift/WriteSiteTerm.lean` (term meaning; generic)

The meaning of the write-site checker's provenance terms (`Blanc.Lift.WriteSite.Term`): a term is
read in an environment of frame constants and the current function's entry words.  The headline is
`Term.den_subst`: instantiating a callee's term at a call site is sound.  Nothing here mentions a
contract. -/

namespace Blanc.Lift.WriteSite

open Jaune

/-- The frame constants a term reads, and the current function's entry words. -/
structure Env : Type where
  caller : B256
  self : B256
  data : Bytes
  args : List B256

/-- A frame's root environment: entry `0` has no entry words. -/
def Env.root (sevm : Sevm) : Env := ⟨sevm.caller.toB256, sevm.currentTarget.toB256, sevm.data, []⟩

def Term.eval (ε : Env) : Term → B256
  | .top => 0
  | .caller => ε.caller
  | .self => ε.self
  | .cd t => Bytes.toB256 (ε.data.sliceD (t.eval ε).toNat 32 0)
  | .const c => c
  | .arg i => ε.args.getD i 0
  | .op2 o a b => o.eval (a.eval ε) (b.eval ε)
  | .kecc a b => mapSlot (a.eval ε) (b.eval ε)
  | .kecc1 t => ((t.eval ε).toBytes).keccak

/-- The word `w` is what the term says (a term with `top` in it says nothing). -/
def Term.Den (ε : Env) (t : Term) (w : B256) : Prop := t.known = true → w = t.eval ε

theorem Op2.eval_comm {o : Op2} (h : o.comm = true) (x y : B256) : o.eval x y = o.eval y x := by
  cases o
  · exact B256.add_comm
  · exact absurd h Bool.false_ne_true
  · exact B256.mul_comm x y
  · exact absurd h Bool.false_ne_true
  · exact B256.and_comm x y
  · exact B256.or_comm x y
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true
  · exact absurd h Bool.false_ne_true

theorem mkOp2'_eval (ε : Env) (o : Op2) (a b : Term) :
    (mkOp2' o a b).eval ε = o.eval (a.eval ε) (b.eval ε) := by
  unfold mkOp2'
  split
  · rename_i t m m'
    split
    · rename_i hm
      subst hm
      exact (B256.and_idem_right (t.eval ε) (Term.eval ε (.const m))).symm
    · rfl
  · rfl

theorem mkOp2_eval (ε : Env) (o : Op2) {a b : Term} (ha : a.known = true) (hb : b.known = true) :
    (mkOp2 o a b).eval ε = o.eval (a.eval ε) (b.eval ε) := by
  unfold mkOp2
  rw [ite_eq_left (by simp only [ha, hb, Bool.and_self])]
  split
  · rfl
  · split
    · rename_i x b' _ hc
      rw [mkOp2'_eval]
      exact Op2.eval_comm hc _ _
    · rfl
  · exact mkOp2'_eval ε o _ _

theorem mkOp2_known {o : Op2} {a b : Term} (h : (mkOp2 o a b).known = true) :
    a.known = true ∧ b.known = true := by
  unfold mkOp2 at h
  split at h
  · rename_i hab
    exact Bool.and_eq_true_iff.mp hab
  · exact absurd h Bool.false_ne_true

theorem mkKecc_eq {a b : Term} (h : (mkKecc a b).known = true) :
    a.known = true ∧ b.known = true ∧ mkKecc a b = .kecc a b := by
  unfold mkKecc at h ⊢
  split at h
  · rename_i hab
    exact ⟨(Bool.and_eq_true_iff.mp hab).1, (Bool.and_eq_true_iff.mp hab).2, ite_eq_left hab⟩
  · exact absurd h Bool.false_ne_true

theorem mkCd_eq {t : Term} (h : (mkCd t).known = true) : t.known = true ∧ mkCd t = .cd t := by
  unfold mkCd at h ⊢
  split at h
  · rename_i ht
    exact ⟨ht, ite_eq_left ht⟩
  · exact absurd h Bool.false_ne_true

theorem mkKecc1_eq {t : Term} (h : (mkKecc1 t).known = true) :
    t.known = true ∧ mkKecc1 t = .kecc1 t := by
  unfold mkKecc1 at h ⊢
  split at h
  · rename_i ht
    exact ⟨ht, ite_eq_left ht⟩
  · exact absurd h Bool.false_ne_true

/-- A known instantiated term reads, in the caller's environment, what the callee's term reads in
the callee's. -/
theorem Term.eval_subst {ε ε' : Env} {pa : List Term}
    (hglob : ε'.caller = ε.caller ∧ ε'.self = ε.self ∧ ε'.data = ε.data)
    (hpa : ∀ (i : Nat) (u : Term), pa[i]? = some u → u.known = true → ε'.args[i]? = some (u.eval ε)) :
    ∀ (t : Term), (t.subst pa).known = true → (t.subst pa).eval ε = t.eval ε'
  | .top, h => absurd h Bool.false_ne_true
  | .caller, _ => hglob.1.symm
  | .self, _ => hglob.2.1.symm
  | .const _, _ => rfl
  | .arg i, h => by
    change (pa.getD i .top).known = true at h
    show (pa.getD i .top).eval ε = ε'.args.getD i 0
    rw [List.getD_eq_getElem?_getD] at h
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    cases hu : pa[i]? with
    | none =>
      rw [hu] at h
      exact absurd h Bool.false_ne_true
    | some u =>
      rw [hu] at h
      rw [hpa i u hu h]
      rfl
  | .cd t, h => by
    obtain ⟨ht, he⟩ := mkCd_eq h
    show (mkCd (t.subst pa)).eval ε = _
    rw [he]
    show Bytes.toB256 (ε.data.sliceD ((t.subst pa).eval ε).toNat 32 0) =
      Bytes.toB256 (ε'.data.sliceD (t.eval ε').toNat 32 0)
    rw [Term.eval_subst hglob hpa t ht, hglob.2.2]
  | .op2 o a b, h => by
    obtain ⟨ha, hb⟩ := mkOp2_known h
    show (mkOp2 o (a.subst pa) (b.subst pa)).eval ε = o.eval (a.eval ε') (b.eval ε')
    rw [mkOp2_eval ε o ha hb, Term.eval_subst hglob hpa a ha, Term.eval_subst hglob hpa b hb]
  | .kecc a b, h => by
    obtain ⟨ha, hb, he⟩ := mkKecc_eq h
    show (mkKecc (a.subst pa) (b.subst pa)).eval ε = _
    rw [he]
    show mapSlot ((a.subst pa).eval ε) ((b.subst pa).eval ε) = mapSlot (a.eval ε') (b.eval ε')
    rw [Term.eval_subst hglob hpa a ha, Term.eval_subst hglob hpa b hb]
  | .kecc1 t, h => by
    obtain ⟨ht, he⟩ := mkKecc1_eq h
    show (mkKecc1 (t.subst pa)).eval ε = _
    rw [he]
    show (((t.subst pa).eval ε).toBytes).keccak = ((t.eval ε').toBytes).keccak
    rw [Term.eval_subst hglob hpa t ht]

/-- **Instantiation is sound**: a callee term read in the callee's environment is the caller's
instantiated term read in the caller's, when the caller's terms describe the callee's entry words. -/
theorem Term.den_subst {ε ε' : Env} {pa : List Term} {t : Term} {w : B256}
    (hglob : ε'.caller = ε.caller ∧ ε'.self = ε.self ∧ ε'.data = ε.data)
    (hpa : ∀ (i : Nat) (u : Term), pa[i]? = some u → u.known = true → ε'.args[i]? = some (u.eval ε))
    (h : (t.subst pa).Den ε w) (hk : (t.subst pa).known = true) : t.Den ε' w := by
  intro _
  rw [h hk]
  exact Term.eval_subst hglob hpa t hk

end Blanc.Lift.WriteSite
