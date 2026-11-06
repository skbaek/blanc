import Blanc.Lift.ForeignKeep

/-!
# Which external instructions a closed region of a certificate decodes

`ExecsSet p fs E`: every tree of `E` decodes external instructions satisfying `p` and refers only into
`E`. `Reach.execs_of_set`: a reach from such a region stands only at external instructions satisfying
`p`. `ExecFreeSet` is the case `p = fun _ => false`. `execs_of_reach`: the chain form.
-/

namespace Blanc.Lift

open Jaune Blanc

/-- The tree's external instructions satisfy `p`, and it refers only into `E`. -/
def SFunc.execsIn (p : Xinst → Bool) (E : List Nat) (f : SFunc) : Bool :=
  f.execsSatisfy p && f.refs.all (· ∈ E)

/-- `E` is closed, and its trees' external instructions satisfy `p`. -/
def ExecsSet (p : Xinst → Bool) (fs : List SFunc) (E : List Nat) : Bool :=
  E.all fun k => match fs[k]? with
    | some g => g.execsIn p E
    | none => false

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {p : Xinst → Bool}

theorem ExecsSet.lookup {E : List Nat} (hE : ExecsSet p fs E = true) {k : Nat}
    {g : SFunc} (hk : k ∈ E) (hg : fs[k]? = some g) : g.execsIn p E = true := by
  have h := (List.all_eq_true.mp hE) k hk
  rw [hg] at h
  exact h

private theorem execsIn_step {E : List Nat} (hE : ExecsSet p fs E = true) {a b : Conf}
    (step : ConfStep P fs sevm a b) (ha : a.f.execsIn p E = true)
    (hK : ∀ s ∈ a.K, s.execsIn p E = true) :
    b.f.execsIn p E = true ∧ ∀ s ∈ b.K, s.execsIn p E = true := by
  cases step with
  | @next d d' n f K _ =>
      refine ⟨?_, hK⟩
      cases n <;> simp_all only [SFunc.execsIn, SFunc.execsSatisfy, SFunc.refs, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq, implies_true, and_self]
  | dest _ => exact ⟨by simpa only [SFunc.execsIn, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, SFunc.execsSatisfy, SFunc.refs] using ha, hK⟩
  | zero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.execsIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.1, ha.2.1⟩
  | succ _ _ _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.execsIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.2, ha.2.2⟩
  | toZero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.execsIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ha.2.2⟩
  | @toSucc d d' f g k K _ _ _ hk _ =>
      refine ⟨ExecsSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.execsIn, SFunc.refs, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at ha
      exact ha.2.1
  | @jump d d' g k K _ hk _ =>
      refine ⟨ExecsSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.execsIn, SFunc.refs, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ha.2
  | @call d d' f g k K _ hk _ =>
      simp only [SFunc.execsIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      refine ⟨ExecsSet.lookup hE ha.2.1 hk, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · simp only [SFunc.execsIn, Bool.and_eq_true]
        exact ⟨ha.1, ha.2.2⟩
      · exact hK s hs
  | ret _ _ => exact ⟨hK _ List.mem_cons_self, fun s hs => hK s (List.mem_cons_of_mem _ hs)⟩
  | pcAt _ _ => exact ⟨by simpa only [SFunc.execsIn, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, SFunc.execsSatisfy, SFunc.refs] using ha, hK⟩

/-- **A reach from a region stands only at external instructions satisfying `p`.** -/
theorem Reach.execs_of_set {E : List Nat} (hE : ExecsSet p fs E = true) {d : Devm}
    {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, f, K⟩ T) (hf : f.execsIn p E = true)
    (hK : ∀ s ∈ K, s.execsIn p E = true) {x : Xinst} {g : SFunc}
    (hT : T.f = .next (.exec x) g) : p x = true := by
  suffices ∀ {a : Conf}, Reach P fs sevm a T → a.f.execsIn p E = true →
      (∀ s ∈ a.K, s.execsIn p E = true) → p x = true from this h hf hK
  intro a h ha hK
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rw [hT] at ha
      simp only [SFunc.execsIn, SFunc.execsSatisfy, Bool.and_eq_true] at ha
      exact ha.1.1
  | head step _ ih =>
      obtain ⟨hb, hbK⟩ := execsIn_step hE step ha hK
      exact ih hb hbK

/-- **Every external instruction a certified frame's chain decodes satisfies `p`**, when every reach
from the certificate's root tree stands only at such. Any outcome. -/
theorem execs_of_reach {code : ByteArray} {c : Cert} {f0 : SFunc} (checked : Cert.check code c = true)
    (hf0 : (Cursor.start c).f = f0) (hK : (Cursor.start c).K = [])
    {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hr : ∀ T, Reach (StepIn ⟨0, sevm, pre, out, run⟩) c.prog sevm
      ⟨St pre pre.stack pre.memory pre.gasLeft, f0, []⟩ T → AtExec T →
      ∀ x g, T.f = .next (.exec x) g → p x = true) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → p x = true := by
  intro N hN x hat
  obtain ⟨κ, reach, okN⟩ := reach_of_parentPrefix_noStateGas checked rfl hcode hsg hN
  obtain ⟨g, hg, -⟩ := okN.tree_of_exec hat
  refine hr (κ.conf N.devm) ?_ ⟨x, g, hg⟩ x g hg
  rw [← St.self rfl rfl]
  have e : (Cursor.start c).conf pre = ⟨pre, f0, []⟩ := by
    simp only [Cursor.conf, hf0, hK, List.map_nil]
  rw [← e]
  exact reach

/-- A conditional jump of a reach: an arm inside the region `hE` closes the goal `p x = true`. -/
macro "rbranchK " h:ident t:ident hx:ident hE:term : tactic => `(tactic| first
  | (have h' := rr_branch $h $t; clear $h; rcases h' with ⟨_, _, $h:ident⟩ | ⟨_, _, $h:ident⟩ <;>
      try (exact Reach.execs_of_set $hE $h (by decide) (fun _ hs => absurd hs List.not_mem_nil) $hx))
  | (have h' := rr_branchTo $h $t; clear $h; rcases h' with ⟨_, _, $h:ident⟩ | ⟨_, _, _, hg, $h:ident⟩ <;>
      first
      | (exact Reach.execs_of_set $hE $h (by decide) (fun _ hs => absurd hs List.not_mem_nil) $hx)
      | (cases hg; exact Reach.execs_of_set $hE $h (by decide) (fun _ hs => absurd hs List.not_mem_nil) $hx)
      | skip))

end Blanc.Lift
