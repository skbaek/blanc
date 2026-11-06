import Blanc.Lift.ReachWalk
import Blanc.Lift.SelectorRoute
import Blanc.Lift.ForeignKeep
import Blanc.Lift.BalanceLocality
import Blanc.Lift.CurveCoins.Keep

/-!
# A frame on a certified code whose chain executes only allowed external instructions

`ExecFreeSet` with a predicate: `AllowedSet p fs E` says `E` is closed under references and its trees execute only `p`.
`Reach.exec_allowed`: a reach inside it stands only at allowed instructions. `chain_static_descendants`: a frame
whose chain executes only `STATICCALL` has static descendants. So a code that has one calling path, like FiatToken's
`rescueERC20`, is a `CertFrame` on every other selector (`selector_chain_of_routes`).
-/

namespace Blanc.Lift

open Jaune Blanc

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-- `f` executes only `p` and refers into `E`. -/
def SFunc.allowedIn (p : Xinst → Bool) (E : List Nat) (f : SFunc) : Bool :=
  f.execsSatisfy p && f.refs.all (· ∈ E)

/-- `E` is closed, and its trees execute only `p`. -/
def AllowedSet (p : Xinst → Bool) (fs : List SFunc) (E : List Nat) : Bool :=
  E.all fun k => match fs[k]? with
    | some g => g.allowedIn p E
    | none => false

variable {p : Xinst → Bool}

theorem AllowedSet.lookup {E : List Nat} (hE : AllowedSet p fs E = true) {k : Nat}
    {g : SFunc} (hk : k ∈ E) (hg : fs[k]? = some g) : g.allowedIn p E = true := by
  have h := (List.all_eq_true.mp hE) k hk
  rw [hg] at h
  exact h

private theorem allowed_step {E : List Nat} (hE : AllowedSet p fs E = true) {a b : Conf}
    (step : ConfStep P fs sevm a b) (ha : a.f.allowedIn p E = true)
    (hK : ∀ s ∈ a.K, s.allowedIn p E = true) :
    b.f.allowedIn p E = true ∧ ∀ s ∈ b.K, s.allowedIn p E = true := by
  cases step with
  | @next d d' n f K _ =>
      refine ⟨?_, hK⟩
      cases n <;> simp_all only [SFunc.allowedIn, SFunc.execsSatisfy, SFunc.refs, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Bool.true_and, decide_true, implies_true, Bool.false_and, Bool.false_eq_true]
  | dest _ => exact ⟨by simpa only [SFunc.allowedIn, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, SFunc.execsSatisfy, SFunc.refs] using ha, hK⟩
  | zero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.allowedIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.1, ha.2.1⟩
  | succ _ _ _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.allowedIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.2, ha.2.2⟩
  | toZero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.allowedIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ha.2.2⟩
  | @toSucc d d' f g k K _ _ _ hk _ =>
      refine ⟨AllowedSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.allowedIn, SFunc.refs, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at ha
      exact ha.2.1
  | @jump d d' g k K _ hk _ =>
      refine ⟨AllowedSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.allowedIn, SFunc.refs, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ha.2
  | @call d d' f g k K _ hk _ =>
      simp only [SFunc.allowedIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      refine ⟨AllowedSet.lookup hE ha.2.1 hk, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · simp only [SFunc.allowedIn, Bool.and_eq_true]
        exact ⟨ha.1, ha.2.2⟩
      · exact hK s hs
  | ret _ _ => exact ⟨hK _ List.mem_cons_self, fun s hs => hK s (List.mem_cons_of_mem _ hs)⟩
  | pcAt _ _ => exact ⟨by simpa only [SFunc.allowedIn, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, SFunc.execsSatisfy, SFunc.refs] using ha, hK⟩

/-- **A reach inside an allowed set stands only at allowed instructions.** -/
theorem Reach.exec_allowed {E : List Nat} (hE : AllowedSet p fs E = true) {d : Devm} {f : SFunc} {K : List SFunc}
    {T : Conf} (h : Reach P fs sevm ⟨d, f, K⟩ T) {x : Xinst} {g : SFunc} (hT : T.f = .next (.exec x) g)
    (hf : f.allowedIn p E = true) (hK : ∀ s ∈ K, s.allowedIn p E = true) : p x = true := by
  suffices ∀ {a : Conf}, Reach P fs sevm a T → a.f.allowedIn p E = true →
      (∀ s ∈ a.K, s.allowedIn p E = true) → p x = true from this h hf hK
  intro a h ha hK
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rw [hT] at ha
      simp only [SFunc.allowedIn, SFunc.execsSatisfy, Bool.and_eq_true] at ha
      exact ha.1.1
  | head step _ ih =>
      obtain ⟨hb, hbK⟩ := allowed_step hE step ha hK
      exact ih hb hbK

/-- **A frame whose chain executes only `STATICCALL` has static descendants.** -/
theorem chain_static_descendants {root : Exec.Deriv}
    (only : ∀ N, Exec.Deriv.ParentPrefix root N → ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → x = .staticcall) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec pc sevm pre out),
      Exec.Deriv.ParentPrefix root ⟨pc, sevm, pre, out, run⟩ →
      ∀ D ∈ Exec.rawFrameDescendants run, D.sevm.isStatic = true := by
  intro pc sevm pre out run
  induction run with
  | halt step => simp only [Exec.rawFrameDescendants, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true]
  | cont step next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.cont step next))
  | doneErr step enter resume => simp only [Exec.rawFrameDescendants, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | doneOk step enter resume next ih =>
    intro chain
    simpa only [Exec.rawFrameDescendants] using ih (chain.snoc (.doneOk step enter resume next))
  | runErr step enter child resume ih =>
    intro chain D member
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall := only _ chain x instruction
    subst x
    have stc := (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    exact Exec.rawFrameRoots_isStatic child stc D (by
      simpa only [Exec.rawFrameRoots, Exec.rawFrameDescendants] using member)
  | runOk step enter child resume next childIH nextIH =>
    intro chain D member
    obtain ⟨x, instruction, spawn, _⟩ := Evm.step_spawn_inv step
    have onlyStatic : x = .staticcall := only _ chain x instruction
    subst x
    have stc := (Frame.enter_run_isStatic enter).trans (Xinst.step_staticcall_spawn_isStatic spawn)
    simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · exact stc
    · exact Exec.rawFrameRoots_isStatic child stc D (List.mem_cons_of_mem _ member)
    · exact nextIH (chain.snoc (.runOk step enter child resume next)) D member

/-- A chain node's reach, from a certified frame: the instruction it stands at is one the root reach allows. -/
theorem chain_exec_of_reach {code : ByteArray} {c : Cert} {f0 : SFunc} (checked : Cert.check code c = true)
    (hf0 : (Cursor.start c).f = f0) (hK : (Cursor.start c).K = []) {p : Xinst → Bool}
    {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (hcode : sevm.code = code) (hsg : sevm.benvStat.rules.stateGas = none)
    (hr : ∀ T x g, Reach (StepIn ⟨0, sevm, pre, out, run⟩) c.prog sevm
      ⟨St pre pre.stack pre.memory pre.gasLeft, f0, []⟩ T → T.f = .next (.exec x) g → p x = true) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N →
      ∀ x, Ninst.At N.sevm.code N.pc (.exec x) → p x = true := by
  intro N hN x hat
  obtain ⟨κ, reach, okN⟩ := reach_of_parentPrefix_noStateGas checked rfl hcode hsg hN
  obtain ⟨g, hg, -⟩ := okN.tree_of_exec hat
  refine hr (κ.conf N.devm) x g ?_ hg
  rw [← St.self rfl rfl]
  have e : (Cursor.start c).conf pre = ⟨pre, f0, []⟩ := by
    simp only [Cursor.conf, hf0, hK, List.map_nil]
  rw [← e]
  exact reach

/-- **Past a selector's comparison tree, a reach enters a goto of another constant or a leaf.** So a dispatcher sends
every selector but `c₀` into the allowed set when each goto but `c₀`'s and each leaf lies in it. -/
theorem Reach.exec_allowed_of_routes {E : List Nat} (hE : AllowedSet p fs E = true) {σ c₀ : B256} {tree : SFunc}
    (hne : σ ≠ c₀) (pairs : ∀ q ∈ tree.selPairs, q.1 = c₀ ∨ q.2 ∈ E)
    (leaves : ∀ t ∈ tree.selLeaves, t.allowedIn p E = true)
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (h : Reach P fs sevm ⟨St b (σ :: S) M G, tree, []⟩ T) {x : Xinst} {g : SFunc} (hT : T.f = .next (.exec x) g) :
    p x = true := by
  have at_ : AtExec T := ⟨x, g, hT⟩
  cases hw : tree.selWalk σ with
  | inr t =>
    obtain ⟨G', r⟩ := Reach.selWalk_inr hP hw h at_
    exact r.exec_allowed hE hT (leaves t (SFunc.selWalk_mem_leaves hw)) (fun _ hs => absurd hs List.not_mem_nil)
  | inl q =>
    obtain ⟨c, j⟩ := q
    obtain ⟨eq, g', G', hg, r⟩ := Reach.selWalk_inl hP hw h at_
    rcases pairs _ (SFunc.selWalk_mem_pairs hw) with same | mem
    · exact absurd (eq.trans same) hne
    · exact r.exec_allowed hE hT (AllowedSet.lookup hE mem hg) (fun _ hs => absurd hs List.not_mem_nil)

end Blanc.Lift
