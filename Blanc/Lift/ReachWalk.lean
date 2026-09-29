import Blanc.Lift.Reach
import Blanc.Lift.CallRestriction
import Blanc.Lift.Silent
import Blanc.Lift.InvWalk

/-!
# Walking a prefix reach to an external instruction

Kit for proving a prefix fact of a certified frame from `reach_of_parentPrefix`:
a reach from entry `0` to a configuration about to run an external instruction
(`AtExec`).  The node inversions over the walk state `St b S M G` mirror the
big-step ones (`rr_next`, `rr_dest`, `rr_branch`, `rr_call`), and two
certificate-level facts discharge whole regions at once:

* `Reach.false_of_execFree`: from a tree whose instructions are all internal and
  whose referenced entries lie in an exec-free, reference-closed set
  (`ExecFreeSet`, decidable), no external instruction is reached — used for the
  selector wrappers that make no call, for reverting arms, and for a callee
  (`rr_callOver`: the reach then crosses the callee as a big-step run);
* `Reach.gotoTree`: a dispatcher-shaped tree (safe instructions, gotos into `W`)
  hands the reach to one goto target in a state satisfying a step-stable `Ψ`.
-/

namespace Blanc.Lift

open Jaune

/-- A tree with no external instruction, all of whose entry references lie in `E`. -/
def SFunc.execFreeIn (E : List Nat) (f : SFunc) : Bool :=
  f.execsSatisfy (fun _ => false) && f.refs.all (· ∈ E)

/-- `E` is closed and exec-free: each member's tree is `execFreeIn E`. -/
def ExecFreeSet (fs : List SFunc) (E : List Nat) : Bool :=
  E.all fun k => match fs[k]? with
    | some g => g.execFreeIn E
    | none => false

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

theorem ExecFreeSet.lookup {E : List Nat} (hE : ExecFreeSet fs E = true) {k : Nat}
    {g : SFunc} (hk : k ∈ E) (hg : fs[k]? = some g) : g.execFreeIn E = true := by
  have h := (List.all_eq_true.mp hE) k hk
  rw [hg] at h
  exact h

private theorem execFree_step {E : List Nat} (hE : ExecFreeSet fs E = true) {a b : Conf}
    (step : ConfStep P fs sevm a b) (ha : a.f.execFreeIn E = true)
    (hK : ∀ s ∈ a.K, s.execFreeIn E = true) :
    b.f.execFreeIn E = true ∧ ∀ s ∈ b.K, s.execFreeIn E = true := by
  cases step with
  | @next d d' n f K _ =>
      refine ⟨?_, hK⟩
      cases n <;> simp_all [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs]
  | dest _ => exact ⟨by simpa [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using ha, hK⟩
  | zero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.1, ha.2.1⟩
  | succ _ _ _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.2, ha.2.2⟩
  | toZero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ha.2.2⟩
  | @toSucc d d' f g k K _ _ _ hk _ =>
      refine ⟨ExecFreeSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.execFreeIn, SFunc.refs, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at ha
      exact ha.2.1
  | @jump d d' g k K _ hk _ =>
      refine ⟨ExecFreeSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.execFreeIn, SFunc.refs, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ha.2
  | @call d d' f g k K _ hk _ =>
      simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      refine ⟨ExecFreeSet.lookup hE ha.2.1 hk, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · simp only [SFunc.execFreeIn, Bool.and_eq_true]
        exact ⟨ha.1, ha.2.2⟩
      · exact hK s hs
  | ret _ _ => exact ⟨hK _ List.mem_cons_self, fun s hs => hK s (List.mem_cons_of_mem _ hs)⟩
  | pcAt _ _ => exact ⟨by simpa [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using ha, hK⟩

/-- **No external instruction in an exec-free region.**  A reach from a tree and
pending continuations that are all exec-free within a closed exec-free set never
arrives at an external instruction. -/
theorem Reach.false_of_execFree {E : List Nat} (hE : ExecFreeSet fs E = true) {d : Devm}
    {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, f, K⟩ T) (hT : AtExec T) (hf : f.execFreeIn E = true)
    (hK : ∀ s ∈ K, s.execFreeIn E = true) : False := by
  suffices ∀ {a : Conf}, Reach P fs sevm a T → a.f.execFreeIn E = true →
      (∀ s ∈ a.K, s.execFreeIn E = true) → False from this h hf hK
  intro a h ha hK
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      obtain ⟨x, f', hx⟩ := hT
      rw [hx] at ha
      simp [SFunc.execFreeIn, SFunc.execsSatisfy] at ha
  | head step _ ih =>
      obtain ⟨hb, hbK⟩ := execFree_step hE step ha hK
      exact ih hb hbK

section St

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f g : SFunc} {K : List SFunc}
  {T : Conf}

theorem rr_next {n : Ninst} {d : Devm} (run : Reach P fs sevm ⟨d, .next n f, K⟩ T)
    (hT : AtExec T) (hn : ∀ x, n ≠ .exec x := by intro x h; cases h) :
    ∃ d', P sevm d n d' ∧ Reach P fs sevm ⟨d', f, K⟩ T :=
  Reach.next hn run hT

theorem rr_dest (run : Reach P fs sevm ⟨St b S M G, .dest f, K⟩ T) (hT : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T := by
  obtain ⟨d', burn, rest⟩ := Reach.dest run hT
  exact ⟨_, (St.of_burn burn) ▸ rest⟩

theorem rr_branch {dd w : B256}
    (run : Reach P fs sevm ⟨St b (dd :: w :: S) M G, .branch f g, K⟩ T) (hT : AtExec T) :
    (w = 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases Reach.branch run hT with ⟨t, d', pop, rest⟩ | ⟨t, w0, d', hw, pop, rest⟩
  · obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    exact .inl ⟨hw, _, e ▸ rest⟩
  · obtain ⟨-, hw', e⟩ := St.of_pop2 pop
    exact .inr ⟨hw' ▸ hw, _, e ▸ rest⟩

/-- A `callNext` whose callee is exec-free: the callee returns (a big-step run)
before the target. -/
theorem rr_callOver {E : List Nat} (hE : ExecFreeSet fs E = true) {k : Nat} {dd : B256}
    (hk : fs[k]? = some g) (hkE : k ∈ E)
    (run : Reach P fs sevm ⟨St b (dd :: S) M G, .callNext k f, K⟩ T) (hT : AtExec T) :
    ∃ G' D, SFunc.RunP P fs sevm (St b S M G') g (.returned D) ∧
      Reach P fs sevm ⟨D, f, K⟩ T := by
  obtain ⟨t, g', d', hk', pop, inside | ⟨D, callee, rest⟩⟩ := Reach.call run hT
  · rw [hk] at hk'
    cases hk'
    obtain ⟨T', r', rfl⟩ := inside
    exact (Reach.false_of_execFree hE r' hT (ExecFreeSet.lookup hE hkE hk) (by simp)).elim
  · rw [hk] at hk'
    cases hk'
    obtain ⟨-, e⟩ := St.of_pop1 pop
    exact ⟨_, D, e ▸ callee, rest⟩

/-- A `callNext` whose continuation (with the pending ones) is exec-free: the
target lies inside the callee, reached from an empty stack. -/
theorem rr_callInto {E : List Nat} (hE : ExecFreeSet fs E = true) {k : Nat} {dd : B256}
    (hk : fs[k]? = some g) (hf : f.execFreeIn E = true) (hK : ∀ s ∈ K, s.execFreeIn E = true)
    (run : Reach P fs sevm ⟨St b (dd :: S) M G, .callNext k f, K⟩ T) (hT : AtExec T) :
    ∃ G' T', Reach P fs sevm ⟨St b S M G', g, []⟩ T' ∧ T = T'.below (f :: K) := by
  obtain ⟨t, g', d', hk', pop, ⟨T', r', hT'⟩ | ⟨D, _, rest⟩⟩ := Reach.call run hT
  · rw [hk] at hk'
    cases hk'
    obtain ⟨-, e⟩ := St.of_pop1 pop
    exact ⟨_, T', e ▸ r', hT'⟩
  · exact (Reach.false_of_execFree hE rest hT hf hK).elim

end St

/-- A dispatcher-shaped tree: instructions accepted by `ok`, reverts and halts,
and gotos into `W`. -/
def SFunc.gotoTree (W : List Nat) (ok : Ninst → Bool) : SFunc → Bool
  | .branch f g => f.gotoTree W ok && g.gotoTree W ok
  | .branchTo f k => decide (k ∈ W) && f.gotoTree W ok
  | .next n f => ok n && f.gotoTree W ok
  | .dest f => f.gotoTree W ok
  | .last _ => true
  | .jump k => decide (k ∈ W)
  | _ => false

/-- **Through a dispatcher.**  A reach from a `gotoTree W ok` tree to an external
instruction first enters some goto target `k ∈ W`, in a state satisfying any `Ψ`
that the accepted instructions, pops and burns keep. -/
theorem Reach.gotoTree {W : List Nat} {ok : Ninst → Bool} {Ψ : Devm → Prop}
    (hok : ∀ x, ok (.exec x) = false)
    (hstep : ∀ {d n d'}, ok n = true → P sevm d n d' → Ψ d → Ψ d')
    (hpop : ∀ {xs d d'}, Devm.PopBurn xs d d' → Ψ d → Ψ d')
    (hburn : ∀ {d d'}, Devm.Burn d d' → Ψ d → Ψ d') :
    ∀ {f : SFunc} {d : Devm} {K : List SFunc} {T : Conf},
      Reach P fs sevm ⟨d, f, K⟩ T → AtExec T → f.gotoTree W ok = true → Ψ d →
      ∃ k ∈ W, ∃ g d', fs[k]? = some g ∧ Ψ d' ∧ Reach P fs sevm ⟨d', g, K⟩ T := by
  intro f
  induction f with
  | branch f g ihf ihg =>
      intro d K T h hT hf hΨ
      simp only [SFunc.gotoTree, Bool.and_eq_true] at hf
      rcases Reach.branch h hT with ⟨t, d', pop, rest⟩ | ⟨t, w, d', _, pop, rest⟩
      · exact ihf rest hT hf.1 (hpop pop hΨ)
      · exact ihg rest hT hf.2 (hpop pop hΨ)
  | branchTo f k ih =>
      intro d K T h hT hf hΨ
      simp only [SFunc.gotoTree, Bool.and_eq_true, decide_eq_true_eq] at hf
      rcases Reach.branchTo h hT with ⟨t, d', pop, rest⟩ | ⟨t, w, g, d', _, hk, pop, rest⟩
      · exact ih rest hT hf.2 (hpop pop hΨ)
      · exact ⟨k, hf.1, g, d', hk, hpop pop hΨ, rest⟩
  | last l =>
      intro d K T h hT _ _
      exact (Reach.not_last h hT).elim
  | next n f ih =>
      intro d K T h hT hf hΨ
      simp only [SFunc.gotoTree, Bool.and_eq_true] at hf
      have hn : ∀ x, n ≠ .exec x := by
        rintro x rfl
        rw [hok] at hf
        exact Bool.false_ne_true hf.1
      obtain ⟨d', step, rest⟩ := Reach.next hn h hT
      exact ih rest hT hf.2 (hstep hf.1 step hΨ)
  | dest f ih =>
      intro d K T h hT hf hΨ
      obtain ⟨d', burn, rest⟩ := Reach.dest h hT
      exact ih rest hT hf (hburn burn hΨ)
  | jump k =>
      intro d K T h hT hf hΨ
      simp only [SFunc.gotoTree, decide_eq_true_eq] at hf
      obtain ⟨t, g, d', hk, pop, rest⟩ := Reach.jump h hT
      exact ⟨k, hf, g, d', hk, hpop pop hΨ, rest⟩
  | callNext _ _ _ => intro _ _ _ _ _ hf; simp [SFunc.gotoTree] at hf
  | ret => intro _ _ _ _ _ hf; simp [SFunc.gotoTree] at hf
  | pcAt _ _ _ => intro _ _ _ _ _ hf; simp [SFunc.gotoTree] at hf
  | undefined => intro _ _ _ _ _ hf; simp [SFunc.gotoTree] at hf

/-- A non-jump instruction that writes no persistent state and spawns nothing: a
register instruction other than `SSTORE`/`TSTORE`, or a push. -/
def regSilent : Ninst → Bool
  | .reg r => r != .sstore && r != .tstore
  | .push _ _ => true
  | _ => false

theorem Ninst.Run.state_of_regSilent {s : Sevm} {d d' : Devm} {n : Ninst}
    (hn : regSilent n = true) (h : Ninst.Run s d n d') : d'.state = d.state := by
  cases n with
  | push xs le => exact (Devm.pushBurn_of_run (Ninst.run_push_eq h)).state.symm
  | reg r =>
      rcases h with ⟨xl, -, pc, run⟩
      simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
      simp only [regSilent, Bool.and_eq_true, bne_iff_ne, ne_eq] at hn
      exact (Rinst.preserves_state hn.1 hn.2 run.2.symm).symm
  | exec _ => simp [regSilent] at hn
  | dupn _ => simp [regSilent] at hn
  | swapn _ => simp [regSilent] at hn
  | exchange _ => simp [regSilent] at hn

/-- Every path of the tree runs instructions accepted by `ok` (no call or goto)
up to at most one external instruction, after which it is exec-free in `E`. -/
def SFunc.lastExec (ok : Ninst → Bool) (E : List Nat) : SFunc → Bool
  | .next (.exec _) g => g.execFreeIn E
  | .next n f => ok n && f.lastExec ok E
  | .dest f => f.lastExec ok E
  | .branch f g => f.lastExec ok E && g.lastExec ok E
  | .last _ => true
  | _ => false

/-- **At the last external instruction.**  A reach from a `lastExec ok E` tree,
over exec-free pending continuations, to an external instruction stops at the
first one on its path, in a state satisfying any `Ψ` the accepted instructions,
pops and burns keep. -/
theorem Reach.lastExec {ok : Ninst → Bool} {E : List Nat} {Ψ : Devm → Prop}
    (hE : ExecFreeSet fs E = true)
    (hstep : ∀ {d n d'}, ok n = true → P sevm d n d' → Ψ d → Ψ d')
    (hpop : ∀ {xs d d'}, Devm.PopBurn xs d d' → Ψ d → Ψ d')
    (hburn : ∀ {d d'}, Devm.Burn d d' → Ψ d → Ψ d') :
    ∀ {f : SFunc} {d : Devm} {K : List SFunc} {T : Conf},
      Reach P fs sevm ⟨d, f, K⟩ T → AtExec T → f.lastExec ok E = true →
      (∀ s ∈ K, s.execFreeIn E = true) → Ψ d → Ψ T.d := by
  intro f
  induction f with
  | branch f g ihf ihg =>
      intro d K T h hT hf hK hΨ
      simp only [SFunc.lastExec, Bool.and_eq_true] at hf
      rcases Reach.branch h hT with ⟨t, d', pop, rest⟩ | ⟨t, w, d', _, pop, rest⟩
      · exact ihf rest hT hf.1 hK (hpop pop hΨ)
      · exact ihg rest hT hf.2 hK (hpop pop hΨ)
  | last l =>
      intro d K T h hT _ _ _
      exact (Reach.not_last h hT).elim
  | next n f ih =>
      intro d K T h hT hf hK hΨ
      cases n with
      | exec x =>
          rcases Reach.exec h with rfl | ⟨d', _, rest⟩
          · exact hΨ
          · exact (Reach.false_of_execFree hE rest hT hf hK).elim
      | reg r =>
          simp only [SFunc.lastExec, Bool.and_eq_true] at hf
          obtain ⟨d', step, rest⟩ := Reach.next (by intro x hx; cases hx) h hT
          exact ih rest hT hf.2 hK (hstep hf.1 step hΨ)
      | push xs le =>
          simp only [SFunc.lastExec, Bool.and_eq_true] at hf
          obtain ⟨d', step, rest⟩ := Reach.next (by intro x hx; cases hx) h hT
          exact ih rest hT hf.2 hK (hstep hf.1 step hΨ)
      | dupn i =>
          simp only [SFunc.lastExec, Bool.and_eq_true] at hf
          obtain ⟨d', step, rest⟩ := Reach.next (by intro x hx; cases hx) h hT
          exact ih rest hT hf.2 hK (hstep hf.1 step hΨ)
      | swapn i =>
          simp only [SFunc.lastExec, Bool.and_eq_true] at hf
          obtain ⟨d', step, rest⟩ := Reach.next (by intro x hx; cases hx) h hT
          exact ih rest hT hf.2 hK (hstep hf.1 step hΨ)
      | exchange i =>
          simp only [SFunc.lastExec, Bool.and_eq_true] at hf
          obtain ⟨d', step, rest⟩ := Reach.next (by intro x hx; cases hx) h hT
          exact ih rest hT hf.2 hK (hstep hf.1 step hΨ)
  | dest f ih =>
      intro d K T h hT hf hK hΨ
      obtain ⟨d', burn, rest⟩ := Reach.dest h hT
      exact ih rest hT hf hK (hburn burn hΨ)
  | branchTo _ _ _ => intro _ _ _ _ _ hf; simp [SFunc.lastExec] at hf
  | jump _ => intro _ _ _ _ _ hf; simp [SFunc.lastExec] at hf
  | callNext _ _ _ => intro _ _ _ _ _ hf; simp [SFunc.lastExec] at hf
  | ret => intro _ _ _ _ _ hf; simp [SFunc.lastExec] at hf
  | pcAt _ _ _ => intro _ _ _ _ _ hf; simp [SFunc.lastExec] at hf
  | undefined => intro _ _ _ _ _ hf; simp [SFunc.lastExec] at hf

end Blanc.Lift
