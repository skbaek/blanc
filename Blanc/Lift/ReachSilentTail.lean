import Blanc.Lift.ReachFirstExec
import Blanc.Lift.ReachChain
import Blanc.Lift.CallSiteChildren

/-!
# A silent tail after an external instruction (contract-neutral)

`silent_after_exec`: in a certified frame whose program passes two decidable checks, the frame's
post state is the state right after any external instruction it decodes, and no later node of the
frame decodes another one.  The checks:

* `ExecSilent S` at every node (`SFunc.nodesSatisfy`): the tree after an external instruction is
  silent within the closed silent set `S`;
* `SFunc.contsIn E S` at every tree: each internal call either enters the closed exec-free set `E`
  or pushes a continuation silent within `S`.

The second check bounds the pending continuations at an external instruction (`Reach.conts_silent`):
an exec-free callee returns before any external instruction, so at one every pending continuation
is silent.  Together with the first, the remainder of the frame after the instruction is silent
(`CursorOK.state_post_of_silent`, `noExec_after_of_cursor`).
-/

namespace Blanc.Lift

open Jaune Blanc

/-- Each internal call of the tree either enters `E` or pushes a continuation silent within `S`. -/
def SFunc.contsIn (E S : List Nat) : SFunc → Bool
  | .next _ f => f.contsIn E S
  | .dest f => f.contsIn E S
  | .pcAt _ f => f.contsIn E S
  | .branch f g => f.contsIn E S && g.contsIn E S
  | .branchTo f _ => f.contsIn E S
  | .callNext k f => (decide (k ∈ E) || f.silentIn S) && f.contsIn E S
  | _ => true

/-- The tree after an external instruction is silent within `S`. -/
def ExecSilent (S : List Nat) (n : Ninst) (g : SFunc) : Bool :=
  match n with
  | .exec _ => g.silentIn S
  | _ => true

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

private theorem execFreeIn_next {E : List Nat} {n : Ninst} {f : SFunc}
    (h : (SFunc.next n f).execFreeIn E = true) : f.execFreeIn E = true := by
  cases n <;> simp_all only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, Bool.and_eq_true,
    Bool.false_and, Bool.false_eq_true, and_self]

private theorem execFreeIn_of_mem {E : List Nat} (hE : ExecFreeSet fs E = true) {k : Nat} {g : SFunc}
    (hk : k ∈ E) (hg : fs[k]? = some g) : g.execFreeIn E = true :=
  ExecFreeSet.lookup hE hk hg

/-- The configuration invariant of `Reach.conts_silent`: in a checked tree with silent checked
continuations, or inside an exec-free callee below a checked continuation. -/
private def ContsInv (E S : List Nat) (a : Conf) : Prop :=
  (a.f.contsIn E S = true ∧ ∀ s ∈ a.K, s.silentIn S = true ∧ s.contsIn E S = true) ∨
    (a.f.execFreeIn E = true ∧ ∃ L g K₁, a.K = L ++ g :: K₁ ∧ (∀ s ∈ L, s.execFreeIn E = true) ∧
      g.contsIn E S = true ∧ ∀ s ∈ K₁, s.silentIn S = true ∧ s.contsIn E S = true)

private theorem contsInv_step {E S : List Nat} (hE : ExecFreeSet fs E = true)
    (hall : ∀ f ∈ fs, f.contsIn E S = true) {a b : Conf} (step : ConfStep P fs sevm a b)
    (ha : ContsInv E S a) : ContsInv E S b := by
  have mem : ∀ {k : Nat} {g : SFunc}, fs[k]? = some g → g.contsIn E S = true := fun hg =>
    hall _ (List.mem_of_getElem? hg)
  rcases ha with ⟨hf, hK⟩ | ⟨hf, L, g, K₁, hK, hL, hg, hK₁⟩
  · cases step with
    | next _ => exact .inl ⟨by simpa only [SFunc.contsIn] using hf, hK⟩
    | dest _ => exact .inl ⟨by simpa only [SFunc.contsIn] using hf, hK⟩
    | zero _ _ =>
        simp only [SFunc.contsIn, Bool.and_eq_true] at hf
        exact .inl ⟨hf.1, hK⟩
    | succ _ _ _ _ =>
        simp only [SFunc.contsIn, Bool.and_eq_true] at hf
        exact .inl ⟨hf.2, hK⟩
    | toZero _ _ => exact .inl ⟨by simpa only [SFunc.contsIn] using hf, hK⟩
    | toSucc _ _ _ hk _ => exact .inl ⟨mem hk, hK⟩
    | jump _ hk _ => exact .inl ⟨mem hk, hK⟩
    | @call _ _ f' g' k K _ hk _ =>
        simp only [SFunc.contsIn, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hf
        rcases hf.1 with inE | silent
        · exact .inr ⟨execFreeIn_of_mem hE inE hk, [], f', K, rfl,
            fun _ h => (List.not_mem_nil h).elim, hf.2, hK⟩
        · refine .inl ⟨mem hk, fun s hs => ?_⟩
          rcases List.mem_cons.mp hs with rfl | hs
          · exact ⟨silent, hf.2⟩
          · exact hK s hs
    | ret _ =>
        refine .inl ⟨(hK _ List.mem_cons_self).2, fun s hs => hK s (List.mem_cons_of_mem _ hs)⟩
    | pcAt _ _ => exact .inl ⟨by simpa only [SFunc.contsIn] using hf, hK⟩
  · cases step with
    | next _ => exact .inr ⟨execFreeIn_next hf, L, g, K₁, hK, hL, hg, hK₁⟩
    | dest _ => exact .inr ⟨by simpa only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using hf,
        L, g, K₁, hK, hL, hg, hK₁⟩
    | zero _ _ =>
        simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
          Bool.and_eq_true] at hf
        exact .inr ⟨by simp only [SFunc.execFreeIn, hf.1.1, hf.2.1, Bool.and_self], L, g, K₁, hK, hL, hg,
          hK₁⟩
    | succ _ _ _ _ =>
        simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_append,
          Bool.and_eq_true] at hf
        exact .inr ⟨by simp only [SFunc.execFreeIn, hf.1.2, hf.2.2, Bool.and_self], L, g, K₁, hK, hL, hg,
          hK₁⟩
    | toZero _ _ =>
        simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
          Bool.and_eq_true] at hf
        exact .inr ⟨by simp only [SFunc.execFreeIn, hf.1, hf.2.2, Bool.and_self], L, g, K₁, hK, hL, hg,
          hK₁⟩
    | toSucc _ _ _ hk _ =>
        simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
          Bool.and_eq_true, decide_eq_true_eq] at hf
        exact .inr ⟨execFreeIn_of_mem hE hf.2.1 hk, L, g, K₁, hK, hL, hg, hK₁⟩
    | jump _ hk _ =>
        simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons, List.all_nil,
          Bool.and_true, Bool.true_and, decide_eq_true_eq] at hf
        exact .inr ⟨execFreeIn_of_mem hE hf hk, L, g, K₁, hK, hL, hg, hK₁⟩
    | @call _ _ f' g' k K _ hk _ =>
        simp only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs, List.all_cons,
          Bool.and_eq_true, decide_eq_true_eq] at hf
        refine .inr ⟨execFreeIn_of_mem hE hf.2.1 hk, f' :: L, g, K₁, by change f' :: K = _; change K = _ at hK; rw [hK]; rfl, fun s hs => ?_,
          hg, hK₁⟩
        rcases List.mem_cons.mp hs with rfl | hs
        · simp only [SFunc.execFreeIn, hf.1, hf.2.2, Bool.and_self]
        · exact hL s hs
    | @ret _ _ f' K _ _ =>
        cases L with
        | nil =>
            obtain ⟨rfl, rfl⟩ := List.cons.inj hK
            exact .inl ⟨hg, hK₁⟩
        | cons h L' =>
            obtain ⟨rfl, rfl⟩ := List.cons.inj hK
            exact .inr ⟨hL _ List.mem_cons_self, L', g, K₁, rfl,
              fun s hs => hL s (List.mem_cons_of_mem _ hs), hg, hK₁⟩
    | pcAt _ _ => exact .inr ⟨by simpa only [SFunc.execFreeIn, SFunc.execsSatisfy, SFunc.refs] using hf,
        L, g, K₁, hK, hL, hg, hK₁⟩

/-- **The pending continuations at an external instruction are silent.** -/
theorem Reach.conts_silent {E S : List Nat} (hE : ExecFreeSet fs E = true)
    (hall : ∀ f ∈ fs, f.contsIn E S = true) {d : Devm} {f : SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, f, []⟩ T) (hT : AtExec T) (hf : f.contsIn E S = true) :
    ∀ s ∈ T.K, s.silentIn S = true := by
  suffices ∀ {a : Conf}, Reach P fs sevm a T → ContsInv E S a → ∀ s ∈ T.K, s.silentIn S = true from
    this h (.inl ⟨hf, fun _ h => (List.not_mem_nil h).elim⟩)
  intro a h ha
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      obtain ⟨x, f', hx⟩ := hT
      rcases ha with ⟨-, hK⟩ | ⟨hfree, -⟩
      · exact fun s hs => (hK s hs).1
      · rw [hx] at hfree
        simp only [SFunc.execFreeIn, SFunc.execsSatisfy, Bool.false_and, Bool.false_eq_true] at hfree
  | head step _ ih => exact ih (contsInv_step hE hall step ha)

/-- The first tree of a certificate whose trees all pass `contsIn` passes it. -/
theorem Cursor.start_contsIn {c : Cert} {E S : List Nat} (hall : ∀ f ∈ c.prog, f.contsIn E S = true) :
    (Cursor.start c).f.contsIn E S = true := by
  cases c with
  | nil => rfl
  | cons e c => exact hall e.2 List.mem_cons_self

/-- **The silent tail after an external instruction.**  In a successful pc-`0` frame of certified
bytes whose program passes `contsIn E S` and `ExecSilent S`, the frame's post state is the state
right after any external instruction its chain decodes, and no later node decodes another one. -/
theorem silent_after_exec {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {E S : List Nat} (hE : ExecFreeSet c.prog E = true) (hS : SilentSet c.prog S = true)
    (hall : ∀ f ∈ c.prog, f.contsIn E S = true)
    (hx : ∀ f ∈ c.prog, f.nodesSatisfy (ExecSilent S) = true)
    {R : Exec.Deriv} {post : Devm} (hpc : R.pc = 0) (hcode : R.sevm.code = code)
    (hfork : CoveredFork R.sevm.benvStat.fork) (success : R.exn = .ok post)
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix R N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    ∀ N', Exec.Deriv.ParentStep N' N → post.state = N'.devm.state ∧
      ∀ M, Exec.Deriv.ParentPrefix N' M → ∀ y, ¬ Ninst.At M.sevm.code M.pc (.exec y) := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix hc hpc hcode hfork chain
  obtain ⟨g, hf, hg⟩ := ok.nodesSatisfy_exec (Reach.nodesSatisfy hx reach).1 hat
  have hK : ∀ s ∈ κ.K.map Cont.f, s.silentIn S = true := by
    have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
    have start : (Cursor.start c).conf R.devm = ⟨R.devm, (Cursor.start c).f, []⟩ := by
      cases c <;> rfl
    rw [start] at reach
    exact Reach.conts_silent hE hall reach hT (Cursor.start_contsIn hall)
  intro N' edge
  have hsevmN : N.sevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq chain
  have hforkN : CoveredFork N.sevm.benvStat.fork := by rw [hsevmN]; exact hfork
  obtain ⟨κ₁, hs, -, ok₁⟩ := cursor_stepS hc ok edge hforkN
  obtain ⟨f, pc, a, m, K⟩ := κ
  dsimp only at hf hK
  subst hf
  cases hs with
  | next habs =>
    have hchain : Exec.Deriv.ParentPrefix R N' := chain.snoc edge
    have hsevmN' : N'.sevm = R.sevm := Blanc.Exec.Deriv.ParentPrefix.sevm_eq hchain
    have hforkN' : CoveredFork N'.sevm.benvStat.fork := by rw [hsevmN']; exact hfork
    have success' : N'.exn = .ok post := (Exec.Deriv.ParentPrefix.exn_eq hchain).trans success
    simp only [ExecSilent] at hg
    refine ⟨CursorOK.state_post_of_silent hc hS _ rfl ok₁ success' hforkN' hg hK,
      fun M hM y => noExec_after_of_cursor hc hchain hM hfork ok₁ (ExecFreeSet.of_silentSet hS)
        (SFunc.execFreeIn_of_silentIn hg) (fun s hs => SFunc.execFreeIn_of_silentIn (hK s hs)) y⟩

end Blanc.Lift
