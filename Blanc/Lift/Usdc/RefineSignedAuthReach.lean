import Blanc.Lift.ReachWalk
import Blanc.Lift.ShuffleSkip

/-!
# The world at the first external instruction of a reach (U6e3)

A reach of a certified frame to an external instruction (`AtExec`), from a tree whose every path
runs state-silent instructions, calls into state-silent closures, and reaches at most one external
instruction after which (and after every call into a closure that may contain one) nothing external
remains, arrives at that instruction with the world state it started from.

* `SFunc.preExec okx W0 W E`: the trees of that shape.  Calls go into the silent set `W0` (a
  `SilentSet`) with a `preExec` continuation, or into `W` (trees of the same shape) or the
  exec-free set `E` with an exec-free continuation; the external instruction satisfies `okx` and
  is followed by an exec-free tree;
* `PreExecSet`: every member of `W` is `preExec`;
* `Reach.preExec_state`: the reach's target runs an `okx` instruction from the starting world.

Nothing here mentions a contract.  (Hoist candidate: a contract-neutral reach lemma.)
-/

namespace Blanc.Lift

open Jaune

/-- Trees whose paths run state-silent instructions up to at most one external instruction
accepted by `okx`, after which they are exec-free in `E`; calls into `W0` keep this shape in the
continuation, calls into `W` or `E` need an exec-free continuation. -/
def SFunc.preExec (okx : Xinst → Bool) (W0 W E : List Nat) : SFunc → Bool
  | .next (.exec x) f => okx x && f.execFreeIn E
  | .next n f => n.stateSilent && f.preExec okx W0 W E
  | .dest f => f.preExec okx W0 W E
  | .branch f g => f.preExec okx W0 W E && g.preExec okx W0 W E
  | .branchTo f k => decide (k ∈ W) && f.preExec okx W0 W E
  | .jump k => decide (k ∈ W)
  | .callNext k f => (decide (k ∈ W0) && f.preExec okx W0 W E) ||
      (decide (k ∈ W ∨ k ∈ E) && f.execFreeIn E)
  | .ret => true
  | .last _ => true
  | .undefined => true
  | .pcAt _ f => f.preExec okx W0 W E

/-- Every member of `W` is a `preExec` tree. -/
def PreExecSet (fs : List SFunc) (okx : Xinst → Bool) (W0 W E : List Nat) : Bool :=
  W.all fun k => match fs[k]? with
    | some g => g.preExec okx W0 W E
    | none => false

/-- A silent tree with references in `W0`. -/
def SFunc.silentIn (W0 : List Nat) (f : SFunc) : Bool := f.silent && f.refs.all (· ∈ W0)

section PreExec

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {okx : Xinst → Bool} {W0 W E : List Nat}

/-- Continuation stacks of the before phase. -/
def PreK (okx : Xinst → Bool) (W0 W E : List Nat) : List SFunc → Prop
  | [] => True
  | s :: K => (s.preExec okx W0 W E = true ∧ ∀ t ∈ K, t.execFreeIn E = true) ∨
      (s.silentIn W0 = true ∧ PreK okx W0 W E K) ∨
      (s.execFreeIn E = true ∧ ∀ t ∈ K, t.execFreeIn E = true)

/-- The before-phase configurations. -/
def PreInv (okx : Xinst → Bool) (W0 W E : List Nat) (f : SFunc) (K : List SFunc) : Prop :=
  (f.preExec okx W0 W E = true ∧ ∀ t ∈ K, t.execFreeIn E = true) ∨
    (f.silentIn W0 = true ∧ PreK okx W0 W E K)

theorem SilentSet.lookup' (hS : SilentSet fs W0 = true) {k : Nat} {g : SFunc} (hk : k ∈ W0)
    (hg : fs[k]? = some g) : g.silentIn W0 = true := by
  have h := (List.all_eq_true.mp hS) k hk
  rw [hg] at h
  exact h

theorem PreExecSet.lookup (hW : PreExecSet fs okx W0 W E = true) {k : Nat} {g : SFunc}
    (hk : k ∈ W) (hg : fs[k]? = some g) : g.preExec okx W0 W E = true := by
  have h := (List.all_eq_true.mp hW) k hk
  rw [hg] at h
  exact h

/-- One step of the before phase: it stays in the before phase with the same world state, or
enters a region with nothing external left. -/
theorem ConfStep.preExec (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hE : ExecFreeSet fs E = true) (hS : SilentSet fs W0 = true)
    (hW : PreExecSet fs okx W0 W E = true) {a b : Conf} (step : ConfStep P fs sevm a b)
    (inv : PreInv okx W0 W E a.f a.K) :
    (b.d.state = a.d.state ∧ PreInv okx W0 W E b.f b.K) ∨
      (b.f.execFreeIn E = true ∧ ∀ t ∈ b.K, t.execFreeIn E = true) := by
  cases step with
  | @next d d' n f K hp =>
      cases n with
      | exec x =>
          rcases inv with ⟨hf, hK⟩ | ⟨hf, -⟩
          · simp only [SFunc.preExec, Bool.and_eq_true] at hf
            exact .inr ⟨hf.2, hK⟩
          · simp only [SFunc.silentIn, SFunc.silent, Ninst.stateSilent, Bool.false_and,
              Bool.false_eq_true] at hf
      | _ =>
          rename_i arg
          rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
          · simp only [SFunc.preExec, Bool.and_eq_true] at hf
            exact .inl ⟨ninst_state_of_stateSilent hf.1 (hP hp), .inl ⟨hf.2, hK⟩⟩
          · simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, Bool.and_eq_true] at hf
            exact .inl ⟨ninst_state_of_stateSilent hf.1.1 (hP hp),
              .inr ⟨by simp only [SFunc.silentIn, hf.1.2, hf.2, Bool.and_self], hK⟩⟩
  | dest burn =>
      refine .inl ⟨burn.state.symm, ?_⟩
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · exact .inl ⟨hf, hK⟩
      · exact .inr ⟨by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using hf, hK⟩
  | zero t pop =>
      refine .inl ⟨pop.state.symm, ?_⟩
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · simp only [SFunc.preExec, Bool.and_eq_true] at hf
        exact .inl ⟨hf.1, hK⟩
      · simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append,
          Bool.and_eq_true] at hf
        exact .inr ⟨by simp only [SFunc.silentIn, hf.1.1, hf.2.1, Bool.and_self], hK⟩
  | succ t w hw pop =>
      refine .inl ⟨pop.state.symm, ?_⟩
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · simp only [SFunc.preExec, Bool.and_eq_true] at hf
        exact .inl ⟨hf.2, hK⟩
      · simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append,
          Bool.and_eq_true] at hf
        exact .inr ⟨by simp only [SFunc.silentIn, hf.1.2, hf.2.2, Bool.and_self], hK⟩
  | toZero t pop =>
      refine .inl ⟨pop.state.symm, ?_⟩
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · simp only [SFunc.preExec, Bool.and_eq_true] at hf
        exact .inl ⟨hf.2, hK⟩
      · simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons,
          Bool.and_eq_true] at hf
        exact .inr ⟨by simp only [SFunc.silentIn, hf.1, hf.2.2, Bool.and_self], hK⟩
  | toSucc t w hw hk pop =>
      refine .inl ⟨pop.state.symm, ?_⟩
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · simp only [SFunc.preExec, Bool.and_eq_true, decide_eq_true_eq] at hf
        exact .inl ⟨PreExecSet.lookup hW hf.1 hk, hK⟩
      · simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons,
          Bool.and_eq_true, decide_eq_true_eq] at hf
        exact .inr ⟨SilentSet.lookup' hS hf.2.1 hk, hK⟩
  | jump t hk pop =>
      refine .inl ⟨pop.state.symm, ?_⟩
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · simp only [SFunc.preExec, decide_eq_true_eq] at hf
        exact .inl ⟨PreExecSet.lookup hW hf hk, hK⟩
      · simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, List.all_nil,
          Bool.and_true, Bool.true_and, decide_eq_true_eq] at hf
        exact .inr ⟨SilentSet.lookup' hS hf hk, hK⟩
  | @call d d' f g k K t hk pop =>
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · simp only [SFunc.preExec, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
        rcases hf with ⟨h0, hc⟩ | ⟨h1 | h1, hc⟩
        · exact .inl ⟨pop.state.symm, .inr ⟨SilentSet.lookup' hS h0 hk, .inl ⟨hc, hK⟩⟩⟩
        · refine .inl ⟨pop.state.symm, .inl ⟨PreExecSet.lookup hW h1 hk, ?_⟩⟩
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hc
          · exact hK s hs
        · refine .inr ⟨ExecFreeSet.lookup hE h1 hk, ?_⟩
          intro s hs
          rcases List.mem_cons.mp hs with rfl | hs
          · exact hc
          · exact hK s hs
      · simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons,
          Bool.and_eq_true, decide_eq_true_eq] at hf
        exact .inl ⟨pop.state.symm, .inr ⟨SilentSet.lookup' hS hf.2.1 hk,
          .inr (.inl ⟨by simp only [SFunc.silentIn, hf.1, hf.2.2, Bool.and_self], hK⟩)⟩⟩
  | @ret d d' f K t pop =>
      rcases inv with ⟨-, hK⟩ | ⟨-, hK⟩
      · exact .inr ⟨hK f List.mem_cons_self, fun s hs => hK s (List.mem_cons_of_mem _ hs)⟩
      · rcases hK with h | h | h
        · exact .inl ⟨pop.state.symm, .inl h⟩
        · exact .inl ⟨pop.state.symm, .inr h⟩
        · exact .inr h
  | pcAt hp hr =>
      refine .inl ⟨ninst_state_of_stateSilent (n := .reg .pc) rfl (hP hp), ?_⟩
      rcases inv with ⟨hf, hK⟩ | ⟨hf, hK⟩
      · exact .inl ⟨hf, hK⟩
      · exact .inr ⟨by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using hf, hK⟩

/-- **The world at the first external instruction.**  A reach from a before-phase configuration
to an external instruction arrives with the starting world state, at an instruction `okx`
accepts. -/
theorem Reach.preExec_state (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hE : ExecFreeSet fs E = true) (hS : SilentSet fs W0 = true)
    (hW : PreExecSet fs okx W0 W E = true) {a T : Conf} (reach : Reach P fs sevm a T)
    (hT : AtExec T) (inv : PreInv okx W0 W E a.f a.K) :
    T.d.state = a.d.state ∧ ∃ x f', T.f = .next (.exec x) f' ∧ okx x = true := by
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      obtain ⟨x, f', hx⟩ := hT
      refine ⟨rfl, x, f', hx, ?_⟩
      rcases inv with ⟨hf, -⟩ | ⟨hf, -⟩
      · rw [hx] at hf
        simp only [SFunc.preExec, Bool.and_eq_true] at hf
        exact hf.1
      · rw [hx] at hf
        simp only [SFunc.silentIn, SFunc.silent, Ninst.stateSilent, Bool.false_and,
          Bool.false_eq_true] at hf
  | @head a b step rest ih =>
      rcases step.preExec hP hE hS hW inv with ⟨hs, inv'⟩ | ⟨hf, hK⟩
      · obtain ⟨hT', rest'⟩ := ih inv'
        exact ⟨hT'.trans hs, rest'⟩
      · obtain ⟨d, f, K⟩ := b
        exact (Reach.false_of_execFree hE rest hT hf hK).elim

end PreExec

end Blanc.Lift
