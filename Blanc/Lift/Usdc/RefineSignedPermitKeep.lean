import Blanc.Lift.ReachWalk
import Blanc.Lift.Silent
import Blanc.Lift.ShuffleSkip

/-!
# A reach to the first external instruction of a state-keeping region

A node-clause fact (`ImplStepLaw`) is a statement about the machine at an external-instruction
node of a frame's own chain; `reach_of_parentPrefix` (`Blanc/Lift/Cursor.lean`) places that node at
a `Reach` of the certificate.  When the code from some configuration up to the external instruction
writes no state, the node's world state is that configuration's, whatever the stack, the memory and
the number of loop iterations in between.

`SFunc.keepTo xok W Sil E` says a tree runs state-silent instructions, gotos into the entries `W`
(whose trees are of the same kind, `KeepSet`), internal calls of state-silent entries `Sil`
(`SilentSet`) with a continuation of the same kind, internal calls of `W` entries whose
continuation is exec-free in `E` (`ExecFreeSet`), returns, halts, and external instructions `x`
with `xok x` after which it is exec-free in `E`.  `Reach.keepTo`: a reach from such a tree, over
exec-free pending continuations, to an external instruction keeps the world state and stands at an
instruction accepted by `xok`.  Loops cost nothing: the argument is an induction over the reach.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- `n` is an external instruction accepted by `xok`. -/
def _root_.Jaune.Ninst.execOk (xok : Xinst → Bool) : Ninst → Bool
  | .exec x => xok x
  | _ => false

/-- A state-silent tree whose entry references lie in `Sil`. -/
def SFunc.silentIn (Sil : List Nat) (f : SFunc) : Bool := f.silent && f.refs.all (· ∈ Sil)

/-- A state-keeping region up to an accepted external instruction (see the module doc). -/
def SFunc.keepTo (xok : Xinst → Bool) (W Sil E : List Nat) : SFunc → Bool
  | .branch f g => f.keepTo xok W Sil E && g.keepTo xok W Sil E
  | .branchTo f k => decide (k ∈ W) && f.keepTo xok W Sil E
  | .last _ => true
  | .next n f => (n.stateSilent && f.keepTo xok W Sil E) || (n.execOk xok && f.execFreeIn E)
  | .dest f => f.keepTo xok W Sil E
  | .jump k => decide (k ∈ W)
  | .callNext k f =>
      (decide (k ∈ Sil) && f.keepTo xok W Sil E) || (decide (k ∈ W) && f.execFreeIn E)
  | .ret => true
  | .pcAt _ f => f.keepTo xok W Sil E
  | .undefined => true

/-- Every entry of `W` is a state-keeping region. -/
def KeepSet (fs : List SFunc) (xok : Xinst → Bool) (W Sil E : List Nat) : Bool :=
  W.all fun k => match fs[k]? with
    | some g => g.keepTo xok W Sil E
    | none => false

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

theorem KeepSet.lookup {xok : Xinst → Bool} {W Sil E : List Nat}
    (h : KeepSet fs xok W Sil E = true) {k : Nat} {g : SFunc} (hk : k ∈ W)
    (hg : fs[k]? = some g) : g.keepTo xok W Sil E = true := by
  have h' := (List.all_eq_true.mp h) k hk
  rw [hg] at h'
  exact h'

theorem SilentSet.lookupIn {Sil : List Nat} (h : SilentSet fs Sil = true) {k : Nat} {g : SFunc}
    (hk : k ∈ Sil) (hg : fs[k]? = some g) : g.silentIn Sil = true := by
  have h' := (List.all_eq_true.mp h) k hk
  rw [hg] at h'
  exact h'

/-- The invariant of `Reach.keepTo`: inside the region at the configuration's stack, or inside a
silent callee entered from it. -/
private abbrev KeepInv (xok : Xinst → Bool) (W Sil E : List Nat) (s0 : State) (a : Conf) : Prop :=
  a.d.state = s0 ∧
    ((a.f.keepTo xok W Sil E = true ∧ ∀ s ∈ a.K, s.execFreeIn E = true) ∨
      (a.f.silentIn Sil = true ∧ ∃ L g B, a.K = L ++ g :: B ∧ (∀ s ∈ L, s.silentIn Sil = true) ∧
        g.keepTo xok W Sil E = true ∧ ∀ s ∈ B, s.execFreeIn E = true))

/-- **A reach out of a state-keeping region.**  From a `keepTo` tree over exec-free pending
continuations, a reach to an external instruction keeps the world state, and the instruction is
accepted by `xok`. -/
theorem Reach.keepTo (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {xok : Xinst → Bool}
    {W Sil E : List Nat} (hW : KeepSet fs xok W Sil E = true) (hSil : SilentSet fs Sil = true)
    (hE : ExecFreeSet fs E = true) {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, f, K⟩ T) (hT : AtExec T) (hf : f.keepTo xok W Sil E = true)
    (hK : ∀ s ∈ K, s.execFreeIn E = true) :
    T.d.state = d.state ∧ ∃ x f', T.f = .next (.exec x) f' ∧ xok x = true := by
  suffices ∀ {a : Conf}, Reach P fs sevm a T → KeepInv xok W Sil E d.state a →
      T.d.state = d.state ∧ ∃ x f', T.f = .next (.exec x) f' ∧ xok x = true from
    this h ⟨rfl, .inl ⟨hf, hK⟩⟩
  intro a h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rintro ⟨hs, hA | ⟨hS, -⟩⟩
      · obtain ⟨x, f', hx⟩ := hT
        refine ⟨hs, x, f', hx, ?_⟩
        rw [hx] at hA
        have e := hA.1
        simp only [SFunc.keepTo, Ninst.stateSilent, Bool.false_and, Bool.false_or, Ninst.execOk,
          Bool.and_eq_true] at e
        exact e.1
      · obtain ⟨x, f', hx⟩ := hT
        rw [hx] at hS
        simp only [SFunc.silentIn, SFunc.silent, Ninst.stateSilent, Bool.false_and,
          Bool.false_eq_true] at hS
  | @head a b step rest ih =>
      rintro ⟨hs, hA | ⟨hS, L, g0, B, hKb, hL, hg0, hB⟩⟩
      · obtain ⟨hf, hK⟩ := hA
        cases step with
        | @next d d' n f K hp =>
            simp only [SFunc.keepTo, Bool.or_eq_true, Bool.and_eq_true] at hf
            rcases hf with ⟨hn, hf⟩ | ⟨hn, hf⟩
            · exact ih ⟨(ninst_state_of_stateSilent hn (hP hp)).trans hs, .inl ⟨hf, hK⟩⟩
            · exact (Reach.false_of_execFree hE rest hT hf hK).elim
        | dest burn => exact ih ⟨burn.state.symm.trans hs, .inl ⟨hf, hK⟩⟩
        | zero t pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨hf.1, hK⟩⟩
        | succ t w hw pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨hf.2, hK⟩⟩
        | toZero t pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨hf.2, hK⟩⟩
        | toSucc t w hw hk pop =>
            simp only [SFunc.keepTo, Bool.and_eq_true, decide_eq_true_eq] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨KeepSet.lookup hW hf.1 hk, hK⟩⟩
        | jump t hk pop =>
            simp only [SFunc.keepTo, decide_eq_true_eq] at hf
            exact ih ⟨pop.state.symm.trans hs, .inl ⟨KeepSet.lookup hW hf hk, hK⟩⟩
        | @call d d' f g k K t hk pop =>
            simp only [SFunc.keepTo, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
            rcases hf with ⟨hkS, hf⟩ | ⟨hkW, hf⟩
            · exact ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hkS hk, [], f, K, rfl,
                fun _ hm => absurd hm List.not_mem_nil, hf, hK⟩⟩
            · refine ih ⟨pop.state.symm.trans hs, .inl ⟨KeepSet.lookup hW hkW hk, fun s hm => ?_⟩⟩
              rcases List.mem_cons.mp hm with rfl | hm
              · exact hf
              · exact hK s hm
        | ret t pop =>
            exact (Reach.false_of_execFree hE rest hT (hK _ List.mem_cons_self)
              (fun s hm => hK s (List.mem_cons_of_mem _ hm))).elim
        | pcAt hp hr =>
            exact ih ⟨(ninst_state_of_stateSilent (n := .reg .pc) rfl (hP hp)).trans hs,
              .inl ⟨hf, hK⟩⟩
      · cases step with
        | @next d d' n f K hp =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, Bool.and_eq_true] at hS
            exact ih ⟨(ninst_state_of_stateSilent hS.1.1 (hP hp)).trans hs,
              .inr ⟨by simp only [SFunc.silentIn, hS.1.2, hS.2, Bool.and_self], L, g0, B, hKb, hL,
                hg0, hB⟩⟩
        | dest burn =>
            exact ih ⟨burn.state.symm.trans hs, .inr ⟨by simpa only [SFunc.silentIn, SFunc.silent,
              SFunc.refs] using hS, L, g0, B, hKb, hL, hg0, hB⟩⟩
        | zero t pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append,
              Bool.and_eq_true] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨by simp only [SFunc.silentIn, hS.1.1, hS.2.1,
              Bool.and_self], L, g0, B, hKb, hL, hg0, hB⟩⟩
        | succ t w hw pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_append,
              Bool.and_eq_true] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨by simp only [SFunc.silentIn, hS.1.2, hS.2.2,
              Bool.and_self], L, g0, B, hKb, hL, hg0, hB⟩⟩
        | toZero t pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons,
              Bool.and_eq_true] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨by simp only [SFunc.silentIn, hS.1, hS.2.2,
              Bool.and_self], L, g0, B, hKb, hL, hg0, hB⟩⟩
        | toSucc t w hw hk pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true,
              decide_eq_true_eq] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hS.2.1 hk, L, g0, B, hKb, hL,
              hg0, hB⟩⟩
        | jump t hk pop =>
            simp only [SFunc.silentIn, SFunc.refs, List.all_cons, List.all_nil, Bool.and_true,
              Bool.and_eq_true, decide_eq_true_eq] at hS
            exact ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hS.2 hk, L, g0, B, hKb, hL,
              hg0, hB⟩⟩
        | @call d d' f g k K t hk pop =>
            simp only [SFunc.silentIn, SFunc.silent, SFunc.refs, List.all_cons, Bool.and_eq_true,
              decide_eq_true_eq] at hS
            refine ih ⟨pop.state.symm.trans hs, .inr ⟨SilentSet.lookupIn hSil hS.2.1 hk, f :: L, g0, B,
              congrArg (List.cons f) hKb, fun s hm => ?_, hg0, hB⟩⟩
            rcases List.mem_cons.mp hm with rfl | hm
            · simp only [SFunc.silentIn, hS.1, hS.2.2, Bool.and_self]
            · exact hL s hm
        | @ret d d' f K t pop =>
            cases L with
            | nil =>
                simp only [List.nil_append, List.cons.injEq] at hKb
                obtain ⟨rfl, rfl⟩ := hKb
                exact ih ⟨pop.state.symm.trans hs, .inl ⟨hg0, hB⟩⟩
            | cons s L =>
                simp only [List.cons_append, List.cons.injEq] at hKb
                obtain ⟨rfl, rfl⟩ := hKb
                exact ih ⟨pop.state.symm.trans hs, .inr ⟨hL _ List.mem_cons_self, L, g0, B, rfl,
                  fun s' hm => hL s' (List.mem_cons_of_mem _ hm), hg0, hB⟩⟩
        | pcAt hp hr =>
            exact ih ⟨(ninst_state_of_stateSilent (n := .reg .pc) rfl (hP hp)).trans hs,
              .inr ⟨by simpa only [SFunc.silentIn, SFunc.silent, SFunc.refs] using hS, L, g0, B,
                hKb, hL, hg0, hB⟩⟩

end Blanc.Lift
