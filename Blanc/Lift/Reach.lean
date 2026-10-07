import Blanc.Lift.Basic

/-!
# Stateful prefixes of synthetic runs

`SFunc.RunP` relates a synthetic tree to the *outcome* of a whole run; no
statement about it can name an intermediate machine state.  This module is the
prefix form with state: a configuration `Conf` is the machine state, the tree
still to run, and the pending `callNext` continuation trees (innermost first);
`ConfStep` is one synthetic step, with exactly the premise of the matching
`SFunc.RunP` constructor; `Reach` is its reflexive-transitive closure.

* `Reach.split`: a reach that starts inside a callee either stays inside it (a
  reach in the truncated stack) or the callee returns, which is an ordinary
  big-step `SFunc.RunP … (.returned d)` of the callee followed by a reach from the
  continuation.  So a walk over a prefix reuses the big-step callee specs.
* `AtExec` names a target configuration about to run an external instruction,
  and the inversions `Reach.next`, `Reach.exec`, `Reach.call` walk a prefix to
  such a target.

`Blanc/Lift/Cursor.lean` places every same-frame node of a certified frame at
such a reach (`reach_of_parentPrefix`).
-/

namespace Blanc.Lift

open Jaune

/-- A synthetic configuration: state, remaining tree, pending continuations. -/
structure Conf : Type where
  d : Devm
  f : SFunc
  K : List SFunc

/-- One synthetic step, with the premise of the matching `SFunc.RunP` rule. -/
inductive ConfStep (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc) (sevm : Sevm) :
    Conf → Conf → Prop
  | next {d d' : Devm} {n : Ninst} {f : SFunc} {K : List SFunc} :
    P sevm d n d' → ConfStep P fs sevm ⟨d, .next n f, K⟩ ⟨d', f, K⟩
  | dest {d d' : Devm} {f : SFunc} {K : List SFunc} :
    Devm.Burn d d' → ConfStep P fs sevm ⟨d, .dest f, K⟩ ⟨d', f, K⟩
  | zero {d d' : Devm} {f g : SFunc} {K : List SFunc} (t : B256) :
    Devm.PopBurn [t, 0] d d' → ConfStep P fs sevm ⟨d, .branch f g, K⟩ ⟨d', f, K⟩
  | succ {d d' : Devm} {f g : SFunc} {K : List SFunc} (t w : B256) :
    w ≠ 0 → Devm.PopBurn [t, w] d d' → ConfStep P fs sevm ⟨d, .branch f g, K⟩ ⟨d', g, K⟩
  | toZero {d d' : Devm} {f : SFunc} {k : Nat} {K : List SFunc} (t : B256) :
    Devm.PopBurn [t, 0] d d' → ConfStep P fs sevm ⟨d, .branchTo f k, K⟩ ⟨d', f, K⟩
  | toSucc {d d' : Devm} {f g : SFunc} {k : Nat} {K : List SFunc} (t w : B256) :
    w ≠ 0 → fs[k]? = some g → Devm.PopBurn [t, w] d d' →
    ConfStep P fs sevm ⟨d, .branchTo f k, K⟩ ⟨d', g, K⟩
  | jump {d d' : Devm} {g : SFunc} {k : Nat} {K : List SFunc} (t : B256) :
    fs[k]? = some g → Devm.PopBurn [t] d d' → ConfStep P fs sevm ⟨d, .jump k, K⟩ ⟨d', g, K⟩
  | call {d d' : Devm} {f g : SFunc} {k : Nat} {K : List SFunc} (t : B256) :
    fs[k]? = some g → Devm.PopBurn [t] d d' →
    ConfStep P fs sevm ⟨d, .callNext k f, K⟩ ⟨d', g, f :: K⟩
  | ret {d d' : Devm} {f : SFunc} {K : List SFunc} (t : B256) :
    Devm.PopBurn [t] d d' → ConfStep P fs sevm ⟨d, .ret, f :: K⟩ ⟨d', f, K⟩
  | pcAt {d d' : Devm} {p : Nat} {f : SFunc} {K : List SFunc} :
    P sevm d (.reg .pc) d' → Ninst.StepRun p sevm d (.reg .pc) .none (.ok d') →
    ConfStep P fs sevm ⟨d, .pcAt p f, K⟩ ⟨d', f, K⟩

/-- Reachability of synthetic configurations. -/
abbrev Reach (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc) (sevm : Sevm) :
    Conf → Conf → Prop :=
  Relation.ReflTransGen (ConfStep P fs sevm)

/-- The target configuration is about to run an external instruction. -/
def AtExec (T : Conf) : Prop := ∃ x f', T.f = .next (.exec x) f'

/-- Append `L` below a configuration's pending continuations. -/
def Conf.below (c : Conf) (L : List SFunc) : Conf := ⟨c.d, c.f, c.K ++ L⟩

theorem AtExec.below {T : Conf} {L : List SFunc} : AtExec (T.below L) ↔ AtExec T :=
  Iff.rfl

variable {P Q : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

theorem ConfStep.mono (hPQ : ∀ {s d n d'}, P s d n d' → Q s d n d') {a b : Conf}
    (h : ConfStep P fs sevm a b) : ConfStep Q fs sevm a b := by
  cases h with
  | next h => exact .next (hPQ h)
  | dest h => exact .dest h
  | zero t h => exact .zero t h
  | succ t w hw h => exact .succ t w hw h
  | toZero t h => exact .toZero t h
  | toSucc t w hw hk h => exact .toSucc t w hw hk h
  | jump t hk h => exact .jump t hk h
  | call t hk h => exact .call t hk h
  | ret t h => exact .ret t h
  | pcAt h hr => exact .pcAt (hPQ h) hr

theorem Reach.mono (hPQ : ∀ {s d n d'}, P s d n d' → Q s d n d') {a b : Conf}
    (h : Reach P fs sevm a b) : Reach Q fs sevm a b := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step.mono hPQ)

/-- A step does not look below the top of the continuation stack. -/
theorem ConfStep.below {a b : Conf} (L : List SFunc) (h : ConfStep P fs sevm a b) :
    ConfStep P fs sevm (a.below L) (b.below L) := by
  cases h with
  | next h => exact .next h
  | dest h => exact .dest h
  | zero t h => exact .zero t h
  | succ t w hw h => exact .succ t w hw h
  | toZero t h => exact .toZero t h
  | toSucc t w hw hk h => exact .toSucc t w hw hk h
  | jump t hk h => exact .jump t hk h
  | call t hk h => exact .call t hk h
  | ret t h => exact .ret t h
  | pcAt h hr => exact .pcAt h hr

theorem Reach.below {a b : Conf} (L : List SFunc) (h : Reach P fs sevm a b) :
    Reach P fs sevm (a.below L) (b.below L) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step.below L)

/-- A step from a configuration whose stack ends in `L` either is a step of the
truncated configuration, or pops the top of `L` from an empty truncated stack. -/
theorem ConfStep.of_below {d : Devm} {f : SFunc} {S L : List SFunc} {c : Conf}
    (h : ConfStep P fs sevm ⟨d, f, S ++ L⟩ c) :
    (∃ c', ConfStep P fs sevm ⟨d, f, S⟩ c' ∧ c = c'.below L) ∨
      (S = [] ∧ f = .ret ∧ ∃ t f₀ L₀, L = f₀ :: L₀ ∧ Devm.PopBurn [t] d c.d ∧
        c = ⟨c.d, f₀, L₀⟩) := by
  generalize ha : (⟨d, f, S ++ L⟩ : Conf) = a at h
  cases h with
  | next h => cases ha; exact .inl ⟨_, .next h, rfl⟩
  | dest h => cases ha; exact .inl ⟨_, .dest h, rfl⟩
  | zero t h => cases ha; exact .inl ⟨_, .zero t h, rfl⟩
  | succ t w hw h => cases ha; exact .inl ⟨_, .succ t w hw h, rfl⟩
  | toZero t h => cases ha; exact .inl ⟨_, .toZero t h, rfl⟩
  | toSucc t w hw hk h => cases ha; exact .inl ⟨_, .toSucc t w hw hk h, rfl⟩
  | jump t hk h => cases ha; exact .inl ⟨_, .jump t hk h, rfl⟩
  | call t hk h =>
      cases ha
      exact .inl ⟨⟨_, _, _ :: S⟩, .call t hk h, rfl⟩
  | pcAt h hr => cases ha; exact .inl ⟨_, .pcAt h hr, rfl⟩
  | @ret d₀ d' f₀ K t h =>
      injection ha with hd hf hK
      subst hd hf
      cases S with
      | nil =>
          simp only [List.nil_append] at hK
          exact .inr ⟨rfl, rfl, t, f₀, K, hK, h, rfl⟩
      | cons s S =>
          simp only [List.cons_append, List.cons.injEq] at hK
          obtain ⟨rfl, rfl⟩ := hK
          exact .inl ⟨_, .ret t h, rfl⟩

/-! ## Returning callees are big-step runs -/

/-- Run `g` from `d` to its return, then each pending continuation in `S`
in order to its return; the last return leaves `d'`. -/
def RunPS (P : Sevm → Devm → Ninst → Devm → Prop) (fs : List SFunc) (sevm : Sevm) :
    SFunc → List SFunc → Devm → Devm → Prop
  | g, [], d, d' => SFunc.RunP P fs sevm d g (.returned d')
  | g, s :: S, d, d' => ∃ d₁, SFunc.RunP P fs sevm d g (.returned d₁) ∧ RunPS P fs sevm s S d₁ d'

theorem RunPS.of_head {g g₁ : SFunc} {d d₁ : Devm} {S : List SFunc} {d'' : Devm}
    (h : ∀ {e}, SFunc.RunP P fs sevm d₁ g₁ (.returned e) → SFunc.RunP P fs sevm d g (.returned e))
    (run : RunPS P fs sevm g₁ S d₁ d'') : RunPS P fs sevm g S d d'' := by
  cases S with
  | nil => exact h run
  | cons s S =>
      obtain ⟨e, r, rest⟩ := run
      exact ⟨e, h r, rest⟩

theorem RunPS.callRet {k : Nat} {f g : SFunc} {S : List SFunc} {t : B256} {d d₁ d₂ d'' : Devm}
    (hk : fs[k]? = some g) (pop : Devm.PopBurn [t] d d₁)
    (callee : SFunc.RunP P fs sevm d₁ g (.returned d₂)) (rest : RunPS P fs sevm f S d₂ d'') :
    RunPS P fs sevm (.callNext k f) S d d'' := by
  cases S with
  | nil => exact SFunc.RunP.callRet t hk pop callee rest
  | cons s S =>
      obtain ⟨e, r, rest⟩ := rest
      exact ⟨e, SFunc.RunP.callRet t hk pop callee r, rest⟩

/-- A step taken inside the truncated stack prepends to a run to the return. -/
theorem RunPS.back {d d₁ d'' : Devm} {g g₁ : SFunc} {S S₁ : List SFunc}
    (step : ConfStep P fs sevm ⟨d, g, S⟩ ⟨d₁, g₁, S₁⟩) (run : RunPS P fs sevm g₁ S₁ d₁ d'') :
    RunPS P fs sevm g S d d'' := by
  generalize ha : (⟨d, g, S⟩ : Conf) = a at step
  generalize hb : (⟨d₁, g₁, S₁⟩ : Conf) = b at step
  cases step with
  | next h => cases ha; cases hb; exact RunPS.of_head (fun r => .next h r) run
  | dest h => cases ha; cases hb; exact RunPS.of_head (fun r => .dest h r) run
  | zero t h => cases ha; cases hb; exact RunPS.of_head (fun r => .zero t h r) run
  | succ t w hw h => cases ha; cases hb; exact RunPS.of_head (fun r => .succ t w hw h r) run
  | toZero t h => cases ha; cases hb; exact RunPS.of_head (fun r => .toZero t h r) run
  | toSucc t w hw hk h =>
      cases ha; cases hb; exact RunPS.of_head (fun r => .toSucc t w hw hk h r) run
  | jump t hk h => cases ha; cases hb; exact RunPS.of_head (fun r => .jump t hk h r) run
  | pcAt h hr => cases ha; cases hb; exact RunPS.of_head (fun r => .pcAt h hr r) run
  | call t hk h =>
      cases ha; cases hb
      obtain ⟨e, callee, rest⟩ := run
      exact RunPS.callRet hk h callee rest
  | ret t h =>
      cases ha; cases hb
      exact ⟨_, .ret t h, run⟩

/-- **Split a reach at a callee's return.**  A reach from a configuration whose
stack ends in `f :: K` either stays above `f :: K` (a reach of the truncated
configuration) or first returns through `f`: the truncated part is then a
big-step run to the return (`RunPS`), followed by a reach from `f`. -/
theorem Reach.split {f : SFunc} {K : List SFunc} {T : Conf} :
    ∀ {a : Conf}, Reach P fs sevm a T → ∀ {d g S}, a = ⟨d, g, S ++ f :: K⟩ →
      (∃ T', Reach P fs sevm ⟨d, g, S⟩ T' ∧ T = T'.below (f :: K)) ∨
        ∃ d'', RunPS P fs sevm g S d d'' ∧ Reach P fs sevm ⟨d'', f, K⟩ T := by
  intro a h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro d g S ha
      exact .inl ⟨⟨d, g, S⟩, .refl, ha⟩
  | head step rest ih =>
      intro d g S ha
      subst ha
      rcases ConfStep.of_below step with ⟨c', step', rfl⟩ | ⟨rfl, rfl, t, f₀, L₀, hL, pop, hc⟩
      · rcases ih (d := c'.d) (g := c'.f) (S := c'.K) rfl with ⟨T', r', hT⟩ | ⟨d'', run, r⟩
        · exact .inl ⟨T', .head step' r', hT⟩
        · exact .inr ⟨d'', RunPS.back step' run, r⟩
      · injection hL with h₁ h₂
        subst h₁ h₂
        rw [hc] at rest
        exact .inr ⟨_, SFunc.RunP.ret t pop, rest⟩

/-! ## Walking a reach to an external-instruction target -/

theorem Reach.next {d : Devm} {n : Ninst} {f : SFunc} {K : List SFunc} {T : Conf}
    (hn : ∀ x, n ≠ .exec x) (h : Reach P fs sevm ⟨d, .next n f, K⟩ T) (hT : AtExec T) :
    ∃ d', P sevm d n d' ∧ Reach P fs sevm ⟨d', f, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    injection hx with hx
    exact (hn x hx).elim
  · cases step with
    | next hp => exact ⟨_, hp, rest⟩

/-- At an external instruction, the reach stops there or takes the step. -/
theorem Reach.exec {d : Devm} {x : Xinst} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .next (.exec x) f, K⟩ T) :
    T = ⟨d, .next (.exec x) f, K⟩ ∨
      ∃ d', P sevm d (.exec x) d' ∧ Reach P fs sevm ⟨d', f, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · exact .inl rfl
  · cases step with
    | next hp => exact .inr ⟨_, hp, rest⟩

theorem Reach.dest {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .dest f, K⟩ T) (hT : AtExec T) :
    ∃ d', Devm.Burn d d' ∧ Reach P fs sevm ⟨d', f, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step with
    | dest hb => exact ⟨_, hb, rest⟩

theorem Reach.branch {d : Devm} {f g : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .branch f g, K⟩ T) (hT : AtExec T) :
    (∃ t d', Devm.PopBurn [t, 0] d d' ∧ Reach P fs sevm ⟨d', f, K⟩ T) ∨
      (∃ t w d', w ≠ 0 ∧ Devm.PopBurn [t, w] d d' ∧ Reach P fs sevm ⟨d', g, K⟩ T) := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step with
    | zero t hp => exact .inl ⟨t, _, hp, rest⟩
    | succ t w hw hp => exact .inr ⟨t, w, _, hw, hp, rest⟩

theorem Reach.branchTo {d : Devm} {f : SFunc} {k : Nat} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .branchTo f k, K⟩ T) (hT : AtExec T) :
    (∃ t d', Devm.PopBurn [t, 0] d d' ∧ Reach P fs sevm ⟨d', f, K⟩ T) ∨
      (∃ t w g d', w ≠ 0 ∧ fs[k]? = some g ∧ Devm.PopBurn [t, w] d d' ∧
        Reach P fs sevm ⟨d', g, K⟩ T) := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step with
    | toZero t hp => exact .inl ⟨t, _, hp, rest⟩
    | toSucc t w hw hk hp => exact .inr ⟨t, w, _, _, hw, hk, hp, rest⟩

theorem Reach.jump {d : Devm} {k : Nat} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .jump k, K⟩ T) (hT : AtExec T) :
    ∃ t g d', fs[k]? = some g ∧ Devm.PopBurn [t] d d' ∧ Reach P fs sevm ⟨d', g, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step with
    | jump t hk hp => exact ⟨t, _, _, hk, hp, rest⟩

/-- **Through a `callNext`.**  Either the target lies inside the callee (a reach
of the callee from an empty stack, re-based below `f :: K`), or the callee
returns (a big-step run) and the target is reached from the continuation. -/
theorem Reach.call {d : Devm} {k : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .callNext k f, K⟩ T) (hT : AtExec T) :
    ∃ t g d', fs[k]? = some g ∧ Devm.PopBurn [t] d d' ∧
      ((∃ T', Reach P fs sevm ⟨d', g, []⟩ T' ∧ T = T'.below (f :: K)) ∨
        ∃ d'', SFunc.RunP P fs sevm d' g (.returned d'') ∧ Reach P fs sevm ⟨d'', f, K⟩ T) := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step with
    | call t hk hp =>
        exact ⟨t, _, _, hk, hp, Reach.split (S := []) rest rfl⟩

theorem Reach.pcAt {d : Devm} {p : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .pcAt p f, K⟩ T) (hT : AtExec T) :
    ∃ d', P sevm d (.reg .pc) d' ∧ Ninst.StepRun p sevm d (.reg .pc) .none (.ok d') ∧
      Reach P fs sevm ⟨d', f, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step with
    | pcAt hp hr => exact ⟨_, hp, hr, rest⟩

/-- No reach leaves a halting instruction. -/
theorem Reach.not_last {d : Devm} {l : Linst} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .last l, K⟩ T) (hT : AtExec T) : False := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step

/-- An empty-stack return has no step. -/
theorem Reach.not_ret_nil {d : Devm} {T : Conf}
    (h : Reach P fs sevm ⟨d, .ret, []⟩ T) (hT : AtExec T) : False := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨x, f', hx⟩ := hT
    cases hx
  · cases step

end Blanc.Lift
