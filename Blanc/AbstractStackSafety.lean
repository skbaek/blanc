import Blanc.CompiledStackSafety

/-!
A contract-neutral full-stack abstraction and forward primitive safety.
An arbitrary word forgets value only; stack length is always exact. Error
arms remain part of the semantic judgment, so no adequate-gas or successful
execution premise is required. This is the primitive layer for a later
checked decoded-instruction table, not that table's soundness theorem.
-/

namespace Blanc.AbstractStackSafety

open Jaune CompiledStackSafety

abbrev Pattern := List (Option B256)

/-- An exact literal or an arbitrary word at one operand position. -/
def WordMatches (word : Option B256) (value : B256) : Prop :=
  word = none ∨ word = some value

/-- Match the complete operand stack, not merely a prefix. -/
def Matches : Pattern → Stack → Prop
  | [], [] => True
  | word :: words, value :: values => WordMatches word value ∧ Matches words values
  | _, _ => False

@[simp] theorem matches_nil : Matches [] [] := True.intro

@[simp] theorem matches_cons {word : Option B256} {words : Pattern}
    {value : B256} {values : Stack} :
    Matches (word :: words) (value :: values) ↔
      WordMatches word value ∧ Matches words values := Iff.rfl

/-- An exact abstract word determines the matching concrete word. -/
theorem WordMatches.eq_of_some {expected actual : B256}
    (matched : WordMatches (some expected) actual) : actual = expected := by
  rcases matched with impossible | exact
  · cases impossible
  · exact Option.some.inj exact |>.symm

theorem Matches.length {words : Pattern} {values : Stack}
    (matched : Matches words values) : values.length = words.length := by
  induction words generalizing values with
  | nil => cases values <;> simp_all [Matches]
  | cons word words ih =>
      cases values with
      | nil => exact False.elim matched
      | cons value values =>
          obtain ⟨_, rest⟩ := matched
          simp only [List.length_cons, ih rest]

theorem Matches.push_exact {words : Pattern} {values : Stack}
    (matched : Matches words values) (value : B256) :
    Matches (some value :: words) (value :: values) :=
  ⟨Or.inr rfl, matched⟩

theorem Matches.push_any {words : Pattern} {values : Stack}
    (matched : Matches words values) (value : B256) :
    Matches (none :: words) (value :: values) :=
  ⟨Or.inl rfl, matched⟩

/-- Forward postcondition together with exclusion of locally generated
operand-stack faults on every error arm. Other errors remain allowed. -/
def SafeResult {α : Type} (postcondition : α → Prop) :
    Except (EvmError × Devm) α → Prop
  | .ok value => postcondition value
  | .error (error, _) => ¬ StackFault error

theorem SafeResult.bind {α β : Type} {p : α → Prop} {q : β → Prop}
    {action : Except (EvmError × Devm) α}
    {next : α → Except (EvmError × Devm) β}
    (safe : SafeResult p action)
    (continuation : ∀ value, p value → SafeResult q (next value)) :
    SafeResult q (action >>= next) := by
  cases action with
  | error error => exact safe
  | ok value => exact continuation value safe

/-- Gas failure is permitted; every successful charge preserves the exact
stack abstraction without requiring a gas lower bound. -/
theorem chargeGas_safe (cost : Nat) {pre : Devm} {words : Pattern}
    (matched : Matches words pre.stack) :
    SafeResult (fun post => Matches words post.stack) (chargeGas cost pre) := by
  rw [chargeGas_def]
  split
  · simp [SafeResult, StackFault]
  · exact matched

/-- Actual bounded push, including its overflow check. -/
theorem push_safe (value : B256) {pre : Devm} {words : Pattern}
    (matched : Matches words pre.stack) (room : words.length < 1024) :
    SafeResult (fun post => Matches (some value :: words) post.stack)
      (pre.push value) := by
  have bound : pre.stack.length < 1024 := matched.length ▸ room
  rw [Devm.push_def]
  simp only [Except.assert, if_pos bound, bind, Except.bind, SafeResult,
    Devm.stack_setMach]
  exact matched.push_exact value

/-- Actual pop, deriving its head and remaining full stack rather than
assuming a successful pop result. -/
theorem pop_safe {pre : Devm} {word : Option B256} {words : Pattern}
    (matched : Matches (word :: words) pre.stack) :
    SafeResult (fun result => WordMatches word result.1 ∧
      Matches words result.2.stack) pre.pop := by
  rw [Devm.pop_def]
  cases stackEq : pre.stack with
  | nil => simp [stackEq, Matches] at matched
  | cons value values =>
      simpa only [stackEq, SafeResult, Devm.stack_setMach, Matches] using matched

/-- The semantic judgment plugs directly into an ordinary decoded-step
continuation or error, with no successful-outcome restriction. -/
theorem step_ofExecution_safe {pc : Nat} {invariant : Nat → Devm → Prop}
    {action : Execution}
    (safe : SafeResult (invariant pc) action) :
    StepSafe invariant (Step.ofExecution pc action) := by
  cases action with
  | ok post => exact safe
  | error error =>
      rcases error with ⟨error, post⟩
      intro other actual equality
      cases equality
      exact safe

/-- The semantic judgment also plugs into a control-flow step, retaining the
actual successor counter supplied by the jump implementation. -/
theorem step_ofJump_safe {invariant : Nat → Devm → Prop}
    {action : Except (EvmError × Devm) (Nat × Devm)}
    (safe : SafeResult (fun result => invariant result.1 result.2) action) :
    StepSafe invariant (Step.ofJump action) := by
  cases action with
  | ok result => exact safe
  | error error =>
      rcases error with ⟨error, post⟩
      intro other actual equality
      cases equality
      exact safe

/-- Weaken only the success postcondition; error safety is retained. -/
theorem SafeResult.mono {α : Type} {p q : α → Prop}
    {action : Except (EvmError × Devm) α}
    (safe : SafeResult p action) (weaken : ∀ value, p value → q value) :
    SafeResult q action := by
  cases action with
  | error error => exact safe
  | ok value => exact weaken value safe

/-- Forget only the pushed value, preserving the exact remaining stack. -/
theorem Matches.forget_head {value : B256} {words : Pattern} {values : Stack}
    (matched : Matches (some value :: words) values) :
    Matches (none :: words) values := by
  cases values with
  | nil => exact False.elim matched
  | cons head tail => exact ⟨Or.inl rfl, matched.2⟩

theorem pushItem_safe (value : B256) (cost : Nat)
    {pre : Devm} {words : Pattern}
    (matched : Matches words pre.stack) (room : words.length < 1024) :
    SafeResult (fun post => Matches (some value :: words) post.stack)
      (pushItem value cost pre) := by
  rw [pushItem_def]
  exact (chargeGas_safe cost matched).bind
    (fun _ charged => push_safe value charged room)

/-- Arbitrary word arithmetic is safe at the operand level even when gas
runs out; this theorem does not assert absence of arithmetic wrap. -/
theorem applyUnary_safe (operation : B256 → B256) (cost : Nat)
    {pre : Devm} {word : Option B256} {words : Pattern}
    (matched : Matches (word :: words) pre.stack) (room : words.length < 1024) :
    SafeResult (fun post => Matches (none :: words) post.stack)
      (applyUnary operation cost pre) := by
  rw [applyUnary_def]
  apply (pop_safe matched).bind
  intro result popped
  exact (pushItem_safe (operation result.1) cost popped.2 room).mono
    (fun _ pushed => pushed.forget_head)

theorem applyBinary_safe (operation : B256 → B256 → B256) (cost : Nat)
    {pre : Devm} {first second : Option B256} {words : Pattern}
    (matched : Matches (first :: second :: words) pre.stack)
    (room : words.length < 1024) :
    SafeResult (fun post => Matches (none :: words) post.stack)
      (applyBinary operation cost pre) := by
  rw [applyBinary_def]
  apply (pop_safe matched).bind
  intro firstResult firstPop
  apply (pop_safe firstPop.2).bind
  intro secondResult secondPop
  exact (pushItem_safe (operation firstResult.1 secondResult.1) cost
    secondPop.2 room).mono (fun _ pushed => pushed.forget_head)

/-- Actual Ninst PUSH step, including gas failure and exact next PC. -/
theorem ninst_push_safe {evm : Evm} {bytes : Bytes} {fits : bytes.length ≤ 32}
    {words : Pattern} (matched : Matches words evm.dyna.stack)
    (room : words.length < 1024) :
    StepSafe (fun pc post => pc = evm.pc + (Ninst.push bytes fits).size ∧
      Matches (some bytes.toB256 :: words) post.stack)
      (Ninst.step evm (.push bytes fits)) := by
  unfold Ninst.step
  apply step_ofExecution_safe
  exact ((chargeGas_safe _ matched).bind
    (fun _ charged => push_safe bytes.toB256 charged room)).mono
    (fun _ pushed => ⟨rfl, pushed⟩)

/-- A checked abstract lookup exposes a real operand, including exact
literal information when present. -/
theorem Matches.getElem? {words : Pattern} {values : Stack}
    (matched : Matches words values) {index : Nat} {word : Option B256}
    (lookup : words[index]? = some word) :
    ∃ value, values[index]? = some value ∧ WordMatches word value := by
  induction words generalizing values index with
  | nil => simp at lookup
  | cons head words ih =>
      cases values with
      | nil => exact False.elim matched
      | cons value values =>
          obtain ⟨first, rest⟩ := matched
          cases index with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
              subst word
              exact ⟨value, rfl, first⟩
          | succ index =>
              exact ih rest lookup

/-- Overwriting corresponding cells preserves full-stack matching. -/
theorem Matches.set {words : Pattern} {values : Stack}
    (matched : Matches words values) (index : Nat)
    {word : Option B256} {value : B256} (head : WordMatches word value) :
    Matches (words.set index word) (values.set index value) := by
  induction words generalizing values index with
  | nil => cases values <;> simp_all [Matches]
  | cons first words ih =>
      cases values with
      | nil => exact False.elim matched
      | cons actual values =>
          obtain ⟨firstMatch, rest⟩ := matched
          cases index with
          | zero => exact ⟨head, rest⟩
          | succ index => exact ⟨firstMatch, ih rest index⟩

/-- Exact-index DUP, through actual charge/lookup/push error arms. -/
theorem dup_safe {evm : Evm} {words : Pattern} {index : Fin 16}
    {word : Option B256} (matched : Matches words evm.dyna.stack)
    (lookup : words[index.val]? = some word) (room : words.length < 1024) :
    SafeResult (fun post => Matches (word :: words) post.stack)
      (Rinst.run evm (.dup index)) := by
  unfold Rinst.run Rinst.runCore
  apply (chargeGas_safe _ matched).bind
  intro charged chargedMatch
  obtain ⟨value, actualLookup, valueMatch⟩ := chargedMatch.getElem? lookup
  rw [Fin.getElem?_fin, actualLookup]
  apply (push_safe value chargedMatch room).mono
  intro post pushed
  cases stackEq : post.stack with
  | nil => simp [stackEq, Matches] at pushed
  | cons actual tail =>
      rw [stackEq] at pushed
      obtain ⟨head, rest⟩ := pushed
      have equal : value = actual := by simpa [WordMatches] using head
      subst actual
      exact ⟨valueMatch, rest⟩

/-- A checked abstract SWAP witnesses the actual list operation and its
entire resulting pattern. -/
theorem Matches.swap {words output : Pattern} {values : Stack}
    (matched : Matches words values) {index : Nat}
    (checked : Jaune.List.swap words index = some output) :
    ∃ actual, Jaune.List.swap values index = some actual ∧ Matches output actual := by
  cases words with
  | nil => simp [Jaune.List.swap] at checked
  | cons head words =>
      cases values with
      | nil => exact False.elim matched
      | cons value values =>
          obtain ⟨headMatch, rest⟩ := matched
          cases lookup : words[index]? with
          | none => simp [Jaune.List.swap, lookup] at checked
          | some selected =>
              obtain ⟨actual, actualLookup, selectedMatch⟩ := rest.getElem? lookup
              simp only [Jaune.List.swap, lookup, bind, Option.bind,
                Option.some.injEq] at checked
              subst output
              refine ⟨actual :: values.set index value, ?_,
                selectedMatch, rest.set index headMatch⟩
              simp [Jaune.List.swap, actualLookup]

/-- Actual gas-charged SWAP, including the otherwise possible underflow arm. -/
theorem swap_safe {evm : Evm} {words output : Pattern} {index : Fin 16}
    (matched : Matches words evm.dyna.stack)
    (checked : Jaune.List.swap words index.val = some output) :
    SafeResult (fun post => Matches output post.stack)
      (Rinst.run evm (.swap index)) := by
  unfold Rinst.run Rinst.runCore
  apply (chargeGas_safe _ matched).bind
  intro charged chargedMatch
  obtain ⟨actual, actualSwap, outputMatch⟩ := chargedMatch.swap checked
  rw [actualSwap]
  exact outputMatch

/-- A CALL continuation matches the complete parent stack plus either
status word. Fatal child errors keep the shared inherited-error provenance. -/
theorem call_resume_safe {parent : Devm} {words : Pattern} (pc oi os : Nat)
    (matched : Matches words parent.stack) (room : words.length < 1024) :
    ResumeSafe (fun _ post => Matches (none :: words) post.stack)
      pc (.call parent oi os) := by
  apply resume_call_safe parent oi os (matched.length ▸ room)
  intro post flag _ stack
  rw [stack]
  exact matched.push_any flag

end Blanc.AbstractStackSafety
