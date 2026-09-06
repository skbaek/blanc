import Blanc.AbstractStackSafety

/-!
Forward stack safety for concrete regular and control-flow instructions.

Each theorem unfolds the actual Jaune opcode implementation.  Successful
outcomes preserve the checked full-stack pattern and precise successor facts,
while every raw error arm excludes a locally generated stack fault.
-/

namespace Blanc.AbstractStackSafety

open Jaune CompiledStackSafety

/-- Map a successful result without losing error-arm stack safety. -/
theorem SafeResult.map {α β : Type} {p : α → Prop} {q : β → Prop}
    {action : Except (EvmError × Devm) α}
    (safe : SafeResult p action) (f : α → β)
    (forward : ∀ value, p value → q (f value)) :
    SafeResult q (f <$> action) := by
  cases action with
  | error error => exact safe
  | ok value => exact forward value safe

/-- A pure `Except.ok` step contributes no error arm, so safety of the
continuation at that value is safety of the whole bind. -/
theorem SafeResult.pure_bind {α β : Type} {q : β → Prop} (value : α)
    {next : α → Except (EvmError × Devm) β}
    (safe : SafeResult q (next value)) :
    SafeResult q (Except.ok value >>= next) := safe

/-- Forget the concrete value produced by a gas-charged push. -/
theorem pushUnknown_safe (value : B256) (cost : Nat)
    {pre : Devm} {words : Pattern}
    (matched : Matches words pre.stack) (room : words.length < 1024) :
    SafeResult (fun post => Matches (none :: words) post.stack)
      (pushItem value cost pre) :=
  (pushItem_safe value cost matched room).mono
    (fun _ pushed => pushed.forget_head)

/-- `popToNat` has the same checked stack effect as the underlying word pop. -/
theorem popToNat_safe {pre : Devm} {word : Option B256} {words : Pattern}
    (matched : Matches (word :: words) pre.stack) :
    SafeResult (fun result => Matches words result.2.stack) pre.popToNat := by
  rw [Devm.popToNat_def]
  exact (pop_safe matched).map (Prod.mapFst B256.toNat)
    (fun _ popped => popped.2)

/-- `popToAdr` has the same checked stack effect as the underlying word pop. -/
theorem popToAdr_safe {pre : Devm} {word : Option B256} {words : Pattern}
    (matched : Matches (word :: words) pre.stack) :
    SafeResult (fun result => Matches words result.2.stack) pre.popToAdr := by
  rw [Devm.popToAdr_def]
  exact (pop_safe matched).map (Prod.mapFst B256.toAdr)
    (fun _ popped => popped.2)

def unaryTransfer : Pattern → Option Pattern
  | _ :: words => some (none :: words)
  | [] => none

def binaryTransfer : Pattern → Option Pattern
  | _ :: _ :: words => some (none :: words)
  | _ => none

def dropOneTransfer : Pattern → Option Pattern
  | _ :: words => some words
  | [] => none

def dropTwoTransfer : Pattern → Option Pattern
  | _ :: _ :: words => some words
  | _ => none

theorem applyUnary_transfer_safe (operation : B256 → B256) (cost : Nat)
    {pre : Devm} {input output : Pattern}
    (matched : Matches input pre.stack) (bound : input.length ≤ 8)
    (checked : unaryTransfer input = some output) :
    SafeResult (fun post => Matches output post.stack)
      (applyUnary operation cost pre) := by
  cases input with
  | nil => simp [unaryTransfer] at checked
  | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked
      subst output
      have room : words.length < 1024 := by
        simp only [List.length_cons] at bound
        omega
      exact applyUnary_safe operation cost matched room

theorem applyBinary_transfer_safe
    (operation : B256 → B256 → B256) (cost : Nat)
    {pre : Devm} {input output : Pattern}
    (matched : Matches input pre.stack) (bound : input.length ≤ 8)
    (checked : binaryTransfer input = some output) :
    SafeResult (fun post => Matches output post.stack)
      (applyBinary operation cost pre) := by
  cases input with
  | nil => simp [binaryTransfer] at checked
  | cons first rest =>
      cases rest with
      | nil => simp [binaryTransfer] at checked
      | cons second words =>
          simp only [binaryTransfer, Option.some.injEq] at checked
          subst output
          have room : words.length < 1024 := by
            simp only [List.length_cons] at bound
            omega
          exact applyBinary_safe operation cost matched room

/-- Decidable abstract stack transfer for the regular opcodes used by DRIP.
`none` rejects either an unsupported opcode or an insufficient input shape. -/
def regularTransfer : Rinst → Pattern → Option Pattern
  | .add, words => binaryTransfer words
  | .mul, words => binaryTransfer words
  | .sub, words => binaryTransfer words
  | .div, words => binaryTransfer words
  | .lt, words => binaryTransfer words
  | .gt, words => binaryTransfer words
  | .eq, words => binaryTransfer words
  | .iszero, words => unaryTransfer words
  | .and, words => binaryTransfer words
  | .shr, words => binaryTransfer words
  | .caller, words => some (none :: words)
  | .callvalue, words => some (none :: words)
  | .calldataload, words => unaryTransfer words
  | .calldatasize, words => some (none :: words)
  | .timestamp, words => some (none :: words)
  | .pop, words => dropOneTransfer words
  | .mload, words => unaryTransfer words
  | .mstore, words => dropTwoTransfer words
  | .sload, words => unaryTransfer words
  | .sstore, words => dropTwoTransfer words
  | .gas, words => some (none :: words)
  | .dup index, words =>
      match words[index]? with
      | some word => some (word :: words)
      | none => none
  | .swap index, words => Jaune.List.swap words index
  | _, _ => none

theorem Matches.of_stack_eq {words : Pattern} {pre post : Devm}
    (matched : Matches words pre.stack) (same : post.stack = pre.stack) :
    Matches words post.stack := by
  rw [same]
  exact matched

theorem Matches.memWrite {words : Pattern} {pre : Devm}
    (matched : Matches words pre.stack) (index : Nat) (value : Bytes) :
    Matches words (pre.memWrite index value).stack := by
  exact matched.of_stack_eq rfl

theorem Matches.memRead {words : Pattern} {pre : Devm}
    (matched : Matches words pre.stack) (index size : Nat) :
    Matches words (pre.memRead index size).2.stack := by
  exact matched.of_stack_eq rfl

theorem Matches.addAccessedStorageKey {words : Pattern} {pre : Devm}
    (matched : Matches words pre.stack) (address : Adr) (key : B256) :
    Matches words (Jaune.addAccessedStorageKey pre address key).stack := by
  exact matched.of_stack_eq rfl

theorem Matches.withRefundCounter {words : Pattern} {pre : Devm}
    (matched : Matches words pre.stack) (refund : Int) :
    Matches words (pre.withRefundCounter refund).stack := by
  exact matched.of_stack_eq rfl

theorem Matches.setStorVal {words : Pattern} {pre : Devm}
    (matched : Matches words pre.stack) (address : Adr) (key value : B256) :
    Matches words (pre.setStorVal address key value).stack := by
  exact matched.of_stack_eq rfl

theorem noStackFault_outOfGas :
    ¬ StackFault (.halt (.outOfGas .none)) := by
  simp [StackFault]

theorem noStackFault_writeInStaticContext :
    ¬ StackFault (.halt (.writeInStaticContext .none)) := by
  simp [StackFault]

/-- A raw `Except.assert` on any decidable proposition can only fail with the
supplied error, so it never generates a stack fault. -/
theorem assert_safe (condition : Prop) [Decidable condition]
    {error : EvmError} {pre : Devm} (notFault : ¬ StackFault error) :
    SafeResult (fun _ : Unit => True)
      (Except.assert condition (error, pre)) := by
  unfold Except.assert
  split <;> simp [SafeResult, notFault]

/-- A successful assertion exposes the proposition it checked, while its
supplied failure remains a permitted non-stack error. -/
theorem assert_true_safe (condition : Prop) [Decidable condition]
    {error : EvmError} {pre : Devm} (notFault : ¬ StackFault error) :
    SafeResult (fun _ : Unit => condition)
      (Except.assert condition (error, pre)) := by
  unfold Except.assert
  split <;> simp_all [SafeResult]

theorem assertDynamic_safe (sevm : Sevm) (pre : Devm) :
    SafeResult (fun _ : Unit => True) (assertDynamic sevm pre) := by
  unfold assertDynamic
  exact assert_safe _ noStackFault_writeInStaticContext

theorem gas_safe (pc : Nat) (sevm : Sevm) {pre : Devm} {words : Pattern}
    (matched : Matches words pre.stack) (room : words.length < 1024) :
    SafeResult (fun post => Matches (none :: words) post.stack)
      (Rinst.runCore pc pre sevm .gas) := by
  simp only [Rinst.runCore]
  apply (chargeGas_safe gBase matched).bind
  intro charged chargedMatch
  exact (push_safe charged.gasLeft.toB256 chargedMatch room).mono
    (fun _ pushed => pushed.forget_head)

theorem calldataload_safe (pc : Nat) (sevm : Sevm)
    {pre : Devm} {word : Option B256} {words : Pattern}
    (matched : Matches (word :: words) pre.stack)
    (room : words.length < 1024) :
    SafeResult (fun post => Matches (none :: words) post.stack)
      (Rinst.runCore pc pre sevm .calldataload) := by
  simp only [Rinst.runCore]
  apply (pop_safe matched).bind
  intro result popped
  apply (chargeGas_safe gVerylow popped.2).bind
  intro charged chargedMatch
  exact (push_safe
    (Bytes.toB256 (sevm.data.sliceD result.1.toNat 32 0)) chargedMatch room).mono
    (fun _ pushed => pushed.forget_head)

theorem mload_safe (pc : Nat) (sevm : Sevm)
    {pre : Devm} {word : Option B256} {words : Pattern}
    (matched : Matches (word :: words) pre.stack)
    (room : words.length < 1024) :
    SafeResult (fun post => Matches (none :: words) post.stack)
      (Rinst.runCore pc pre sevm .mload) := by
  simp only [Rinst.runCore]
  apply (popToNat_safe matched).bind
  intro result popped
  apply (chargeGas_safe (gVerylow + result.2.extCost [(result.1, 32)])
    popped).bind
  intro charged chargedMatch
  exact (push_safe (Bytes.toB256 (charged.memRead result.1 32).1)
    (chargedMatch.memRead result.1 32) room).mono
    (fun _ pushed => pushed.forget_head)

theorem mstore_safe (pc : Nat) (sevm : Sevm)
    {pre : Devm} {index value : Option B256} {words : Pattern}
    (matched : Matches (index :: value :: words) pre.stack) :
    SafeResult (fun post => Matches words post.stack)
      (Rinst.runCore pc pre sevm .mstore) := by
  simp only [Rinst.runCore]
  apply (popToNat_safe matched).bind
  intro indexResult indexPop
  apply (pop_safe indexPop).bind
  intro valueResult valuePop
  apply (chargeGas_safe
    (gVerylow + valueResult.2.extCost [(indexResult.1, 32)])
    valuePop.2).bind
  intro charged chargedMatch
  exact chargedMatch.memWrite indexResult.1 valueResult.1.toBytes

theorem sload_safe (pc : Nat) (sevm : Sevm)
    {pre : Devm} {key : Option B256} {words : Pattern}
    (matched : Matches (key :: words) pre.stack)
    (room : words.length < 1024) :
    SafeResult (fun post => Matches (none :: words) post.stack)
      (Rinst.runCore pc pre sevm .sload) := by
  simp only [Rinst.runCore]
  apply (pop_safe matched).bind
  intro result popped
  by_cases warm : (sevm.currentTarget, result.1) ∈
      result.2.accessedStorageKeys
  · simp only [warm, if_pos]
    apply (chargeGas_safe gasWarmAccess popped.2).bind
    intro charged chargedMatch
    exact (push_safe
      (charged.getStorVal sevm.currentTarget result.1) chargedMatch room).mono
      (fun _ pushed => pushed.forget_head)
  · simp only [warm]
    have accessedMatch :=
      popped.2.addAccessedStorageKey sevm.currentTarget result.1
    apply (chargeGas_safe gasColdSload accessedMatch).bind
    intro charged chargedMatch
    exact (push_safe
      (charged.getStorVal sevm.currentTarget result.1) chargedMatch room).mono
      (fun _ pushed => pushed.forget_head)

theorem sstore_safe (pc : Nat) (sevm : Sevm)
    {pre : Devm} {key value : Option B256} {words : Pattern}
    (matched : Matches (key :: value :: words) pre.stack) :
    SafeResult (fun post => Matches words post.stack)
      (Rinst.runCore pc pre sevm .sstore) := by
  simp only [Rinst.runCore]
  apply (pop_safe matched).bind
  intro keyResult keyPop
  apply (pop_safe keyPop.2).bind
  intro valueResult valuePop
  apply (assert_safe _ noStackFault_outOfGas).bind
  intro _ _
  apply SafeResult.pure_bind
  apply SafeResult.pure_bind
  apply SafeResult.pure_bind
  have keyedMatch : Matches words
      (if (sevm.currentTarget, keyResult.1) ∉
          valueResult.2.accessedStorageKeys then
        (addAccessedStorageKey valueResult.2 sevm.currentTarget keyResult.1,
          gasColdSload)
      else (valueResult.2, 0)).1.stack := by
    split
    · exact valuePop.2.addAccessedStorageKey sevm.currentTarget keyResult.1
    · exact valuePop.2
  apply (chargeGas_safe _ (keyedMatch.withRefundCounter _)).bind
  intro charged chargedMatch
  apply (assertDynamic_safe sevm charged).bind
  intro _ _
  exact chargedMatch.setStorVal sevm.currentTarget keyResult.1 valueResult.1

/-- Actual `POP`, including the initial operand check and later gas failure. -/
theorem ninst_pop_safe {evm : Evm} {word : Option B256} {words : Pattern}
    (matched : Matches (word :: words) evm.dyna.stack) :
    StepSafe (fun pc post =>
      pc = evm.pc + (Ninst.reg .pop).size ∧ Matches words post.stack)
      (Ninst.step evm (.reg .pop)) := by
  unfold Ninst.step Rinst.run
  simp only [Rinst.runCore]
  apply step_ofExecution_safe
  apply ((pop_safe matched).map
    (q := fun post => Matches words post.stack) Prod.snd
    (fun result popped => popped.2)).bind
  intro post popped
  exact (chargeGas_safe gBase popped).mono
    (fun _ charged => ⟨rfl, charged⟩)

/-- Every accepted regular transfer is sound for the actual interpreter,
including all error arms. The input bound supplies room for every push;
the successful abstract check supplies the required operands. -/
theorem regularTransfer_safe {evm : Evm} {instruction : Rinst}
    {input output : Pattern}
    (matched : Matches input evm.dyna.stack) (bound : input.length ≤ 8)
    (checked : regularTransfer instruction input = some output) :
    SafeResult (fun post => Matches output post.stack)
      (Rinst.run evm instruction) := by
  have room : input.length < 1024 := by omega
  cases instruction <;> simp only [regularTransfer] at checked
  case add | mul | sub | div | lt | gt | eq | and | shr =>
    simp only [Rinst.run, Rinst.runCore]
    exact applyBinary_transfer_safe _ _ matched bound checked
  case iszero =>
    simp only [Rinst.run, Rinst.runCore]
    exact applyUnary_transfer_safe _ _ matched bound checked
  case caller | callvalue | calldatasize | timestamp =>
    cases checked
    exact pushUnknown_safe _ _ matched room
  case gas =>
    cases checked
    exact gas_safe evm.pc evm.sta matched room
  case calldataload =>
    cases input with
    | nil => simp [unaryTransfer] at checked
    | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked
      subst output
      exact calldataload_safe evm.pc evm.sta matched (by
        simp only [List.length_cons] at room
        omega)
  case mload =>
    cases input with
    | nil => simp [unaryTransfer] at checked
    | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked
      subst output
      exact mload_safe evm.pc evm.sta matched (by
        simp only [List.length_cons] at room
        omega)
  case sload =>
    cases input with
    | nil => simp [unaryTransfer] at checked
    | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked
      subst output
      exact sload_safe evm.pc evm.sta matched (by
        simp only [List.length_cons] at room
        omega)
  case pop =>
    cases input with
    | nil => simp [dropOneTransfer] at checked
    | cons word words =>
      simp only [dropOneTransfer, Option.some.injEq] at checked
      subst output
      simp only [Rinst.run, Rinst.runCore]
      apply ((pop_safe matched).map
        (q := fun post => Matches words post.stack) Prod.snd
        (fun _ popped => popped.2)).bind
      intro post popped
      exact chargeGas_safe gBase popped
  case mstore =>
    cases input with
    | nil => simp [dropTwoTransfer] at checked
    | cons index words =>
      cases words with
      | nil => simp [dropTwoTransfer] at checked
      | cons value words =>
        simp only [dropTwoTransfer, Option.some.injEq] at checked
        subst output
        exact mstore_safe evm.pc evm.sta matched
  case sstore =>
    cases input with
    | nil => simp [dropTwoTransfer] at checked
    | cons key words =>
      cases words with
      | nil => simp [dropTwoTransfer] at checked
      | cons value words =>
        simp only [dropTwoTransfer, Option.some.injEq] at checked
        subst output
        exact sstore_safe evm.pc evm.sta matched
  case dup index =>
    cases lookup : input[index]? with
    | none => simp [lookup] at checked
    | some word =>
      simp only [lookup, Option.some.injEq] at checked
      subst output
      exact dup_safe matched (by simpa only [Fin.getElem?_fin] using lookup) room
  case swap index => exact swap_safe matched checked
  all_goals cases checked

/-- The actual regular `Ninst` step has the checked full-stack output and
the exact fall-through PC, or a non-stack error. No successful-run premise
or adequate-gas assumption is needed. -/
theorem ninst_regularTransfer_safe {evm : Evm} {instruction : Rinst}
    {input output : Pattern}
    (matched : Matches input evm.dyna.stack) (bound : input.length ≤ 8)
    (checked : regularTransfer instruction input = some output) :
    StepSafe (fun pc post => pc = evm.pc + (Ninst.reg instruction).size ∧
      Matches output post.stack) (Ninst.step evm (.reg instruction)) := by
  apply step_ofExecution_safe
  exact (regularTransfer_safe matched bound checked).mono
    (fun _ transferred => ⟨rfl, transferred⟩)

/-! ## Control-flow transfer -/

/-- Abstract transfer for `JUMP`. The destination must be exact, while the
remaining full-stack pattern is preserved. Destination validity is checked by
the actual opcode semantics and reflected in the successful postcondition. -/
def jumpTransfer : Pattern → Option (B256 × Pattern)
  | some destination :: words => some (destination, words)
  | _ => none

/-- Abstract transfer for `JUMPI`. The destination must be exact; the branch
condition may remain abstract because the theorem covers both actual arms. -/
def jumpiTransfer : Pattern → Option (B256 × Option B256 × Pattern)
  | some destination :: condition :: words =>
      some (destination, condition, words)
  | _ => none

/-- `JUMPDEST` preserves the complete operand-stack pattern. -/
def jumpdestTransfer (input : Pattern) : Option Pattern := some input

theorem noStackFault_invalidJumpDest :
    ¬ StackFault (.halt (.invalidJumpDest .none)) := by
  simp [StackFault]

/-- Universal `JUMP` transfer soundness against the actual `Jinst.run`.
An accepted transfer excludes stack underflow. On success it exposes both the
exact target and its actual `jumpable` check; gas and invalid-target failures
remain permitted non-stack errors. -/
theorem jumpTransfer_safe {evm : Evm} {input output : Pattern}
    {destination : B256}
    (matched : Matches input evm.dyna.stack)
    (checked : jumpTransfer input = some (destination, output)) :
    SafeResult (fun result =>
      result.1 = destination.toNat ∧
      jumpable evm.sta.code destination.toNat = true ∧
      Matches output result.2.stack)
      (Jinst.run evm .jump) := by
  cases input with
  | nil => simp [jumpTransfer] at checked
  | cons abstractDestination words =>
      cases abstractDestination with
      | none => simp [jumpTransfer] at checked
      | some expected =>
          simp only [jumpTransfer, Option.some.injEq, Prod.mk.injEq] at checked
          rcases checked with ⟨rfl, rfl⟩
          simp only [Jinst.run, Jinst.runCore]
          apply (pop_safe matched).bind
          intro result popped
          rcases result with ⟨actualDestination, afterPop⟩
          have destinationEq : actualDestination = expected :=
            WordMatches.eq_of_some popped.1
          subst actualDestination
          apply (chargeGas_safe gMid popped.2).bind
          intro charged chargedMatch
          apply (assert_true_safe _ noStackFault_invalidJumpDest).bind
          intro _ valid
          exact ⟨rfl, valid, chargedMatch⟩

/-- Universal `JUMPI` transfer soundness against the actual `Jinst.run`.
The actual condition selects the exact one-byte fall-through arm or the exact
validated target arm. Invalid taken destinations remain non-stack errors. -/
theorem jumpiTransfer_safe {evm : Evm} {input output : Pattern}
    {destination : B256} {condition : Option B256}
    (matched : Matches input evm.dyna.stack)
    (checked :
      jumpiTransfer input = some (destination, condition, output)) :
    SafeResult (fun result =>
      ∃ actualCondition,
        WordMatches condition actualCondition ∧
        ((actualCondition = 0 ∧ result.1 = evm.pc + 1) ∨
          (actualCondition ≠ 0 ∧
            result.1 = destination.toNat ∧
            jumpable evm.sta.code destination.toNat = true)) ∧
        Matches output result.2.stack)
      (Jinst.run evm .jumpi) := by
  cases input with
  | nil => simp [jumpiTransfer] at checked
  | cons abstractDestination rest =>
      cases rest with
      | nil => simp [jumpiTransfer] at checked
      | cons abstractCondition words =>
          cases abstractDestination with
          | none => simp [jumpiTransfer] at checked
          | some expected =>
              simp only [jumpiTransfer, Option.some.injEq, Prod.mk.injEq]
                at checked
              rcases checked with ⟨rfl, rfl, rfl⟩
              simp only [Jinst.run, Jinst.runCore]
              apply (pop_safe matched).bind
              intro destinationResult destinationPopped
              rcases destinationResult with ⟨actualDestination, afterDestination⟩
              have destinationEq : actualDestination = expected :=
                WordMatches.eq_of_some destinationPopped.1
              subst actualDestination
              apply (pop_safe destinationPopped.2).bind
              intro conditionResult conditionPopped
              rcases conditionResult with ⟨actualCondition, afterCondition⟩
              apply (chargeGas_safe gHigh conditionPopped.2).bind
              intro charged chargedMatch
              by_cases zero : actualCondition = 0
              · simp only [zero, if_pos, bind, Except.bind, SafeResult]
                exact ⟨actualCondition, conditionPopped.1,
                  Or.inl ⟨zero, True.intro⟩,
                  chargedMatch⟩
              · simp only [if_neg zero]
                apply (assert_true_safe _ noStackFault_invalidJumpDest).bind
                intro _ valid
                exact ⟨actualCondition, conditionPopped.1,
                  Or.inr ⟨zero, rfl, valid⟩, chargedMatch⟩

/-- Universal `JUMPDEST` transfer soundness against the actual `Jinst.run`.
It charges the real opcode gas, advances by its exact one-byte size, and
preserves the complete stack pattern. -/
theorem jumpdestTransfer_safe {evm : Evm} {input output : Pattern}
    (matched : Matches input evm.dyna.stack)
    (checked : jumpdestTransfer input = some output) :
    SafeResult (fun result => result.1 = evm.pc + 1 ∧
      Matches output result.2.stack)
      (Jinst.run evm .jumpdest) := by
  simp only [jumpdestTransfer, Option.some.injEq] at checked
  subst output
  simp only [Jinst.run, Jinst.runCore]
  apply (chargeGas_safe gJumpdest matched).bind
  intro charged chargedMatch
  exact ⟨rfl, chargedMatch⟩

/-- The actual `JUMP` control-flow step has the checked successor relation. -/
theorem jinst_jumpTransfer_safe {evm : Evm} {input output : Pattern}
    {destination : B256}
    (matched : Matches input evm.dyna.stack)
    (checked : jumpTransfer input = some (destination, output)) :
    StepSafe (fun pc post =>
      pc = destination.toNat ∧
      jumpable evm.sta.code destination.toNat = true ∧
      Matches output post.stack)
      (Step.ofJump (Jinst.run evm .jump)) :=
  step_ofJump_safe (jumpTransfer_safe matched checked)

/-- The actual `JUMPI` control-flow step records the concrete condition and
therefore its exact taken or one-byte fall-through successor. -/
theorem jinst_jumpiTransfer_safe {evm : Evm} {input output : Pattern}
    {destination : B256} {condition : Option B256}
    (matched : Matches input evm.dyna.stack)
    (checked :
      jumpiTransfer input = some (destination, condition, output)) :
    StepSafe (fun pc post =>
      ∃ actualCondition,
        WordMatches condition actualCondition ∧
        ((actualCondition = 0 ∧ pc = evm.pc + 1) ∨
          (actualCondition ≠ 0 ∧ pc = destination.toNat ∧
            jumpable evm.sta.code destination.toNat = true)) ∧
        Matches output post.stack)
      (Step.ofJump (Jinst.run evm .jumpi)) :=
  step_ofJump_safe (jumpiTransfer_safe matched checked)

/-- The actual `JUMPDEST` control-flow step advances by exactly one byte. -/
theorem jinst_jumpdestTransfer_safe {evm : Evm} {input output : Pattern}
    (matched : Matches input evm.dyna.stack)
    (checked : jumpdestTransfer input = some output) :
    StepSafe (fun pc post => pc = evm.pc + 1 ∧ Matches output post.stack)
      (Step.ofJump (Jinst.run evm .jumpdest)) :=
  step_ofJump_safe (jumpdestTransfer_safe matched checked)

end Blanc.AbstractStackSafety
