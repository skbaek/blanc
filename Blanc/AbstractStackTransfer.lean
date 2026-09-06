import Blanc.AbstractStackSafety

/-!
Forward stack safety for concrete non-control instructions.

Each theorem unfolds the actual Jaune opcode implementation.  Successful
outcomes preserve the checked full-stack pattern, while every raw error arm
excludes a locally generated stack fault.
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

end Blanc.AbstractStackSafety
