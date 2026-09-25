import Blanc.Lift.Basic
import Blanc.AbstractStackTransfer

/-!
# Instruction stack transfer for lifted bytecode

The lift checker (`Blanc/Lift/Check.lean`) tracks a frame-relative abstract
stack.  It does not restate any opcode's stack effect: it runs the shared
`AbstractStackSafety.regularTransfer` family (extended here by the opcodes that
solc output needs and that family does not accept yet) on an *index* pattern and
reads the result back.  That is sound because every accepted transfer is
*natural*: it only drops, copies or permutes input words and pushes `none` for
computed results (`ninstTransfer_map`), and it only inspects the words it
consumes (`ninstTransfer_append`).

`ninstTransfer_run` is the success-only reading of a transfer: unlike
`regularTransfer_safe` it needs no bound on the stack, because a successful run
has already had room for every push.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- Pop `n` words and push nothing. -/
def dropTransfer : Nat → Pattern → Option Pattern
  | 0, words => some words
  | n + 1, _ :: words => dropTransfer n words
  | _ + 1, [] => none

/-- `regularTransfer`, extended by the regular opcodes of solc output that it
rejects. -/
def liftRegularTransfer : Rinst → Pattern → Option Pattern
  | .exp, words => binaryTransfer words
  | .not, words => unaryTransfer words
  | .keccak256, words => binaryTransfer words
  | .address, words => some (none :: words)
  | .balance, words => unaryTransfer words
  | .log n, words => dropTransfer (n.val + 2) words
  | r, words => regularTransfer r words

/-- Stack transfer of a non-push, non-jump instruction.  `PUSH` is handled by
the checker itself because it is the one instruction whose output word is a
literal rather than a copy of an input. -/
def ninstTransfer : Ninst → Pattern → Option Pattern
  | .reg r, words => liftRegularTransfer r words
  | .exec .call, words => callTransfer words
  | _, _ => none

private theorem dropTransfer_map (φ : Option B256 → Option B256)
    (_hφ : φ none = none) (n : Nat) (words : Pattern) :
    (dropTransfer n words).map (List.map φ) = dropTransfer n (words.map φ) := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih =>
      cases words with
      | nil => rfl
      | cons word words =>
          simp only [dropTransfer, List.map_cons]
          exact ih words

private theorem dropTransfer_append (n : Nat) {words output below : Pattern}
    (checked : dropTransfer n words = some output) :
    dropTransfer n (words ++ below) = some (output ++ below) := by
  induction n generalizing words output with
  | zero => cases checked; rfl
  | succ n ih =>
      cases words with
      | nil => simp [dropTransfer] at checked
      | cons word words =>
          apply ih
          simpa [dropTransfer] using checked

private theorem unaryTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : unaryTransfer words = some output) :
    unaryTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp [unaryTransfer] at checked
  | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked ⊢
      cases checked
      simp [hφ]

private theorem binaryTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : binaryTransfer words = some output) :
    binaryTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp [binaryTransfer] at checked
  | cons first words =>
      cases words with
      | nil => simp [binaryTransfer] at checked
      | cons second words =>
          simp only [binaryTransfer, Option.some.injEq] at checked ⊢
          cases checked
          simp [hφ]

private theorem dropOneTransfer_map (φ : Option B256 → Option B256)
    (_hφ : φ none = none) {words output : Pattern}
    (checked : dropOneTransfer words = some output) :
    dropOneTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp [dropOneTransfer] at checked
  | cons word words =>
      simp only [dropOneTransfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem dropTwoTransfer_map (φ : Option B256 → Option B256)
    (_hφ : φ none = none) {words output : Pattern}
    (checked : dropTwoTransfer words = some output) :
    dropTwoTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp [dropTwoTransfer] at checked
  | cons first words =>
      cases words with
      | nil => simp [dropTwoTransfer] at checked
      | cons second words =>
          simp only [dropTwoTransfer, Option.some.injEq] at checked ⊢
          cases checked
          rfl

private theorem unaryTransfer_append {words output below : Pattern}
    (checked : unaryTransfer words = some output) :
    unaryTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp [unaryTransfer] at checked
  | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem binaryTransfer_append {words output below : Pattern}
    (checked : binaryTransfer words = some output) :
    binaryTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp [binaryTransfer] at checked
  | cons first words =>
      cases words with
      | nil => simp [binaryTransfer] at checked
      | cons second words =>
          simp only [binaryTransfer, Option.some.injEq] at checked ⊢
          cases checked
          rfl

private theorem dropOneTransfer_append {words output below : Pattern}
    (checked : dropOneTransfer words = some output) :
    dropOneTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp [dropOneTransfer] at checked
  | cons word words =>
      simp only [dropOneTransfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem dropTwoTransfer_append {words output below : Pattern}
    (checked : dropTwoTransfer words = some output) :
    dropTwoTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp [dropTwoTransfer] at checked
  | cons first words =>
      cases words with
      | nil => simp [dropTwoTransfer] at checked
      | cons second words =>
          simp only [dropTwoTransfer, Option.some.injEq] at checked ⊢
          cases checked
          rfl

private theorem swap_map (φ : Option B256 → Option B256) (words : Pattern)
    (index : Nat) :
    Jaune.List.swap (words.map φ) index =
      (Jaune.List.swap words index).map (List.map φ) := by
  cases words with
  | nil => rfl
  | cons word words =>
      cases lookup : words[index]? with
      | none =>
          have mapped : (words.map φ)[index]? = none := by
            rw [List.getElem?_map, lookup]
            rfl
          simp [Jaune.List.swap, lookup, mapped]
      | some selected =>
          have mapped : (words.map φ)[index]? = some (φ selected) := by
            rw [List.getElem?_map, lookup]
            rfl
          simp [Jaune.List.swap, lookup, mapped, List.map_set]

private theorem swap_append {words output below : Pattern} {index : Nat}
    (checked : Jaune.List.swap words index = some output) :
    Jaune.List.swap (words ++ below) index = some (output ++ below) := by
  cases words with
  | nil => simp [Jaune.List.swap] at checked
  | cons word words =>
      cases lookup : words[index]? with
      | none => simp [Jaune.List.swap, lookup] at checked
      | some selected =>
          have bound : index < words.length :=
            (List.getElem?_eq_some_iff.mp lookup).1
          change (words ++ below)[index]?.bind
            (fun selected =>
              some (selected :: (words ++ below).set index word)) =
            some (output ++ below)
          rw [List.getElem?_append_left bound,
            List.set_append_left index word bound]
          have output_eq : selected :: words.set index word = output := by
            simpa [Jaune.List.swap, lookup] using checked
          rw [← output_eq, lookup]
          rfl

private theorem regularTransfer_map {r : Rinst} {words output : Pattern}
    (φ : Option B256 → Option B256) (hφ : φ none = none)
    (checked : regularTransfer r words = some output) :
    regularTransfer r (words.map φ) = some (output.map φ) := by
  cases r <;> simp only [regularTransfer] at checked ⊢
  case add | mul | sub | div | lt | gt | eq | and | shr =>
      exact binaryTransfer_map φ hφ checked
  case iszero | calldataload | mload | sload =>
      exact unaryTransfer_map φ hφ checked
  case caller | callvalue | calldatasize | timestamp | gas =>
      cases checked
      simp [hφ]
  case pop => exact dropOneTransfer_map φ hφ checked
  case mstore | sstore => exact dropTwoTransfer_map φ hφ checked
  case dup index =>
      cases lookup : words[index]? with
      | none => simp [lookup] at checked
      | some selected =>
          simp only [lookup, Option.some.injEq] at checked
          subst output
          have lookupNat : words[index.val]? = some selected := by
            simpa only [Fin.getElem?_fin] using lookup
          have mapped : (words.map φ)[index.val]? = some (φ selected) := by
            rw [List.getElem?_map, lookupNat]
            rfl
          have mappedFin : (words.map φ)[index]? = some (φ selected) := by
            simpa only [Fin.getElem?_fin] using mapped
          rw [mappedFin]
          rfl
  case swap index =>
      rw [swap_map φ words index.val]
      simpa using congrArg (Option.map (List.map φ)) checked
  all_goals cases checked

private theorem regularTransfer_append {r : Rinst} {words output below : Pattern}
    (checked : regularTransfer r words = some output) :
    regularTransfer r (words ++ below) = some (output ++ below) := by
  cases r <;> simp only [regularTransfer] at checked ⊢
  case add | mul | sub | div | lt | gt | eq | and | shr =>
      exact binaryTransfer_append checked
  case iszero | calldataload | mload | sload =>
      exact unaryTransfer_append checked
  case caller | callvalue | calldatasize | timestamp | gas =>
      cases checked
      rfl
  case pop => exact dropOneTransfer_append checked
  case mstore | sstore => exact dropTwoTransfer_append checked
  case dup index =>
      cases lookup : words[index]? with
      | none => simp [lookup] at checked
      | some selected =>
          simp only [lookup, Option.some.injEq] at checked
          subst output
          have lookupNat : words[index.val]? = some selected := by
            simpa only [Fin.getElem?_fin] using lookup
          have bound : index < words.length :=
            (List.getElem?_eq_some_iff.mp lookupNat).1
          have appended : (words ++ below)[index.val]? = some selected := by
            rw [List.getElem?_append_left bound, lookupNat]
          have appendedFin : (words ++ below)[index]? = some selected := by
            simpa only [Fin.getElem?_fin] using appended
          rw [appendedFin]
          rfl
  case swap index => exact swap_append (index := index.val) checked
  all_goals cases checked

private theorem liftRegularTransfer_map {r : Rinst} {words output : Pattern}
    (φ : Option B256 → Option B256) (hφ : φ none = none)
    (checked : liftRegularTransfer r words = some output) :
    liftRegularTransfer r (words.map φ) = some (output.map φ) := by
  cases r <;> simp only [liftRegularTransfer] at checked ⊢
  case exp | keccak256 => exact binaryTransfer_map φ hφ checked
  case not | balance => exact unaryTransfer_map φ hφ checked
  case address => cases checked; simp [hφ]
  case log n =>
      rw [← dropTransfer_map φ hφ (n.val + 2) words]
      simpa using congrArg (Option.map (List.map φ)) checked
  all_goals exact regularTransfer_map φ hφ checked

private theorem liftRegularTransfer_append {r : Rinst}
    {words output below : Pattern}
    (checked : liftRegularTransfer r words = some output) :
    liftRegularTransfer r (words ++ below) = some (output ++ below) := by
  cases r <;> simp only [liftRegularTransfer] at checked ⊢
  case exp | keccak256 => exact binaryTransfer_append checked
  case not | balance => exact unaryTransfer_append checked
  case address => cases checked; rfl
  case log n => exact dropTransfer_append (n.val + 2) checked
  all_goals exact regularTransfer_append checked

private theorem callTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : callTransfer words = some output) :
    callTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp [callTransfer] at checked
  | cons a words =>
      cases words with
      | nil => simp [callTransfer] at checked
      | cons b words =>
          cases words with
          | nil => simp [callTransfer] at checked
          | cons c words =>
              cases words with
              | nil => simp [callTransfer] at checked
              | cons d words =>
                  cases words with
                  | nil => simp [callTransfer] at checked
                  | cons e words =>
                      cases words with
                      | nil => simp [callTransfer] at checked
                      | cons f words =>
                          cases words with
                          | nil => simp [callTransfer] at checked
                          | cons g words =>
                              simp only [callTransfer, Option.some.injEq] at checked ⊢
                              cases checked
                              simp [hφ]

private theorem callTransfer_append {words output below : Pattern}
    (checked : callTransfer words = some output) :
    callTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp [callTransfer] at checked
  | cons a words =>
      cases words with
      | nil => simp [callTransfer] at checked
      | cons b words =>
          cases words with
          | nil => simp [callTransfer] at checked
          | cons c words =>
              cases words with
              | nil => simp [callTransfer] at checked
              | cons d words =>
                  cases words with
                  | nil => simp [callTransfer] at checked
                  | cons e words =>
                      cases words with
                      | nil => simp [callTransfer] at checked
                      | cons f words =>
                          cases words with
                          | nil => simp [callTransfer] at checked
                          | cons g words =>
                              simp only [callTransfer, Option.some.injEq] at checked ⊢
                              cases checked
                              rfl

/-- Success-only soundness: a successful run of an accepted instruction leaves
a stack matching the transferred pattern. -/
theorem ninstTransfer_run {sevm : Sevm} {devm devm' : Devm} {n : Ninst}
    {input output : Pattern}
    (matched : Matches input devm.stack)
    (checked : ninstTransfer n input = some output)
    (run : Ninst.Run sevm devm n devm') :
    Matches output devm'.stack := by
  sorry

/-- Naturality: an accepted transfer commutes with any relabelling of words
that keeps unknown words unknown. -/
theorem ninstTransfer_map {n : Ninst} {input output : Pattern}
    (φ : Option B256 → Option B256) (hφ : φ none = none)
    (checked : ninstTransfer n input = some output) :
    ninstTransfer n (input.map φ) = some (output.map φ) := by
  cases n with
  | reg r => exact liftRegularTransfer_map φ hφ checked
  | exec x =>
      cases x with
      | call => exact callTransfer_map φ hφ checked
      | create | callcode | delegatecall | create2 | staticcall => cases checked
  | push bs fits => cases checked
  | dupn imm => cases checked
  | swapn imm => cases checked
  | exchange imm => cases checked

/-- Locality: an accepted transfer ignores the words below those it inspects. -/
theorem ninstTransfer_append {n : Ninst} {input output : Pattern}
    (below : Pattern) (checked : ninstTransfer n input = some output) :
    ninstTransfer n (input ++ below) = some (output ++ below) := by
  cases n with
  | reg r => exact liftRegularTransfer_append checked
  | exec x =>
      cases x with
      | call => exact callTransfer_append checked
      | create | callcode | delegatecall | create2 | staticcall => cases checked
  | push bs fits => cases checked
  | dupn imm => cases checked
  | swapn imm => cases checked
  | exchange imm => cases checked

end Blanc.Lift
