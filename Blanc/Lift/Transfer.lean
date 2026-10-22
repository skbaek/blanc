import Blanc.Lift.Basic
import Blanc.AbstractStackTransfer
import Blanc.Ladder
import Blanc.Lift.CallEffects
import Blanc.TransientSettlement

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
has already had room for every push.  The generic core selects the actual no-state-gas lane and handles both access and
delegation settings; `ninstTransfer_run` retains its covered-fork interface.
-/

namespace Blanc.Lift

open Jaune AbstractStackSafety

/-- Pop `n` words and push nothing. -/
def dropTransfer : Nat → Pattern → Option Pattern
  | 0, words => some words
  | n + 1, _ :: words => dropTransfer n words
  | _ + 1, [] => none

/-- `regularTransfer`, extended by the regular opcodes of solc output that it
rejects (and `XOR`, which Vyper uses for `!=`). -/
def liftRegularTransfer : Rinst → Pattern → Option Pattern
  | .exp, words => binaryTransfer words
  | .slt, words => binaryTransfer words
  | .not, words => unaryTransfer words
  | .keccak256, words => binaryTransfer words
  | .address, words => some (none :: words)
  | .balance, words => unaryTransfer words
  | .extcodesize, words => unaryTransfer words
  | .extcodehash, words => unaryTransfer words
  | .log n, words => dropTransfer (n.val + 2) words
  | .mod, words => binaryTransfer words
  | .or, words => binaryTransfer words
  | .xor, words => binaryTransfer words
  | .byte, words => binaryTransfer words
  | .shl, words => binaryTransfer words
  | .calldatacopy, words => dropTransfer 3 words
  | .codecopy, words => dropTransfer 3 words
  | .returndatasize, words => some (none :: words)
  | .returndatacopy, words => dropTransfer 3 words
  | .mstore8, words => dropTwoTransfer words
  | .tload, words => unaryTransfer words
  | .tstore, words => dropTwoTransfer words
  | .sdiv, words => binaryTransfer words
  | .signextend, words => binaryTransfer words
  | .sgt, words => binaryTransfer words
  | .origin, words => some (none :: words)
  | .number, words => some (none :: words)
  | .chainid, words => some (none :: words)
  | .codesize, words => some (none :: words)
  | .selfbalance, words => some (none :: words)
  | r, words => regularTransfer r words

def staticcallTransfer : Pattern → Option Pattern
  | _ :: _ :: _ :: _ :: _ :: _ :: words => some (none :: words)
  | _ => none

/-- `CREATE2` pops endowment, memory offset, size and salt, and pushes the new address (or
zero). -/
def create2Transfer : Pattern → Option Pattern
  | _ :: _ :: _ :: _ :: words => some (none :: words)
  | _ => none

/-- `DELEGATECALL` pops gas, target, input offset and size, output offset and size, and pushes the
success flag. -/
def delegatecallTransfer : Pattern → Option Pattern
  | _ :: _ :: _ :: _ :: _ :: _ :: words => some (none :: words)
  | _ => none

/-- Stack transfer of a non-push, non-jump instruction.  `PUSH` is handled by
the checker itself because it is the one instruction whose output word is a
literal rather than a copy of an input. -/
def ninstTransfer : Ninst → Pattern → Option Pattern
  | .reg r, words => liftRegularTransfer r words
  | .exec .call, words => callTransfer words
  | .exec .staticcall, words => staticcallTransfer words
  | .exec .create2, words => create2Transfer words
  | .exec .delegatecall, words => delegatecallTransfer words
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
      | nil => simp only [dropTransfer, reduceCtorEq] at checked
      | cons word words =>
          apply ih
          simpa only [dropTransfer] using checked

private theorem unaryTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : unaryTransfer words = some output) :
    unaryTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp only [unaryTransfer, reduceCtorEq] at checked
  | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked ⊢
      cases checked
      simp only [List.map_cons, hφ]

private theorem binaryTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : binaryTransfer words = some output) :
    binaryTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp only [binaryTransfer, reduceCtorEq] at checked
  | cons first words =>
      cases words with
      | nil => simp only [binaryTransfer, reduceCtorEq] at checked
      | cons second words =>
          simp only [binaryTransfer, Option.some.injEq] at checked ⊢
          cases checked
          simp only [List.map_cons, hφ]

private theorem dropOneTransfer_map (φ : Option B256 → Option B256)
    (_hφ : φ none = none) {words output : Pattern}
    (checked : dropOneTransfer words = some output) :
    dropOneTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp only [dropOneTransfer, reduceCtorEq] at checked
  | cons word words =>
      simp only [dropOneTransfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem dropTwoTransfer_map (φ : Option B256 → Option B256)
    (_hφ : φ none = none) {words output : Pattern}
    (checked : dropTwoTransfer words = some output) :
    dropTwoTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp only [dropTwoTransfer, reduceCtorEq] at checked
  | cons first words =>
      cases words with
      | nil => simp only [dropTwoTransfer, reduceCtorEq] at checked
      | cons second words =>
          simp only [dropTwoTransfer, Option.some.injEq] at checked ⊢
          cases checked
          rfl

private theorem unaryTransfer_append {words output below : Pattern}
    (checked : unaryTransfer words = some output) :
    unaryTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp only [unaryTransfer, reduceCtorEq] at checked
  | cons word words =>
      simp only [unaryTransfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem binaryTransfer_append {words output below : Pattern}
    (checked : binaryTransfer words = some output) :
    binaryTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp only [binaryTransfer, reduceCtorEq] at checked
  | cons first words =>
      cases words with
      | nil => simp only [binaryTransfer, reduceCtorEq] at checked
      | cons second words =>
          simp only [binaryTransfer, Option.some.injEq] at checked ⊢
          cases checked
          rfl

private theorem dropOneTransfer_append {words output below : Pattern}
    (checked : dropOneTransfer words = some output) :
    dropOneTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp only [dropOneTransfer, reduceCtorEq] at checked
  | cons word words =>
      simp only [dropOneTransfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem dropTwoTransfer_append {words output below : Pattern}
    (checked : dropTwoTransfer words = some output) :
    dropTwoTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp only [dropTwoTransfer, reduceCtorEq] at checked
  | cons first words =>
      cases words with
      | nil => simp only [dropTwoTransfer, reduceCtorEq] at checked
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
          simp only [Jaune.List.swap, List.map_cons, mapped, Option.bind_eq_bind, Option.bind_none,
            lookup, Option.map_none]
      | some selected =>
          have mapped : (words.map φ)[index]? = some (φ selected) := by
            rw [List.getElem?_map, lookup]
            rfl
          simp only [Jaune.List.swap, List.map_cons, mapped, Option.bind_eq_bind, Option.bind_some,
            lookup, Option.map_some, List.map_set]

private theorem swap_append {words output below : Pattern} {index : Nat}
    (checked : Jaune.List.swap words index = some output) :
    Jaune.List.swap (words ++ below) index = some (output ++ below) := by
  cases words with
  | nil => simp only [Jaune.List.swap, reduceCtorEq] at checked
  | cons word words =>
      cases lookup : words[index]? with
      | none => simp only [Jaune.List.swap, lookup, Option.bind_eq_bind, Option.bind_none,
        reduceCtorEq] at checked
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
            simpa only [Jaune.List.swap, lookup, Option.bind_eq_bind, Option.bind_some,
              Option.some.injEq] using checked
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
  case caller | callvalue | calldatasize | timestamp | number | gas =>
      cases checked
      simp only [List.map_cons, hφ]
  case pop => exact dropOneTransfer_map φ hφ checked
  case mstore | sstore => exact dropTwoTransfer_map φ hφ checked
  case dup index =>
      cases lookup : words[index]? with
      | none => simp only [lookup, reduceCtorEq] at checked
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
      simpa only [Option.map_eq_some_iff, Option.map_some] using
        congrArg (Option.map (List.map φ)) checked
  all_goals cases checked

private theorem regularTransfer_append {r : Rinst} {words output below : Pattern}
    (checked : regularTransfer r words = some output) :
    regularTransfer r (words ++ below) = some (output ++ below) := by
  cases r <;> simp only [regularTransfer] at checked ⊢
  case add | mul | sub | div | lt | gt | eq | and | shr =>
      exact binaryTransfer_append checked
  case iszero | calldataload | mload | sload =>
      exact unaryTransfer_append checked
  case caller | callvalue | calldatasize | timestamp | number | gas =>
      cases checked
      rfl
  case pop => exact dropOneTransfer_append checked
  case mstore | sstore => exact dropTwoTransfer_append checked
  case dup index =>
      cases lookup : words[index]? with
      | none => simp only [lookup, reduceCtorEq] at checked
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
  case exp | slt | keccak256 | sdiv | signextend | sgt => exact binaryTransfer_map φ hφ checked
  case not | balance | extcodesize | extcodehash | tload => exact unaryTransfer_map φ hφ checked
  case address | origin | chainid | selfbalance | codesize | number => cases checked; simp only [List.map_cons,
    hφ]
  case log n =>
      rw [← dropTransfer_map φ hφ (n.val + 2) words]
      simpa only [Option.map_eq_some_iff, Option.map_some] using
        congrArg (Option.map (List.map φ)) checked
  case mod | or | xor | byte | shl => exact binaryTransfer_map φ hφ checked
  case calldatacopy | codecopy | returndatacopy =>
      rw [← dropTransfer_map φ hφ 3 words]
      simpa only [Option.map_eq_some_iff, Option.map_some] using
        congrArg (Option.map (List.map φ)) checked
  case returndatasize => cases checked; simp only [List.map_cons, hφ]
  case mstore8 | tstore => exact dropTwoTransfer_map φ hφ checked
  all_goals exact regularTransfer_map φ hφ checked

private theorem liftRegularTransfer_append {r : Rinst}
    {words output below : Pattern}
    (checked : liftRegularTransfer r words = some output) :
    liftRegularTransfer r (words ++ below) = some (output ++ below) := by
  cases r <;> simp only [liftRegularTransfer] at checked ⊢
  case exp | slt | keccak256 | sdiv | signextend | sgt => exact binaryTransfer_append checked
  case not | balance | extcodesize | extcodehash | tload => exact unaryTransfer_append checked
  case address | origin | chainid | selfbalance | codesize | number => cases checked; rfl
  case log n => exact dropTransfer_append (n.val + 2) checked
  case mod | or | xor | byte | shl => exact binaryTransfer_append checked
  case calldatacopy | codecopy | returndatacopy => exact dropTransfer_append 3 checked
  case returndatasize => cases checked; rfl
  case mstore8 | tstore => exact dropTwoTransfer_append checked
  all_goals exact regularTransfer_append checked

private theorem callTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : callTransfer words = some output) :
    callTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp only [callTransfer, reduceCtorEq] at checked
  | cons a words =>
      cases words with
      | nil => simp only [callTransfer, reduceCtorEq] at checked
      | cons b words =>
          cases words with
          | nil => simp only [callTransfer, reduceCtorEq] at checked
          | cons c words =>
              cases words with
              | nil => simp only [callTransfer, reduceCtorEq] at checked
              | cons d words =>
                  cases words with
                  | nil => simp only [callTransfer, reduceCtorEq] at checked
                  | cons e words =>
                      cases words with
                      | nil => simp only [callTransfer, reduceCtorEq] at checked
                      | cons f words =>
                          cases words with
                          | nil => simp only [callTransfer, reduceCtorEq] at checked
                          | cons g words =>
                              simp only [callTransfer, Option.some.injEq] at checked ⊢
                              cases checked
                              simp only [List.map_cons, hφ]

private theorem callTransfer_append {words output below : Pattern}
    (checked : callTransfer words = some output) :
    callTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp only [callTransfer, reduceCtorEq] at checked
  | cons a words =>
      cases words with
      | nil => simp only [callTransfer, reduceCtorEq] at checked
      | cons b words =>
          cases words with
          | nil => simp only [callTransfer, reduceCtorEq] at checked
          | cons c words =>
              cases words with
              | nil => simp only [callTransfer, reduceCtorEq] at checked
              | cons d words =>
                  cases words with
                  | nil => simp only [callTransfer, reduceCtorEq] at checked
                  | cons e words =>
                      cases words with
                      | nil => simp only [callTransfer, reduceCtorEq] at checked
                      | cons f words =>
                          cases words with
                          | nil => simp only [callTransfer, reduceCtorEq] at checked
                          | cons g words =>
                              simp only [callTransfer, Option.some.injEq] at checked ⊢
                              cases checked
                              rfl

private theorem staticcallTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : staticcallTransfer words = some output) :
    staticcallTransfer (words.map φ) = some (output.map φ) := by
  cases words with
  | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
  | cons a words =>
      cases words with
      | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
      | cons b words =>
          cases words with
          | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
          | cons c words =>
              cases words with
              | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
              | cons d words =>
                  cases words with
                  | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
                  | cons e words =>
                      cases words with
                      | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
                      | cons f words =>
                          simp only [staticcallTransfer, Option.some.injEq] at checked ⊢
                          cases checked
                          simp only [List.map_cons, hφ]

private theorem staticcallTransfer_append {words output below : Pattern}
    (checked : staticcallTransfer words = some output) :
    staticcallTransfer (words ++ below) = some (output ++ below) := by
  cases words with
  | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
  | cons a words =>
      cases words with
      | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
      | cons b words =>
          cases words with
          | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
          | cons c words =>
              cases words with
              | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
              | cons d words =>
                  cases words with
                  | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
                  | cons e words =>
                      cases words with
                      | nil => simp only [staticcallTransfer, reduceCtorEq] at checked
                      | cons f words =>
                          simp only [staticcallTransfer, Option.some.injEq] at checked ⊢
                          cases checked
                          rfl

private theorem create2Transfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : create2Transfer words = some output) :
    create2Transfer (words.map φ) = some (output.map φ) := by
  match words, checked with
  | _ :: _ :: _ :: _ :: words, checked =>
      simp only [create2Transfer, Option.some.injEq] at checked ⊢
      cases checked
      simp only [List.map_cons, hφ]

private theorem create2Transfer_append {words output below : Pattern}
    (checked : create2Transfer words = some output) :
    create2Transfer (words ++ below) = some (output ++ below) := by
  match words, checked with
  | _ :: _ :: _ :: _ :: words, checked =>
      simp only [create2Transfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem delegatecallTransfer_map (φ : Option B256 → Option B256)
    (hφ : φ none = none) {words output : Pattern}
    (checked : delegatecallTransfer words = some output) :
    delegatecallTransfer (words.map φ) = some (output.map φ) := by
  match words, checked with
  | _ :: _ :: _ :: _ :: _ :: _ :: words, checked =>
      simp only [delegatecallTransfer, Option.some.injEq] at checked ⊢
      cases checked
      simp only [List.map_cons, hφ]

private theorem delegatecallTransfer_append {words output below : Pattern}
    (checked : delegatecallTransfer words = some output) :
    delegatecallTransfer (words ++ below) = some (output ++ below) := by
  match words, checked with
  | _ :: _ :: _ :: _ :: _ :: _ :: words, checked =>
      simp only [delegatecallTransfer, Option.some.injEq] at checked ⊢
      cases checked
      rfl

private theorem matches_pop {input : Pattern} {xs : Stack}
    {s rest : Stack} (matched : Matches input s)
    (popped : Stack.Pop xs s rest) :
    Matches (input.drop xs.length) rest := by
  induction xs generalizing input s with
  | nil =>
      simp only [Stack.Pop, Split, List.nil_append] at popped
      subst s
      simpa only [List.length_nil, List.drop_zero] using matched
  | cons x xs ih =>
      cases input with
      | nil =>
          cases s with
          | nil => simp only [Stack.Pop, Split, List.cons_append, List.nil_eq,
            reduceCtorEq] at popped
          | cons value values => cases matched
      | cons word input =>
          cases s with
          | nil => simp only [Stack.Pop, Split, List.cons_append, List.nil_eq,
            reduceCtorEq] at popped
          | cons value values =>
              obtain ⟨head, tail⟩ := matched
              simp only [Stack.Pop, Split, List.cons_append] at popped
              injection popped with _ htail
              exact ih tail htail

private theorem matches_push_none {tail : Pattern} {zs mid final : Stack}
    (matched : Matches tail mid) (pushed : Stack.Push zs mid final) :
    Matches (List.replicate zs.length none ++ tail) final := by
  simp only [Stack.Push, Split] at pushed
  subst final
  induction zs generalizing mid with
  | nil => simpa only [List.length_nil, List.replicate_zero, List.nil_append] using matched
  | cons z zs ih =>
      change Matches (none :: (List.replicate zs.length none ++ tail))
        (z :: (zs ++ mid))
      exact ⟨Or.inl rfl, ih matched⟩

private theorem matches_diff {input : Pattern} {xs zs : Stack}
    {s s' : Stack} (matched : Matches input s)
    (diff : Stack.Diff xs zs s s') :
    Matches (List.replicate zs.length none ++ input.drop xs.length) s' := by
  rcases diff with ⟨mid, popped, pushed⟩
  exact matches_push_none (matches_pop matched popped) pushed

private theorem dropTransfer_eq_drop {n : Nat} {input output : Pattern}
    (checked : dropTransfer n input = some output) :
    input.drop n = output := by
  induction n generalizing input with
  | zero => cases checked; rfl
  | succ n ih =>
      cases input with
      | nil => simp only [dropTransfer, reduceCtorEq] at checked
      | cons word input =>
          exact ih (by simpa only [dropTransfer] using checked)

private theorem diff_of_pop_push {xs zs s mid s' : Stack}
    (popped : Stack.Pop xs s mid) (pushed : Stack.Push zs mid s') :
    Stack.Diff xs zs s s' := ⟨mid, popped, pushed⟩

private theorem diff_of_pop {xs s s' : Stack} (popped : Stack.Pop xs s s') :
    Stack.Diff xs [] s s' :=
  diff_of_pop_push popped (by simp only [Stack.Push, Split, List.nil_append])

private theorem diff_of_push {zs s s' : Stack} (pushed : Stack.Push zs s s') :
    Stack.Diff [] zs s s' :=
  diff_of_pop_push (by simp only [Stack.Pop, Split, List.nil_append]) pushed

private theorem unary_checked {input output : Pattern}
    (checked : unaryTransfer input = some output) :
    ∃ head tail, input = head :: tail ∧ output = none :: tail := by
  cases input with
  | nil => simp only [unaryTransfer, reduceCtorEq] at checked
      | cons word tail =>
          simp only [unaryTransfer, Option.some.injEq] at checked
          exact ⟨word, tail, rfl, checked.symm⟩

private theorem binary_checked {input output : Pattern}
    (checked : binaryTransfer input = some output) :
    ∃ head head' tail, input = head :: head' :: tail ∧ output = none :: tail := by
  cases input with
  | nil => simp only [binaryTransfer, reduceCtorEq] at checked
  | cons word rest =>
      cases rest with
      | nil => simp only [binaryTransfer, reduceCtorEq] at checked
      | cons word' tail =>
          simp only [binaryTransfer, Option.some.injEq] at checked
          exact ⟨word, word', tail, rfl, checked.symm⟩

private theorem dropOne_checked {input output : Pattern}
    (checked : dropOneTransfer input = some output) :
    ∃ head tail, input = head :: tail ∧ output = tail := by
  cases input with
  | nil => simp only [dropOneTransfer, reduceCtorEq] at checked
  | cons head tail =>
      simp only [dropOneTransfer, Option.some.injEq] at checked
      exact ⟨head, tail, rfl, checked.symm⟩

private theorem dropTwo_checked {input output : Pattern}
    (checked : dropTwoTransfer input = some output) :
    ∃ head head' tail, input = head :: head' :: tail ∧ output = tail := by
  cases input with
  | nil => simp only [dropTwoTransfer, reduceCtorEq] at checked
  | cons head rest =>
      cases rest with
      | nil => simp only [dropTwoTransfer, reduceCtorEq] at checked
      | cons head' tail =>
          simp only [dropTwoTransfer, Option.some.injEq] at checked
          exact ⟨head, head', tail, rfl, checked.symm⟩

private theorem matches_push_word {head : Option B256} {tail : Pattern}
    {x : B256} {mid final : Stack} (headMatch : WordMatches head x)
    (matched : Matches tail mid) (pushed : Stack.Push [x] mid final) :
    Matches (head :: tail) final := by
  simp only [Stack.Push, Split] at pushed
  subst final
  exact ⟨headMatch, matched⟩

private theorem matches_six {a b c d e f : Option B256} {tail : Pattern}
    {s : Stack} (matched : Matches (a :: b :: c :: d :: e :: f :: tail) s) :
    ∃ (x1 x2 x3 x4 x5 x6 : B256) (xs : Stack),
      s = x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: xs ∧ Matches tail xs := by
  cases s with
  | nil => simp only [Matches] at matched
  | cons x1 s =>
    cases s with
    | nil => simp_all only [Matches, and_false]
    | cons x2 s =>
      cases s with
      | nil => simp_all only [Matches, and_false]
      | cons x3 s =>
        cases s with
        | nil => simp_all only [Matches, and_false]
        | cons x4 s =>
          cases s with
          | nil => simp_all only [Matches, and_false]
          | cons x5 s =>
            cases s with
            | nil => simp_all only [Matches, and_false]
            | cons x6 xs =>
              simp only [Matches] at matched
              exact ⟨x1, x2, x3, x4, x5, x6, xs, rfl,
                matched.2.2.2.2.2.2⟩

private theorem matches_seven {a b c d e f g : Option B256} {tail : Pattern}
    {s : Stack} (matched : Matches (a :: b :: c :: d :: e :: f :: g :: tail) s) :
    ∃ (x1 x2 x3 x4 x5 x6 x7 : B256) (xs : Stack),
      s = x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: xs ∧ Matches tail xs := by
  cases s with
  | nil => simp only [Matches] at matched
  | cons x1 s =>
    cases s with
    | nil => simp_all only [Matches, and_false]
    | cons x2 s =>
      cases s with
      | nil => simp_all only [Matches, and_false]
      | cons x3 s =>
        cases s with
        | nil => simp_all only [Matches, and_false]
        | cons x4 s =>
          cases s with
          | nil => simp_all only [Matches, and_false]
          | cons x5 s =>
            cases s with
            | nil => simp_all only [Matches, and_false]
            | cons x6 s =>
              cases s with
              | nil => simp_all only [Matches, and_false]
              | cons x7 xs =>
                simp only [Matches] at matched
                exact ⟨x1, x2, x3, x4, x5, x6, x7, xs, rfl,
                  matched.2.2.2.2.2.2.2⟩

private theorem call_fail_stack_exact {sevm : Sevm} {s sf : Devm}
    {g c v ii is oi os : B256} {xs : Stack}
    (hs : s.stack = g :: c :: v :: ii :: is :: oi :: os :: xs)
    (h_run : Ninst.Run sevm s Ninst.call sf)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hfail : ((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) :
    sf.stack = 0 :: xs := by
  obtain ⟨w, hw⟩ := (CallEffects.call_run_effects hfork.rules_stateGas_none hs h_run).1
  have hz : (0 : B256) = w :=
    pref_head_unique (by simpa only [hw, List.cons_append, List.nil_append] using hfail.1) (pref_append [w] xs)
  rw [hw, ← hz]

private theorem ninstTransfer_run_call_noStateGas {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hstateGas : sevm.benvStat.rules.stateGas = none)
    (matched : Matches input devm.stack)
    (checked : callTransfer input = some output)
    (run : Ninst.Run sevm devm (.exec .call) devm') :
    Matches output devm'.stack := by
  match input, checked with
  | a :: b :: c :: d :: e :: f :: g :: rest, checked =>
      simp only [callTransfer, Option.some.injEq] at checked
      cases checked
      obtain ⟨x1, x2, x3, x4, x5, x6, x7, xs, hstack, hrest⟩ := matches_seven matched
      obtain ⟨w, hw⟩ := (CallEffects.call_run_effects hstateGas hstack run).1
      rw [hw]
      exact ⟨Or.inl rfl, hrest⟩

private theorem ninstTransfer_run_call {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches input devm.stack)
    (checked : callTransfer input = some output)
    (run : Ninst.Run sevm devm (.exec .call) devm') :
    Matches output devm'.stack :=
  ninstTransfer_run_call_noStateGas hfork.rules_stateGas_none matched checked run

private theorem staticcall_fail_stack_exact {sevm : Sevm} {s sf : Devm}
    {g t ii is oi os : B256} {xs : Stack}
    (hs : s.stack = g :: t :: ii :: is :: oi :: os :: xs)
    (h_run : Ninst.Run sevm s Ninst.staticcall sf)
    (hfork : CoveredFork sevm.benvStat.fork)
    (hfail : ((0 : B256) :: xs <<+ sf.stack) ∧ Devm.WorldEq s sf) :
    sf.stack = 0 :: xs := by
  obtain ⟨w, hw⟩ := (CallEffects.call6_run_effects (Or.inr rfl) hfork.rules_stateGas_none hs h_run).1
  have hz : (0 : B256) = w :=
    pref_head_unique (by simpa only [hw, List.cons_append, List.nil_append] using hfail.1) (pref_append [w] xs)
  rw [hw, ← hz]

private theorem ninstTransfer_run_staticcall_noStateGas {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hstateGas : sevm.benvStat.rules.stateGas = none)
    (matched : Matches input devm.stack)
    (checked : staticcallTransfer input = some output)
    (run : Ninst.Run sevm devm (.exec .staticcall) devm') :
    Matches output devm'.stack := by
  match input, checked with
  | a :: b :: c :: d :: e :: f :: rest, checked =>
      simp only [staticcallTransfer, Option.some.injEq] at checked
      cases checked
      obtain ⟨x1, x2, x3, x4, x5, x6, xs, hstack, hrest⟩ := matches_six matched
      obtain ⟨w, hw⟩ := (CallEffects.call6_run_effects (Or.inr rfl) hstateGas hstack run).1
      rw [hw]
      exact ⟨Or.inl rfl, hrest⟩

private theorem ninstTransfer_run_staticcall {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches input devm.stack)
    (checked : staticcallTransfer input = some output)
    (run : Ninst.Run sevm devm (.exec .staticcall) devm') :
    Matches output devm'.stack :=
  ninstTransfer_run_staticcall_noStateGas hfork.rules_stateGas_none matched checked run

/-- A `CREATE` resume leaves exactly one word on the parent's stack. -/
private theorem create_resume_stack {parent : Devm} {na : Adr}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {sf : Devm}
    (h : (Resume.create parent na).run r = .ok sf) : ∃ w, sf.stack = w :: parent.stack := by
  have key : ∀ d : Devm, d.stack = parent.stack → ∀ v : B256,
      Devm.push v d = .ok sf → ∃ w, sf.stack = w :: parent.stack := by
    intro d hd v hh
    refine ⟨v, ?_⟩
    rw [(Devm.push_of_push hh).stack, hd]
    rfl
  cases r with
  | error e => exact (Resume.create_run_error h).elim
  | ok child =>
    unfold Resume.run liftToExecution at h
    dsimp only [bind, Except.bind] at h
    split at h
    · exact key (incorporateChildOnError parent child child.output) rfl 0 h
    · exact key (incorporateChildOnSuccess parent child []) rfl _ h

/-- A successful `genericCreate` step leaves exactly one word on its input stack. -/
private theorem genericCreate_stack {sevm : Sevm} {d : Devm} {v : B256} {na : Adr}
    {mi ms : Nat} {xl : Xlot} {sf : Devm}
    (h : XStep.Run (genericCreate.step sevm d v na mi ms) xl (.ok sf)) :
    ∃ w, sf.stack = w :: d.stack := by
  have done : ∀ {e e' : Devm}, e.stack = d.stack → Devm.push 0 e = .ok e' →
      XStep.Run (XStep.ofExcept (.ok (XStep.done (.ok e')))) xl (.ok sf) →
      ∃ w, sf.stack = w :: d.stack := by
    intro e e' he hpush hrun
    have hs := Except.ok.inj hrun.2
    subst hs
    exact ⟨0, by rw [(Devm.push_of_push hpush).stack, he]; rfl⟩
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert, assertDynamic,
    Pure.pure, Except.pure] at h
  split at h
  · cases XStep.run_ofExcept_error h
  split at h
  · cases XStep.run_ofExcept_error h
  split at h
  · split at h
    · cases XStep.run_ofExcept_error h
    · rename_i hpush
      exact (done · hpush h) rfl
  split at h
  · split at h
    · cases XStep.run_ofExcept_error h
    · rename_i hpush
      exact (done · hpush h) rfl
  · obtain ⟨r, -, hres⟩ := h
    obtain ⟨w, hw⟩ := create_resume_stack hres.symm
    exact ⟨w, hw⟩

private theorem matches_four {a b c d : Option B256} {tail : Pattern}
    {s : Stack} (matched : Matches (a :: b :: c :: d :: tail) s) :
    ∃ (x1 x2 x3 x4 : B256) (xs : Stack), s = x1 :: x2 :: x3 :: x4 :: xs ∧ Matches tail xs := by
  match s, matched with
  | x1 :: x2 :: x3 :: x4 :: xs, matched =>
    simp only [Matches] at matched
    exact ⟨x1, x2, x3, x4, xs, rfl, matched.2.2.2.2⟩

private theorem create2_run_stack {sevm : Sevm} {s sf : Devm} {v i sz salt : B256}
    {xs : Stack} (hs : s.stack = v :: i :: sz :: salt :: xs)
    (h_run : Ninst.Run sevm s Ninst.create2 sf)
    (hstateGas : sevm.benvStat.rules.stateGas = none) :
    ∃ w, sf.stack = w :: xs := by
  rcases h_run with ⟨xl, h_fill, pc, h_run⟩
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step,
    hstateGas] at h_run
  have henabled : sevm.benvStat.rules.op.create2 = true := by
    by_contra disabled
    simp only [disabled, ↓reduceIte] at h_run
    cases XStep.run_ofExcept_error h_run
  simp only [henabled, ↓reduceIte, Bind.bind, Except.bind] at h_run
  rcases eq1 : Devm.pop s with _ | ⟨v1, s1⟩ <;> simp only [eq1] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e1 := (Devm.pop_of_pop eq1).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e1
  rcases eq2 : Devm.popToNat s1 with _ | ⟨n2, s2⟩ <;> simp only [eq2] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq2 with ⟨x2, f2, -⟩
  have e2 := f2.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e2
  rcases eq3 : Devm.popToNat s2 with _ | ⟨n3, s3⟩ <;> simp only [eq3] at h_run
  · cases XStep.run_ofExcept_error h_run
  rcases Devm.pop_of_popToNat_val eq3 with ⟨x3, f3, -⟩
  have e3 := f3.stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e3
  rcases eq4 : Devm.pop s3 with _ | ⟨v4, s4⟩ <;> simp only [eq4] at h_run
  · cases XStep.run_ofExcept_error h_run
  have e4 := (Devm.pop_of_pop eq4).stack
  simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at e4
  have hs4 : s4.stack = xs := by
    have estack : s.stack = v1 :: x2 :: x3 :: v4 :: s4.stack := by rw [e1, e2, e3, e4]
    have hparts := hs.symm.trans estack
    simp only [List.cons.injEq] at hparts
    exact hparts.2.2.2.2.symm
  split at h_run
  · cases XStep.run_ofExcept_error h_run
  rename_i s5 eq5
  have hs5 : s5.stack = xs := (Devm.burn_of_chargeGas eq5).stack.symm.trans hs4
  obtain ⟨w, hw⟩ := genericCreate_stack h_run
  exact ⟨w, hw.trans (congrArg (w :: ·) hs5)⟩

private theorem ninstTransfer_run_create2_noStateGas {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hstateGas : sevm.benvStat.rules.stateGas = none)
    (matched : Matches input devm.stack)
    (checked : create2Transfer input = some output)
    (run : Ninst.Run sevm devm (.exec .create2) devm') :
    Matches output devm'.stack := by
  match input, checked with
  | a :: b :: c :: d :: rest, checked =>
      simp only [create2Transfer, Option.some.injEq] at checked
      cases checked
      obtain ⟨x1, x2, x3, x4, xs, hstack, hrest⟩ := matches_four matched
      obtain ⟨w, hw⟩ := create2_run_stack hstack (by simpa only [Ninst.create2] using run) hstateGas
      rw [hw]
      exact ⟨Or.inl rfl, hrest⟩

private theorem ninstTransfer_run_create2 {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches input devm.stack)
    (checked : create2Transfer input = some output)
    (run : Ninst.Run sevm devm (.exec .create2) devm') :
    Matches output devm'.stack :=
  ninstTransfer_run_create2_noStateGas hfork.rules_stateGas_none matched checked run

/-- A successful `genericCall` step leaves exactly one word (the success flag) on its input
stack. -/
private theorem genericCall_stack {sevm : Sevm} {d : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {transfer static : Bool} {ii is oi os : Nat}
    {code : ByteArray} {dp : Bool} {xl : Xlot} {sf : Devm}
    (h : XStep.Run (genericCall.step sevm d gas value caller target codeAddress transfer static
      ii is oi os code dp) xl (.ok sf)) :
    ∃ w, sf.stack = w :: d.stack :=
  CallEffects.genericCall_stack h

/-- A successful `DELEGATECALL` pops six words and pushes one. -/
private theorem delegatecall_run_stack {sevm : Sevm} {s sf : Devm}
    {g t ii is oi os : B256} {xs : Stack}
    (hs : s.stack = g :: t :: ii :: is :: oi :: os :: xs)
    (h_run : Ninst.Run sevm s (.exec .delegatecall) sf)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∃ w, sf.stack = w :: xs :=
  (CallEffects.call6_run_effects (Or.inl rfl) hfork.rules_stateGas_none hs h_run).1

private theorem ninstTransfer_run_delegatecall_noStateGas {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hstateGas : sevm.benvStat.rules.stateGas = none)
    (matched : Matches input devm.stack)
    (checked : delegatecallTransfer input = some output)
    (run : Ninst.Run sevm devm (.exec .delegatecall) devm') :
    Matches output devm'.stack := by
  match input, checked with
  | a :: b :: c :: d :: e :: f :: rest, checked =>
      simp only [delegatecallTransfer, Option.some.injEq] at checked
      cases checked
      obtain ⟨x1, x2, x3, x4, x5, x6, xs, hstack, hrest⟩ := matches_six matched
      obtain ⟨w, hw⟩ := (CallEffects.call6_run_effects (Or.inl rfl) hstateGas hstack run).1
      rw [hw]
      exact ⟨Or.inl rfl, hrest⟩

private theorem ninstTransfer_run_delegatecall {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches input devm.stack)
    (checked : delegatecallTransfer input = some output)
    (run : Ninst.Run sevm devm (.exec .delegatecall) devm') :
    Matches output devm'.stack :=
  ninstTransfer_run_delegatecall_noStateGas hfork.rules_stateGas_none matched checked run

/-- `EXTCODEHASH` at a known stack, read through Jaune's arm: it pops the address, charges the
warm access or the fork's cold access (warming the address), and pushes zero for an empty
account and the keccak-256 of the account's code otherwise, both read from the instruction's
input state.  Memory is untouched. -/
theorem run_extcodehash_val {sevm : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hs : s.stack = x :: xs) (run : Ninst.Run sevm s (.reg .extcodehash) r) :
    r.stack =
        (if (s.getAcct x.toAdr).Empty then (0 : B256)
         else ByteArray.keccak 0 (s.getAcct x.toAdr).code.size (s.getAcct x.toAdr).code) :: xs ∧
      r.memory = s.memory := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  have henabled : sevm.benvStat.rules.op.extCodeHash = true := by
    by_contra disabled
    simp only [disabled, ↓reduceIte, reduceCtorEq] at hrun
  rw [ite_eq_left henabled] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨adr, d0⟩, hpopAdr, hrun⟩
  rcases Devm.pop_of_popToAdr hpopAdr with ⟨word, hadr, hpop⟩
  have hp := Devm.pop_of_pop hpop
  have hsplit := hp.stack
  simp only [Stack.Pop, Split, hs, List.cons_append, List.nil_append, List.cons.injEq] at hsplit
  obtain ⟨rfl, htail⟩ := hsplit
  subst hadr
  dsimp only at hrun
  have hd0 : s.state = d0.state := hp.state
  cases haccess : sevm.benvStat.rules.access <;> simp only [haccess] at hrun
  all_goals try (split at hrun)
  all_goals
    rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hb := Devm.burn_of_chargeGas hgas
    have hst : s.state = d2.state := hd0.trans hb.state
    have hacct : (Devm.balReadAccount sevm.benvStat.rules x.toAdr d2).getAcct x.toAdr =
        s.getAcct x.toAdr := by
      rw [Devm.balReadAccount_getAcct]
      unfold Devm.getAcct
      rw [hst]
    have hq := Devm.push_of_push hpush
    rw [hacct] at hq
    refine ⟨?_, ?_⟩
    · rw [hq.stack]
      simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and,
        Devm.balReadAccount_stack]
      rw [← hb.stack, htail]
      all_goals rfl
    · rw [← hq.memory]
      exact (hp.memory.trans hb.memory).symm

/-- Successful BALANCE reads its input account and replaces exactly the top word,
under either access schedule. -/
theorem run_balance_stack {sevm : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hs : s.stack = x :: xs) (run : Ninst.Run sevm s (.reg .balance) r) :
    r.stack = (s.getAcct x.toAdr).bal :: xs := by
  rcases of_run_reg run with ⟨pc, h⟩
  rcases s with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  change stack = x :: xs at hs
  subst hs
  simp only [Rinst.run, Rinst.runCore, liftMachMetaWorldExecution, liftMachMetaExecution,
    liftMachMeta, Rinst.balanceCore, Footprint.toExecution, Footprint.liftOutcome,
    Mach.pop, Mach.chargeGas, Mach.push] at h
  revert h
  generalize sevm.benvStat.rules.access = acc
  intro h
  cases acc with
  | eip2929 =>
    dsimp only at h
    cases hg : safeSub gasLeft (if x.toAdr ∈ view.accessedAddresses then gasWarmAccess
        else sevm.benvStat.rules.gas.coldAccountAccess) with
    | none => simp only [hg, reduceCtorEq] at h
    | some g =>
      by_cases hl : xs.length < 1024
      · simp only [hg, hl, ↓reduceIte, Except.ok.injEq] at h
        subst h
        rfl
      · simp only [hg, hl, ↓reduceIte, reduceCtorEq] at h
  | flat fg =>
    dsimp only at h
    cases hg : safeSub gasLeft fg.balance with
    | none => simp only [hg, reduceCtorEq] at h
    | some g =>
      by_cases hl : xs.length < 1024
      · simp only [hg, hl, ↓reduceIte, Except.ok.injEq] at h
        subst h
        rfl
      · simp only [hg, hl, ↓reduceIte, reduceCtorEq] at h

/-- Success-only soundness: a successful run of an accepted instruction leaves
a stack matching the transferred pattern. -/
theorem ninstTransfer_run_noStateGas {sevm : Sevm} {devm devm' : Devm} {n : Ninst}
    {input output : Pattern} (hstateGas : sevm.benvStat.rules.stateGas = none)
    (matched : Matches input devm.stack)
    (checked : ninstTransfer n input = some output)
    (run : Ninst.Run sevm devm n devm') :
    Matches output devm'.stack := by
  cases n with
  | reg r =>
      simp only [ninstTransfer] at checked
      simp only [liftRegularTransfer] at checked
      cases r with
      | add | mul | sub | div | lt | gt | slt | eq | and =>
          simp only [regularTransfer] at checked
          rcases binary_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hd⟩
          exact matches_diff matched hd.stack
      | iszero | not =>
          simp only [regularTransfer] at checked
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          rcases Devm.diffBurn_of_applyUnary hr with ⟨x, hd⟩
          exact matches_diff matched hd.stack
      | calldataload =>
          simp only [regularTransfer] at checked
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          rcases of_run_calldataload run with ⟨x, y, hd⟩
          exact matches_diff matched hd
      | mload =>
          simp only [regularTransfer] at checked
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          rcases of_run_mload run with ⟨x, y, hd⟩
          exact matches_diff matched hd
      | sload =>
          simp only [regularTransfer] at checked
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          rcases of_run_sload run with ⟨x, hd⟩
          exact matches_diff matched hd
      | tload =>
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          cases hstack : devm.stack with
          | nil => simp only [hstack, Matches] at matched
          | cons key rest =>
              rw [hstack] at matched
              obtain ⟨_, tailMatched⟩ := matched
              have postStack := (tload_run_cell run hstack).1
              rw [postStack]
              exact ⟨Or.inl rfl, tailMatched⟩
      | tstore =>
          rcases dropTwo_checked checked with ⟨head, head', tail, rfl, rfl⟩
          cases hstack : devm.stack with
          | nil => simp only [hstack, Matches] at matched
          | cons key rest =>
              cases rest with
              | nil => simp only [hstack, matches_cons, Matches, and_false] at matched
              | cons value xs =>
                  rw [hstack] at matched
                  obtain ⟨_, _, tailMatched⟩ := matched
                  have postStack := (tstore_run_cell run hstack).1
                  rw [postStack]
                  exact tailMatched
      | exp =>
          rcases binary_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          rcases Except.bind_eq_ok hr with ⟨⟨x, s₁⟩, h1, hr⟩
          rcases Except.bind_eq_ok hr with ⟨⟨y, s₂⟩, h2, hr⟩
          rcases Except.bind_eq_ok hr with ⟨s₃, h3, h4⟩
          have hp := (Devm.pop_append (Devm.pop_of_pop h1)
            (Devm.pop_of_pop h2)).stack
          have hb := (Devm.burn_of_chargeGas h3).stack
          have hpush := (Devm.push_of_push h4).stack
          have hp' : Stack.Pop [x, y] devm.stack s₃.stack := by
            rw [← hb]
            exact hp
          exact matches_diff matched
            (diff_of_pop_push hp' hpush)
      | keccak256 =>
          rcases binary_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_keccak256 run with ⟨x, y, z, hd⟩
          exact matches_diff matched hd
      | log n =>
          rcases of_run_log run with ⟨zs, hlen, hp⟩
          have hd := matches_pop matched hp
          rw [← dropTransfer_eq_drop checked]
          rw [← hlen]
          simpa only using hd
      | mod | or | xor | byte | sdiv | signextend | sgt =>
          rcases binary_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hd⟩
          exact matches_diff matched hd.stack
      | shr | shl =>
          simp only [regularTransfer] at checked
          rcases binary_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          split at hr
          · rcases Devm.diffBurn_of_applyBinary hr with ⟨x, y, hd⟩
            exact matches_diff matched hd.stack
          · cases hr
      | calldatacopy =>
          rcases of_run_calldatacopy run with ⟨x, y, z, hp⟩
          rw [← dropTransfer_eq_drop checked]
          exact matches_pop matched hp
      | codecopy =>
          rcases of_run_codecopy_mem run with ⟨x, y, z, hp, _⟩
          rw [← dropTransfer_eq_drop checked]
          exact matches_pop matched hp
      | returndatacopy =>
          rcases of_run_returndatacopy run with ⟨x, y, z, hp⟩
          rw [← dropTransfer_eq_drop checked]
          exact matches_pop matched hp
      | returndatasize =>
          cases checked
          rcases of_run_returndatasize run with ⟨x, hp⟩
          exact matches_push_word (head := none) (x := x)
            (headMatch := Or.inl rfl) matched hp.stack
      | mstore8 =>
          rcases dropTwo_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_mstore8_val run with ⟨x, y, hp, _⟩
          exact matches_diff matched (diff_of_pop hp)
      | caller =>
          simp only [regularTransfer] at checked
          cases checked
          exact matches_diff matched (diff_of_push (of_run_caller run).stack)
      | callvalue =>
          simp only [regularTransfer] at checked
          cases checked
          exact matches_diff matched (diff_of_push (of_run_callvalue run).stack)
      | calldatasize =>
          simp only [regularTransfer] at checked
          cases checked
          exact matches_diff matched (diff_of_push (of_run_calldatasize run).stack)
      | timestamp =>
          simp only [regularTransfer] at checked
          cases checked
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          exact matches_diff matched (diff_of_push (Devm.pushBurn_of_pushItem hr).stack)
      | gas =>
          simp only [regularTransfer] at checked
          cases checked
          rcases of_run_gas run with ⟨x, hp⟩
          exact matches_diff matched (diff_of_push hp.stack)
      | pop =>
          simp only [regularTransfer] at checked
          rcases dropOne_checked checked with ⟨head, tail, rfl, rfl⟩
          rcases of_run_pop run with ⟨x, hp⟩
          exact matches_diff matched (diff_of_pop hp.stack)
      | mstore =>
          simp only [regularTransfer] at checked
          rcases dropTwo_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_mstore run with ⟨x, y, hp⟩
          exact matches_diff matched (diff_of_pop hp)
      | sstore =>
          simp only [regularTransfer] at checked
          rcases dropTwo_checked checked with ⟨head, head', tail, rfl, rfl⟩
          rcases of_run_sstore run with ⟨x, y, hp⟩
          exact matches_diff matched (diff_of_pop hp)
      | address =>
          cases checked
          exact matches_diff matched (diff_of_push (of_run_address run).stack)
      | origin | codesize | number =>
          cases checked
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          exact matches_diff matched (diff_of_push (Devm.pushBurn_of_pushItem hr).stack)
      | chainid =>
          cases checked
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore] at hr
          split at hr
          · exact matches_diff matched (diff_of_push (Devm.pushBurn_of_pushItem hr).stack)
          · cases hr
      | selfbalance =>
          cases checked
          exact matches_diff matched (diff_of_push (of_run_selfbalance_stack run))
      | balance =>
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          cases hstack : devm.stack with
          | nil => simp only [hstack, Matches] at matched
          | cons address xs =>
              rw [hstack] at matched
              obtain ⟨_, tailMatched⟩ := matched
              rw [run_balance_stack hstack run]
              exact ⟨Or.inl rfl, tailMatched⟩
      | extcodesize =>
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          cases hstack : devm.stack with
          | nil => simp only [hstack, Matches] at matched
          | cons address xs =>
              rw [hstack] at matched
              obtain ⟨_, tailMatched⟩ := matched
              have pref :
                  (devm.getCode address.toAdr).size.toB256 :: xs <<+ devm'.stack :=
                (prefix_of_extcodesize_val
                  (by rw [hstack]; simpa only [List.append_nil] using pref_append (address :: xs) []) run).1
              have sameLength : devm'.stack.length = (address :: xs).length := by
                rcases of_run_reg run with ⟨pc, hr⟩
                simp only [Rinst.run, Rinst.runCore] at hr
                rcases Except.bind_eq_ok hr with ⟨⟨adr, d0⟩, hpop, hr⟩
                rcases Devm.pop_of_popToAdr hpop with ⟨word, _, hp⟩
                have hpStack := (Devm.pop_of_pop hp).stack
                cases haccess : sevm.benvStat.rules.access <;> simp only [haccess] at hr
                all_goals try (split at hr)
                all_goals
                  rcases Except.bind_eq_ok hr with ⟨d1, hgas, hpush⟩
                  have hbStack := (Devm.burn_of_chargeGas hgas).stack
                  have hpushStack := (Devm.push_of_push hpush).stack
                  simp only [Stack.Pop, Stack.Push, Split,
                    Devm.balReadAccount_stack] at hpStack hpushStack
                  simp only [hstack, List.cons_append, List.nil_append, List.cons.injEq] at hpStack
                  change d0.stack = d1.stack at hbStack
                  rw [hpushStack]
                  simp only [List.length_cons]
                  rw [← hbStack, ← hpStack.2]
                  simp only [Jaune.Devm.balReadAccount_getCode, List.cons_append, List.nil_append,
                    List.length_cons]
              have exactStack :
                  (devm.getCode address.toAdr).size.toB256 :: xs = devm'.stack :=
                List.pref_unique (by simpa only [List.length_cons] using sameLength.symm) pref
                  (by simpa only [List.append_nil] using pref_append devm'.stack [])
              rw [← exactStack]
              exact ⟨Or.inl rfl, tailMatched⟩
      | extcodehash =>
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          cases hstack : devm.stack with
          | nil => simp only [hstack, Matches] at matched
          | cons address xs =>
              rw [hstack] at matched
              obtain ⟨_, tailMatched⟩ := matched
              rw [(run_extcodehash_val hstack run).1]
              exact ⟨Or.inl rfl, tailMatched⟩
      | dup index =>
          simp only [regularTransfer] at checked
          rcases lookup : input[index]? with _ | selected
          · simp only [lookup, reduceCtorEq] at checked
          · simp only [lookup, Option.some.injEq] at checked
            subst output
            rcases of_run_dup run with ⟨x, hx, hp⟩
            obtain ⟨actual, hactual, hmatch⟩ := matched.getElem? lookup
            have hsame : actual = x :=
              Option.some.inj (hactual.symm.trans hx)
            subst actual
            exact matches_push_word hmatch matched hp.stack
      | swap index =>
          simp only [regularTransfer] at checked
          rcases of_run_swap run with hswap
          obtain ⟨actual, hactual, hmatch⟩ := matched.swap checked
          have : actual = devm'.stack := Option.some.inj (hactual.symm.trans hswap)
          subst actual
          simpa only using hmatch
      | _ => cases checked
  | exec x =>
      cases x with
      | call =>
          simp only [ninstTransfer] at checked
          exact ninstTransfer_run_call_noStateGas hstateGas matched checked run
      | staticcall =>
          simp only [ninstTransfer] at checked
          exact ninstTransfer_run_staticcall_noStateGas hstateGas matched checked run
      | create2 =>
          simp only [ninstTransfer] at checked
          exact ninstTransfer_run_create2_noStateGas hstateGas matched checked run
      | delegatecall =>
          simp only [ninstTransfer] at checked
          exact ninstTransfer_run_delegatecall_noStateGas hstateGas matched checked run
      | _ => cases checked
  | _ => cases checked

/-- Modern compatibility statement for success-only checked stack transfer. -/
theorem ninstTransfer_run {sevm : Sevm} {devm devm' : Devm} {n : Ninst}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches input devm.stack)
    (checked : ninstTransfer n input = some output)
    (run : Ninst.Run sevm devm n devm') :
    Matches output devm'.stack :=
  ninstTransfer_run_noStateGas hfork.rules_stateGas_none matched checked run

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
      | staticcall => exact staticcallTransfer_map φ hφ checked
      | create2 => exact create2Transfer_map φ hφ checked
      | delegatecall => exact delegatecallTransfer_map φ hφ checked
      | create | callcode => cases checked
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
      | staticcall => exact staticcallTransfer_append checked
      | create2 => exact create2Transfer_append checked
      | delegatecall => exact delegatecallTransfer_append checked
      | create | callcode => cases checked
  | push bs fits => cases checked
  | dupn imm => cases checked
  | swapn imm => cases checked
  | exchange imm => cases checked

end Blanc.Lift
