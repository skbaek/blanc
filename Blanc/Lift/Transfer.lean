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
has already had room for every push.  It is stated on Blanc's covered forks,
the scope of every lifting claim, because Blanc's CALL inversions are.
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

private theorem matches_pop {input : Pattern} {xs : Stack}
    {s rest : Stack} (matched : Matches input s)
    (popped : Stack.Pop xs s rest) :
    Matches (input.drop xs.length) rest := by
  induction xs generalizing input s with
  | nil =>
      simp only [Stack.Pop, Split, List.nil_append] at popped
      subst s
      simpa using matched
  | cons x xs ih =>
      cases input with
      | nil =>
          cases s with
          | nil => simp [Stack.Pop, Split] at popped
          | cons value values => cases matched
      | cons word input =>
          cases s with
          | nil => simp [Stack.Pop, Split] at popped
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
  | nil => simpa using matched
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
      | nil => simp [dropTransfer] at checked
      | cons word input =>
          exact ih (by simpa [dropTransfer] using checked)

private theorem diff_of_pop_push {xs zs s mid s' : Stack}
    (popped : Stack.Pop xs s mid) (pushed : Stack.Push zs mid s') :
    Stack.Diff xs zs s s' := ⟨mid, popped, pushed⟩

private theorem diff_of_pop {xs s s' : Stack} (popped : Stack.Pop xs s s') :
    Stack.Diff xs [] s s' :=
  diff_of_pop_push popped (by simp [Stack.Push, Split])

private theorem diff_of_push {zs s s' : Stack} (pushed : Stack.Push zs s s') :
    Stack.Diff [] zs s s' :=
  diff_of_pop_push (by simp [Stack.Pop, Split]) pushed

private theorem unary_checked {input output : Pattern}
    (checked : unaryTransfer input = some output) :
    ∃ head tail, input = head :: tail ∧ output = none :: tail := by
  cases input with
  | nil => simp [unaryTransfer] at checked
      | cons word tail =>
          simp only [unaryTransfer, Option.some.injEq] at checked
          exact ⟨word, tail, rfl, checked.symm⟩

private theorem binary_checked {input output : Pattern}
    (checked : binaryTransfer input = some output) :
    ∃ head head' tail, input = head :: head' :: tail ∧ output = none :: tail := by
  cases input with
  | nil => simp [binaryTransfer] at checked
  | cons word rest =>
      cases rest with
      | nil => simp [binaryTransfer] at checked
      | cons word' tail =>
          simp only [binaryTransfer, Option.some.injEq] at checked
          exact ⟨word, word', tail, rfl, checked.symm⟩

private theorem dropOne_checked {input output : Pattern}
    (checked : dropOneTransfer input = some output) :
    ∃ head tail, input = head :: tail ∧ output = tail := by
  cases input with
  | nil => simp [dropOneTransfer] at checked
  | cons head tail =>
      simp only [dropOneTransfer, Option.some.injEq] at checked
      exact ⟨head, tail, rfl, checked.symm⟩

private theorem dropTwo_checked {input output : Pattern}
    (checked : dropTwoTransfer input = some output) :
    ∃ head head' tail, input = head :: head' :: tail ∧ output = tail := by
  cases input with
  | nil => simp [dropTwoTransfer] at checked
  | cons head rest =>
      cases rest with
      | nil => simp [dropTwoTransfer] at checked
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

private theorem ninstTransfer_run_call {sevm : Sevm} {devm devm' : Devm}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches input devm.stack)
    (checked : callTransfer input = some output)
    (run : Ninst.Run sevm devm (.exec .call) devm') :
    Matches output devm'.stack := by
  sorry

/-- Success-only soundness: a successful run of an accepted instruction leaves
a stack matching the transferred pattern. -/
theorem ninstTransfer_run {sevm : Sevm} {devm devm' : Devm} {n : Ninst}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
    (matched : Matches input devm.stack)
    (checked : ninstTransfer n input = some output)
    (run : Ninst.Run sevm devm n devm') :
    Matches output devm'.stack := by
  cases n with
  | reg r =>
      simp only [ninstTransfer] at checked
      simp only [liftRegularTransfer] at checked
      cases r with
      | add | mul | sub | div | lt | gt | eq | and | shr =>
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
          simpa using hd
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
      | balance =>
          rcases unary_checked checked with ⟨head, tail, rfl, rfl⟩
          rcases of_run_reg run with ⟨pc, hr⟩
          simp only [Rinst.run, Rinst.runCore, Rinst.balanceCore,
            liftMachMetaWorldExecution, liftMachMetaExecution, liftMachMeta,
            Footprint.toExecution, Footprint.liftOutcome] at hr
          cases hpop : devm.mach.pop with
          | error e => simp [hpop] at hr
          | ok p =>
              rcases p with ⟨top, mach0⟩
              cases hgas : Mach.chargeGas
                (if top.toAdr ∈ devm.meta.accessedAddresses then gasWarmAccess
                 else sevm.benvStat.rules.gas.coldAccountAccess) mach0 with
              | error e => simp [hpop, hgas] at hr
              | ok q =>
                  rcases q with ⟨u, mach1⟩
                  cases hpush : Mach.push (devm.world.state.get top.toAdr).bal mach1 with
                  | error e => simp [hpop, hgas, hpush] at hr
                  | ok q =>
                      rcases q with ⟨u, mach2⟩
                      simp [hpop, hgas, hpush] at hr
                      rw [← hr]
                      have hp0 : Stack.Pop [top] devm.stack mach0.stack := by
                        cases hstack : devm.mach.stack with
                        | nil => simp [hstack, Mach.pop] at hpop
                        | cons a rest =>
                            simp [hstack, Mach.pop] at hpop
                            rcases hpop with ⟨htop, hmach⟩
                            change devm.mach.stack = top :: mach0.stack
                            rw [hstack, htop]
                            simpa using congrArg Mach.stack hmach
                      have h01 : mach0.stack = mach1.stack := by
                        simp only [Mach.chargeGas] at hgas
                        split at hgas
                        · cases hgas
                        · cases hgas
                          rfl
                      have hpopped : Stack.Pop [top] devm.stack mach1.stack := by
                        rw [← h01]
                        exact hp0
                      have htail := matches_pop matched hpopped
                      have hpushed : Stack.Push
                          [(devm.world.state.get top.toAdr).bal]
                          mach1.stack mach2.stack := by
                        simp only [Mach.push] at hpush
                        split at hpush
                        · cases hpush
                          simp [Stack.Push, Split]
                        · cases hpush
                      apply matches_push_word (head := none)
                        (x := (devm.world.state.get top.toAdr).bal)
                        (headMatch := Or.inl rfl) htail
                      exact hpushed
      | dup index =>
          simp only [regularTransfer] at checked
          rcases lookup : input[index]? with _ | selected
          · simp [lookup] at checked
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
          simpa using hmatch
      | _ => cases checked
  | exec x =>
      cases x with
      | call =>
          simp only [ninstTransfer] at checked
          exact ninstTransfer_run_call hfork matched checked run
      | _ => cases checked
  | _ => cases checked

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
