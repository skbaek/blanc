import Blanc.AbstractStackTransfer

/-!
Checked finite tables of whole-stack patterns for actual decoded execution.
The tree representation bounds lookup and reduction depth; its shape supplies
no trusted premise. Every row is checked against the public bytecode decoder,
every successor is checked separately, and tree search order is checked too.
-/

namespace Blanc.AbstractStackSafety

open Jaune CompiledStackSafety

/-- A post-pattern may forget a literal, but never an operand position. -/
def covers : Pattern → Pattern → Bool
  | [], [] => true
  | actual :: rest, expected :: tail =>
      (expected.isNone || actual == expected) && covers rest tail
  | _, _ => false

theorem Matches.covered {actual expected : Pattern} {values : Stack}
    (matched : Matches actual values) (checked : covers actual expected = true) :
    Matches expected values := by
  induction actual generalizing expected values with
  | nil => cases expected <;> cases values <;> simp_all [covers, Matches]
  | cons word rest ih =>
      cases expected with
      | nil => simp [covers] at checked
      | cons wanted tail =>
          cases values with
          | nil => exact False.elim matched
          | cons value values =>
              obtain ⟨head, remaining⟩ := matched
              simp only [covers, Bool.and_eq_true, Bool.or_eq_true,
                Option.isNone_iff_eq_none, beq_iff_eq] at checked
              refine ⟨?_, ih remaining checked.2⟩
              rcases checked.1 with absent | same
              · exact Or.inl absent
              · simpa only [same] using head

/-- Weakening keeps all successful continuations and fatal-error provenance. -/
theorem stepSafe_mono {p q : Nat → Devm → Prop} {step : Step}
    (safe : StepSafe p step) (forward : ∀ pc post, p pc post → q pc post) :
    StepSafe q step := by
  cases step with
  | halt out => exact safe
  | cont pc post => exact forward pc post safe
  | spawn child resume pc =>
      intro settled
      exact ⟨fun post run => forward pc post ((safe settled).1 post run),
        (safe settled).2⟩

/-- A finite search tree. Correct ordering is a checked property, not a
generator guarantee. Patterns describe the entire top-first operand stack. -/
inductive Table where
  | empty
  | node (pc : Nat) (input : Pattern) (left right : Table)

def Table.lookup : Table → Nat → Option Pattern
  | .empty, _ => none
  | .node key input left right, pc =>
      if pc < key then left.lookup pc
      else if key < pc then right.lookup pc
      else some input

/-- Every row in a tree satisfies a Boolean predicate. -/
def Table.all (check : Nat → Pattern → Bool) : Table → Bool
  | .empty => true
  | .node pc input left right =>
      check pc input && left.all check && right.all check

theorem Table.lookup_all {table : Table} {check : Nat → Pattern → Bool}
    (checked : table.all check = true) {pc : Nat} {input : Pattern}
    (found : table.lookup pc = some input) : check pc input = true := by
  induction table with
  | empty => cases found
  | node key words left right ihLeft ihRight =>
      simp only [Table.all, Bool.and_eq_true] at checked
      simp only [Table.lookup] at found
      split at found
      · exact ihLeft checked.1.2 found
      · split at found
        · exact ihRight checked.2 found
        · have same : pc = key := by omega
          cases same
          cases found
          exact checked.1.1

/-- Exact invariant selected by finite lookup. -/
def Table.Invariant (table : Table) (pc : Nat) (pre : Devm) : Prop :=
  ∃ input, table.lookup pc = some input ∧ Matches input pre.stack

/-- Every outgoing stack has its own bound and must match an existing row.
Input headroom alone does not discharge this check. -/
def checkSuccessor (table : Table) (maximum pc : Nat) (output : Pattern) : Bool :=
  match table.lookup pc with
  | none => false
  | some expected =>
      decide (output.length ≤ maximum) && decide (expected.length ≤ maximum) &&
        covers output expected

theorem checkSuccessor_safe {table : Table} {maximum pc : Nat}
    {output : Pattern} {post : Devm}
    (checked : checkSuccessor table maximum pc output = true)
    (matched : Matches output post.stack) : table.Invariant pc post := by
  unfold checkSuccessor at checked
  cases found : table.lookup pc with
  | none => simp [found] at checked
  | some expected =>
      simp only [found, Bool.and_eq_true, decide_eq_true_eq] at checked
      exact ⟨expected, found, matched.covered checked.2⟩

/-- Instruction-local validation uses the actual decoder's instruction and
literal bytes. Unsupported instructions fail closed. -/
def checkInstruction (code : ByteArray) (table : Table) (maximum pc : Nat)
    (input : Pattern) : Inst → Bool
  | .next (.push bytes fits) =>
      checkSuccessor table maximum (pc + (Ninst.push bytes fits).size)
        (some bytes.toB256 :: input)
  | .next (.reg instruction) =>
      match regularTransfer instruction input with
      | none => false
      | some output =>
          checkSuccessor table maximum (pc + (Ninst.reg instruction).size) output
  | .next (.exec .call) =>
      match callTransfer input with
      | none => false
      | some output =>
          checkSuccessor table maximum (pc + (Ninst.exec .call).size) output
  | .next (.exec _) => false
  | .jump .jumpdest => checkSuccessor table maximum (pc + 1) input
  | .jump .jump =>
      match jumpTransfer input with
      | none => false
      | some (destination, output) =>
          jumpable code destination.toNat &&
            checkSuccessor table maximum destination.toNat output
  | .jump .jumpi =>
      match jumpiTransfer input with
      | none => false
      | some (destination, _, output) =>
          jumpable code destination.toNat &&
            checkSuccessor table maximum destination.toNat output &&
            checkSuccessor table maximum (pc + 1) output
  | .last instruction =>
      match terminalTransfer instruction input with
      | none => false
      | some output => decide (output.length ≤ maximum)

def instructionStep (evm : Evm) : Inst → Step
  | .next instruction => Ninst.step evm instruction
  | .jump instruction => Step.ofJump (Jinst.run evm instruction)
  | .last instruction => .halt (Linst.run evm.sta evm.dyna instruction)

theorem checkInstruction_safe {evm : Evm} {table : Table} {maximum : Nat}
    {input : Pattern} {instruction : Inst}
    (matched : Matches input evm.dyna.stack) (bound : input.length ≤ 8)
    (checked : checkInstruction evm.sta.code table maximum evm.pc input instruction = true) :
    StepSafe table.Invariant (instructionStep evm instruction) := by
  cases instruction with
  | next instruction =>
      cases instruction with
      | push bytes fits =>
          have room : input.length < 1024 := by omega
          apply stepSafe_mono (ninst_push_safe (fits := fits) matched room)
          intro pc post result
          obtain ⟨rfl, postMatch⟩ := result
          exact checkSuccessor_safe checked postMatch
      | reg instruction =>
          cases transferred : regularTransfer instruction input with
          | none => simp [checkInstruction, transferred] at checked
          | some output =>
              simp only [checkInstruction, transferred] at checked
              apply stepSafe_mono (ninst_regularTransfer_safe matched bound transferred)
              intro pc post result
              obtain ⟨rfl, postMatch⟩ := result
              exact checkSuccessor_safe checked postMatch
      | exec instruction =>
          cases instruction <;> try simp [checkInstruction] at checked
          cases transferred : callTransfer input with
          | none => simp [transferred] at checked
          | some output =>
              simp only [transferred] at checked
              apply stepSafe_mono (ninst_callTransfer_safe matched bound transferred)
              intro pc post result
              obtain ⟨rfl, postMatch⟩ := result
              exact checkSuccessor_safe checked postMatch
  | jump instruction =>
      cases instruction with
      | jumpdest =>
          apply stepSafe_mono (jinst_jumpdestTransfer_safe matched (output := input) rfl)
          intro pc post result
          obtain ⟨rfl, postMatch⟩ := result
          exact checkSuccessor_safe checked postMatch
      | jump =>
          cases transferred : jumpTransfer input with
          | none => simp [checkInstruction, transferred] at checked
          | some pair =>
              obtain ⟨destination, output⟩ := pair
              simp only [checkInstruction, transferred, Bool.and_eq_true] at checked
              apply stepSafe_mono (jinst_jumpTransfer_safe matched transferred)
              intro pc post result
              obtain ⟨rfl, _, postMatch⟩ := result
              exact checkSuccessor_safe checked.2 postMatch
      | jumpi =>
          cases transferred : jumpiTransfer input with
          | none => simp [checkInstruction, transferred] at checked
          | some triple =>
              obtain ⟨destination, condition, output⟩ := triple
              simp only [checkInstruction, transferred, Bool.and_eq_true] at checked
              apply stepSafe_mono (jinst_jumpiTransfer_safe matched transferred)
              intro pc post result
              obtain ⟨actualCondition, _, branch, postMatch⟩ := result
              rcases branch with ⟨_, rfl⟩ | ⟨_, rfl, _⟩
              · exact checkSuccessor_safe checked.2 postMatch
              · exact checkSuccessor_safe checked.1.2 postMatch
  | last instruction =>
      cases transferred : terminalTransfer instruction input with
      | none => simp [checkInstruction, transferred] at checked
      | some output =>
          exact (terminalTransfer_safe matched transferred).noStackFault

/-- Width of the decoded instruction, including its actual PUSH immediate. -/
def instructionWidth : Inst → Nat
  | .next instruction => instruction.size
  | _ => 1

/-- A row must be in actual code and must not rely on padded PUSH bytes. -/
def checkRow (code : ByteArray) (table : Table) (maximum pc : Nat)
    (input : Pattern) : Bool :=
  decide (input.length ≤ maximum) && decide (pc < code.size) &&
    match code.getInst pc with
    | none => false
    | some instruction =>
        decide (pc + instructionWidth instruction ≤ code.size) &&
          checkInstruction code table maximum pc input instruction

theorem checkRow_safe {sevm : Sevm} {table : Table} {maximum pc : Nat}
    {input : Pattern} {pre : Devm}
    (limit : maximum ≤ 8) (matched : Matches input pre.stack)
    (checked : checkRow sevm.code table maximum pc input = true) :
    StepSafe table.Invariant (Evm.step ⟨pc, sevm, pre⟩) := by
  simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at checked
  have bound : input.length ≤ 8 := Nat.le_trans checked.1.1 limit
  cases decoded : sevm.code.getInst pc with
  | none => simp [decoded] at checked
  | some instruction =>
      simp only [decoded, Bool.and_eq_true, decide_eq_true_eq] at checked
      have safe := checkInstruction_safe (evm := ⟨pc, sevm, pre⟩)
        matched bound checked.2.2
      cases instruction <;>
        simpa only [Evm.step, Evm.getInst, decoded, instructionStep] using safe

/-- Structural row membership, independently of the search algorithm. -/
def Table.Row : Table → Nat → Pattern → Prop
  | .empty, _, _ => False
  | .node key words left right, pc, input =>
      (key = pc ∧ words = input) ∨ left.Row pc input ∨ right.Row pc input

theorem Table.row_all {table : Table} {check : Nat → Pattern → Bool}
    (checked : table.all check = true) {pc : Nat} {input : Pattern}
    (row : table.Row pc input) : check pc input = true := by
  induction table with
  | empty => exact False.elim row
  | node key words left right ihLeft ihRight =>
      simp only [Table.all, Bool.and_eq_true] at checked
      rcases row with ⟨rfl, rfl⟩ | row | row
      · exact checked.1.1
      · exact ihLeft checked.1.2 row
      · exact ihRight checked.2 row

/-- Strict ordering of every key in each subtree excludes duplicate PCs. -/
def Table.Ordered : Table → Prop
  | .empty => True
  | .node key _ left right =>
      (∀ pc input, left.Row pc input → pc < key) ∧
      (∀ pc input, right.Row pc input → key < pc) ∧
      left.Ordered ∧ right.Ordered

def Table.checkOrder : Table → Bool
  | .empty => true
  | .node pc _ left right =>
      left.all (fun key _ => decide (key < pc)) &&
      right.all (fun key _ => decide (pc < key)) &&
      left.checkOrder && right.checkOrder

theorem Table.checkOrder_sound {table : Table}
    (checked : table.checkOrder = true) : table.Ordered := by
  induction table with
  | empty => trivial
  | node key words left right ihLeft ihRight =>
      simp only [Table.checkOrder, Bool.and_eq_true] at checked
      refine ⟨?_, ?_, ihLeft checked.1.2, ihRight checked.2⟩
      · intro pc input row
        exact of_decide_eq_true (Table.row_all checked.1.1.1 row)
      · intro pc input row
        exact of_decide_eq_true (Table.row_all checked.1.1.2 row)

theorem Table.lookup_of_row {table : Table} (ordered : table.Ordered)
    {pc : Nat} {input : Pattern} (row : table.Row pc input) :
    table.lookup pc = some input := by
  induction table with
  | empty => exact False.elim row
  | node key words left right ihLeft ihRight =>
      rcases row with ⟨rfl, rfl⟩ | row | row
      · simp [Table.lookup]
      · have before := ordered.1 _ _ row
        simp only [Table.lookup, if_pos before]
        exact ihLeft ordered.2.2.1 row
      · have after := ordered.2.1 _ _ row
        have before : ¬ pc < key := by omega
        simp only [Table.lookup, if_neg before, if_pos after]
        exact ihRight ordered.2.2.2 row

theorem Table.row_of_lookup {table : Table} {pc : Nat} {input : Pattern}
    (found : table.lookup pc = some input) : table.Row pc input := by
  induction table with
  | empty => cases found
  | node key words left right ihLeft ihRight =>
      simp only [Table.lookup] at found
      split at found
      · exact Or.inr (Or.inl (ihLeft found))
      · split at found
        · exact Or.inr (Or.inr (ihRight found))
        · have same : key = pc := by omega
          exact Or.inl ⟨same, Option.some.inj found⟩

/-- Under checked strict ordering, search covers exactly the structural rows. -/
theorem Table.lookup_iff_row {table : Table} (ordered : table.Ordered)
    {pc : Nat} {input : Pattern} :
    table.lookup pc = some input ↔ table.Row pc input :=
  ⟨Table.row_of_lookup, Table.lookup_of_row ordered⟩

/-- No two structural rows assign different patterns to the same PC. -/
theorem Table.row_unique {table : Table} (ordered : table.Ordered)
    {pc : Nat} {input output : Pattern}
    (first : table.Row pc input) (second : table.Row pc output) : input = output := by
  have one := Table.lookup_of_row ordered first
  have two := Table.lookup_of_row ordered second
  exact Option.some.inj (one.symm.trans two)

/-- Complete finite validation, retaining the accepted transfer family's
eight-word ceiling as an explicit limit of this checker. -/
def checkTable (code : ByteArray) (table : Table) (maximum : Nat) : Bool :=
  decide (maximum ≤ 8) && table.checkOrder &&
    table.all (checkRow code table maximum)

/-- A successful finite check constructs all local actual-execution obligations. -/
theorem checkTable_certificate {sevm : Sevm} {table : Table} {maximum : Nat}
    (checked : checkTable sevm.code table maximum = true) :
    Certificate sevm table.Invariant maximum := by
  simp only [checkTable, Bool.and_eq_true, decide_eq_true_eq] at checked
  constructor
  · intro pc pre valid
    obtain ⟨input, found, matched⟩ := valid
    have row := Table.lookup_all checked.2 found
    simp only [checkRow, Bool.and_eq_true, decide_eq_true_eq] at row
    exact matched.length ▸ row.1.1
  · intro pc pre valid
    obtain ⟨input, found, matched⟩ := valid
    exact checkRow_safe checked.1.1 matched (Table.lookup_all checked.2 found)

end Blanc.AbstractStackSafety
