import Blanc.AbstractStackCertificate
import Blanc.ProxyPairUpgradePrograms

/-!
# Operand-stack safety for the deployed v1 upgrade-witness runtime

The first in-tree consumer of the shared stack-safety certificate checker.
`Blanc/AbstractStackCertificate.lean` owns the checker and a four-byte worked
example; this module points it at real compiled contract bytes — `v1Code`, the
74-byte runtime installed at `v1Implementation` in the proxy-pair upgrade
fixture and executed there by `ProxyPairUpgradeRefinement`.

The whole obligation is one finite `Table` and one `decide`. Nothing here is a
hand-rolled stack-height counter, and nothing here weakens the checker: the
table is checked against the public decoder, row by row, over the compiled
bytes the contract's own artifact theorems already pin.

What the runtime does, and why it is in reach of the accepted family: `fsig`
reads the selector with `PUSH0/CALLDATALOAD/PUSH1 0xe0/SHR`, `linearDispatchWith`
compares it with `DUP1/PUSH4/EQ` and a `JUMPI` per entry, each endpoint is
guarded by `CALLVALUE/ISZERO/JUMPI`, and the two bodies use only
`SLOAD/MSTORE/RETURN` and `CALLDATALOAD/SSTORE/STOP`. Every jump destination is
a `PUSH2` literal, including the dispatcher's fallback `JUMP`, which targets the
program's own entry `JUMPDEST` at 0 and so makes the certified region a genuine
cycle rather than a straight line.

The certified region is the 47 reachable program counters `0`-`69`. The four
bytes `70`-`73` are the compiled auxiliary `Func.revert` that the compiled
fallback never reaches; the checker asks for a row per reachable counter, not
per byte, so they carry none.

Semantic boundary: as at the owner module, this is local and same-frame. It
excludes operand-stack underflow and overflow at every reached node and bounds
the operand stack by three words. It says nothing about gas, termination — the
fallback loop in particular does not terminate — or whether any counter is
reached at all.
-/

namespace Blanc.ProxyPair.Upgrade

open Jaune AbstractStackSafety CompiledStackSafety

/-- One row per reachable program counter of `v1Code`, top-first, written as a
right-leaning search tree so the rows read in program order against the
disassembly. `none` forgets a literal, never an operand position.

```
  pc  instruction      row pattern
   0  JUMPDEST         []
   1  PUSH0            []
   2  CALLDATALOAD     [some 0]
   3  PUSH1 0xe0       [none]
   5  SHR              [some 224, none]
   6  DUP1             [none]
   7  PUSH4 selector   [none, none]
  12  EQ               [some valueSelector, none, none]
  13  PUSH2 0x31       [none, none]
  16  JUMPI            [some 49, none, none]
  17  PUSH4 selector   [none]
  22  EQ               [some setValueSelector, none]
  23  PUSH2 0x1f       [none]
  26  JUMPI            [some 31, none]
  27  PUSH2 0x00       []
  30  JUMP             [some 0]          -- fallback, back to the entry
  31  JUMPDEST         []                -- setValue guard
  32  CALLVALUE        []
  33  ISZERO           [none]
  34  PUSH2 0x29       [none]
  37  JUMPI            [some 41, none]
  38  PUSH0            []
  39  PUSH0            [some 0]
  40  REVERT           [some 0, some 0]
  41  JUMPDEST         []                -- setValue body
  42  PUSH1 0x04       []
  44  CALLDATALOAD     [some 4]
  45  PUSH1 0x07       [none]
  47  SSTORE           [some 7, none]
  48  STOP             []
  49  JUMPDEST         [none]            -- value() arm, selector still live
  50  POP              [none]
  51  CALLVALUE        []
  52  ISZERO           [none]
  53  PUSH2 0x3c       [none]
  56  JUMPI            [some 60, none]
  57  PUSH0            []
  58  PUSH0            [some 0]
  59  REVERT           [some 0, some 0]
  60  JUMPDEST         []                -- value() body
  61  PUSH1 0x07       []
  63  SLOAD            [some 7]
  64  PUSH0            [none]
  65  MSTORE           [some 0, none]
  66  PUSH1 0x20       []
  68  PUSH0            [some 32]
  69  RETURN           [some 0, some 32]
```
-/
def v1StackTable : AbstractStackSafety.Table :=
  .node 0 [] .empty <|
  .node 1 [] .empty <|
  .node 2 [some 0] .empty <|
  .node 3 [none] .empty <|
  .node 5 [some 224, none] .empty <|
  .node 6 [none] .empty <|
  .node 7 [none, none] .empty <|
  .node 12 [some valueSelector, none, none] .empty <|
  .node 13 [none, none] .empty <|
  .node 16 [some 49, none, none] .empty <|
  .node 17 [none] .empty <|
  .node 22 [some setValueSelector, none] .empty <|
  .node 23 [none] .empty <|
  .node 26 [some 31, none] .empty <|
  .node 27 [] .empty <|
  .node 30 [some 0] .empty <|
  .node 31 [] .empty <|
  .node 32 [] .empty <|
  .node 33 [none] .empty <|
  .node 34 [none] .empty <|
  .node 37 [some 41, none] .empty <|
  .node 38 [] .empty <|
  .node 39 [some 0] .empty <|
  .node 40 [some 0, some 0] .empty <|
  .node 41 [] .empty <|
  .node 42 [] .empty <|
  .node 44 [some 4] .empty <|
  .node 45 [none] .empty <|
  .node 47 [some 7, none] .empty <|
  .node 48 [] .empty <|
  .node 49 [none] .empty <|
  .node 50 [none] .empty <|
  .node 51 [] .empty <|
  .node 52 [none] .empty <|
  .node 53 [none] .empty <|
  .node 56 [some 60, none] .empty <|
  .node 57 [] .empty <|
  .node 58 [some 0] .empty <|
  .node 59 [some 0, some 0] .empty <|
  .node 60 [] .empty <|
  .node 61 [] .empty <|
  .node 63 [some 7] .empty <|
  .node 64 [none] .empty <|
  .node 65 [some 0, none] .empty <|
  .node 66 [] .empty <|
  .node 68 [some 32] .empty <|
  .node 69 [some 0, some 32] .empty .empty

/-- The whole obligation over the real compiled bytes: one finite evaluation
against the public decoder, `jumpable`, and the accepted transfer family. -/
theorem v1StackTable_checked : checkTable v1Code v1StackTable 3 = true := by
  decide +kernel

/-- ... and that evaluation is the certificate, for every machine running the
deployed v1 implementation code. -/
theorem v1Code_certificate {sevm : Sevm} (code : sevm.code = v1Code) :
    Certificate sevm v1StackTable.Invariant 3 :=
  checkTable_certificate (code ▸ v1StackTable_checked)

/-- Entering the runtime at its own entry counter with an empty operand stack
satisfies the checked invariant, so the certificate applies to actual calls. -/
theorem v1StackTable_entry {devm : Devm} (stack : devm.stack = []) :
    v1StackTable.Invariant 0 devm :=
  ⟨[], rfl, by rw [stack]; exact matches_nil⟩

/-- The transported conclusion, over the existing same-frame chronology: every
node an actual v1 frame reaches from its entry keeps at most three operand
words and generates no operand-stack fault. Terminal and failing nodes are
included; a fault arriving through a child settlement is attributed to the
child by `InheritedStackFault`, not excluded. -/
theorem v1_stack_safe_from_entry {sevm : Sevm} {root node : Exec.Deriv}
    (code : sevm.code = v1Code)
    (frame : root.sevm = sevm) (entry : root.pc = 0)
    (stack : root.devm.stack = [])
    (reached : Exec.Deriv.ParentPrefix root node) :
    node.devm.stack.length ≤ 3 ∧
      StepSafe v1StackTable.Invariant
        (Evm.step ⟨node.pc, node.sevm, node.devm⟩) :=
  (v1Code_certificate code).at_parentPrefix reached frame
    (by rw [entry]; exact v1StackTable_entry stack)

/-! ### The check bites

Four negative controls, each a live evaluation rather than a comment. They
establish that `v1StackTable_checked` is a fact about *these* bytes and *this*
table, not a shape the checker accepts by default. -/

/-- The same table against the v2 runtime is rejected: the certificate is
about the compiled bytes, not about the row format. -/
example : checkTable v2Code v1StackTable 3 = false := by decide +kernel

/-- A row whose successor is absent from the table is rejected. `SSTORE` at 47
continues to 48, and a table without that row cannot discharge it. -/
example :
    checkTable v1Code (.node 47 [some 7, none] .empty .empty) 3 = false := by
  decide +kernel

/-- A literal jump destination that is not a `JUMPDEST` is rejected. Naming 50
instead of 49 at the first `JUMPI` lands inside the `value()` arm's `POP`.
The bytecode's `PUSH2` immediate and the complete accepted table are changed
together, so neither a stale predecessor literal nor missing successor rows
can account for the rejection. -/
private def v1CodeInvalidDestination : ByteArray :=
  ByteArray.mk ((v1Bytes.set 15 50).toArray)

private def v1StackTableInvalidDestination : AbstractStackSafety.Table :=
  .node 0 [] .empty <|
  .node 1 [] .empty <|
  .node 2 [some 0] .empty <|
  .node 3 [none] .empty <|
  .node 5 [some 224, none] .empty <|
  .node 6 [none] .empty <|
  .node 7 [none, none] .empty <|
  .node 12 [some valueSelector, none, none] .empty <|
  .node 13 [none, none] .empty <|
  .node 16 [some 50, none, none] .empty <|
  .node 17 [none] .empty <|
  .node 22 [some setValueSelector, none] .empty <|
  .node 23 [none] .empty <|
  .node 26 [some 31, none] .empty <|
  .node 27 [] .empty <|
  .node 30 [some 0] .empty <|
  .node 31 [] .empty <|
  .node 32 [] .empty <|
  .node 33 [none] .empty <|
  .node 34 [none] .empty <|
  .node 37 [some 41, none] .empty <|
  .node 38 [] .empty <|
  .node 39 [some 0] .empty <|
  .node 40 [some 0, some 0] .empty <|
  .node 41 [] .empty <|
  .node 42 [] .empty <|
  .node 44 [some 4] .empty <|
  .node 45 [none] .empty <|
  .node 47 [some 7, none] .empty <|
  .node 48 [] .empty <|
  .node 49 [none] .empty <|
  .node 50 [none] .empty <|
  .node 51 [] .empty <|
  .node 52 [none] .empty <|
  .node 53 [none] .empty <|
  .node 56 [some 60, none] .empty <|
  .node 57 [] .empty <|
  .node 58 [some 0] .empty <|
  .node 59 [some 0, some 0] .empty <|
  .node 60 [] .empty <|
  .node 61 [] .empty <|
  .node 63 [some 7] .empty <|
  .node 64 [none] .empty <|
  .node 65 [some 0, none] .empty <|
  .node 66 [] .empty <|
  .node 68 [some 32] .empty <|
  .node 69 [some 0, some 32] .empty .empty

/-- The original destination is accepted by the otherwise identical table. -/
example : checkTable v1Code v1StackTable 3 = true := v1StackTable_checked

example : checkTable v1CodeInvalidDestination v1StackTableInvalidDestination 3 = false := by
  decide +kernel

/-- The declared ceiling binds: the table's deepest row is three words, so a
ceiling of one is rejected rather than silently widened. -/
example : checkTable v1Code v1StackTable 1 = false := by decide +kernel

end Blanc.ProxyPair.Upgrade
