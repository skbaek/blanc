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

/-- Success-only soundness: a successful run of an accepted instruction leaves
a stack matching the transferred pattern. -/
theorem ninstTransfer_run {sevm : Sevm} {devm devm' : Devm} {n : Ninst}
    {input output : Pattern} (hfork : CoveredFork sevm.benvStat.fork)
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
  sorry

/-- Locality: an accepted transfer ignores the words below those it inspects. -/
theorem ninstTransfer_append {n : Ninst} {input output : Pattern}
    (below : Pattern) (checked : ninstTransfer n input = some output) :
    ninstTransfer n (input ++ below) = some (output ++ below) := by
  sorry

end Blanc.Lift
