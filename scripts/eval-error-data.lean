-- eval-error-data.lean : evaluate Blanc's landed Error(string) encoding.
--
-- Run from the repository root:
--
--     lake env lean --run scripts/eval-error-data.lean 'WETH: Expired permit'
--
-- It prints exactly one 0x-prefixed hexadecimal blob for each supplied string.
-- `check-error-data.sh` owns the lock enumeration and compares this direct
-- evaluation with its independent Python ABI derivation.

import Blanc.RevertPayload

namespace Blanc

open Jaune

private def hexOf (bs : Bytes) : String := "0x" ++ Bytes.toHex bs

/-- The fresh-memory instantiation of `runCompiledTo_revertWith`'s additive gas
term.  It deliberately excludes a table-entry `JUMPDEST`: this is the emitted
`Func.revertWith` body measured by the payload report. -/
private def freshGas (s : String) : Nat :=
  let blob := errorData s
  storesFixedCost (bytesWords blob).zipIdx +
    pushCost (Nat.toB256 blob.length).toBytes.sig + gBase +
    Mem.expansionCost Mem.empty 0 (32 * (bytesWords blob).length)

private def inlineCodeBytes? (s : String) : Option Nat :=
  match Func.compile [] 0 (Func.revertWith s) with
  | some bs => some bs.length
  | none => none

end Blanc

def main (inputs : List String) : IO Unit := do
  let measure := inputs.head? = some "--measure"
  let reasons := if measure then inputs.drop 1 else inputs
  if reasons.isEmpty then
    throw (IO.userError "usage: eval-error-data.lean <reason> [<reason> ...]")
  for s in reasons do
    if measure then
      match Blanc.inlineCodeBytes? s with
      | some codeBytes =>
          IO.println s!"{(Blanc.errorData s).length}\t{codeBytes}\t{Blanc.freshGas s}"
      | none =>
          throw (IO.userError s!"Func.revertWith failed to compile for {repr s}")
    else
      IO.println (Blanc.hexOf (Blanc.errorData s))
