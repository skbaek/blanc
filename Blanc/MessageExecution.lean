import Blanc.Semantics
import Jaune.MessageExecution

/-!
# From raw code execution to settled message results

The contract-neutral adapters between `exec (initEvm msg)` and top-level
`processMessage msg` (`Jaune.MessageExecution`, including the canonical settled
machines `settledRevert` and `settledHalt`) and the canonical message-entry
projections are owned by Jaune's `Jaune.MessageExecution`.  This module keeps
Blanc's import point for them.
-/
