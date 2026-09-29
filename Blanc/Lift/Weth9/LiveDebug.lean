import Lean

open Lean Meta Elab Tactic in
elab "rshow" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let args := t.getAppArgs
  let d := args[2]!
  let d ← whnfR d
  let da := d.getAppArgs
  logInfo m!"stack {da[1]!}
mem {da[2]!}
gas {da[3]!}"

