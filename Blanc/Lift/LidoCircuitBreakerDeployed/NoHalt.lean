import Blanc.Lift.LidoCircuitBreakerDeployed.Prog
import Blanc.Lift.InvWalkWorld

/-! The entries the two Registry writers' walks call never halt the frame: each
ends only in `revert` or an internal return.  One kernel check over their
closure, kept in its own module so no language-server file elaborates it. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Blanc.Lift

/-- The call closure of the `registerPauser` body (21) and the `pause` body (13). -/
def writerNoHalt : List Nat :=
  [2, 3, 4, 5, 7, 13, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 32, 33, 37, 38, 39, 40, 42]

theorem writerNoHalt_set : NoHaltSet prog writerNoHalt = true := by
  decide +kernel

/-- A step that is not an external operation (no `CALL`/`CREATE`-family `exec`). -/
def instRegOnly : Jaune.Ninst → Bool
  | .reg _ => true
  | .push _ _ => true
  | _ => false

/-- A tree whose steps are all `instRegOnly` and which halts only by reverting. -/
def treeRegOnly : SFunc → Bool
  | .branch f g => treeRegOnly f && treeRegOnly g
  | .branchTo f _ => treeRegOnly f
  | .last .revert => true
  | .last _ => false
  | .next n f => instRegOnly n && treeRegOnly f
  | .dest f => treeRegOnly f
  | .jump _ => true
  | .callNext _ f => treeRegOnly f
  | .ret => true
  | .pcAt _ f => treeRegOnly f
  | .undefined => true

/-- `S` is closed under references, and all its members are `treeRegOnly`. -/
def RegOnlySet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => treeRegOnly g && g.refs.all (· ∈ S)
    | none => false

/-- The call closure of `setPauser` (entry 32). -/
def setPauserClosure : List Nat := [3, 4, 5, 24, 25, 26, 27, 28, 32, 38, 39, 40, 42]

theorem setPauserClosure_regOnly : RegOnlySet prog setPauserClosure = true := by
  decide +kernel

end Blanc.Lift.LidoCircuitBreakerDeployed
