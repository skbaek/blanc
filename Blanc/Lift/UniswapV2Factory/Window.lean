import Blanc.Lift.CursorWindow
import Blanc.Lift.UniswapV2Factory.Cert

/-!
# The factory's `CREATE2` → `CALL` window, kernel-checked

`createPair`'s body occurs in two clones of the certificate (entries `c2` and `c10`), each with the
`CREATE2` node at pc `0x5e2` and the `initialize` `CALL` at pc `0x661`.  `window` lists, for both clones,
the trees from the one after the `CREATE2` node to the `CALL` node (60 each: the straight line to the
`EXTCODESIZE` check's `JUMPI`, its taken arm, `POP`, `GAS`, `CALL`), each with its predecessor.
`cert_windowOk` checks over the whole certificate that these trees are entered only from their
predecessors and that the two window `CALL` nodes are the certificate's only `CALL` nodes.  Kept in its
own module so that no language-server worker elaborates the decisions.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune

/-- The `j`-th window tree of a clone: after the `CREATE2` node of `t5`, then into the taken arm `t6`. -/
def wtree (t5 t6 : SFunc) (j : Nat) : SFunc :=
  if j < 56 then SFunc.lineDrop (81 + j) t5 else SFunc.lineDrop (j - 56) t6

/-- The predecessor of the `j`-th window tree: the `CREATE2` node, then the previous window tree. -/
def wpred (t5 t6 : SFunc) : Nat → SFunc
  | 0 => SFunc.lineDrop 80 t5
  | j + 1 => wtree t5 t6 j

/-- One clone's window, indexed from `base`. -/
def windowOf (t5 t6 : SFunc) (base : Nat) : List WindowEntry :=
  (List.range 60).map fun j => (wtree t5 t6 j, wpred t5 t6 j, base + j)

/-- Both clones' windows: clone `c2` indexed from `0`, clone `c10` from `100`. -/
def window : List WindowEntry := windowOf t_0531_c2 t_065e_c2 0 ++ windowOf t_0531_c10 t_065e_c10 100

/-- The two window `CALL` nodes. -/
def callSites : List SFunc := [wtree t_0531_c2 t_065e_c2 59, wtree t_0531_c10 t_065e_c10 59]

/-- **The window check.**  Window trees are entered only from their predecessors, and the window `CALL`
nodes are the certificate's only `CALL` nodes. -/
theorem cert_windowOk : cert.windowOk window callSites = true := by decide +kernel

/-- The predecessor of the first window tree is the `CREATE2` node. -/
theorem wpred_zero_c2 : wpred t_0531_c2 t_065e_c2 0 =
    .next (.exec .create2) (wtree t_0531_c2 t_065e_c2 0) := by decide +kernel

theorem wpred_zero_c10 : wpred t_0531_c10 t_065e_c10 0 =
    .next (.exec .create2) (wtree t_0531_c10 t_065e_c10 0) := by decide +kernel


/-- One window edge: an instruction node, a `JUMPI` node (its taken arm), or a `JUMPDEST`. -/
inductive EdgeOp where
  | inst (n : Ninst)
  | branch
  | dest
deriving DecidableEq

/-- The edge a tree's head node makes. -/
def edgeOp : SFunc → Option EdgeOp
  | .next n _ => some (.inst n)
  | .branch _ _ => some .branch
  | .dest _ => some .dest
  | _ => none

/-- The 59 window edges, from the node after `CREATE2` to the `CALL` node. -/
def windowOps : List EdgeOp := [
  .inst (.push [0x40] (by decide)),
  .inst (.reg (.dup 0)),
  .inst (.reg .mload),
  .inst (.push [0x48, 0x5c, 0xc9, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)),
  .inst (.reg (.dup 1)),
  .inst (.reg .mstore),
  .inst (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] (by decide)),
  .inst (.reg (.dup 7)),
  .inst (.reg (.dup 1)),
  .inst (.reg .and),
  .inst (.push [0x04] (by decide)),
  .inst (.reg (.dup 3)),
  .inst (.reg .add),
  .inst (.reg .mstore),
  .inst (.reg (.dup 6)),
  .inst (.reg (.dup 1)),
  .inst (.reg .and),
  .inst (.push [0x24] (by decide)),
  .inst (.reg (.dup 3)),
  .inst (.reg .add),
  .inst (.reg .mstore),
  .inst (.reg (.swap 1)),
  .inst (.reg .mload),
  .inst (.reg (.swap 2)),
  .inst (.reg (.swap 7)),
  .inst (.reg .pop),
  .inst (.reg (.swap 0)),
  .inst (.reg (.dup 7)),
  .inst (.reg .and),
  .inst (.reg (.swap 1)),
  .inst (.push [0x48, 0x5c, 0xc9, 0x55] (by decide)),
  .inst (.reg (.swap 1)),
  .inst (.push [0x44] (by decide)),
  .inst (.reg (.dup 0)),
  .inst (.reg (.dup 2)),
  .inst (.reg .add),
  .inst (.reg (.swap 2)),
  .inst (.push [0x00] (by decide)),
  .inst (.reg (.swap 2)),
  .inst (.reg (.swap 0)),
  .inst (.reg (.swap 1)),
  .inst (.reg (.swap 0)),
  .inst (.reg (.dup 2)),
  .inst (.reg (.swap 0)),
  .inst (.reg .sub),
  .inst (.reg .add),
  .inst (.reg (.dup 1)),
  .inst (.reg (.dup 3)),
  .inst (.reg (.dup 7)),
  .inst (.reg (.dup 0)),
  .inst (.reg .extcodesize),
  .inst (.reg .iszero),
  .inst (.reg (.dup 0)),
  .inst (.reg .iszero),
  .inst (.push [0x06, 0x5e] (by decide)),
  .branch,
  .dest,
  .inst (.reg .pop),
  .inst (.reg .gas)]

/-- Both clones' window edges are `windowOps`. -/
theorem windowOps_c2 : ∀ j < 59, edgeOp (wtree t_0531_c2 t_065e_c2 j) = windowOps[j]? := by
  decide +kernel

theorem windowOps_c10 : ∀ j < 59, edgeOp (wtree t_0531_c10 t_065e_c10 j) = windowOps[j]? := by
  decide +kernel

end Blanc.Lift.UniswapV2Factory
