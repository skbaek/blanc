import Blanc.Lift.VyperNonreentrantDeployed.Token20.Run
import Blanc.Lift.ExactLeaf

/-!
# The synthetic token `T` as a node-walk child of a pool frame

The forms of `Run.lean` a pool witness consumes at a `CALL` or `STATICCALL` into `T`
(`spawn_resume_ok`, `Blanc/Lift/NodeWalkFrames.lean`).  Each `*_child` theorem takes the child's
start configuration `c` (pc 0, empty stack and memory) with its agreeing shadows (`PAgree c`, as
`call_node`/`staticcall_node` hand it over), the selector, and premises read from the shadows
only, and gives, under any covered fork:

* the shadows of the machine the child returns (`ChildAgree`): the accessed keys, and the
  storage shadow with exactly the token's writes prepended — nothing else moves;
* for every derivation node at `c`: the successful outcome, an explicit machine evaluated over
  the shadows (`*PostS`; no hash set is inspected), and no raw frame descendant (the code spawns
  nothing, `spawnFreeReach`).

Gas is exact: the frame's gas is `G + *GasS`, the post's gas left `G`.  Every executed instruction
is one of `PUSH*`, `DUP*`, `SWAP*`, `POP`, `CALLDATALOAD`, `SHR`, `EQ`, `LT`, `GT`, `ADD`, `SUB`,
`AND`, `CALLER`, `MSTORE`, `KECCAK256`, `SLOAD`, `SSTORE`, `JUMP`, `JUMPI`, `JUMPDEST`, `RETURN`:
all fork-neutral, and the theorems hold for every `CoveredFork` directly.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Token20

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk

/-! ## The move, on the shadows -/

section MoveS

variable (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow) (src dst : Adr) (v : B256)

end MoveS

/-! ## `transfer` -/

/-! ## `transferFrom` -/

section TfS

variable (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow)

end TfS

/-! ## `approve` -/

/-- The allowance slot `approve` writes. -/
abbrev apSlot (sevm : Sevm) : B256 := allowSlot sevm.caller (apSpender sevm)

/-- What `approve` costs, on the shadows. -/
def approveGasS (sevm : Sevm) (keys : List (Adr × B256)) (stor : StorShadow) : Nat :=
  203 + sstoreCostS sevm keys stor (apSlot sevm) (apVal sevm)

/-- The machine a successful `approve` halts with, on the shadows. -/
def approvePostS (sevm : Sevm) (c : PCfg) (G : Nat) : Devm :=
  retPost (afterSstoreS sevm c.keys c.stor c.devm (apSlot sevm) (apVal sevm)) [Sevm.selector sevm]
    (okMem (scratch sevm.caller.toB256 (apSpender sevm).toB256)) G 1

/-- **`approve(spender, v)` from a frame** (the token owner's root call in a setup).  The child
returns the word `1` with `allowance[caller][spender] := v` prepended to the storage shadow. -/
theorem approve_child {sevm : Sevm} {c : PCfg} {G : Nat} (hcode : sevm.code = code)
    (hfork : CoveredFork sevm.benvStat.fork) (hstatic : sevm.isStatic = false)
    (hsel : Sevm.selector sevm = 0x095ea7b3) (hpc : c.pc = 0) (hstack : c.devm.stack = [])
    (hmem : c.devm.memory = Mem.empty) (hag : PAgree c)
    (hgas : c.devm.gasLeft = G + approveGasS sevm c.keys c.stor) (hsent : gCallStipend < G) :
    ChildAgree (approvePostS sevm c G) ((sevm.currentTarget, apSlot sevm) :: c.keys) c.adrs
        (((sevm.currentTarget, apSlot sevm), apVal sevm) :: c.stor) c.acs ∧
      ∀ x, NodeAt sevm c x → x.exn = .ok (approvePostS sevm c G) ∧
        Exec.rawFrameDescendants x.exc = [] := by
  have h := childAgree_of_pagree hag
  have hpost : approvePost sevm c.devm G = approvePostS sevm c G := by
    unfold approvePost approveBase approvePostS; rw [afterSstore_shadow h]
  have hrun := approve_runExact (G := G) hfork hstatic hsel hstack hmem
    (by rw [hgas]; unfold approveGas approveGasS; rw [sstoreCost_shadow h]) hsent
  rw [hpost] at hrun
  refine ⟨?_, exact_leaf cert_check cert_jumpsOk spawnFreeReach hcode hfork hpc hrun⟩
  rw [← hpost]
  exact ChildAgree.ret (ChildAgree.afterSstore (sevm := sevm) h (apSlot sevm) (apVal sevm)) _ _ _ _ _ _

/-! ## `balanceOf` -/

end Blanc.Lift.VyperNonreentrantDeployed.Token20
