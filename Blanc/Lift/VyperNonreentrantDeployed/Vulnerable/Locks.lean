import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame0

/-!
V- witness, the lock facts and the frames' identities as closed evaluations (kernel only;
do not open this file in the language server).

* The deployed implementation's bytes: `remove_liquidity`'s guard is `PUSH1 2; SLOAD;
  PUSH2 0x447a; JUMPI; PUSH1 1; PUSH1 2; SSTORE` at pcs 6900-6911 and its release
  `PUSH1 0; PUSH1 2; SSTORE` at 7788-7792; `add_liquidity`'s guard is the same pattern on
  slot 0 at pcs 88-99 and its release at 2017-2021.  Two functions, one lock name, two
  slots: the defect.
* Frame 1 at its `CALL` to the attacker (step 339) holds slot 2 = 1.
* The attacker's frame (EELS frame 2) runs `A`'s code with the 100 wei; the proxy frame it
  spawns (frame 3) is `P` running the proxy with `add_liquidity([100, 0], 0, A)`; frame 4
  is `P` running the implementation with that calldata, entered with slot 2 = 1 (the outer
  lock) and slot 0 = 0.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Subtree

/-- `add_liquidity(uint256[2],uint256,address)` = `0x0c3e4b54`, `([100, 0], 0, A)`: the
calldata the attacker's code builds. -/
def addCalldata : Bytes :=
  [0x0c, 0x3e, 0x4b, 0x54] ++ word 100 ++ word 0 ++ word 0 ++ word attackerAddress.toNat

/-! ### The two guards in the deployed bytes -/

theorem remove_guard_bytes :
    (code.getInst 6900, code.getInst 6902, code.getInst 6906, code.getInst 6907,
      code.getInst 6909, code.getInst 6911) =
    (some (.next (.push [0x02] (by decide))), some (.next (.reg .sload)),
      some (.jump .jumpi), some (.next (.push [0x01] (by decide))),
      some (.next (.push [0x02] (by decide))), some (.next (.reg .sstore))) := by
  kernel_rfl

theorem remove_release_bytes :
    (code.getInst 7788, code.getInst 7790, code.getInst 7792) =
    (some (.next (.push [0x00] (by decide))), some (.next (.push [0x02] (by decide))),
      some (.next (.reg .sstore))) := by
  kernel_rfl

theorem add_guard_bytes :
    (code.getInst 88, code.getInst 90, code.getInst 94, code.getInst 95, code.getInst 97,
      code.getInst 99) =
    (some (.next (.push [0x00] (by decide))), some (.next (.reg .sload)),
      some (.jump .jumpi), some (.next (.push [0x01] (by decide))),
      some (.next (.push [0x00] (by decide))), some (.next (.reg .sstore))) := by
  kernel_rfl

theorem add_release_bytes :
    (code.getInst 2017, code.getInst 2019, code.getInst 2021) =
    (some (.next (.push [0x00] (by decide))), some (.next (.push [0x00] (by decide))),
      some (.next (.reg .sstore))) := by
  kernel_rfl

/-! ### The run -/

/-- Frame 1 at its `CALL` of the attacker: the remove-lock (slot 2) is held. -/
theorem lock_cfg339 : lookupS cfg339.stor proxyAddress (2 : Nat).toB256 = (1 : Nat).toB256 := by
  kernel_rfl

/-- The attacker's frame, the proxy frame it spawns, and frame 4 (the reentrant
`add_liquidity`), with the storage frame 4 is entered with. -/
theorem subtree_facts :
    (e2.sta.currentTarget, e2.sta.code, e2.sta.value,
      e3.sta.currentTarget, e3.sta.caller, e3.sta.data,
      e4.pc, e4.sta.currentTarget, e4.sta.caller, e4.sta.data,
      lookupS aCall.stor proxyAddress (2 : Nat).toB256,
      lookupS aCall.stor proxyAddress (0 : Nat).toB256) =
    (attackerAddress, attackerCode, (100 : Nat).toB256,
      proxyAddress, attackerAddress, addCalldata,
      0, proxyAddress, attackerAddress, addCalldata,
      (1 : Nat).toB256, 0) := by
  kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Top
