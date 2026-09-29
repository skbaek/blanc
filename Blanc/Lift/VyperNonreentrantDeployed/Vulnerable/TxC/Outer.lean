import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTopC
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Outer

/-!
V- as an admitted transaction under every covered fork, the outer transaction frame: the kernel
decision.

The tx-level dispatcher attacker `A'` (`Attacker2`), entered from the real transaction-shaped
message `msgC` (`TxTopC`: `prepareMessage` under EIP-2929 pre-warming, EOA `E` -> `A'`), runs its
own certificate to its `CALL` into the pool proxy `P` (`callCfgC`/`cp0C`) and, from a settled
child with the tx trace's gas, return data and refund counter (all its other parts free), resumes,
drops the success flag and `STOP`s with the observed gas, empty output, no error and the child's
storage shadow untouched (`frame0txC_kernel`).  `OuterAt.lean` turns this into the `Exec` and
`processMessage` facts of the whole outer frame under any covered fork.

Kernel-only boundary facts (`kernel_forall_rfl`); do not open this file in the language server
alongside the deep chain.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- The EELS gas at `A'`'s `STOP` (tx trace, frame 0): 15,822,837. -/
def gas0outC : Nat := 15822837

/-- The gas `A'`'s child frame (`P` running `remove_liquidity`) returns with (tx trace,
frame 1): 15,573,249. -/
def childGasC : Nat := 15573249

/-- `A'`'s frame after its `CALL` to `P`, from a settled child `d1` and the child's shadows:
resume the `CALL` (dropping its output, `retLen = 0`), then `POP`; `STOP` (two nodes). -/
def run0C (d1 : Devm) (ck : List (Adr × B256)) (ca : List Adr)
    (cs : StorShadow) (cc : AcctShadow) : Res :=
  match callResume e0C.sta callCfgC d1 ck ca cs cc with
  | some c => wrun fs2 e0C.sta 2 c
  | none => .stuck

/-- `A'`'s halt: gas, return data (empty), success, and the halting configuration's storage
shadow (which is the child's, since `POP`; `STOP` change no storage).  Reading `P`'s
`totalSupply` (slot 26) and the attacker's LP balance from that shadow is what carries the
corruption up from the child. -/
def obs0C : Res → Option (Nat × List Nat × Bool × StorShadow × AdrSet)
  | .done (.halted d) cl => some (d.gasLeft, d.output.map UInt8.toNat,
      d.error.isNone && decide (d.refundCounter = refund0), cl.stor, d.accountsToDelete)
  | _ => none

/-- **`A'`'s outer frame halts, for any settled child** with the tx trace's gas and return
data (all its other parts free): `A'` drops the success flag and `STOP`s with its own gas and
empty output, no error, leaving the child's storage shadow `cs` untouched. -/
theorem frame0txC_kernel : ∀ (d1 : Devm) (ck : List (Adr × B256)) (ca : List Adr)
    (cs : StorShadow) (cc : AcctShadow),
    obs0C (run0C (childObsX childGasC childOut refund0 d1) ck ca cs cc) =
      some (gas0outC, [], true, cs, .emptyWithCapacity) := by
  kernel_forall_rfl

theorem e0txC_code : e0C.sta.code = Attacker2.code := by
  have h := e0C_facts; simp only [Prod.mk.injEq] at h; exact h.2.1

theorem e0txC_pc : e0C.pc = 0 := by
  have h := e0C_facts; simp only [Prod.mk.injEq] at h; exact h.1

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
