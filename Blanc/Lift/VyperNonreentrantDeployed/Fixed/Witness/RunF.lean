import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness.Setup

/-!
# V+ witness, the pool frame `F` up to its `STATICCALL`

Kernel decisions (do not open this file in the language server): the pool frame's walk
from its entry to the `remove_liquidity` body start `0x1bae` (174 steps), and from there to
the `STATICCALL` of `_balances` at `0x337a` (57 steps, none at a release pc), and the
`STATICCALL`'s spawn of the reader frame.  The step counts are the EELS trace's
(`scripts/lift/witness/vplus_run.py`); the kernel checks them.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun

/-- A walk configuration or a default. -/
def getC (d : PCfg) : PRes → PCfg
  | .cont c => c
  | _ => d

/-- No check. -/
def okAll : Nat → Bool := fun _ => true
/-- Not at a release `SSTORE`. -/
def okRel : Nat → Bool := fun pc => !lockReleasePcs.contains pc
/-- Not at a guarded body start. -/
def okBody : Nat → Bool := fun pc => !lockBodies.contains pc

/-- The pool frame at the body start of `remove_liquidity`. -/
def cB : PCfg := getC c0 (pwalk codeTries e0.sta okAll 174 c0)

theorem walkB : pwalk codeTries e0.sta okAll 174 c0 = .cont cB := by kernel_rfl

theorem cB_pc : cB.pc = 0x1bae := by kernel_rfl

/-- The pool frame at its `STATICCALL` (`coins[1].balanceOf(self)` in `_balances`). -/
def cH : PCfg := getC c0 (pwalk codeTries e0.sta okRel 57 cB)

theorem walkH : pwalk codeTries e0.sta okRel 57 cB = .cont cH := by kernel_rfl

theorem cH_pc : cH.pc = 0x337a := by kernel_rfl

theorem decodeH : decodeT 15 codeTries.bytes 0x337a = some (.next (.exec .staticcall)) := by
  kernel_rfl

/-- The `STATICCALL`, computed up to its spawn. -/
def cpH : CallPrep :=
  (scallPrep e0.sta cH.devm cH.adrs cH.acs).getD ⟨f0, default, 0, 0, []⟩

theorem scallH : scallPrep e0.sta cH.devm cH.adrs cH.acs = some cpH := by kernel_rfl

/-- The reader frame's entry machine. -/
def eT : Evm := match frameEnterS cpH.f cH.acs with | .run e => e | .done _ => default

theorem enterT : frameEnterS cpH.f cH.acs = .run eT := by kernel_rfl

/-- The pool holds the comparator in the entry shadow. -/
theorem c0_pool_code : (lookupA c0.acs poolAddress).code = code := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness
