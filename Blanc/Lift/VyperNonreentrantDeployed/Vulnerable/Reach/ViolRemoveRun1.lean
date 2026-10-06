import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary

/-!
# V− P2, F2 kernel prefix: `remove_liquidity` entry to its ETH `CALL`

Prague kernel decisions of F2's 339-step prefix (static machine `sRm`, original state
`O0`, certificate interpreter `fsI`) between the committed literal boundaries of
`ViolBoundary.lean`, over **free** shadow tails, world and bookkeeping
(`Boundary.cfgOfT`/`obsDT`, `Blanc/Lift/ShadowTail.lean`): the literal prefixes are decided,
the tails compared as terms. Do not open this file in the language server.

* `rmChunk161`: entry `bRm0` to step 161 (`bRm161`, node `t_1af3_c23`);
* `cRm339`/`cpRm`/`e3Rm`: F2's ETH `CALL` of the attacker as data (no new literal):
  the configuration after 339 steps, the `CALL` preparation, and the spawned
  callback frame F3.

The post-`CALL` stages (callback resume, token child, halt) and the fork/orig-state
transport live in later `ViolRemoveRun*` modules and `Reach/ViolRemove.lean`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-- Steps 0 to 161, over any tails, world and bookkeeping. -/
theorem rmChunk161 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRm161 (wrun fsI sRm 161 (Boundary.cfgOfT bRm0 tS tA m w)) =
      Boundary.obsDOkT bRm161 tS tA := by
  kernel_forall_rfl

/-! ## F2 to its ETH `CALL`, as data -/

/-- F2 at its ETH `CALL` of the attacker: the configuration after 339 steps. -/
def cRm339 (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Cfg :=
  match wrun fsI sRm 339 (Boundary.cfgOfT bRm0 tS tA m w) with
  | .cont c => c
  | _ => Boundary.cfgOfT bRm0 tS tA m w

theorem cRm339_eq : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    wrun fsI sRm 339 (Boundary.cfgOfT bRm0 tS tA m w) =
      .cont (cRm339 tS tA m w) := by
  kernel_forall_rfl

/-- F2's `CALL` up to its spawn. -/
def cpRm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : CallPrep :=
  (callPrep sRm (cRm339 tS tA m w)).getD noPrepI

theorem cpRm_eq : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    callPrep sRm (cRm339 tS tA m w) = some (cpRm tS tA m w) := by
  kernel_forall_rfl

/-- The callback frame F3 as spawned by F2's `CALL`. -/
def e3Rm (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) : Evm :=
  match frameEnterS (cpRm tS tA m w).f (cRm339 tS tA m w).acs with
  | .run e => e
  | .done _ => default

theorem e3Rm_eq : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    frameEnterS (cpRm tS tA m w).f (cRm339 tS tA m w).acs =
      .run (e3Rm tS tA m w) := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
