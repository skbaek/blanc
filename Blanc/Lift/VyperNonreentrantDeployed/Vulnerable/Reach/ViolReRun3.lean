import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolBoundary

/-!
# V− V4, the re-entrant `add_liquidity` frame (F5): step 2625 to its `RETURN`

Prague kernel decisions of the re-entrant frame's run (static machine `sRe`, original state
`O0`) between the committed literal boundaries, over free shadow tails, world and
bookkeeping (as `ViolReRun1.lean`), and its halt.  Do not open this file in the language
server.

* `reChunk3088`, `reChunk4048`, `reChunk4377`: step 2625 (`bReBody`) to 3088 (`bRe3088`,
  node `t_046d_c152`), to 4048 (`bRe4048`, node `t_04e0_c155`), to 4377 (`bRe4377`, node
  `t_056f_c4`);
* `reHalt`: from step 4377, 127 steps and the `RETURN` (`wrun … 128` halts), decided by the
  halt observation `reHaltObs` (gas `gasRe`, output `outRe`, no error, the accessed keys
  `keysRe` and addresses `adrsRe`, the storage prefix `storRe` and the account prefix's
  addresses, nonces and balances) and `reHaltRest` (the account prefix's storage and code and
  the two tails, compared as terms).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-- What F5's halt shows, decided value by value. -/
def reHaltObs : Res → Bool
  | .done (.halted d) cl =>
    decide (d.gasLeft = gasRe) && decide (d.output = outRe) && d.error.isNone &&
      decide (cl.keys = keysRe) && decide (cl.adrs = adrsRe) &&
      decide (cl.stor.take storRe.length = storRe) &&
      decide ((cl.acs.take acsRe.length).map Boundary.acctKey = acsRe.map Boundary.acctKey)
  | _ => false

/-- What F5's halt shows as terms: the account prefix's storage and code, and what follows
the two prefixes. -/
def reHaltRest : Res → List (Stor × ByteArray) × StorShadow × AcctShadow
  | .done (.halted _) cl =>
    ((cl.acs.take acsRe.length).map Boundary.acctRest, cl.stor.drop storRe.length,
      cl.acs.drop acsRe.length)
  | _ => ([], [], [])

/-- Steps 2625 to 3088, over any tails, world and bookkeeping. -/
theorem reChunk3088 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRe3088 (wrun fsI sRe 463 (Boundary.cfgOfT bReBody tS tA m w)) =
      Boundary.obsDOkT bRe3088 tS tA := by
  kernel_forall_rfl

/-- Steps 3088 to 4048, over any tails, world and bookkeeping. -/
theorem reChunk4048 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRe4048 (wrun fsI sRe 960 (Boundary.cfgOfT bRe3088 tS tA m w)) =
      Boundary.obsDOkT bRe4048 tS tA := by
  kernel_forall_rfl

/-- Steps 4048 to 4377, over any tails, world and bookkeeping. -/
theorem reChunk4377 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    Boundary.obsDT bRe4377 (wrun fsI sRe 329 (Boundary.cfgOfT bRe4048 tS tA m w)) =
      Boundary.obsDOkT bRe4377 tS tA := by
  kernel_forall_rfl

/-- **F5's halt**: from step 4377, the `RETURN` within 128 steps, decided. -/
theorem reHalt : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    reHaltObs (wrun fsI sRe 128 (Boundary.cfgOfT bRe4377 tS tA m w)) = true ∧
      reHaltRest (wrun fsI sRe 128 (Boundary.cfgOfT bRe4377 tS tA m w)) =
        (Boundary.restsOf acsRe, tS, tA) := by
  kernel_forall_rfl_and

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
