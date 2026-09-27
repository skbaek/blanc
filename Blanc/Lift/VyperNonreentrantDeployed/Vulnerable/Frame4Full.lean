import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4

/-!
V- witness frame-4 kernel-cost probe: the whole reentrant `add_liquidity([100, 0], 0, A)`
(4,505 steps) in one kernel decision.  It halts by `RETURN` with gas 28,053,821 (the EELS
Prague trace's), returning 106 (the LP minted to `A`), with `totalSupply` (slot 26) and
`balanceOf[A]` both 2106 in `P`'s storage.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1

theorem frame4_full :
    (match wrun (Cert.prog cert) sevm4 4505 c4 with
      | .done (.halted d) => some (d.gasLeft, d.output.map UInt8.toNat,
          (d.getStorVal proxyAddress (26 : Nat).toB256).toNat,
          (d.getStorVal proxyAddress balanceOfASlot.toB256).toNat)
      | _ => none) =
    some (28053821, List.replicate 31 0 ++ [106], 2106, 2106) := by
  decide +kernel

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame4
