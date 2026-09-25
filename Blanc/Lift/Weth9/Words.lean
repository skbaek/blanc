import Blanc.Lift.Weth9.Spec
import Blanc.AddressSlotProofs

/-!
# Pushed-literal word facts for the WETH9 walks

The literals solc 0.4.19 pushes in WETH9's function bodies, rewritten once by
`decide`.  `line_execute` stalls on the 20-byte address mask, so the walks in
`Deposit.lean` and `Withdraw.lean` push each literal with `prefix_of_push` and
rewrite it with these lemmas.
-/

namespace Blanc.Lift.Weth9

open Jaune
open Blanc

/-- The 20-byte all-ones push word is the complement of `addressMask`. -/
theorem ff20_eq :
    Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = ~~~ addressMask := by
  decide

/-- Masking an address word with the 20-byte all-ones word is the identity. -/
theorem ff20_and_adr (a : Adr) :
    (Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& a.toB256) =
      a.toB256 := by
  rw [ff20_eq]
  exact addressSlotReadWord_toB256 a

theorem w00_eq : Bytes.toB256 [0x00] = 0 := by decide
theorem w03_eq : Bytes.toB256 [0x03] = 3 := by decide
theorem w20_eq : Bytes.toB256 [0x20] = 32 := by decide
theorem w32_add_0 : (32 : B256) + 0 = 32 := by decide
theorem w32_add_32 : (32 : B256) + 32 = 64 := by decide
theorem w0_toNat : (0 : B256).toNat = 0 := by decide
theorem w32_toNat : (32 : B256).toNat = 32 := by decide
theorem w64_toNat : (64 : B256).toNat = 64 := by decide

end Blanc.Lift.Weth9
