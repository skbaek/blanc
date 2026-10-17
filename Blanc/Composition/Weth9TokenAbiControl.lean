import Blanc.Composition.Weth9Token
import Blanc.Lift.Token.Abi

/-!
# Evidence for an ERC-20 ABI facet amendment: the frozen facet fails for WETH9

`Erc20Abi` (Appendix A §6a) reads every message with at least 68 bytes of calldata and the
`transfer` selector as a transfer.  WETH9 reads `CALLDATASIZE` mod `2^256`: calldata of length
`2^256` is a short call, booked as a deposit (`weth9Book_not_erc20Abi`).
-/

namespace Blanc.Composition.Weth9Token

open Jaune Blanc Blanc.Lift Blanc.Lift.Weth9 Blanc.Lift.Token

/-- **The frozen ERC-20 ABI facet does not hold for WETH9's book**: any message whose calldata is
`2^256` bytes long and begins with the `transfer` selector (such calldata exists, e.g. the selector
followed by `2^256 - 4` zero bytes) is a short call to WETH9 (`CALLDATASIZE` wraps), booked as a
deposit, not as the transfer the facet demands. -/
theorem weth9Book_not_erc20Abi {e : Sevm} (length : e.data.length = 2 ^ 256)
    (selector : Blanc.Sevm.selector e = 0xa9059cbb) : ¬ Erc20Abi weth9Book := by
  intro abi
  have short : shortCall e := by
    unfold shortCall
    rw [length]
    decide +kernel
  have long : 68 ≤ e.data.length := by
    rw [length]
    decide +kernel
  have op := abi.transfer e long selector
  rw [show weth9Book.op = weth9Op from rfl] at op
  unfold weth9Op decodeCall at op
  rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h.1 short),
    ite_eq_left_of_eq_true _ _ (eq_true short)] at op
  dsimp only at op
  by_cases zero : e.value = 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true zero)] at op
    cases op
  · rw [ite_eq_right_of_eq_false _ _ (eq_false zero)] at op
    cases op

end Blanc.Composition.Weth9Token
