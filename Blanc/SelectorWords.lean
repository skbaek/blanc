import Blanc.CommonCore

/-!
# Selector words

The four-byte word of each ABI selector a hand-written Blanc contract
dispatches on, stated once and checked by the kernel.

`selector name args` is the top four bytes of `String.keccak` of the
signature. Anything that makes the elaborator *evaluate* that term (`decide`,
`rfl`, `whnf`, a defeq check against a numeral) runs a full keccak-f[1600]
through the meta-level reducer, and one evaluation nests deeper than Lean's
default `maxRecDepth` of 512. The kernel evaluates it cheaply. So each word is
proved here by `decide +kernel`, once, and consumers rewrite a `selector` term
to its numeral before any tactic looks at it:

* a dispatch table restated with numeral keys (`Blanc.Fmint.fmint_eq_words`,
  `Blanc.weth_eq_words`) lets `func_run` walk a whole dispatcher with no
  raised limit and no hand-stepped `PUSH`;
* a separation between two selectors is a separation between two numerals.

The facts live in `namespace Blanc.SelectorWord` so a module's own private
`selector_*_val` copies cannot collide with them. Nothing here is a claim
about any runtime.
-/

namespace Blanc

open Jaune

namespace SelectorWord

theorem name : selector "name" [] = (0x06fdde03 : B256) := by decide +kernel

theorem approve : selector "approve" [.address, .uint256] = (0x095ea7b3 : B256) := by
  decide +kernel

theorem totalSupply : selector "totalSupply" [] = (0x18160ddd : B256) := by decide +kernel

theorem transferFrom :
    selector "transferFrom" [.address, .address, .uint256] = (0x23b872dd : B256) := by
  decide +kernel

theorem withdraw : selector "withdraw" [.uint256] = (0x2e1a7d4d : B256) := by decide +kernel

theorem decimals : selector "decimals" [] = (0x313ce567 : B256) := by decide +kernel

theorem flashLoan :
    selector "flashLoan" [.address, .address, .uint256, .dynBytes] = (0x5cffe9de : B256) := by
  decide +kernel

theorem maxFlashLoan : selector "maxFlashLoan" [.address] = (0x613255ab : B256) := by
  decide +kernel

theorem balanceOf : selector "balanceOf" [.address] = (0x70a08231 : B256) := by decide +kernel

theorem symbol : selector "symbol" [] = (0x95d89b41 : B256) := by decide +kernel

theorem transfer : selector "transfer" [.address, .uint256] = (0xa9059cbb : B256) := by
  decide +kernel

theorem flashFee : selector "flashFee" [.address, .uint256] = (0xd9d98ce4 : B256) := by
  decide +kernel

theorem allowance : selector "allowance" [.address, .address] = (0xdd62ed3e : B256) := by
  decide +kernel

end SelectorWord
end Blanc
