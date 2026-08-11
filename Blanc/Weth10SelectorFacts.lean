import Blanc.Weth10Attribution

/-!
Selector separations for the exact Blanc WETH10 runtime.

Every dispatched selector is the top four bytes of a keccak hash, so a
separation `a ≠ b` is decidable but each kernel run that decides one
from the signature strings recomputes two keccaks.  The allowance-region
arms, the hardened outflow reconciliation and the dormancy residual
between them need a couple of hundred such separations, drawn from a
handful of selectors, so deciding them one pair at a time paid for the
same hash over and over.

This module pays once per selector instead.  A private numeral fact per
selector runs the keccak in the kernel exactly once; every separation
below then rewrites both sides to their numerals and compares words, and
a pair needed in both directions derives its reverse with `Ne.symm`
rather than deciding again.  Nothing here is a claim about the runtime:
these are arithmetic facts about the ABI signature hashes, stated so the
modules that consume them state no local copies.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## The selector words

One kernel keccak per selector.  These are private: the separations
below are the module's interface, and a consumer that wanted a selector's
literal word would be reaching past them. -/

private theorem selector_name_val :
    selector "name" [] = (0x06fdde03 : B256) := by decide +kernel

private theorem selector_symbol_val :
    selector "symbol" [] = (0x95d89b41 : B256) := by decide +kernel

private theorem selector_decimals_val :
    selector "decimals" [] = (0x313ce567 : B256) := by decide +kernel

private theorem selector_PERMIT_TYPEHASH_val :
    selector "PERMIT_TYPEHASH" [] = (0x30adf81f : B256) := by decide +kernel

private theorem selector_CALLBACK_SUCCESS_val :
    selector "CALLBACK_SUCCESS" [] = (0x8237e538 : B256) := by decide +kernel

private theorem selector_totalSupply_val :
    selector "totalSupply" [] = (0x18160ddd : B256) := by decide +kernel

private theorem selector_balanceOf_val :
    selector "balanceOf" [.address] = (0x70a08231 : B256) := by decide +kernel

private theorem selector_nonces_val :
    selector "nonces" [.address] = (0x7ecebe00 : B256) := by decide +kernel

private theorem selector_flashMinted_val :
    selector "flashMinted" [] = (0x8b28d32f : B256) := by decide +kernel

private theorem selector_deploymentChainId_val :
    selector "deploymentChainId" [] = (0xcd0d0096 : B256) := by decide +kernel

private theorem selector_DOMAIN_SEPARATOR_val :
    selector "DOMAIN_SEPARATOR" [] = (0x3644e515 : B256) := by decide +kernel

private theorem selector_maxFlashLoan_val :
    selector "maxFlashLoan" [.address] = (0x613255ab : B256) := by
  decide +kernel

private theorem selector_flashFee_val :
    selector "flashFee" [.address, .uint256] = (0xd9d98ce4 : B256) := by
  decide +kernel

private theorem approveSelector_val :
    approveSelector = (0x095ea7b3 : B256) := by decide +kernel

private theorem allowanceSelector_val :
    allowanceSelector = (0xdd62ed3e : B256) := by decide +kernel

private theorem approveAndCallSelector_val :
    approveAndCallSelector = (0xcae9ca51 : B256) := by decide +kernel

private theorem permitSelector_val :
    permitSelector = (0xd505accf : B256) := by decide +kernel

private theorem transferFromSelector_val :
    transferFromSelector = (0x23b872dd : B256) := by decide +kernel

private theorem withdrawFromSelector_val :
    withdrawFromSelector = (0x9555a942 : B256) := by decide +kernel

private theorem flashLoanSelector_val :
    flashLoanSelector = (0x5cffe9de : B256) := by decide +kernel

private theorem transferSelector_val :
    transferSelector = (0xa9059cbb : B256) := by decide +kernel

private theorem transferAndCallSelector_val :
    transferAndCallSelector = (0x4000aea0 : B256) := by decide +kernel

private theorem withdrawSelector_val :
    withdrawSelector = (0x2e1a7d4d : B256) := by decide +kernel

private theorem withdrawToSelector_val :
    withdrawToSelector = (0x205c2878 : B256) := by decide +kernel

private theorem depositSelector_val :
    depositSelector = (0xd0e30db0 : B256) := by decide +kernel

private theorem depositToSelector_val :
    depositToSelector = (0xb760faf9 : B256) := by decide +kernel

private theorem depositToAndCallSelector_val :
    depositToAndCallSelector = (0x5ddb7d7e : B256) := by decide +kernel

/-! ## The childless views

Each read-only view is separated from the seven selectors the allowance
event chain tests, which is what makes its frame's event `none`. -/

/-! ### `name` -/

theorem selector_name_ne_approveSelector :
    selector "name" [] ≠ approveSelector := by
  rw [selector_name_val, approveSelector_val]; decide

theorem selector_name_ne_approveAndCallSelector :
    selector "name" [] ≠ approveAndCallSelector := by
  rw [selector_name_val, approveAndCallSelector_val]; decide

theorem selector_name_ne_permitSelector :
    selector "name" [] ≠ permitSelector := by
  rw [selector_name_val, permitSelector_val]; decide

theorem selector_name_ne_transferFromSelector :
    selector "name" [] ≠ transferFromSelector := by
  rw [selector_name_val, transferFromSelector_val]; decide

theorem selector_name_ne_withdrawFromSelector :
    selector "name" [] ≠ withdrawFromSelector := by
  rw [selector_name_val, withdrawFromSelector_val]; decide

theorem selector_name_ne_flashLoanSelector :
    selector "name" [] ≠ flashLoanSelector := by
  rw [selector_name_val, flashLoanSelector_val]; decide

theorem selector_name_ne_allowanceSelector :
    selector "name" [] ≠ allowanceSelector := by
  rw [selector_name_val, allowanceSelector_val]; decide

/-! ### `symbol` -/

theorem selector_symbol_ne_approveSelector :
    selector "symbol" [] ≠ approveSelector := by
  rw [selector_symbol_val, approveSelector_val]; decide

theorem selector_symbol_ne_approveAndCallSelector :
    selector "symbol" [] ≠ approveAndCallSelector := by
  rw [selector_symbol_val, approveAndCallSelector_val]; decide

theorem selector_symbol_ne_permitSelector :
    selector "symbol" [] ≠ permitSelector := by
  rw [selector_symbol_val, permitSelector_val]; decide

theorem selector_symbol_ne_transferFromSelector :
    selector "symbol" [] ≠ transferFromSelector := by
  rw [selector_symbol_val, transferFromSelector_val]; decide

theorem selector_symbol_ne_withdrawFromSelector :
    selector "symbol" [] ≠ withdrawFromSelector := by
  rw [selector_symbol_val, withdrawFromSelector_val]; decide

theorem selector_symbol_ne_flashLoanSelector :
    selector "symbol" [] ≠ flashLoanSelector := by
  rw [selector_symbol_val, flashLoanSelector_val]; decide

theorem selector_symbol_ne_allowanceSelector :
    selector "symbol" [] ≠ allowanceSelector := by
  rw [selector_symbol_val, allowanceSelector_val]; decide

/-! ### `decimals` -/

theorem selector_decimals_ne_approveSelector :
    selector "decimals" [] ≠ approveSelector := by
  rw [selector_decimals_val, approveSelector_val]; decide

theorem selector_decimals_ne_approveAndCallSelector :
    selector "decimals" [] ≠ approveAndCallSelector := by
  rw [selector_decimals_val, approveAndCallSelector_val]; decide

theorem selector_decimals_ne_permitSelector :
    selector "decimals" [] ≠ permitSelector := by
  rw [selector_decimals_val, permitSelector_val]; decide

theorem selector_decimals_ne_transferFromSelector :
    selector "decimals" [] ≠ transferFromSelector := by
  rw [selector_decimals_val, transferFromSelector_val]; decide

theorem selector_decimals_ne_withdrawFromSelector :
    selector "decimals" [] ≠ withdrawFromSelector := by
  rw [selector_decimals_val, withdrawFromSelector_val]; decide

theorem selector_decimals_ne_flashLoanSelector :
    selector "decimals" [] ≠ flashLoanSelector := by
  rw [selector_decimals_val, flashLoanSelector_val]; decide

theorem selector_decimals_ne_allowanceSelector :
    selector "decimals" [] ≠ allowanceSelector := by
  rw [selector_decimals_val, allowanceSelector_val]; decide

/-! ### `PERMIT_TYPEHASH` -/

theorem selector_PERMIT_TYPEHASH_ne_approveSelector :
    selector "PERMIT_TYPEHASH" [] ≠ approveSelector := by
  rw [selector_PERMIT_TYPEHASH_val, approveSelector_val]; decide

theorem selector_PERMIT_TYPEHASH_ne_approveAndCallSelector :
    selector "PERMIT_TYPEHASH" [] ≠ approveAndCallSelector := by
  rw [selector_PERMIT_TYPEHASH_val, approveAndCallSelector_val]; decide

theorem selector_PERMIT_TYPEHASH_ne_permitSelector :
    selector "PERMIT_TYPEHASH" [] ≠ permitSelector := by
  rw [selector_PERMIT_TYPEHASH_val, permitSelector_val]; decide

theorem selector_PERMIT_TYPEHASH_ne_transferFromSelector :
    selector "PERMIT_TYPEHASH" [] ≠ transferFromSelector := by
  rw [selector_PERMIT_TYPEHASH_val, transferFromSelector_val]; decide

theorem selector_PERMIT_TYPEHASH_ne_withdrawFromSelector :
    selector "PERMIT_TYPEHASH" [] ≠ withdrawFromSelector := by
  rw [selector_PERMIT_TYPEHASH_val, withdrawFromSelector_val]; decide

theorem selector_PERMIT_TYPEHASH_ne_flashLoanSelector :
    selector "PERMIT_TYPEHASH" [] ≠ flashLoanSelector := by
  rw [selector_PERMIT_TYPEHASH_val, flashLoanSelector_val]; decide

theorem selector_PERMIT_TYPEHASH_ne_allowanceSelector :
    selector "PERMIT_TYPEHASH" [] ≠ allowanceSelector := by
  rw [selector_PERMIT_TYPEHASH_val, allowanceSelector_val]; decide

/-! ### `CALLBACK_SUCCESS` -/

theorem selector_CALLBACK_SUCCESS_ne_approveSelector :
    selector "CALLBACK_SUCCESS" [] ≠ approveSelector := by
  rw [selector_CALLBACK_SUCCESS_val, approveSelector_val]; decide

theorem selector_CALLBACK_SUCCESS_ne_approveAndCallSelector :
    selector "CALLBACK_SUCCESS" [] ≠ approveAndCallSelector := by
  rw [selector_CALLBACK_SUCCESS_val, approveAndCallSelector_val]; decide

theorem selector_CALLBACK_SUCCESS_ne_permitSelector :
    selector "CALLBACK_SUCCESS" [] ≠ permitSelector := by
  rw [selector_CALLBACK_SUCCESS_val, permitSelector_val]; decide

theorem selector_CALLBACK_SUCCESS_ne_transferFromSelector :
    selector "CALLBACK_SUCCESS" [] ≠ transferFromSelector := by
  rw [selector_CALLBACK_SUCCESS_val, transferFromSelector_val]; decide

theorem selector_CALLBACK_SUCCESS_ne_withdrawFromSelector :
    selector "CALLBACK_SUCCESS" [] ≠ withdrawFromSelector := by
  rw [selector_CALLBACK_SUCCESS_val, withdrawFromSelector_val]; decide

theorem selector_CALLBACK_SUCCESS_ne_flashLoanSelector :
    selector "CALLBACK_SUCCESS" [] ≠ flashLoanSelector := by
  rw [selector_CALLBACK_SUCCESS_val, flashLoanSelector_val]; decide

theorem selector_CALLBACK_SUCCESS_ne_allowanceSelector :
    selector "CALLBACK_SUCCESS" [] ≠ allowanceSelector := by
  rw [selector_CALLBACK_SUCCESS_val, allowanceSelector_val]; decide

/-! ### `totalSupply` -/

theorem selector_totalSupply_ne_approveSelector :
    selector "totalSupply" [] ≠ approveSelector := by
  rw [selector_totalSupply_val, approveSelector_val]; decide

theorem selector_totalSupply_ne_approveAndCallSelector :
    selector "totalSupply" [] ≠ approveAndCallSelector := by
  rw [selector_totalSupply_val, approveAndCallSelector_val]; decide

theorem selector_totalSupply_ne_permitSelector :
    selector "totalSupply" [] ≠ permitSelector := by
  rw [selector_totalSupply_val, permitSelector_val]; decide

theorem selector_totalSupply_ne_transferFromSelector :
    selector "totalSupply" [] ≠ transferFromSelector := by
  rw [selector_totalSupply_val, transferFromSelector_val]; decide

theorem selector_totalSupply_ne_withdrawFromSelector :
    selector "totalSupply" [] ≠ withdrawFromSelector := by
  rw [selector_totalSupply_val, withdrawFromSelector_val]; decide

theorem selector_totalSupply_ne_flashLoanSelector :
    selector "totalSupply" [] ≠ flashLoanSelector := by
  rw [selector_totalSupply_val, flashLoanSelector_val]; decide

theorem selector_totalSupply_ne_allowanceSelector :
    selector "totalSupply" [] ≠ allowanceSelector := by
  rw [selector_totalSupply_val, allowanceSelector_val]; decide

/-! ### `balanceOf` -/

theorem selector_balanceOf_ne_approveSelector :
    selector "balanceOf" [.address] ≠ approveSelector := by
  rw [selector_balanceOf_val, approveSelector_val]; decide

theorem selector_balanceOf_ne_approveAndCallSelector :
    selector "balanceOf" [.address] ≠ approveAndCallSelector := by
  rw [selector_balanceOf_val, approveAndCallSelector_val]; decide

theorem selector_balanceOf_ne_permitSelector :
    selector "balanceOf" [.address] ≠ permitSelector := by
  rw [selector_balanceOf_val, permitSelector_val]; decide

theorem selector_balanceOf_ne_transferFromSelector :
    selector "balanceOf" [.address] ≠ transferFromSelector := by
  rw [selector_balanceOf_val, transferFromSelector_val]; decide

theorem selector_balanceOf_ne_withdrawFromSelector :
    selector "balanceOf" [.address] ≠ withdrawFromSelector := by
  rw [selector_balanceOf_val, withdrawFromSelector_val]; decide

theorem selector_balanceOf_ne_flashLoanSelector :
    selector "balanceOf" [.address] ≠ flashLoanSelector := by
  rw [selector_balanceOf_val, flashLoanSelector_val]; decide

theorem selector_balanceOf_ne_allowanceSelector :
    selector "balanceOf" [.address] ≠ allowanceSelector := by
  rw [selector_balanceOf_val, allowanceSelector_val]; decide

/-! ### `nonces` -/

theorem selector_nonces_ne_approveSelector :
    selector "nonces" [.address] ≠ approveSelector := by
  rw [selector_nonces_val, approveSelector_val]; decide

theorem selector_nonces_ne_approveAndCallSelector :
    selector "nonces" [.address] ≠ approveAndCallSelector := by
  rw [selector_nonces_val, approveAndCallSelector_val]; decide

theorem selector_nonces_ne_permitSelector :
    selector "nonces" [.address] ≠ permitSelector := by
  rw [selector_nonces_val, permitSelector_val]; decide

theorem selector_nonces_ne_transferFromSelector :
    selector "nonces" [.address] ≠ transferFromSelector := by
  rw [selector_nonces_val, transferFromSelector_val]; decide

theorem selector_nonces_ne_withdrawFromSelector :
    selector "nonces" [.address] ≠ withdrawFromSelector := by
  rw [selector_nonces_val, withdrawFromSelector_val]; decide

theorem selector_nonces_ne_flashLoanSelector :
    selector "nonces" [.address] ≠ flashLoanSelector := by
  rw [selector_nonces_val, flashLoanSelector_val]; decide

theorem selector_nonces_ne_allowanceSelector :
    selector "nonces" [.address] ≠ allowanceSelector := by
  rw [selector_nonces_val, allowanceSelector_val]; decide

/-! ### `flashMinted` -/

theorem selector_flashMinted_ne_approveSelector :
    selector "flashMinted" [] ≠ approveSelector := by
  rw [selector_flashMinted_val, approveSelector_val]; decide

theorem selector_flashMinted_ne_approveAndCallSelector :
    selector "flashMinted" [] ≠ approveAndCallSelector := by
  rw [selector_flashMinted_val, approveAndCallSelector_val]; decide

theorem selector_flashMinted_ne_permitSelector :
    selector "flashMinted" [] ≠ permitSelector := by
  rw [selector_flashMinted_val, permitSelector_val]; decide

theorem selector_flashMinted_ne_transferFromSelector :
    selector "flashMinted" [] ≠ transferFromSelector := by
  rw [selector_flashMinted_val, transferFromSelector_val]; decide

theorem selector_flashMinted_ne_withdrawFromSelector :
    selector "flashMinted" [] ≠ withdrawFromSelector := by
  rw [selector_flashMinted_val, withdrawFromSelector_val]; decide

theorem selector_flashMinted_ne_flashLoanSelector :
    selector "flashMinted" [] ≠ flashLoanSelector := by
  rw [selector_flashMinted_val, flashLoanSelector_val]; decide

theorem selector_flashMinted_ne_allowanceSelector :
    selector "flashMinted" [] ≠ allowanceSelector := by
  rw [selector_flashMinted_val, allowanceSelector_val]; decide

/-! ### `deploymentChainId` -/

theorem selector_deploymentChainId_ne_approveSelector :
    selector "deploymentChainId" [] ≠ approveSelector := by
  rw [selector_deploymentChainId_val, approveSelector_val]; decide

theorem selector_deploymentChainId_ne_approveAndCallSelector :
    selector "deploymentChainId" [] ≠ approveAndCallSelector := by
  rw [selector_deploymentChainId_val, approveAndCallSelector_val]; decide

theorem selector_deploymentChainId_ne_permitSelector :
    selector "deploymentChainId" [] ≠ permitSelector := by
  rw [selector_deploymentChainId_val, permitSelector_val]; decide

theorem selector_deploymentChainId_ne_transferFromSelector :
    selector "deploymentChainId" [] ≠ transferFromSelector := by
  rw [selector_deploymentChainId_val, transferFromSelector_val]; decide

theorem selector_deploymentChainId_ne_withdrawFromSelector :
    selector "deploymentChainId" [] ≠ withdrawFromSelector := by
  rw [selector_deploymentChainId_val, withdrawFromSelector_val]; decide

theorem selector_deploymentChainId_ne_flashLoanSelector :
    selector "deploymentChainId" [] ≠ flashLoanSelector := by
  rw [selector_deploymentChainId_val, flashLoanSelector_val]; decide

theorem selector_deploymentChainId_ne_allowanceSelector :
    selector "deploymentChainId" [] ≠ allowanceSelector := by
  rw [selector_deploymentChainId_val, allowanceSelector_val]; decide

/-! ### `DOMAIN_SEPARATOR` -/

theorem selector_DOMAIN_SEPARATOR_ne_approveSelector :
    selector "DOMAIN_SEPARATOR" [] ≠ approveSelector := by
  rw [selector_DOMAIN_SEPARATOR_val, approveSelector_val]; decide

theorem selector_DOMAIN_SEPARATOR_ne_approveAndCallSelector :
    selector "DOMAIN_SEPARATOR" [] ≠ approveAndCallSelector := by
  rw [selector_DOMAIN_SEPARATOR_val, approveAndCallSelector_val]; decide

theorem selector_DOMAIN_SEPARATOR_ne_permitSelector :
    selector "DOMAIN_SEPARATOR" [] ≠ permitSelector := by
  rw [selector_DOMAIN_SEPARATOR_val, permitSelector_val]; decide

theorem selector_DOMAIN_SEPARATOR_ne_transferFromSelector :
    selector "DOMAIN_SEPARATOR" [] ≠ transferFromSelector := by
  rw [selector_DOMAIN_SEPARATOR_val, transferFromSelector_val]; decide

theorem selector_DOMAIN_SEPARATOR_ne_withdrawFromSelector :
    selector "DOMAIN_SEPARATOR" [] ≠ withdrawFromSelector := by
  rw [selector_DOMAIN_SEPARATOR_val, withdrawFromSelector_val]; decide

theorem selector_DOMAIN_SEPARATOR_ne_flashLoanSelector :
    selector "DOMAIN_SEPARATOR" [] ≠ flashLoanSelector := by
  rw [selector_DOMAIN_SEPARATOR_val, flashLoanSelector_val]; decide

theorem selector_DOMAIN_SEPARATOR_ne_allowanceSelector :
    selector "DOMAIN_SEPARATOR" [] ≠ allowanceSelector := by
  rw [selector_DOMAIN_SEPARATOR_val, allowanceSelector_val]; decide

/-! ### `maxFlashLoan` -/

theorem selector_maxFlashLoan_ne_approveSelector :
    selector "maxFlashLoan" [.address] ≠ approveSelector := by
  rw [selector_maxFlashLoan_val, approveSelector_val]; decide

theorem selector_maxFlashLoan_ne_approveAndCallSelector :
    selector "maxFlashLoan" [.address] ≠ approveAndCallSelector := by
  rw [selector_maxFlashLoan_val, approveAndCallSelector_val]; decide

theorem selector_maxFlashLoan_ne_permitSelector :
    selector "maxFlashLoan" [.address] ≠ permitSelector := by
  rw [selector_maxFlashLoan_val, permitSelector_val]; decide

theorem selector_maxFlashLoan_ne_transferFromSelector :
    selector "maxFlashLoan" [.address] ≠ transferFromSelector := by
  rw [selector_maxFlashLoan_val, transferFromSelector_val]; decide

theorem selector_maxFlashLoan_ne_withdrawFromSelector :
    selector "maxFlashLoan" [.address] ≠ withdrawFromSelector := by
  rw [selector_maxFlashLoan_val, withdrawFromSelector_val]; decide

theorem selector_maxFlashLoan_ne_flashLoanSelector :
    selector "maxFlashLoan" [.address] ≠ flashLoanSelector := by
  rw [selector_maxFlashLoan_val, flashLoanSelector_val]; decide

theorem selector_maxFlashLoan_ne_allowanceSelector :
    selector "maxFlashLoan" [.address] ≠ allowanceSelector := by
  rw [selector_maxFlashLoan_val, allowanceSelector_val]; decide

/-! ### `flashFee` -/

theorem selector_flashFee_ne_approveSelector :
    selector "flashFee" [.address, .uint256] ≠ approveSelector := by
  rw [selector_flashFee_val, approveSelector_val]; decide

theorem selector_flashFee_ne_approveAndCallSelector :
    selector "flashFee" [.address, .uint256] ≠ approveAndCallSelector := by
  rw [selector_flashFee_val, approveAndCallSelector_val]; decide

theorem selector_flashFee_ne_permitSelector :
    selector "flashFee" [.address, .uint256] ≠ permitSelector := by
  rw [selector_flashFee_val, permitSelector_val]; decide

theorem selector_flashFee_ne_transferFromSelector :
    selector "flashFee" [.address, .uint256] ≠ transferFromSelector := by
  rw [selector_flashFee_val, transferFromSelector_val]; decide

theorem selector_flashFee_ne_withdrawFromSelector :
    selector "flashFee" [.address, .uint256] ≠ withdrawFromSelector := by
  rw [selector_flashFee_val, withdrawFromSelector_val]; decide

theorem selector_flashFee_ne_flashLoanSelector :
    selector "flashFee" [.address, .uint256] ≠ flashLoanSelector := by
  rw [selector_flashFee_val, flashLoanSelector_val]; decide

theorem selector_flashFee_ne_allowanceSelector :
    selector "flashFee" [.address, .uint256] ≠ allowanceSelector := by
  rw [selector_flashFee_val, allowanceSelector_val]; decide

/-! ## The named selectors -/

/-! ### `depositSelector` -/

theorem depositSelector_ne_approveSelector :
    depositSelector ≠ approveSelector := by
  rw [depositSelector_val, approveSelector_val]; decide

theorem depositSelector_ne_approveAndCallSelector :
    depositSelector ≠ approveAndCallSelector := by
  rw [depositSelector_val, approveAndCallSelector_val]; decide

theorem depositSelector_ne_permitSelector :
    depositSelector ≠ permitSelector := by
  rw [depositSelector_val, permitSelector_val]; decide

theorem depositSelector_ne_transferFromSelector :
    depositSelector ≠ transferFromSelector := by
  rw [depositSelector_val, transferFromSelector_val]; decide

theorem depositSelector_ne_withdrawFromSelector :
    depositSelector ≠ withdrawFromSelector := by
  rw [depositSelector_val, withdrawFromSelector_val]; decide

theorem depositSelector_ne_flashLoanSelector :
    depositSelector ≠ flashLoanSelector := by
  rw [depositSelector_val, flashLoanSelector_val]; decide

theorem depositSelector_ne_allowanceSelector :
    depositSelector ≠ allowanceSelector := by
  rw [depositSelector_val, allowanceSelector_val]; decide

/-! ### `depositToSelector` -/

theorem depositToSelector_ne_approveSelector :
    depositToSelector ≠ approveSelector := by
  rw [depositToSelector_val, approveSelector_val]; decide

theorem depositToSelector_ne_approveAndCallSelector :
    depositToSelector ≠ approveAndCallSelector := by
  rw [depositToSelector_val, approveAndCallSelector_val]; decide

theorem depositToSelector_ne_permitSelector :
    depositToSelector ≠ permitSelector := by
  rw [depositToSelector_val, permitSelector_val]; decide

theorem depositToSelector_ne_transferFromSelector :
    depositToSelector ≠ transferFromSelector := by
  rw [depositToSelector_val, transferFromSelector_val]; decide

theorem depositToSelector_ne_withdrawFromSelector :
    depositToSelector ≠ withdrawFromSelector := by
  rw [depositToSelector_val, withdrawFromSelector_val]; decide

theorem depositToSelector_ne_flashLoanSelector :
    depositToSelector ≠ flashLoanSelector := by
  rw [depositToSelector_val, flashLoanSelector_val]; decide

theorem depositToSelector_ne_allowanceSelector :
    depositToSelector ≠ allowanceSelector := by
  rw [depositToSelector_val, allowanceSelector_val]; decide

/-! ### `depositToAndCallSelector` -/

theorem depositToAndCallSelector_ne_approveSelector :
    depositToAndCallSelector ≠ approveSelector := by
  rw [depositToAndCallSelector_val, approveSelector_val]; decide

theorem depositToAndCallSelector_ne_approveAndCallSelector :
    depositToAndCallSelector ≠ approveAndCallSelector := by
  rw [depositToAndCallSelector_val, approveAndCallSelector_val]; decide

theorem depositToAndCallSelector_ne_permitSelector :
    depositToAndCallSelector ≠ permitSelector := by
  rw [depositToAndCallSelector_val, permitSelector_val]; decide

theorem depositToAndCallSelector_ne_transferFromSelector :
    depositToAndCallSelector ≠ transferFromSelector := by
  rw [depositToAndCallSelector_val, transferFromSelector_val]; decide

theorem depositToAndCallSelector_ne_withdrawFromSelector :
    depositToAndCallSelector ≠ withdrawFromSelector := by
  rw [depositToAndCallSelector_val, withdrawFromSelector_val]; decide

theorem depositToAndCallSelector_ne_flashLoanSelector :
    depositToAndCallSelector ≠ flashLoanSelector := by
  rw [depositToAndCallSelector_val, flashLoanSelector_val]; decide

theorem depositToAndCallSelector_ne_allowanceSelector :
    depositToAndCallSelector ≠ allowanceSelector := by
  rw [depositToAndCallSelector_val, allowanceSelector_val]; decide

/-! ### `transferSelector` -/

theorem transferSelector_ne_approveSelector :
    transferSelector ≠ approveSelector := by
  rw [transferSelector_val, approveSelector_val]; decide

theorem transferSelector_ne_approveAndCallSelector :
    transferSelector ≠ approveAndCallSelector := by
  rw [transferSelector_val, approveAndCallSelector_val]; decide

theorem transferSelector_ne_permitSelector :
    transferSelector ≠ permitSelector := by
  rw [transferSelector_val, permitSelector_val]; decide

theorem transferSelector_ne_transferFromSelector :
    transferSelector ≠ transferFromSelector := by
  rw [transferSelector_val, transferFromSelector_val]; decide

theorem transferSelector_ne_withdrawFromSelector :
    transferSelector ≠ withdrawFromSelector := by
  rw [transferSelector_val, withdrawFromSelector_val]; decide

theorem transferSelector_ne_flashLoanSelector :
    transferSelector ≠ flashLoanSelector := by
  rw [transferSelector_val, flashLoanSelector_val]; decide

theorem transferSelector_ne_allowanceSelector :
    transferSelector ≠ allowanceSelector := by
  rw [transferSelector_val, allowanceSelector_val]; decide

/-! ### `transferAndCallSelector` -/

theorem transferAndCallSelector_ne_approveSelector :
    transferAndCallSelector ≠ approveSelector := by
  rw [transferAndCallSelector_val, approveSelector_val]; decide

theorem transferAndCallSelector_ne_approveAndCallSelector :
    transferAndCallSelector ≠ approveAndCallSelector := by
  rw [transferAndCallSelector_val, approveAndCallSelector_val]; decide

theorem transferAndCallSelector_ne_permitSelector :
    transferAndCallSelector ≠ permitSelector := by
  rw [transferAndCallSelector_val, permitSelector_val]; decide

theorem transferAndCallSelector_ne_transferFromSelector :
    transferAndCallSelector ≠ transferFromSelector := by
  rw [transferAndCallSelector_val, transferFromSelector_val]; decide

theorem transferAndCallSelector_ne_withdrawFromSelector :
    transferAndCallSelector ≠ withdrawFromSelector := by
  rw [transferAndCallSelector_val, withdrawFromSelector_val]; decide

theorem transferAndCallSelector_ne_flashLoanSelector :
    transferAndCallSelector ≠ flashLoanSelector := by
  rw [transferAndCallSelector_val, flashLoanSelector_val]; decide

theorem transferAndCallSelector_ne_allowanceSelector :
    transferAndCallSelector ≠ allowanceSelector := by
  rw [transferAndCallSelector_val, allowanceSelector_val]; decide

/-! ### `withdrawSelector` -/

theorem withdrawSelector_ne_approveSelector :
    withdrawSelector ≠ approveSelector := by
  rw [withdrawSelector_val, approveSelector_val]; decide

theorem withdrawSelector_ne_approveAndCallSelector :
    withdrawSelector ≠ approveAndCallSelector := by
  rw [withdrawSelector_val, approveAndCallSelector_val]; decide

theorem withdrawSelector_ne_permitSelector :
    withdrawSelector ≠ permitSelector := by
  rw [withdrawSelector_val, permitSelector_val]; decide

theorem withdrawSelector_ne_transferFromSelector :
    withdrawSelector ≠ transferFromSelector := by
  rw [withdrawSelector_val, transferFromSelector_val]; decide

theorem withdrawSelector_ne_withdrawFromSelector :
    withdrawSelector ≠ withdrawFromSelector := by
  rw [withdrawSelector_val, withdrawFromSelector_val]; decide

theorem withdrawSelector_ne_flashLoanSelector :
    withdrawSelector ≠ flashLoanSelector := by
  rw [withdrawSelector_val, flashLoanSelector_val]; decide

theorem withdrawSelector_ne_allowanceSelector :
    withdrawSelector ≠ allowanceSelector := by
  rw [withdrawSelector_val, allowanceSelector_val]; decide

/-! ### `withdrawToSelector` -/

theorem withdrawToSelector_ne_approveSelector :
    withdrawToSelector ≠ approveSelector := by
  rw [withdrawToSelector_val, approveSelector_val]; decide

theorem withdrawToSelector_ne_approveAndCallSelector :
    withdrawToSelector ≠ approveAndCallSelector := by
  rw [withdrawToSelector_val, approveAndCallSelector_val]; decide

theorem withdrawToSelector_ne_permitSelector :
    withdrawToSelector ≠ permitSelector := by
  rw [withdrawToSelector_val, permitSelector_val]; decide

theorem withdrawToSelector_ne_transferFromSelector :
    withdrawToSelector ≠ transferFromSelector := by
  rw [withdrawToSelector_val, transferFromSelector_val]; decide

theorem withdrawToSelector_ne_withdrawFromSelector :
    withdrawToSelector ≠ withdrawFromSelector := by
  rw [withdrawToSelector_val, withdrawFromSelector_val]; decide

theorem withdrawToSelector_ne_flashLoanSelector :
    withdrawToSelector ≠ flashLoanSelector := by
  rw [withdrawToSelector_val, flashLoanSelector_val]; decide

theorem withdrawToSelector_ne_allowanceSelector :
    withdrawToSelector ≠ allowanceSelector := by
  rw [withdrawToSelector_val, allowanceSelector_val]; decide

/-! ### `approveSelector` -/

theorem approveSelector_ne_flashLoanSelector :
    approveSelector ≠ flashLoanSelector := by
  rw [approveSelector_val, flashLoanSelector_val]; decide

theorem approveSelector_ne_permitSelector :
    approveSelector ≠ permitSelector := by
  rw [approveSelector_val, permitSelector_val]; decide

/-! ### `approveAndCallSelector` -/

theorem approveAndCallSelector_ne_flashLoanSelector :
    approveAndCallSelector ≠ flashLoanSelector := by
  rw [approveAndCallSelector_val, flashLoanSelector_val]; decide

theorem approveAndCallSelector_ne_permitSelector :
    approveAndCallSelector ≠ permitSelector := by
  rw [approveAndCallSelector_val, permitSelector_val]; decide

/-! ### `allowanceSelector` -/

theorem allowanceSelector_ne_approveSelector :
    allowanceSelector ≠ approveSelector := by
  rw [allowanceSelector_val, approveSelector_val]; decide

theorem allowanceSelector_ne_approveAndCallSelector :
    allowanceSelector ≠ approveAndCallSelector := by
  rw [allowanceSelector_val, approveAndCallSelector_val]; decide

theorem allowanceSelector_ne_permitSelector :
    allowanceSelector ≠ permitSelector := by
  rw [allowanceSelector_val, permitSelector_val]; decide

theorem allowanceSelector_ne_transferFromSelector :
    allowanceSelector ≠ transferFromSelector := by
  rw [allowanceSelector_val, transferFromSelector_val]; decide

theorem allowanceSelector_ne_withdrawFromSelector :
    allowanceSelector ≠ withdrawFromSelector := by
  rw [allowanceSelector_val, withdrawFromSelector_val]; decide

theorem allowanceSelector_ne_flashLoanSelector :
    allowanceSelector ≠ flashLoanSelector := by
  rw [allowanceSelector_val, flashLoanSelector_val]; decide

/-! ### `permitSelector` -/

theorem permitSelector_ne_approveSelector :
    permitSelector ≠ approveSelector := by
  rw [permitSelector_val, approveSelector_val]; decide

theorem permitSelector_ne_approveAndCallSelector :
    permitSelector ≠ approveAndCallSelector := by
  rw [permitSelector_val, approveAndCallSelector_val]; decide

theorem permitSelector_ne_flashLoanSelector :
    permitSelector ≠ flashLoanSelector := by
  rw [permitSelector_val, flashLoanSelector_val]; decide

/-! ### `flashLoanSelector` -/

theorem flashLoanSelector_ne_approveSelector :
    flashLoanSelector ≠ approveSelector :=
  approveSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_approveAndCallSelector :
    flashLoanSelector ≠ approveAndCallSelector :=
  approveAndCallSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_permitSelector :
    flashLoanSelector ≠ permitSelector :=
  permitSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_transferFromSelector :
    flashLoanSelector ≠ transferFromSelector := by
  rw [flashLoanSelector_val, transferFromSelector_val]; decide

theorem flashLoanSelector_ne_withdrawFromSelector :
    flashLoanSelector ≠ withdrawFromSelector := by
  rw [flashLoanSelector_val, withdrawFromSelector_val]; decide

/-! ### `transferFromSelector` -/

theorem transferFromSelector_ne_approveSelector :
    transferFromSelector ≠ approveSelector := by
  rw [transferFromSelector_val, approveSelector_val]; decide

theorem transferFromSelector_ne_approveAndCallSelector :
    transferFromSelector ≠ approveAndCallSelector := by
  rw [transferFromSelector_val, approveAndCallSelector_val]; decide

theorem transferFromSelector_ne_permitSelector :
    transferFromSelector ≠ permitSelector := by
  rw [transferFromSelector_val, permitSelector_val]; decide

theorem transferFromSelector_ne_flashLoanSelector :
    transferFromSelector ≠ flashLoanSelector :=
  flashLoanSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_transferSelector :
    transferFromSelector ≠ transferSelector :=
  transferSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_transferAndCallSelector :
    transferFromSelector ≠ transferAndCallSelector :=
  transferAndCallSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_withdrawSelector :
    transferFromSelector ≠ withdrawSelector :=
  withdrawSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_withdrawToSelector :
    transferFromSelector ≠ withdrawToSelector :=
  withdrawToSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_depositSelector :
    transferFromSelector ≠ depositSelector :=
  depositSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_depositToSelector :
    transferFromSelector ≠ depositToSelector :=
  depositToSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_depositToAndCallSelector :
    transferFromSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_transferFromSelector.symm

/-! ### `withdrawFromSelector` -/

theorem withdrawFromSelector_ne_approveSelector :
    withdrawFromSelector ≠ approveSelector := by
  rw [withdrawFromSelector_val, approveSelector_val]; decide

theorem withdrawFromSelector_ne_approveAndCallSelector :
    withdrawFromSelector ≠ approveAndCallSelector := by
  rw [withdrawFromSelector_val, approveAndCallSelector_val]; decide

theorem withdrawFromSelector_ne_permitSelector :
    withdrawFromSelector ≠ permitSelector := by
  rw [withdrawFromSelector_val, permitSelector_val]; decide

theorem withdrawFromSelector_ne_flashLoanSelector :
    withdrawFromSelector ≠ flashLoanSelector :=
  flashLoanSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_transferSelector :
    withdrawFromSelector ≠ transferSelector :=
  transferSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_transferAndCallSelector :
    withdrawFromSelector ≠ transferAndCallSelector :=
  transferAndCallSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_withdrawSelector :
    withdrawFromSelector ≠ withdrawSelector :=
  withdrawSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_withdrawToSelector :
    withdrawFromSelector ≠ withdrawToSelector :=
  withdrawToSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_transferFromSelector :
    withdrawFromSelector ≠ transferFromSelector := by
  rw [withdrawFromSelector_val, transferFromSelector_val]; decide

theorem withdrawFromSelector_ne_depositSelector :
    withdrawFromSelector ≠ depositSelector :=
  depositSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_depositToSelector :
    withdrawFromSelector ≠ depositToSelector :=
  depositToSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_depositToAndCallSelector :
    withdrawFromSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_withdrawFromSelector.symm

end Weth10

end Blanc
