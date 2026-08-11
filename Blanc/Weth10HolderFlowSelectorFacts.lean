import Blanc.Weth10HolderFlow

/-!
Selector separations for the WETH10 holder-flow alphabet.

`Blanc.Weth10SelectorFacts` pays a selector's keccak once and derives its
separations by rewriting, because deciding a pair straight from the two
signature strings recomputes both hashes.  That module sits above
`Blanc.Weth10Attribution`, so the holder-flow layer, which is below it
and needs four hundred separations of its own, could not reach it and was
deciding every pair from scratch.

This module is the lower half of the same facility, and holds exactly the
ten selectors the holder-flow proofs dispatch on: the three deposit
entries, the three transfer entries, the three withdrawal entries and
`flashLoan`.  It states each one's word once and separates all ninety
ordered pairs from those words, `Ne.symm` supplying each reverse.
`Blanc.Weth10SelectorFacts` imports it and adds the pairs that need
`approve`, `permit`, `allowance` or a read-only view, which are not in
scope here.

Nothing here is a claim about the runtime: these are arithmetic facts
about the ABI signature hashes, stated so the modules that consume them
state no local copies.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## The selector words

One kernel keccak per selector, and the only ten in this module's
alphabet.  Unlike the upper half's own words these are not private:
`Blanc.Weth10SelectorFacts` rewrites with them to separate these ten from
the selectors it adds, and re-deciding them there would pay the ten
hashes a second time. -/

theorem depositSelector_val :
    depositSelector = (0xd0e30db0 : B256) := by decide +kernel

theorem depositToSelector_val :
    depositToSelector = (0xb760faf9 : B256) := by decide +kernel

theorem depositToAndCallSelector_val :
    depositToAndCallSelector = (0x5ddb7d7e : B256) := by decide +kernel

theorem transferSelector_val :
    transferSelector = (0xa9059cbb : B256) := by decide +kernel

theorem transferAndCallSelector_val :
    transferAndCallSelector = (0x4000aea0 : B256) := by decide +kernel

theorem transferFromSelector_val :
    transferFromSelector = (0x23b872dd : B256) := by decide +kernel

theorem withdrawSelector_val :
    withdrawSelector = (0x2e1a7d4d : B256) := by decide +kernel

theorem withdrawToSelector_val :
    withdrawToSelector = (0x205c2878 : B256) := by decide +kernel

theorem withdrawFromSelector_val :
    withdrawFromSelector = (0x9555a942 : B256) := by decide +kernel

theorem flashLoanSelector_val :
    flashLoanSelector = (0x5cffe9de : B256) := by decide +kernel

/-! ## The separations

Each unordered pair is compared once on its words; the reverse direction
is that comparison read backwards. -/

/-! ### `deposit` -/

theorem depositSelector_ne_depositToSelector :
    depositSelector ≠ depositToSelector := by
  rw [depositSelector_val, depositToSelector_val]; decide

theorem depositSelector_ne_depositToAndCallSelector :
    depositSelector ≠ depositToAndCallSelector := by
  rw [depositSelector_val, depositToAndCallSelector_val]; decide

theorem depositSelector_ne_transferSelector :
    depositSelector ≠ transferSelector := by
  rw [depositSelector_val, transferSelector_val]; decide

theorem depositSelector_ne_transferAndCallSelector :
    depositSelector ≠ transferAndCallSelector := by
  rw [depositSelector_val, transferAndCallSelector_val]; decide

theorem depositSelector_ne_transferFromSelector :
    depositSelector ≠ transferFromSelector := by
  rw [depositSelector_val, transferFromSelector_val]; decide

theorem depositSelector_ne_withdrawSelector :
    depositSelector ≠ withdrawSelector := by
  rw [depositSelector_val, withdrawSelector_val]; decide

theorem depositSelector_ne_withdrawToSelector :
    depositSelector ≠ withdrawToSelector := by
  rw [depositSelector_val, withdrawToSelector_val]; decide

theorem depositSelector_ne_withdrawFromSelector :
    depositSelector ≠ withdrawFromSelector := by
  rw [depositSelector_val, withdrawFromSelector_val]; decide

theorem depositSelector_ne_flashLoanSelector :
    depositSelector ≠ flashLoanSelector := by
  rw [depositSelector_val, flashLoanSelector_val]; decide

/-! ### `depositTo` -/

theorem depositToSelector_ne_depositSelector :
    depositToSelector ≠ depositSelector :=
  depositSelector_ne_depositToSelector.symm

theorem depositToSelector_ne_depositToAndCallSelector :
    depositToSelector ≠ depositToAndCallSelector := by
  rw [depositToSelector_val, depositToAndCallSelector_val]; decide

theorem depositToSelector_ne_transferSelector :
    depositToSelector ≠ transferSelector := by
  rw [depositToSelector_val, transferSelector_val]; decide

theorem depositToSelector_ne_transferAndCallSelector :
    depositToSelector ≠ transferAndCallSelector := by
  rw [depositToSelector_val, transferAndCallSelector_val]; decide

theorem depositToSelector_ne_transferFromSelector :
    depositToSelector ≠ transferFromSelector := by
  rw [depositToSelector_val, transferFromSelector_val]; decide

theorem depositToSelector_ne_withdrawSelector :
    depositToSelector ≠ withdrawSelector := by
  rw [depositToSelector_val, withdrawSelector_val]; decide

theorem depositToSelector_ne_withdrawToSelector :
    depositToSelector ≠ withdrawToSelector := by
  rw [depositToSelector_val, withdrawToSelector_val]; decide

theorem depositToSelector_ne_withdrawFromSelector :
    depositToSelector ≠ withdrawFromSelector := by
  rw [depositToSelector_val, withdrawFromSelector_val]; decide

theorem depositToSelector_ne_flashLoanSelector :
    depositToSelector ≠ flashLoanSelector := by
  rw [depositToSelector_val, flashLoanSelector_val]; decide

/-! ### `depositToAndCall` -/

theorem depositToAndCallSelector_ne_depositSelector :
    depositToAndCallSelector ≠ depositSelector :=
  depositSelector_ne_depositToAndCallSelector.symm

theorem depositToAndCallSelector_ne_depositToSelector :
    depositToAndCallSelector ≠ depositToSelector :=
  depositToSelector_ne_depositToAndCallSelector.symm

theorem depositToAndCallSelector_ne_transferSelector :
    depositToAndCallSelector ≠ transferSelector := by
  rw [depositToAndCallSelector_val, transferSelector_val]; decide

theorem depositToAndCallSelector_ne_transferAndCallSelector :
    depositToAndCallSelector ≠ transferAndCallSelector := by
  rw [depositToAndCallSelector_val, transferAndCallSelector_val]; decide

theorem depositToAndCallSelector_ne_transferFromSelector :
    depositToAndCallSelector ≠ transferFromSelector := by
  rw [depositToAndCallSelector_val, transferFromSelector_val]; decide

theorem depositToAndCallSelector_ne_withdrawSelector :
    depositToAndCallSelector ≠ withdrawSelector := by
  rw [depositToAndCallSelector_val, withdrawSelector_val]; decide

theorem depositToAndCallSelector_ne_withdrawToSelector :
    depositToAndCallSelector ≠ withdrawToSelector := by
  rw [depositToAndCallSelector_val, withdrawToSelector_val]; decide

theorem depositToAndCallSelector_ne_withdrawFromSelector :
    depositToAndCallSelector ≠ withdrawFromSelector := by
  rw [depositToAndCallSelector_val, withdrawFromSelector_val]; decide

theorem depositToAndCallSelector_ne_flashLoanSelector :
    depositToAndCallSelector ≠ flashLoanSelector := by
  rw [depositToAndCallSelector_val, flashLoanSelector_val]; decide

/-! ### `transfer` -/

theorem transferSelector_ne_depositSelector :
    transferSelector ≠ depositSelector :=
  depositSelector_ne_transferSelector.symm

theorem transferSelector_ne_depositToSelector :
    transferSelector ≠ depositToSelector :=
  depositToSelector_ne_transferSelector.symm

theorem transferSelector_ne_depositToAndCallSelector :
    transferSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_transferSelector.symm

theorem transferSelector_ne_transferAndCallSelector :
    transferSelector ≠ transferAndCallSelector := by
  rw [transferSelector_val, transferAndCallSelector_val]; decide

theorem transferSelector_ne_transferFromSelector :
    transferSelector ≠ transferFromSelector := by
  rw [transferSelector_val, transferFromSelector_val]; decide

theorem transferSelector_ne_withdrawSelector :
    transferSelector ≠ withdrawSelector := by
  rw [transferSelector_val, withdrawSelector_val]; decide

theorem transferSelector_ne_withdrawToSelector :
    transferSelector ≠ withdrawToSelector := by
  rw [transferSelector_val, withdrawToSelector_val]; decide

theorem transferSelector_ne_withdrawFromSelector :
    transferSelector ≠ withdrawFromSelector := by
  rw [transferSelector_val, withdrawFromSelector_val]; decide

theorem transferSelector_ne_flashLoanSelector :
    transferSelector ≠ flashLoanSelector := by
  rw [transferSelector_val, flashLoanSelector_val]; decide

/-! ### `transferAndCall` -/

theorem transferAndCallSelector_ne_depositSelector :
    transferAndCallSelector ≠ depositSelector :=
  depositSelector_ne_transferAndCallSelector.symm

theorem transferAndCallSelector_ne_depositToSelector :
    transferAndCallSelector ≠ depositToSelector :=
  depositToSelector_ne_transferAndCallSelector.symm

theorem transferAndCallSelector_ne_depositToAndCallSelector :
    transferAndCallSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_transferAndCallSelector.symm

theorem transferAndCallSelector_ne_transferSelector :
    transferAndCallSelector ≠ transferSelector :=
  transferSelector_ne_transferAndCallSelector.symm

theorem transferAndCallSelector_ne_transferFromSelector :
    transferAndCallSelector ≠ transferFromSelector := by
  rw [transferAndCallSelector_val, transferFromSelector_val]; decide

theorem transferAndCallSelector_ne_withdrawSelector :
    transferAndCallSelector ≠ withdrawSelector := by
  rw [transferAndCallSelector_val, withdrawSelector_val]; decide

theorem transferAndCallSelector_ne_withdrawToSelector :
    transferAndCallSelector ≠ withdrawToSelector := by
  rw [transferAndCallSelector_val, withdrawToSelector_val]; decide

theorem transferAndCallSelector_ne_withdrawFromSelector :
    transferAndCallSelector ≠ withdrawFromSelector := by
  rw [transferAndCallSelector_val, withdrawFromSelector_val]; decide

theorem transferAndCallSelector_ne_flashLoanSelector :
    transferAndCallSelector ≠ flashLoanSelector := by
  rw [transferAndCallSelector_val, flashLoanSelector_val]; decide

/-! ### `transferFrom` -/

theorem transferFromSelector_ne_depositSelector :
    transferFromSelector ≠ depositSelector :=
  depositSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_depositToSelector :
    transferFromSelector ≠ depositToSelector :=
  depositToSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_depositToAndCallSelector :
    transferFromSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_transferSelector :
    transferFromSelector ≠ transferSelector :=
  transferSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_transferAndCallSelector :
    transferFromSelector ≠ transferAndCallSelector :=
  transferAndCallSelector_ne_transferFromSelector.symm

theorem transferFromSelector_ne_withdrawSelector :
    transferFromSelector ≠ withdrawSelector := by
  rw [transferFromSelector_val, withdrawSelector_val]; decide

theorem transferFromSelector_ne_withdrawToSelector :
    transferFromSelector ≠ withdrawToSelector := by
  rw [transferFromSelector_val, withdrawToSelector_val]; decide

theorem transferFromSelector_ne_withdrawFromSelector :
    transferFromSelector ≠ withdrawFromSelector := by
  rw [transferFromSelector_val, withdrawFromSelector_val]; decide

theorem transferFromSelector_ne_flashLoanSelector :
    transferFromSelector ≠ flashLoanSelector := by
  rw [transferFromSelector_val, flashLoanSelector_val]; decide

/-! ### `withdraw` -/

theorem withdrawSelector_ne_depositSelector :
    withdrawSelector ≠ depositSelector :=
  depositSelector_ne_withdrawSelector.symm

theorem withdrawSelector_ne_depositToSelector :
    withdrawSelector ≠ depositToSelector :=
  depositToSelector_ne_withdrawSelector.symm

theorem withdrawSelector_ne_depositToAndCallSelector :
    withdrawSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_withdrawSelector.symm

theorem withdrawSelector_ne_transferSelector :
    withdrawSelector ≠ transferSelector :=
  transferSelector_ne_withdrawSelector.symm

theorem withdrawSelector_ne_transferAndCallSelector :
    withdrawSelector ≠ transferAndCallSelector :=
  transferAndCallSelector_ne_withdrawSelector.symm

theorem withdrawSelector_ne_transferFromSelector :
    withdrawSelector ≠ transferFromSelector :=
  transferFromSelector_ne_withdrawSelector.symm

theorem withdrawSelector_ne_withdrawToSelector :
    withdrawSelector ≠ withdrawToSelector := by
  rw [withdrawSelector_val, withdrawToSelector_val]; decide

theorem withdrawSelector_ne_withdrawFromSelector :
    withdrawSelector ≠ withdrawFromSelector := by
  rw [withdrawSelector_val, withdrawFromSelector_val]; decide

theorem withdrawSelector_ne_flashLoanSelector :
    withdrawSelector ≠ flashLoanSelector := by
  rw [withdrawSelector_val, flashLoanSelector_val]; decide

/-! ### `withdrawTo` -/

theorem withdrawToSelector_ne_depositSelector :
    withdrawToSelector ≠ depositSelector :=
  depositSelector_ne_withdrawToSelector.symm

theorem withdrawToSelector_ne_depositToSelector :
    withdrawToSelector ≠ depositToSelector :=
  depositToSelector_ne_withdrawToSelector.symm

theorem withdrawToSelector_ne_depositToAndCallSelector :
    withdrawToSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_withdrawToSelector.symm

theorem withdrawToSelector_ne_transferSelector :
    withdrawToSelector ≠ transferSelector :=
  transferSelector_ne_withdrawToSelector.symm

theorem withdrawToSelector_ne_transferAndCallSelector :
    withdrawToSelector ≠ transferAndCallSelector :=
  transferAndCallSelector_ne_withdrawToSelector.symm

theorem withdrawToSelector_ne_transferFromSelector :
    withdrawToSelector ≠ transferFromSelector :=
  transferFromSelector_ne_withdrawToSelector.symm

theorem withdrawToSelector_ne_withdrawSelector :
    withdrawToSelector ≠ withdrawSelector :=
  withdrawSelector_ne_withdrawToSelector.symm

theorem withdrawToSelector_ne_withdrawFromSelector :
    withdrawToSelector ≠ withdrawFromSelector := by
  rw [withdrawToSelector_val, withdrawFromSelector_val]; decide

theorem withdrawToSelector_ne_flashLoanSelector :
    withdrawToSelector ≠ flashLoanSelector := by
  rw [withdrawToSelector_val, flashLoanSelector_val]; decide

/-! ### `withdrawFrom` -/

theorem withdrawFromSelector_ne_depositSelector :
    withdrawFromSelector ≠ depositSelector :=
  depositSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_depositToSelector :
    withdrawFromSelector ≠ depositToSelector :=
  depositToSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_depositToAndCallSelector :
    withdrawFromSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_transferSelector :
    withdrawFromSelector ≠ transferSelector :=
  transferSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_transferAndCallSelector :
    withdrawFromSelector ≠ transferAndCallSelector :=
  transferAndCallSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_transferFromSelector :
    withdrawFromSelector ≠ transferFromSelector :=
  transferFromSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_withdrawSelector :
    withdrawFromSelector ≠ withdrawSelector :=
  withdrawSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_withdrawToSelector :
    withdrawFromSelector ≠ withdrawToSelector :=
  withdrawToSelector_ne_withdrawFromSelector.symm

theorem withdrawFromSelector_ne_flashLoanSelector :
    withdrawFromSelector ≠ flashLoanSelector := by
  rw [withdrawFromSelector_val, flashLoanSelector_val]; decide

/-! ### `flashLoan` -/

theorem flashLoanSelector_ne_depositSelector :
    flashLoanSelector ≠ depositSelector :=
  depositSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_depositToSelector :
    flashLoanSelector ≠ depositToSelector :=
  depositToSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_depositToAndCallSelector :
    flashLoanSelector ≠ depositToAndCallSelector :=
  depositToAndCallSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_transferSelector :
    flashLoanSelector ≠ transferSelector :=
  transferSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_transferAndCallSelector :
    flashLoanSelector ≠ transferAndCallSelector :=
  transferAndCallSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_transferFromSelector :
    flashLoanSelector ≠ transferFromSelector :=
  transferFromSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_withdrawSelector :
    flashLoanSelector ≠ withdrawSelector :=
  withdrawSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_withdrawToSelector :
    flashLoanSelector ≠ withdrawToSelector :=
  withdrawToSelector_ne_flashLoanSelector.symm

theorem flashLoanSelector_ne_withdrawFromSelector :
    flashLoanSelector ≠ withdrawFromSelector :=
  withdrawFromSelector_ne_flashLoanSelector.symm

end Weth10

end Blanc
