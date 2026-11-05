import Blanc.Lift.Token.Core

/-!
# Token interface facet: the ERC-20 ABI

A separate facet over a `Book`: the book reads the standard `transfer` and `balanceOf` selectors as
the standard operations, for every representable calldata (`CALLDATASIZE` is a word: a contract
may read longer calldata modulo `2^256`, as WETH9 does).  Contract-neutral; instances prove it from
their own decoder.
-/

namespace Blanc.Lift.Token

open Jaune

/-- **Facet: ERC-20 ABI.**  The book reads the standard selectors as the standard operations. -/
structure Erc20Abi (B : Book) : Prop where
  transfer : ∀ a : Sevm, 68 ≤ a.data.length → a.data.length < 2 ^ 256 →
    Blanc.Sevm.selector a = 0xa9059cbb →
    B.op a = .transfer (Sevm.dataWord a 4).toAdr (Sevm.dataWord a 36).toNat
  balanceOf : ∀ a : Sevm, 36 ≤ a.data.length → a.data.length < 2 ^ 256 →
    Blanc.Sevm.selector a = 0x70a08231 →
    B.op a = .balanceOf (Sevm.dataWord a 4).toAdr

/-- The canonical `true` answer is an accepted ERC-20 boolean. -/
theorem true_word_accepted :
    (Nat.toB256 1).toBytes = [] ∨ (32 ≤ (Nat.toB256 1).toBytes.length ∧
      Bytes.toB256 ((Nat.toB256 1).toBytes.sliceD 0 32 0) ≠ 0) := by
  refine Or.inr ⟨by rw [B256.length_toBytes], ?_⟩
  rw [Bytes.sliceD_zero_length (B256.length_toBytes _), B256.toB256_toBytes]
  decide

end Blanc.Lift.Token
