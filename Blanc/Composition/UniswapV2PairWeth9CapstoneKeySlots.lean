import Blanc.Composition.UniswapV2PairWeth9CapstoneFeeTo
import Blanc.Composition.UniswapV2PairWeth9CapstoneTx2Raw
import Blanc.Lift.Weth9.Footprint

/-!
# The closed history's key universes and their slots (kernel evaluation)

The finite universes the closed history's HASH-T rows lie in, with their storage slots pairwise
distinct and off the fixed slots, evaluated by the kernel (keccak of each map slot; the `SHA256` and
`RIPEMD160` answers to `feeTo()` for the Pair's reply rows), and the frame keys the history's three
WETH9-side callee calldatas select.

* WETH9: the Pair's balance and its allowance to the trader (`W0`'s rows), and the keys of the
  `transfer(trader, 996)` and `balanceOf(pair)` frames, both called by the Pair.
* Pair: the trader's and address `0`'s share rows (`W0`'s rows), the Pair's own row, and the reply
  rows of the swap frame (its callees' answers `true`, `1001000`, `999004`, and the precompile
  answers to `feeTo()`).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair Blanc.Composition.UniswapV2PairWeth9Instance

/-- WETH9's key universe for the closed history. -/
def wethUniverse : List Weth9.Key :=
  [.bal pair, .allow pair trader, .bal trader, .bal (Nat.toB256 996).toAdr, .allow trader pair,
    .bal 0, .allow pair pair]

/-- The Pair's key universe for the closed history. -/
def pairUniverse : List WriterKey :=
  [.balance trader, .balance 0, .balance pair, .balance (Nat.toB256 1).toAdr,
    .balance (Nat.toB256 1001000).toAdr, .balance (Nat.toB256 999004).toAdr,
    mintReplyRow (Bytes.sha256 feeToData).toBytes,
    mintReplyRow (B256.toBytes (Bytes.toB256 (Bytes.ripemd160 feeToData))),
    mintReplyRow feeToData]

theorem wethUniverse_slots_nodup : (wethUniverse.map Weth9.Key.slot).Nodup := by
  decide +kernel

theorem wethUniverse_slots_apart :
    wethUniverse.all (fun k => decide (Weth9.Key.slot k ∉ Weth9.fixedSlots)) = true := by
  decide +kernel

theorem pairUniverse_slots_nodup : (pairUniverse.map WriterKey.slot).Nodup := by
  decide +kernel

theorem pairUniverse_slots_apart :
    pairUniverse.all (fun k => decide (WriterKey.slot k ∉ writerFixedSlots)) = true := by
  decide +kernel

theorem feeToRows_sub : feeToRows.all (fun k => decide (k ∈ pairUniverse)) = true := by
  decide +kernel

/-- The frame keys of WETH9's `transfer(trader, 996)` called by the Pair. -/
theorem transfer_frameKeys {s : Sevm} (caller : s.caller = pair) (data : s.data = tx2TransferData) :
    Weth9.frameKeys s = [.bal pair, .bal trader, .bal (Nat.toB256 996).toAdr, .allow trader pair,
      .allow pair trader] := by
  unfold Weth9.frameKeys Sevm.dataWord
  rw [caller, data]
  decide +kernel

/-- The frame keys of WETH9's `balanceOf(pair)` called by the Pair. -/
theorem balance_frameKeys {s : Sevm} (caller : s.caller = pair) (data : s.data = tx2BalanceData) :
    Weth9.frameKeys s = [.bal pair, .bal pair, .bal 0, .allow pair pair, .allow pair pair] := by
  unfold Weth9.frameKeys Sevm.dataWord
  rw [caller, data]
  decide +kernel

theorem swap_word4 {s : Sevm} (data : s.data = tx2Data) : (Sevm.dataWord s 4).toAdr = 0 := by
  unfold Sevm.dataWord
  rw [data]
  decide +kernel

/-- The swap's decoded rows: no decoded or view row, the zero `amount0Out` word's row. -/
theorem swap_pairDecoded {s : Sevm} (data : s.data = tx2Data) :
    pairDecodedKeys s ++ staticViewDecodedKeys s ++
      (lpMintTouched (0 : B256).toAdr ++ lpMintTouched (Sevm.dataWord s 4).toAdr) =
      [.balance 0, .balance 0] := by
  have sel := tx2_selector data
  simp only [pairDecodedKeys, staticViewDecodedKeys, sel, lpMintTouched, swap_word4 data,
    show (0x022c0d9f : B256) ≠ 0xa9059cbb by decide, show (0x022c0d9f : B256) ≠ 0x095ea7b3 by decide,
    show (0x022c0d9f : B256) ≠ 0x23b872dd by decide, show (0x022c0d9f : B256) ≠ 0xd505accf by decide,
    show (0x022c0d9f : B256) ≠ 0x70a08231 by decide, show (0x022c0d9f : B256) ≠ 0x7ecebe00 by decide,
    show (0x022c0d9f : B256) ≠ 0xdd62ed3e by decide, ite_false, List.nil_append]
  rfl

end Blanc.Composition.UniswapV2PairWeth9Capstone
