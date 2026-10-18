import Blanc.Lift.Usdc.Model

/-!
# What a committed FiatTokenV2_2 frame asks

`decodeCall e` is the implementation dispatcher's reading of a message, row by row from the
selector table `c0/inventory/impl-selectors.json` (all 55 selectors).  Checked against the deployed
runtime (`c0/rpc/*-finalized/impl-runtime.hex`, Solidity 0.6.12, legacy ABI decoder):

* pc 5: `CALLVALUE ISZERO`, else revert — no function is payable, so a nonzero value reverts;
* pc 18: `CALLDATASIZE < 4` jumps to the revert at pc 877; an unmatched selector falls through to
  the same revert (no fallback, no receive);
* at each entry, `CALLDATASIZE - 4 < 32 * n` reverts, `n` the static head size (`headWords`);
* address arguments are masked to 160 bits (`PUSH20 0xff…ff … AND`), which is `B256.toAdr`;
  integers are read whole; `bytes32` words are kept.

The bounds checks on the offset and length words of a dynamic argument (`bytes`, `string`,
`address[]`) are not modelled: such a row decodes (`some`), and a frame whose dynamic argument is
out of bounds reverts, so no committed frame is misread.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

/-- One row of the dispatcher table: the selector, the static head size in words, and the call it
reads (`w k` is the calldata word at byte `k`). -/
structure Row where
  sel : B256
  headWords : Nat
  read : Sevm → Call

/-- The dispatcher's table (C0 §5.1).  Both overloads of the four signature entries read the same
constructor; the `uint8 v, bytes32 r, bytes32 s` and `bytes signature` tails are not read. -/
def rows : List Row :=
  let w := Sevm.dataWord
  [ -- writers
    ⟨0xa9059cbb, 2, fun e => .transfer (w e 4).toAdr (w e 36).toNat⟩,
    ⟨0x23b872dd, 3, fun e => .transferFrom (w e 4).toAdr (w e 36).toAdr (w e 68).toNat⟩,
    ⟨0x095ea7b3, 2, fun e => .approve (w e 4).toAdr (w e 36).toNat⟩,
    ⟨0x39509351, 2, fun e => .increaseAllowance (w e 4).toAdr (w e 36).toNat⟩,
    ⟨0xa457c2d7, 2, fun e => .decreaseAllowance (w e 4).toAdr (w e 36).toNat⟩,
    ⟨0x9fd5a6cf, 5, fun e => .permit (w e 4).toAdr (w e 36).toAdr (w e 68).toNat⟩,
    ⟨0xd505accf, 7, fun e => .permit (w e 4).toAdr (w e 36).toAdr (w e 68).toNat⟩,
    ⟨0xcf092995, 7, fun e =>
      .transferWithAuthorization (w e 4).toAdr (w e 36).toAdr (w e 68).toNat (w e 164)⟩,
    ⟨0xe3ee160e, 9, fun e =>
      .transferWithAuthorization (w e 4).toAdr (w e 36).toAdr (w e 68).toNat (w e 164)⟩,
    ⟨0x88b7ab63, 7, fun e =>
      .receiveWithAuthorization (w e 4).toAdr (w e 36).toAdr (w e 68).toNat (w e 164)⟩,
    ⟨0xef55bec6, 9, fun e =>
      .receiveWithAuthorization (w e 4).toAdr (w e 36).toAdr (w e 68).toNat (w e 164)⟩,
    ⟨0xb7b72899, 3, fun e => .cancelAuthorization (w e 4).toAdr (w e 36)⟩,
    ⟨0x5a049a70, 5, fun e => .cancelAuthorization (w e 4).toAdr (w e 36)⟩,
    ⟨0x40c10f19, 2, fun e => .mint (w e 4).toAdr (w e 36).toNat⟩,
    ⟨0x42966c68, 1, fun e => .burn (w e 4).toNat⟩,
    ⟨0x4e44d956, 2, fun e => .configureMinter (w e 4).toAdr (w e 36).toNat⟩,
    ⟨0x3092afd5, 1, fun e => .removeMinter (w e 4).toAdr⟩,
    ⟨0xaa20e1e4, 1, fun e => .updateMasterMinter (w e 4).toAdr⟩,
    ⟨0x8456cb59, 0, fun _ => .pause⟩,
    ⟨0x3f4ba83a, 0, fun _ => .unpause⟩,
    ⟨0x554bab3c, 1, fun e => .updatePauser (w e 4).toAdr⟩,
    ⟨0xad38bf22, 1, fun e => .updateBlacklister (w e 4).toAdr⟩,
    ⟨0x2ab60045, 1, fun e => .updateRescuer (w e 4).toAdr⟩,
    ⟨0xf2fde38b, 1, fun e => .transferOwnership (w e 4).toAdr⟩,
    ⟨0xf9f92be4, 1, fun e => .blacklist (w e 4).toAdr⟩,
    ⟨0x1a895266, 1, fun e => .unBlacklist (w e 4).toAdr⟩,
    ⟨0xb2118a8d, 3, fun e => .rescueERC20 (w e 4).toAdr (w e 36).toAdr (w e 68).toNat⟩,
    ⟨0x3357162b, 8, fun _ => .«initialize»⟩,
    ⟨0xd608ea64, 1, fun _ => .initializeV2⟩,
    ⟨0x2fc81e09, 1, fun e => .initializeV2_1 (w e 4).toAdr⟩,
    ⟨0x430239b4, 2, fun _ => .initializeV2_2⟩,
    -- views (and the pure `version()`)
    ⟨0xd9169487, 0, fun _ => .view⟩, ⟨0x3644e515, 0, fun _ => .view⟩,
    ⟨0x30adf81f, 0, fun _ => .view⟩, ⟨0x7f2eecc3, 0, fun _ => .view⟩,
    ⟨0xa0cc6a68, 0, fun _ => .view⟩, ⟨0xdd62ed3e, 2, fun _ => .view⟩,
    ⟨0xe94a0102, 2, fun _ => .view⟩, ⟨0x70a08231, 1, fun _ => .view⟩,
    ⟨0xbd102430, 0, fun _ => .view⟩, ⟨0xe5a6b10f, 0, fun _ => .view⟩,
    ⟨0x313ce567, 0, fun _ => .view⟩, ⟨0xfe575a87, 1, fun _ => .view⟩,
    ⟨0xaa271e1a, 1, fun _ => .view⟩, ⟨0x35d99f35, 0, fun _ => .view⟩,
    ⟨0x8a6db9c3, 1, fun _ => .view⟩, ⟨0x06fdde03, 0, fun _ => .view⟩,
    ⟨0x7ecebe00, 1, fun _ => .view⟩, ⟨0x8da5cb5b, 0, fun _ => .view⟩,
    ⟨0x5c975abb, 0, fun _ => .view⟩, ⟨0x9fd0506d, 0, fun _ => .view⟩,
    ⟨0x38a63183, 0, fun _ => .view⟩, ⟨0x95d89b41, 0, fun _ => .view⟩,
    ⟨0x18160ddd, 0, fun _ => .view⟩, ⟨0x54fd4d50, 0, fun _ => .view⟩ ]

/-- The implementation dispatcher's reading of a message (selector table
`c0/inventory/impl-selectors.json`; `none` for a selector the dispatcher rejects or calldata its ABI
decoder rejects). -/
def decodeCall (e : Sevm) : Option Call :=
  if e.value ≠ 0 ∨ e.data.length < 4 then none
  else match rows.find? (fun r => r.sel = Sevm.selector e) with
    | none => none
    | some r => if 4 + 32 * r.headWords ≤ e.data.length then some (r.read e) else none

/-- The table has the 55 selectors of `c0/inventory/impl-selectors.json`, each once (so `find?`'s
first match is the only one). -/
example : rows.length = 55 ∧ (rows.map Row.sel).Nodup := by decide

/-- A matched row whose head fits decodes by that row. -/
theorem decodeCall_of_find {e : Sevm} {r : Row} (value : e.value = 0)
    (found : rows.find? (fun r => decide (r.sel = Sevm.selector e)) = some r)
    (len : 4 + 32 * r.headWords ≤ e.data.length) : decodeCall e = some (r.read e) := by
  have pass : ¬ (e.value ≠ 0 ∨ e.data.length < 4) := by
    rw [not_or, not_not]; exact ⟨value, by omega⟩
  unfold decodeCall
  simp only [pass, ↓reduceIte, found, len]

/-! ## The rows the token interface reads by selector -/

/-- **`balanceOf(address)`** writes nothing: it decodes to `view` or reverts. -/
theorem decodeCall_balanceOf {e : Sevm} (sel : Sevm.selector e = 0x70a08231) :
    decodeCall e = none ∨ decodeCall e = some .view := by
  have found : rows.find? (fun r => decide (r.sel = Sevm.selector e)) =
      some ⟨0x70a08231, 1, fun _ => .view⟩ := by
    rw [sel]; rfl
  by_cases value : e.value = 0
  · by_cases len : 4 + 32 * 1 ≤ e.data.length
    · exact Or.inr (decodeCall_of_find value found len)
    · left
      unfold decodeCall
      simp only [found, len, ↓reduceIte, ite_self]
  · left
    unfold decodeCall
    simp only [ne_eq, value, not_false_eq_true, true_or, ↓reduceIte]

/-- **`transfer(address,uint256)`**: a long enough nonpayable message decodes to the transfer its
argument words name. -/
theorem decodeCall_transfer {e : Sevm} (sel : Sevm.selector e = 0xa9059cbb)
    (len : 68 ≤ e.data.length) (value : e.value = 0) :
    decodeCall e = some (.transfer (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toNat) :=
  decodeCall_of_find (r := ⟨0xa9059cbb, 2, fun e => .transfer (Sevm.dataWord e 4).toAdr
    (Sevm.dataWord e 36).toNat⟩) value (by rw [sel]; rfl) (by omega)

/-- **`transferFrom(address,address,uint256)`**, likewise. -/
theorem decodeCall_transferFrom {e : Sevm} (sel : Sevm.selector e = 0x23b872dd)
    (len : 100 ≤ e.data.length) (value : e.value = 0) :
    decodeCall e = some (.transferFrom (Sevm.dataWord e 4).toAdr (Sevm.dataWord e 36).toAdr
      (Sevm.dataWord e 68).toNat) :=
  decodeCall_of_find (r := ⟨0x23b872dd, 3, fun e => .transferFrom (Sevm.dataWord e 4).toAdr
    (Sevm.dataWord e 36).toAdr (Sevm.dataWord e 68).toNat⟩) value (by rw [sel]; rfl) (by omega)

end Blanc.Lift.Usdc
