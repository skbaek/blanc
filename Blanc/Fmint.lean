-- Fmint.lean : "fmint", contract #2 — an ERC-3156 flash-mintable ERC-20.
--
-- Program source of truth: `~/plans/flashmint-proposal.md` (D1 resolved pure,
-- D2 fee ≡ 0, D3 storage layout, D4 callback shape, D5 ordering discipline,
-- D6 events).  Behavioral adjudication against the pinned OpenZeppelin
-- reference: `FMINT_DEVIATIONS.md`.
--
-- At this checkpoint the module holds the design-freeze constants and the two
-- codegen spikes only; the twelve dispatch targets and the dispatcher arrive
-- with Step 1 of `~/plans/fmint-code.md`.
--
--
-- WHY A NAMESPACE.  `Blanc/Weth.lean` owns the bare `Blanc.name`,
-- `Blanc.transfer`, `Blanc.approve`, `Blanc.allowance`, `Blanc.balanceOf`,
-- `Blanc.decimals`, `Blanc.transferEvent`, … globals.  fmint has functions of
-- the same names, so everything here lives in `Blanc.Fmint`.
--
--
-- IMPORT `Blanc.Weth` AND REFERENCE, OR COPY INTO THE NAMESPACE?  Decided at
-- the design freeze: **copy into the namespace**, and import only
-- `Blanc.CommonCore`.  Four bodies genuinely carry over verbatim — `decimals`,
-- `balanceOf`, `allowance`, `transfer` — and it is cheap to write them again,
-- so the decision turns entirely on what the import edge would cost:
--
--   1. An import edge is the only mechanism by which work on fmint could
--      perturb WETH's frozen surface.  Without one, `Blanc/Weth.lean` and its
--      audited theorems are unreachable from here by construction, which is
--      the constraint this arc is least willing to risk.
--   2. It would buy nothing on the proof side.  `FuncSound` obligations reach
--      the exact program through `Pre`'s code hypothesis and `Prog.At`
--      (`~/plans/flashmint-proposal.md`, the context-stability bullet), so
--      sharing a `Func` *value* between two contracts does not share a single
--      proof step between them.  Verbatim reuse across programs is an open
--      theorem, not an available fact.
--   3. Sharing the value would also silently couple the two contracts' future:
--      a later fmint-only tweak to a shared body would be a WETH edit.
--   4. `Blanc.CommonCore` (~2.3 s to elaborate) is a lighter dependency than
--      `Blanc.Weth`, which pulls in `Blanc.CommonProofs` (~5.4 s).
--
-- What *is* shared is `Blanc/CommonCore.lean` — `Line`/`Func` machinery,
-- `checkAddress`, `isMax`, `logWith`, `returnTrue`, `signatureHash`,
-- `DispatchTree` — which is the contract-agnostic layer and is shared surface
-- already.  Anything fmint needs that belongs there is added there, additively;
-- `checkAddress` in particular is shared WETH surface and must not change.

import Blanc.CommonCore

namespace Blanc

open Jaune

namespace Fmint

/-! ## Storage layout (proposal D3)

Three regions, one collision discipline:

| region     | slot                          | guard                                     |
|------------|-------------------------------|-------------------------------------------|
| balances   | the raw 256-bit address word  | mutators reject non-address words         |
| allowances | `keccak256(owner ‖ spender)`  | revert if address-shaped **or** `supplySlot` |
| supply     | `supplySlot`                  | fixed; never address-shaped               |
-/

/-- The supply slot: `B256.max`.

Two properties earn it the position.  It is never address-shaped — its upper 96
bits are all ones — so `wbsum`, which sums storage over address-shaped keys
only, excludes it automatically and the conservation statement can be a plain
storage equality with no carve-out.  And it is `not 0`, so pushing it costs two
bytes of code rather than thirty-three.

Relocated here from `Blanc/Flashmint.lean` at the design freeze: `Fmint.lean`
needs the constant in order to *generate* the contract, while `Flashmint.lean`
must import the contract in order to *apply* it, so the constant moves down and
`Flashmint.lean` references it. -/
def supplySlot : B256 := B256.max

/-! ## Event topics (proposal D6)

A topic0 word is the keccak of the event's ABI signature string — the same
`signatureHash` a function selector is built from, without the shift that
narrows one to four bytes.  Naming each event once is how the same event avoids
ending up with two spellings and, one typo later, two topics.

fmint emits exactly two events, both ERC-20's.  There is no `Deposit` and no
`Withdrawal`: fmint is the pure token of D1, with no wrap/unwrap surface.

Mint and burn are `Transfer` events through the zero address —
`Transfer(0x0 → receiver, amount)` on the mint and
`Transfer(receiver → 0x0, amount + fee)` on the burn — which is what the pinned
OpenZeppelin reference emits through `_mint`/`_burn`, so they need no topic of
their own.  The repayment allowance spend emits **no** `Approval`, matching both
OpenZeppelin v5's `_spendAllowance` and WETH9's `transferFrom`.  See
`FMINT_DEVIATIONS.md` rows 12–14. -/

def transferEvent : B256 := signatureHash "Transfer" [.address, .address, .uint256]
def approvalEvent : B256 := signatureHash "Approval" [.address, .address, .uint256]

end Fmint

end Blanc
