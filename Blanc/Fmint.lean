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

open Jaune.Ninst Ninst

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
storage equality with no carve-out.  And it is `not 0`, so pushing it can cost
two bytes of code rather than thirty-three — but only through `pushSupplySlot`
below; `pushB256 supplySlot` emits a `PUSH32` and forfeits the saving.

Relocated here from `Blanc/Flashmint.lean` at the design freeze: `Fmint.lean`
needs the constant in order to *generate* the contract, while `Flashmint.lean`
must import the contract in order to *apply* it, so the constant moves down and
`Flashmint.lean` references it. -/
def supplySlot : B256 := B256.max

/-- Push `supplySlot`.

`( -- supplySlot )`

Use this rather than `pushB256 supplySlot`, which emits a 33-byte `PUSH32`.
`PUSH0; NOT` is two bytes, and `not 0 = B256.max` is the whole reason the
proposal chose `B256.max` for this slot in the first place.  `pushAddressMask`
is the established precedent for the trick.

Found by disassembling the Step-0 spike, which had used `pushB256 supplySlot`
at both burn sites and paid 66 bytes for 4. -/
def pushSupplySlot : Line := [pushB256 0, not]

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

/-! ## ERC-3156 constants -/

/-- The borrower callback's selector, `0x23e30c8b`.  Not a dispatch target of
ours — it is what fmint *calls* — so unlike the twelve entry-point selectors it
is named here rather than appearing in the dispatch list. -/
def onFlashLoanSelector : B256 :=
  selector "onFlashLoan" [.address, .address, .uint256, .uint256, .dynBytes]

/-- `keccak256("ERC3156FlashBorrower.onFlashLoan")` —
`0x439148f0bbc682ca079e46d6e2c2f0c1e3b820f1a291b069d8882abf8cf18dd9`, the word
a compliant borrower must return.  ERC-3156: "If successful, `onFlashLoan` MUST
return the keccak256 hash of 'ERC3156FlashBorrower.onFlashLoan'." -/
def erc3156Magic : B256 := Blanc.String.keccak "ERC3156FlashBorrower.onFlashLoan"

/-! ## The aux table

`Func.call` indices are positional into `main :: aux`, so this order is
**append-only for the lifetime of the contract**: Arc B's per-function
obligations are stated relative to the aux context, and renumbering an entry
silently re-points every `Func.call` that names it.  New entries go on the end.

Frozen here, at the design freeze, because spike 1 below already calls into
slot 2.  Step 1 builds `fmint : Prog := ⟨Func.mainWith fallbackSlot fmintTree,
fmintAux⟩` on top of this list; it may append, never reorder. -/

/-- Index of the reverting fallback in `main :: aux`.  `Func.mainWith` routes a
dispatcher miss here.  WETH points the same slot at `deposit`; fmint is the pure
token of D1 and has no fallback behavior to offer, so an unrecognized selector
— and a bare value transfer — reverts. -/
def fallbackSlot : Nat := 1

/-- Index of the shared burn epilogue in `main :: aux`.  See spike 1. -/
def burnSlot : Nat := 2

/-! ## Spike 1 — the repayment fragment (proposal D4 step 6)

The control-flow risk concentrate of the whole contract, prototyped before the
contract exists.  It is genuinely new code rather than a reuse of WETH's
`updateAllowance`, for three verified reasons:

* `updateAllowance` hashes `src ‖ caller`; repayment needs
  `receiver ‖ address(this)` — the `address` opcode, not `caller`;
* its first guard skips the allowance entirely when `src = caller`, which is not
  the ERC-3156 rule.  A borrower naming itself as `receiver` is the *common*
  case and must still spend allowance, as the pinned OpenZeppelin reference
  does (`FMINT_DEVIATIONS.md` rows 11 and 16);
* every one of its success leaves terminates in `returnTrue`, whereas repayment
  must continue to the burn — and `Func.call` is a tail jump, so nothing returns
  from it.

**Shape decision.**  Both arms of the `isMax` test — preserve an infinite
allowance, or decrement a finite one — have to reach the same burn.  A `Func` is
a tree with no join points, so a shared continuation is either an `aux` entry
reached by `Func.call`, or a duplicated tail, or no branch at all.  Chosen: the
**`aux` entry**, which is the free tail-share case (`~/plans/cps-proposal.md`
structural fact 6: a join that is a function *suffix* costs a `PUSH2`/`JUMP` and
nothing else), and which the proposal names directly.  The two rejected shapes,
recorded so the choice is not re-litigated:

* *duplicated tail* — also correct, but it emits the whole epilogue twice (~70
  bytes here) to save one `PUSH2`/`JUMP`, and leaves Arc B two leaves to walk
  where the aux entry leaves one;
* *branchless fall-through* — computing `amnt - wad * (1 - isMax amnt)` needs a
  `mul` on the storage-writing path, buying a novel arithmetic obligation in
  Arc B to save one jump, and forcing an `SSTORE` of the unchanged value in the
  infinite case.  Rejected on proof cost.

The selector-CPS scheme of `~/plans/cps-proposal.md` is **not** in scope and
must not be introduced here.  Its trigger is a shared *middle* with
caller-specific resumptions; this is a shared *tail*, which needs none of it. -/

/-- The shared burn epilogue, aux slot `burnSlot`.

`( wad :: receiver -- * )`

Written out in full rather than left as a stub: what needed prototyping is
exactly the convergence — the aux entry, the `Func.call` reaching it from both
arms, and the D5-adjacent paired writes — and a stub would have exercised none
of it.  Step 1 owns its final placement inside `flashLoan`.

**Ordering (proposal D5).**  The two `SSTORE`s of the pair are adjacent, with no
external control transfer and no successful halt between them.  The invariant is
an *equality*, so unlike WETH's inequality it cannot survive a half-completed
pair reaching an observable point.  An exceptional halt between them would be
harmless — EVM rollback discards the half-pair — but adjacency costs nothing.

**No supply underflow guard, deliberately.**  `supply - wad` cannot underflow
*because the conservation invariant holds*: `wad ≤ rbal ≤ Σ balances = supply`,
the first inequality being the balance check two lines above.  This is D5's
overflow discipline — the invariant itself bounds every balance — and it is the
reason the conservation statement needs no `nof`-style global hypothesis.  The
argument is invariant-dependent by design; Arc B discharges it. -/
def burnAndReturn : Func :=
  dup 1 ::: sload :::           -- rbal :: wad :: receiver
  dup 1 ::: dup 1 ::: lt :::    -- (rbal <? wad) :: rbal :: wad :: receiver
  .rev <?>                      -- [insufficient balance to burn: revert]
                                -- rbal :: wad :: receiver
  dup 1 ::: swap 0 ::: sub :::  -- (rbal - wad) :: wad :: receiver
  dup 2 ::: sstore :::          -- wad :: receiver
                                -- [receiver balance burnt]
  pushSupplySlot +++ sload :::  -- supply :: wad :: receiver
  dup 1 ::: swap 0 ::: sub :::  -- (supply - wad) :: wad :: receiver
  pushSupplySlot +++ sstore ::: -- wad :: receiver
                                -- [supply burnt; pair complete]
  dup 0 ::: mstoreAt 0 +++      -- wad :: receiver || wad
  pushB256 0 :::                -- 0 :: wad :: receiver || wad
  dup 2 :::                     -- receiver :: 0 :: wad :: receiver || wad
  pushB256 transferEvent :::    -- transferEventSig :: receiver :: 0 :: ... || wad
  logWith 2 0 1 +++             -- 2 indexed topics : from = receiver, to = 0x0
                                -- 1 unindexed data : burnt amount
                                -- [Transfer(receiver, 0x0, wad) is logged]
  returnTrue

/-- Spend the allowance `receiver → address(this)` for `wad`, then burn.

`( wad :: receiver -- * )`

The four departures from `updateAllowance` are all visible in the body: the
spender is `address` and not `caller`; there is no `src = caller` bypass; the
slot guard carries the extra `supplySlot` clause; and both arms end in
`Func.call burnSlot` instead of `returnTrue`.

**The extended slot guard (proposal D3).**  Revert if `keccak256(receiver ‖
self)` is address-shaped — it would collide with a balance slot, as in WETH —
**or** if it equals `supplySlot`, which is the clause the third storage region
adds.  Note `isMax` *is* the `supplySlot` comparison: `supplySlot = B256.max`,
so "the hash is all ones" and "the hash is the supply slot" are the same test,
which is why the clause costs two bytes.  Step 1 commits a Lean witness that
the comparison fires on the concrete colliding word; the clause is not
fixture-testable, needing a 2²⁵⁶ keccak preimage (`FMINT_DEVIATIONS.md` row 18).

**Infinite-allowance preservation** is a WETH9/OpenZeppelin convention, not an
EIP requirement, and specifically *not* "EIP-717" — that attribution is
erroneous.  The pinned reference's `_spendAllowance` skips the write when the
current allowance is `type(uint256).max`; so does this. -/
def spendAllowanceThenBurn : Func :=
  -- key := keccak256(receiver ‖ address(this)), hashed out of memory words 0-1
  dup 1 ::: mstoreAt 0 +++      -- wad :: receiver || receiver
  address ::: mstoreAt 1 +++    -- wad :: receiver || receiver :: self
  pushList [64, 0] +++          -- 0 :: 64 :: wad :: receiver || receiver :: self
  kec :::                       -- hash :: wad :: receiver
  -- the extended slot guard: address-shaped OR equal to supplySlot
  dup 0 ::: checkAddress +++    -- va(hash) :: hash :: wad :: receiver
  dup 1 ::: isMax +++           -- (hash =? supplySlot) :: va(hash) :: hash :: wad :: receiver
  or :::                        -- collides? :: hash :: wad :: receiver
  .rev <?>                      -- [the allowance slot would alias a balance slot
                                --  or the supply slot: revert]
                                -- hash :: wad :: receiver
  dup 0 ::: sload :::           -- amnt :: hash :: wad :: receiver
  dup 0 ::: isMax +++           -- (amnt =? max) :: amnt :: hash :: wad :: receiver
  ( -- INFINITE ARM: an infinite allowance is preserved, never decremented.
    pop ::: pop :::             -- wad :: receiver
    .call burnSlot ) <?>
  ( -- FINITE ARM
    dup 2 ::: dup 1 ::: lt :::  -- (amnt <? wad) :: amnt :: hash :: wad :: receiver
    .rev <?>                    -- [allowance below the amount owed: revert]
                                -- amnt :: hash :: wad :: receiver
    dup 2 ::: swap 0 ::: sub ::: -- (amnt - wad) :: hash :: wad :: receiver
    swap 0 ::: sstore :::       -- wad :: receiver
                                -- [allowance decremented; NO Approval event —
                                --  D6, matching OZ v5 and WETH9]
    .call burnSlot )

/-! ## Spike 2 — the `onFlashLoan` calldata layout (proposal D4 step 4)

The fiddliest new codegen, and the one place where a silent off-by-one produces
a decodable-but-wrong callback.  The layout is fixed here as a table rather than
inferred from the code.

fmint builds the callback's calldata in memory word-aligned and then hands the
`CALL` an *unaligned* window, which is what buys every store an `mstoreAt`:

```
  memory                                  callback calldata
  ------------------------------------    -------------------------------------
  word 0  0x00  selector, right-aligned   bytes 0x1c-0x1f are the 4 selector
                                          bytes; 0x00-0x1b are outside the window
  word 1  0x20  initiator = caller        head word 0   (address)
  word 2  0x40  token     = address       head word 1   (address)
  word 3  0x60  amount                    head word 2   (uint256)
  word 4  0x80  fee = 0                   head word 3   (uint256)
  word 5  0xa0  0xa0                      head word 4   (offset of `data`)
  word 6  0xc0  dataLen                   tail: length of `data`
          0xe0  payload                   tail: `data`, zero-padded to a word
```

* `argsOffset = 0x1c` (`callbackArgsOffset`), `argsSize = 0xc4 + ceil32(dataLen)`
  — 4 selector bytes plus six words plus the padded payload.
* The offset word is `0xa0` because offsets are relative to the start of the
  argument area (memory `0x20`), and the tail begins at memory `0xc0`.
* The padding bytes are zero because EVM memory is zero-initialized and this
  frame writes the payload region exactly once — there is no loop, and a
  reentrant nested `flashLoan` runs in a fresh frame with fresh memory.  Step 1
  must preserve that; writing above `0xe0` before this point would corrupt the
  pad.  Padding at all is a choice: it makes the forwarded bytes byte-identical
  to what Solidity's encoder produces (`FMINT_DEVIATIONS.md` row 9), where the
  unpadded alternative would be accepted by Solidity's decoder but would be a
  divergence row of its own.
* No offset or length validation is performed on our own calldata; that is a
  recorded policy, not an oversight (`FMINT_DEVIATIONS.md` row 21).
  `calldataload` and `calldatacopy` both zero-pad past the end of calldata, so a
  malformed tail forwards zeros rather than reading anything it should not, and
  an absurd `dataLen` is bounded by memory-expansion gas. -/

/-- The `CALL`'s `argsOffset`: four bytes short of memory word 1, so that the
right-aligned selector in word 0 becomes the calldata's first four bytes. -/
def callbackArgsOffset : B256 := 0x1c

/-- Store the selector and the five head words.

`( amount -- )`, leaving memory words 0-5 as tabulated above. -/
def storeCallbackHead : Line :=
  pushB256 onFlashLoanSelector :: mstoreAt 0 ++  -- || sel
  caller :: mstoreAt 1 ++                        -- || sel ; initiator = caller
  address :: mstoreAt 2 ++                       -- || … ; token = self
  mstoreAt 3 ++                                  -- || … ; amount (from the stack)
  pushB256 0 :: mstoreAt 4 ++                    -- || … ; fee = 0 (D2)
  pushB256 0xa0 :: mstoreAt 5                    -- || … ; offset of `data`

/-- Forward the `data` tail of our own calldata into the callback's.

`( -- dataLen )`, writing memory word 6 and the payload region at `0xe0`.

`arg 3` reads the *head* word of `flashLoan`'s fourth argument, which for a
dynamic type is an offset rather than a value — the distinction the `dynBytes`
constructor is careful about.  Following it is this line's job. -/
def forwardCallbackData : Line :=
  arg 3 ++                        -- off              (relative to calldata byte 4)
  pushB256 4 :: add ::            -- p := 4 + off     (absolute: the length word)
  dup 0 :: calldataload ::        -- len :: p
  dup 0 :: mstoreAt 6 ++          -- len :: p         || … ; dataLen
  dup 0 :: swap 1 ::              -- p :: len :: len
  pushB256 32 :: add ::           -- p + 32 :: len :: len   (absolute: the payload)
  pushB256 0xe0 ::                -- 0xe0 :: p + 32 :: len :: len
  calldatacopy :: []              -- len

/-- `( dataLen -- argsSize )` — the `CALL`'s `argsSize`, `0xc4 + ceil32(len)`.

`ceil32` is the usual `(len + 31) & ~31`; `~31` is pushed as `PUSH1 31; NOT`,
two bytes rather than thirty-three, the same trick `pushAddressMask` uses. -/
def callbackArgsSize : Line :=
  pushB256 31 :: add ::               -- len + 31
  pushB256 31 :: not :: Ninst.and ::  -- ceil32(len)
  pushB256 0xc4 :: add :: []          -- 0xc4 + ceil32(len)

/-- The aux table as frozen at the design freeze.  Append-only; see above. -/
def fmintAux : List Func := [Func.rev, burnAndReturn]

end Fmint

end Blanc
