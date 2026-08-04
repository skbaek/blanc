-- Fmint.lean : "fmint", contract #2 — an ERC-3156 flash-mintable ERC-20.
--
-- Program source of truth: `~/plans/flashmint-proposal.md` (D1 resolved pure,
-- D2 fee ≡ 0, D3 storage layout, D4 callback shape, D5 ordering discipline,
-- D6 events).  Behavioral adjudication against the pinned OpenZeppelin
-- reference: `FMINT_DEVIATIONS.md`.
--
-- Reading order: the storage layout and its guard, the event topics, the
-- ERC-3156 constants, the aux table, then `flashLoan` and its fragments — the
-- risk concentrate, written first — then the two ERC-3156 views, then the
-- ERC-20 surface, then the dispatch list and the program.
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

/-- The extended allowance-slot guard (proposal D3).

`( hash -- collides? :: hash )`

An allowance key must alias neither storage region it shares the address space
with: revert if `keccak256(owner ‖ spender)` is address-shaped — it would alias
a balance slot, exactly as in WETH — **or** if it equals `supplySlot`, which is
the clause the third region adds.

Note `isMax` *is* the `supplySlot` comparison: `supplySlot = B256.max`, so "the
hash is all ones" and "the hash is the supply slot" are the same test, which is
why the new clause costs two bytes.  The two `example`s immediately below state
that identity in Lean.

This is a composition of `checkAddress` and `isMax`, not an extension of either:
`checkAddress` is shared WETH surface and must not change.  Every allowance-
*writing* path carries the guard — `approve`, `transferFrom`'s allowance update,
and the flash-loan repayment.  The `allowance` view does not
(`FMINT_DEVIATIONS.md` row 18). -/
def checkSlotCollides : Line :=
  (dup 0 :: checkAddress) ++    -- va(hash) :: hash
  (dup 1 :: isMax) ++           -- (hash =? supplySlot) :: va(hash) :: hash
  [Ninst.or]                    -- collides? :: hash

/-! ### The collision-guard witness

The `supplySlot` clause of the guard above is the one branch of this contract
that no fixture can exercise.  Reaching it needs an allowance key
`keccak256(owner ‖ spender) = B256.max` — an expected-2²⁵⁶ preimage search, and
strictly harder than the ~2⁹⁶ address-shaped collision the WETH suite already
records as untestable (`scripts/fixtures/weth/README.md`, deviation claim 3).
Its evidence is therefore here, in Lean, rather than under
`scripts/fixtures/fmint/` (`FMINT_DEVIATIONS.md` row 18).

`isMax` is `[not, iszero]`, and the machine evaluates that pair as
`B256.eqCheck (~~~ w) 0` (`Jaune/Machine.lean`: `not` is `~~~ ·` and `iszero`
is `.eqCheck · 0`), so the clause is 1 exactly when `w` is all ones.  The two
statements below are the two halves of the claim, and the second is the one
that makes the clause worth its two bytes: `supplySlot` is *not* address-shaped,
so `checkAddress` — the clause fmint inherits from WETH — does not already catch
it.

Both are `example`s, and both are checked by `decide` rather than
`decide +kernel`: `B256`'s comparison instances are built by tactics and stall
in the kernel evaluator (`~/plans/kernel-decidable.md`). -/

/-- The new clause fires on the concrete colliding word. -/
example : B256.eqCheck (~~~ supplySlot) 0 = 1 := by decide

/-- …and the pre-existing clause does not, so the new one is load-bearing.
`checkAddress` masks with `(~~~ 0) <<< 160` and tests the result against zero;
`supplySlot` has all ninety-six of those bits set. -/
example :
    B256.eqCheck (B256.and supplySlot ((~~~ (0 : B256)) <<< (Nat.toB256 160).toNat)) 0
      = 0 := by
  decide

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

**The extended slot guard** is `checkSlotCollides` above; this is one of the
three allowance-writing paths that carry it (proposal D3).

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
  checkSlotCollides +++         -- collides? :: hash :: wad :: receiver
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

`flashLoan`'s fourth argument is the dynamic `bytes`, so its head word is an
offset rather than a value — the distinction the `dynBytes` constructor is
careful about.  `forwardArgTail` follows it, which is work `arg` deliberately
does not do; the Step-0 spike wrote that out here and it now lives in
`Blanc/CommonCore.lean`, being ABI-generic rather than fmint-specific.

The single `6` fixes both destinations: the length word lands at memory word 6
(`0xc0`) and the payload in the word after it (`0xe0`), because the ABI puts a
dynamic argument's payload immediately after its length. -/
def forwardCallbackData : Line := forwardArgTail 3 6

/-- `( dataLen -- argsSize )` — the `CALL`'s `argsSize`, `0xc4 + ceil32(len)`.

`ceil32` is the usual `(len + 31) & ~31`; `~31` is pushed as `PUSH1 31; NOT`,
two bytes rather than thirty-three, the same trick `pushAddressMask` uses. -/
def callbackArgsSize : Line :=
  pushB256 31 :: add ::               -- len + 31
  pushB256 31 :: not :: Ninst.and ::  -- ceil32(len)
  pushB256 0xc4 :: add :: []          -- 0xc4 + ceil32(len)

/-! ## `flashLoan` — the ERC-3156 entry point (proposal D4) -/

/-- `flashLoan(address receiver, address token, uint256 amount, bytes data)`.

Mint, call, check, repay, burn — proposal D4 in its revised order, with the
guards it names and no others.  Written before the ERC-20 surface because it is
where all the new machinery lands; the rest of the contract is pattern work.

Two idioms recur below and are worth stating once.

*Guards revert in the negative direction.*  `.rev <?> …` is the shape WETH uses:
the branch fires when the tested word is nonzero, so a guard computes the
*failure* condition and the success path continues in a straight line.  Where
that means testing an equality, the pair is `eq ::: iszero` rather than a single
`xor`, which would be one byte cheaper: `iszero (if a = b then 1 else 0)` is two
definitional steps for Arc B, whereas `a ^^^ b = 0 ↔ a = b` is a bitvector fact
somebody would have to prove.  One byte is not worth a lemma.

*The two paired writes of D5 are adjacent.*  The mint pair is complete before
the `CALL`; the burn pair lives in `burnAndReturn`.  Nothing between the two
`SSTORE`s of a pair transfers control out of this frame or halts successfully. -/
def flashLoan : Func :=
  -- (0) `token` must be this contract.  ERC-3156 mandates the revert; fmint
  -- reaches it through one explicit guard placed *before* the bound check, so
  -- the reason does not depend on `amount` as the reference's does
  -- (`FMINT_DEVIATIONS.md` row 5).
  arg 1 +++ address ::: eq ::: iszero :::
  .rev <?>                        -- [token ≠ self: revert]
  -- (1) the receiver word must be address-shaped.  CONSERVATION-CRITICAL, not
  -- hygiene: a dirty word would be the mint's `SSTORE` key verbatim, while
  -- `wbsum` sums address-shaped keys only and `CALL` truncates its target to
  -- 160 bits — supply would rise with the minted balance outside Σ, falsifying
  -- the invariant before the callback even runs (row 6).
  arg 0 +++ dup 0 ::: checkNonAddress +++ -- ¬va(receiver) :: receiver
  .rev <?>                        -- [receiver is not address-shaped: revert]
                                  -- receiver
  -- (2) `amount ≤ maxFlashLoan`, where `maxFlashLoan = 2^256 - 1 - supply`.
  -- This is also the whole overflow argument for the mint below: the check
  -- makes `supply + amount` non-overflowing by construction, and `not supply`
  -- computes the bound in one byte.
  arg 2 +++ dup 0 :::             -- amount :: amount :: receiver
  pushSupplySlot +++ sload ::: not ::: -- maxLoan :: amount :: amount :: receiver
  lt :::                          -- (maxLoan <? amount) :: amount :: receiver
  .rev <?>                        -- [amount above the bound: revert]
                                  -- amount :: receiver
  -- (3) mint: both `SSTORE`s complete here, before the `CALL` (D5).
  dup 1 ::: sload :::             -- rbal :: amount :: receiver
  dup 1 ::: add :::               -- (rbal + amount) :: amount :: receiver
  dup 2 ::: sstore :::            -- amount :: receiver
                                  -- [receiver balance minted]
  pushSupplySlot +++ sload :::    -- supply :: amount :: receiver
  dup 1 ::: add :::               -- (supply + amount) :: amount :: receiver
  pushSupplySlot +++ sstore :::   -- amount :: receiver
                                  -- [supply minted; pair complete]
  dup 0 ::: mstoreAt 0 +++        -- amount :: receiver || amount
  dup 1 :::                       -- receiver :: amount :: receiver || amount
  pushB256 0 :::                  -- 0 :: receiver :: amount :: receiver || amount
  pushB256 transferEvent :::      -- transferEventSig :: 0 :: receiver :: … || amount
  logWith 2 0 1 +++               -- 2 indexed topics : from = 0x0, to = receiver
                                  -- 1 unindexed data : minted amount
                                  -- [Transfer(0x0, receiver, amount) is logged]
                                  -- amount :: receiver
  -- (4) the callback.  Memory is laid out per the table above; the `amount` is
  -- duplicated because `storeCallbackHead` consumes one and the repayment
  -- needs the other.  The `CALL`'s seven operands are assembled deepest-first,
  -- which is why the two return-window zeros are pushed before the argument
  -- window is even measured.  All gas is forwarded (EIP-150's 63/64 rule then
  -- applies); the return window is empty because the answer is read with
  -- `retdatacopy` instead.
  dup 0 ::: storeCallbackHead +++ -- amount :: receiver || selector, head words
  pushList [0, 0] +++             -- 0 :: 0 :: amount :: receiver
                                  --   (retSize, then retOffset)
  forwardCallbackData +++         -- dataLen :: 0 :: 0 :: amount :: receiver
                                  --   || … ; length word and payload
  callbackArgsSize +++            -- argsSize :: 0 :: 0 :: amount :: receiver
  pushB256 callbackArgsOffset ::: -- argsOffset :: argsSize :: 0 :: 0 :: amount :: receiver
  pushB256 0 :::                  -- value = 0 :: argsOffset :: …
  dup 6 :::                       -- receiver :: 0 :: argsOffset :: argsSize :: 0 :: 0 :: amount :: receiver
  gas :::                         -- gas :: receiver :: …
  call :::                        -- success? :: amount :: receiver
  iszero :::
  .rev <?>                        -- [the callback failed: revert]
                                  -- amount :: receiver
  -- (5) the return value: at least a word of it, and that word the magic
  -- constant.  The length is branched on first because `retdatacopy` aborts
  -- the frame rather than failing a test when the range overruns (row 10).
  retdataShorterThan 32 +++       -- (retdatasize <? 32) :: amount :: receiver
  .rev <?>                        -- [returndata shorter than a word: revert]
                                  -- amount :: receiver
  checkRetdataHead erc3156Magic 0 +++ -- (head =? magic) :: amount :: receiver
  iszero :::
  .rev <?>                        -- [wrong magic word: revert]
                                  -- amount :: receiver
  -- (6) and (7): spend the allowance `receiver → self`, then burn.  Both arms
  -- of the allowance test converge on `burnAndReturn` in aux slot `burnSlot`,
  -- which performs the burn pair, logs the burn `Transfer`, and returns true.
  spendAllowanceThenBurn

/-! ## The ERC-3156 views -/

/-- `maxFlashLoan(address token)`.

`2^256 - 1 - supply` for `token = self`, and **0** for anything else — ERC-3156
states that as a MUST *not* to revert, so this is the one sibling of the triple
that answers rather than fails (`FMINT_DEVIATIONS.md` row 1). -/
def maxFlashLoan : Func :=
  arg 0 +++ address ::: eq :::         -- (token =? self)
  ( pushSupplySlot +++ sload ::: not ::: -- 2^256 - 1 - supply
    mstoreAt 0 +++
    returnMemoryRange 0 32 ) <?>
  ( pushB256 0 :::                     -- unsupported token: 0, not a revert
    mstoreAt 0 +++
    returnMemoryRange 0 32 )

/-- `flashFee(address token, uint256 amount)`.

0 for `token = self`; **reverts** otherwise, which ERC-3156 states as a MUST and
which is the opposite of `maxFlashLoan`'s rule for the same input
(`FMINT_DEVIATIONS.md` row 3).  `amount` is read and ignored: the fee is
identically zero, not a function of anything (proposal D2). -/
def flashFee : Func :=
  arg 0 +++ address ::: eq ::: iszero :::
  .rev <?>                        -- [token ≠ self: revert]
  pushB256 0 ::: mstoreAt 0 +++
  returnMemoryRange 0 32

/-! ## The ERC-20 surface

Four of these are WETH's bodies written out again in this namespace —
`decimals`, `balanceOf`, `allowance`, `transfer` — copied rather than imported,
for the reasons in the module header.  `name`, `symbol` and `totalSupply` differ
by content, `approve` and `transferFrom` by the extended slot guard, and
`totalSupply` differs by more than content: WETH reads its own ETH balance,
which fmint has no analogue for. -/

-- name() --

/-- `name()` — `"Flashmint"`.

Returned in the ABI's dynamic-string shape: offset word, length word, then the
content left-aligned in the third word.  Nine bytes, so the shift is
`(32 - 9) * 8 = 184`. -/
def name : Func :=
  pushB256 (Blanc.String.toBytes "Flashmint").toB256 :::
  pushB256 184 ::: shl ::: -- "Flashmint" ||
  pushList [9, 32] +++ -- 32 :: 9 :: "Flashmint" ||
  mstoreAt 0 +++ -- 9 :: "Flashmint" || 32
  mstoreAt 1 +++ -- "Flashmint" || 32 9
  mstoreAt 2 +++ -- || 32 9 "Flashmint"
  returnMemoryRange 0 96

-- symbol() --

/-- `symbol()` — `"FMINT"`.  Five bytes, so the shift is `(32 - 5) * 8 = 216`. -/
def symbol : Func :=
  pushB256 (Blanc.String.toBytes "FMINT").toB256 :::
  pushB256 216 ::: shl ::: -- "FMINT" ||
  pushList [5, 32] +++ -- 32 :: 5 :: "FMINT" ||
  mstoreAt 0 +++ -- 5 :: "FMINT" || 32
  mstoreAt 1 +++ -- "FMINT" || 32 5
  mstoreAt 2 +++ -- || 32 5 "FMINT"
  returnMemoryRange 0 96

-- decimals() --

/-- `decimals()` — 18, as WETH and as the OpenZeppelin default. -/
def decimals : Func :=
  pushB256 0x12 ::: -- 0x12 ||
  mstoreAt 0 +++ -- || 0x12
  returnMemoryRange 0 32

-- totalSupply() --

/-- `totalSupply()` — the supply slot.

Emphatically *not* WETH's `address; balance`: fmint's supply is a storage
quantity with no ETH backing it, which is the whole difference between a
conservation invariant and a solvency one.  `pushSupplySlot`, never
`pushB256 supplySlot`. -/
def totalSupply : Func :=
  pushSupplySlot +++ sload ::: -- supply ||
  mstoreAt 0 +++ -- || supply
  returnMemoryRange 0 32

-- balanceOf(address guy) --

/-- `balanceOf(address guy)`.  A balance lives at the raw address word, so this
is one `sload`.  Like WETH's, and unlike the mutators, it applies no address
check to the argument (`FMINT_DEVIATIONS.md` row 19). -/
def balanceOf : Func :=
  arg 0 +++ -- guy ||
  sload ::: -- guy_bal ||
  mstoreAt 0 +++ -- || guy_bal
  returnMemoryRange 0 32

-- allowance(address src, address dst) --

/-- `allowance(address src, address dst)`.  A view, so no slot guard: reading a
colliding key is harmless, and only the writers can create one
(`FMINT_DEVIATIONS.md` row 18). -/
def allowance : Func :=
  argCopy 0 0 2 +++ -- || src dst
  pushList [64, 0] +++ -- 0 :: 64 || src dst
  kec ::: -- hash ||
  sload ::: -- allowAmnt ||
  mstoreAt 0 +++ -- || allow_amnt
  returnMemoryRange 0 32

-- approve(address guy, uint wad) --

/-- `( -- collides? :: caller_guy_hash :: wad )`, assuming `args = [guy, wad]`.

WETH's `prepApprove` with `checkAddress` replaced by `checkSlotCollides`, which
is the only difference `approve` has from WETH's. -/
def prepApprove : Line :=
  caller :: mstoreAt 0 ++ -- || caller
  argCopy 1 0 1 ++ -- || caller :: guy
  arg 1 ++ pushList [64, 0] ++ -- 0 :: 64 :: wad || caller :: guy
  kec :: checkSlotCollides -- collides? :: caller_guy_hash :: wad ||

/-- assumes : `args = [guy, wad]` -/
def logApprove : Line :=
  argCopy 0 1 1 ++ -- || wad
  arg 0 ++ caller ::
  pushB256 approvalEvent :: -- approvalEventSig :: caller :: guy || wad
  logWith 2 0 1 -- 2 indexed topics : caller address, approvee address
                -- 1 unindexed data : approval value

/-- `approve(address guy, uint256 wad)`. -/
def approve : Func :=
  arg 0 +++ -- guy ||
  checkNonAddress +++ -- guy_invalid? ||
  .rev <?> -- [if guy is invalid, revert]
  prepApprove +++ -- collides? :: hash :: wad ||
  .rev <?> -- [ if the allowance slot would alias a balance slot or the
           --   supply slot, revert ]
           -- hash :: wad ||
  sstore :: -- ||
  logApprove +++
  returnTrue

-- transfer(address dst, uint wad) --

/-- assumes : `args = [dst, wad]` -/
def logTransfer : Line :=
  argCopy 0 1 1 ++ -- || wad
  arg 0 ++ caller ::
  pushB256 transferEvent :: -- transferEventSig :: src :: dst || wad
  logWith 2 0 1 -- 2 indexed topics : source address, destination address
                -- 1 unindexed data : transfer value

/-- `( wad dst -- )` -/
def incrWbal : Line :=
  dup 1 :: -- dst :: wad :: dst
  sload :: -- dst_bal :: wad :: dst
  add :: -- (dst_bal + wad) :: dst
  swap 0 :: -- dst :: (dst_bal + wad)
  sstore :: []

/-- assumes : `args = [dst, wad]`.  `( -- dst_invalid :: dst )` -/
def transferTestDst : Line :=
  arg 0 ++ dup 0 :: -- dst :: dst
  checkNonAddress -- dst_invalid :: dst

/-- assumes : `args = [_, wad]`.
`( -- caller_bal_<_wad? :: caller :: caller_bal - wad :: wad :: dst )` -/
def transferTestLt : Line :=
  arg 1 ++ -- wad :: dst
  caller :: -- caller :: wad :: dst
  dup 0 :: -- caller :: caller :: wad :: dst
  sload :: -- caller_bal :: caller :: wad :: dst
  swap 0 :: -- caller :: caller_bal :: wad :: dst
  dup 2 :: -- wad :: caller :: caller_bal :: wad :: dst
  dup 0 :: -- wad :: wad :: caller :: caller_bal :: wad :: dst
  dup 3 :: -- caller_bal :: wad :: wad :: caller :: caller_bal :: wad :: dst
  sub ::   -- caller_bal - wad :: wad :: caller :: caller_bal :: wad :: dst
  swap 2 :: -- caller_bal :: wad :: caller :: caller_bal - wad :: wad :: dst
  lt :: [] -- caller_bal_<_wad? :: caller :: caller_bal - wad :: wad :: dst

/-- `( caller :: caller_bal - wad :: wad :: dst -- * )`

Two balance writes with no supply write: a transfer moves value between two
address-shaped keys, so Σ is unchanged and D5's pairing obligation is
discharged by the second balance write rather than by a supply write. -/
def transferCore : Func :=
  sstore ::: -- wad :: dst [caller balance up to date]
  incrWbal +++ -- [destination balance up to date]
  logTransfer +++
  returnTrue

/-- `transfer(address dst, uint256 wad)`. -/
def transfer : Func :=
  transferTestDst +++ -- dst_invalid? :: dst
  .rev <?> -- [if dst is not a valid address, revert]
           -- dst
  transferTestLt +++ -- (caller_bal < wad) :: caller :: caller_bal - wad :: wad :: dst
  .rev <?> -- [if caller balance < transfer amount, revert]
        -- caller :: caller_bal - wad :: wad :: dst
  transferCore

-- transferFrom(address src, address dst, uint wad) --

/-- `( sbal :: wad :: wad :: src -- wad :: src )` -/
def transferFromUpdateSbal : Line :=
  sub :: -- (sbal - wad) :: wad :: src
  dup 2 :: -- src :: (sbal - wad) :: wad :: src
  sstore :: -- [source balance is up to date]
  []        -- wad :: src

/-- `( dst :: wad :: src -- wad :: src )` -/
def transferFromLog : Line :=
  dup 2 :: -- src :: dst :: wad :: src
  pushB256 transferEvent :: -- transferEventSig :: src :: dst :: wad :: src
  dup 3 :: mstoreAt 0 ++ -- transferEventSig :: src :: dst :: wad :: src || wad
  logWith 2 0 1 -- [Transfer(src,dst,wad) is logged]
                -- wad :: src

/-- `( wad src -- )` — the ERC-20 allowance spend.

Two things distinguish it from the repayment path's `spendAllowanceThenBurn`,
and they are the reason that one is separate code rather than a call to this:
the spender here is `caller`, and a caller spending its *own* balance skips the
allowance entirely.  That bypass is WETH9's, not OpenZeppelin's, and is
deliberately scoped to this function — `FMINT_DEVIATIONS.md` row 16 says so
outright, because ERC-3156 requires the repayment to take the allowance even
when the borrower named itself as receiver.

Infinite-allowance preservation is the WETH9/OpenZeppelin convention of row 15,
and is *not* "EIP-717"; no EIP mandates it. -/
def updateAllowance : Func :=
  prepend [caller, dup 2, eq] <| -- (src =? caller) :: wad :: src
  returnTrue <?> -- if caller is source, do not update allowance
                 -- wad :: src
  swap 0 :: mstoreAt 0 +++ -- wad || src
  caller ::: mstoreAt 1 +++ -- wad || src :: caller
  pushList [64, 0] +++ -- 0 :: 64 :: wad || src :: caller
  kec ::: -- hash :: wad
  checkSlotCollides +++ -- collides? :: hash :: wad
  .rev <?> -- [ if the allowance slot would alias a balance slot or the
           --   supply slot, revert ]
           -- hash :: wad
  swap 0 ::: -- wad :: hash
  dup 1 ::: sload ::: -- amnt :: wad :: hash
  dup 0 ::: isMax +++ -- (amnt =? max) :: amnt :: wad :: hash
  returnTrue <?> -- if the allowed amount is infinite, do not update it
                 -- amnt :: wad :: hash
  dup 1 ::: dup 1 ::: lt ::: -- amnt <? wad :: amnt :: wad :: hash
  .rev <?> -- if allowed amount < transfer amount, revert
           -- amnt :: wad :: hash
  sub ::: swap 0 ::: -- hash :: (amnt - wad)
  sstore ::: returnTrue -- [allowance amount is up to date]

/-- `transferFrom(address src, address dst, uint256 wad)`. -/
def transferFrom : Func :=
  arg 0 +++ dup 0 ::: checkNonAddress +++ -- ¬ va(src) :: src
  .rev <?> -- [if src is not a valid address, revert]
        -- src
  arg 2 +++ dup 0 ::: dup 2 ::: sload ::: -- sbal :: wad :: wad :: src
  dup 1 ::: dup 1 ::: lt ::: -- (sbal <? wad) :: sbal :: wad :: wad :: src
  .rev <?> -- if source balance < wad, then revert
        -- sbal :: wad :: wad :: src
  transferFromUpdateSbal +++ -- wad :: src
  arg 1 +++ dup 0 ::: checkNonAddress +++ -- ¬ va(dst) :: dst :: wad :: src
  .rev <?> -- [if dst is not a valid address, revert]
        -- dst :: wad :: src
  dup 0 ::: dup 2 ::: -- wad :: dst :: dst :: wad :: src
  incrWbal +++ -- [destination balance is up to date]
              -- dst :: wad :: src
  transferFromLog +++ -- wad :: src
  updateAllowance

/-! ## The program -/

/-- The twelve functions the dispatcher routes to, in ascending selector order.

Unlike `wethFuncs` this list is the whole contract: WETH keeps `deposit` out of
it because `deposit` *is* the fallback, whereas fmint's fallback reverts, so
every fmint behaviour is reached through a selector.

Arc B consumes this list — the open-contract theorem's per-function obligation
is stated over exactly these entries — so it is deliberately exposed as a
`List (B256 × Func)` in the `wethFuncs` mold rather than being folded into the
tree. -/
def fmintFuncs : List (B256 × Func) :=
  [ (selector "name" [], name),                                        -- 0x06fdde03
    (selector "approve" [.address, .uint256], approve),                -- 0x095ea7b3
    (selector "totalSupply" [], totalSupply),                          -- 0x18160ddd
    (selector "transferFrom" [.address, .address, .uint256],
      transferFrom),                                                   -- 0x23b872dd
    (selector "decimals" [], decimals),                                -- 0x313ce567
    (selector "flashLoan" [.address, .address, .uint256, .dynBytes],
      flashLoan),                                                      -- 0x5cffe9de
    (selector "maxFlashLoan" [.address], maxFlashLoan),                -- 0x613255ab
    (selector "balanceOf" [.address], balanceOf),                      -- 0x70a08231
    (selector "symbol" [], symbol),                                    -- 0x95d89b41
    (selector "transfer" [.address, .uint256], transfer),              -- 0xa9059cbb
    (selector "flashFee" [.address, .uint256], flashFee),              -- 0xd9d98ce4
    (selector "allowance" [.address, .address], allowance) ]           -- 0xdd62ed3e

/-- `dispatchWith`'s ordering precondition, checked rather than commented, as
`wethFuncs_sorted` is.  A misplaced entry would compile cleanly into a program
where that function is simply unreachable.

Its documented failure signature carries over: `decide` fails and then rendering
the goal has to unfold twelve `String.keccak` calls, so what you see is
`[Error pretty printing: maximum recursion depth has been reached]` rather than
anything legible.  If that appears, `fmintFuncs` is out of ascending selector
order and the trailing comment on each line is the expected value. -/
theorem fmintFuncs_sorted : DispatchTree.sorted fmintFuncs = true := by decide +kernel

def fmintTree : DispatchTree := .ofSorted fmintFuncs

/-- The aux table as frozen at the design freeze.  Append-only; see above. -/
def fmintAux : List Func := [Func.rev, burnAndReturn]

/-- The contract.  `Func.mainWith fallbackSlot` routes a dispatcher miss to aux
slot 1, which is `Func.rev`: an unrecognized selector — and a bare value
transfer — reverts. -/
def fmint : Prog := ⟨Func.mainWith fallbackSlot fmintTree, fmintAux⟩

end Fmint

end Blanc
