-- gen-fmint-borrowers.lean : the named generator for `scripts/fmint-borrowers.json`.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-fmint-borrowers.lean
--
-- Fixture Step 2 of `~/plans/fmint-code.md` deliverable 6: the borrower zoo,
-- "written in Blanc and compiled into fixture pre-state `code` fields"
-- (`~/plans/flashmint-proposal.md`, evidence plan). This script IS that Blanc
-- source -- a second, cheap exercise of the code-reuse question the proposal
-- names, using the exact `Func`/`Line`/`Prog` machinery `Blanc/Fmint.lean`
-- itself is written in. It is deliberately a standalone script under
-- `scripts/`, not a `Blanc/*.lean` module: Step 2's mandate is "fixture work
-- must not touch Lean outside scripts/", and nothing here is imported by
-- `Blanc.lean` or consumed by any proof.
--
-- Each borrower assumes its ENTIRE calldata is one ERC-3156
-- `onFlashLoan(address initiator, address token, uint256 amount, uint256 fee,
-- bytes data)` call -- exactly the shape `Blanc.Fmint.flashLoan` constructs
-- (`Blanc/Fmint.lean`, spike 2's layout table) -- rather than dispatching on
-- a selector, in the same idiom `gen-weth-fixtures.py`'s hand-authored
-- `attacker_bytecode`/`prober_bytecode` use for straight-line test props: a
-- borrower has exactly one caller (fmint, mid-`flashLoan`) and exactly one
-- job.
--
-- Every borrower that must call back into the token (to `approve`,
-- `transfer`, `balanceOf`, `totalSupply`, or a nested `flashLoan`) targets
-- `caller()`: fmint always calls a borrower directly, so the borrower's
-- caller inside `onFlashLoan` IS the token's address -- there is no separate
-- "token" constant to thread through.
--
-- Regenerating must leave the working tree clean
-- (`git diff --exit-code scripts/fmint-borrowers.json`), exactly like
-- `gen-fmint-code.lean` / `Blanc/FmintCode.lean` and
-- `gen-weth-selectors.lean` / `scripts/weth-selectors.json`.

import Blanc.Fmint

namespace Blanc

namespace FmintBorrowers

open Jaune

open Jaune.Ninst Ninst

/-! ## Shared machinery

Every borrower here either does nothing (`revertingBorrower`), or opens with
`recordObservations` -- the anti-vacuity requirement
(`~/plans/flashmint-proposal.md`, evidence plan): "each borrower records into
its own storage, *during* the callback, the observed `msg.sender`, all five
`onFlashLoan` arguments (`data` by its keccak hash), and the token's reported
`balanceOf(self)` and `totalSupply()` mid-loan". -/

/-- Storage slots a borrower's observations land in. Plain small integers,
distinct from every slot the token itself could ever address (an fmint
balance/allowance/supply slot is either a raw address word, a keccak digest,
or `B256.max` -- none is a small integer). -/
def OBS_SENDER : B256 := 0      -- `caller()` during the callback
def OBS_INITIATOR : B256 := 1   -- onFlashLoan arg 0
def OBS_TOKEN : B256 := 2       -- onFlashLoan arg 1
def OBS_AMOUNT : B256 := 3      -- onFlashLoan arg 2
def OBS_FEE : B256 := 4         -- onFlashLoan arg 3
def OBS_DATAHASH : B256 := 5    -- keccak256(onFlashLoan arg 4, the `data` tail)
def OBS_BAL_SELF : B256 := 6    -- balanceOf(address(this)), read mid-callback
def OBS_SUPPLY : B256 := 7      -- totalSupply(), read mid-callback

/-- The word index a returned value from an outgoing `CALL` lands at (byte
`0x200`), chosen clear of every calldata-building region below (words 0-5). -/
def RET_WORD : B256 := 16

/-- The `CALL`'s `argsOffset`, four bytes short of memory word 1 -- the same
"selector, right-aligned in word 0" trick `Blanc.Fmint.callbackArgsOffset`
uses, so calldata is built with plain word-aligned `mstoreAt`s. -/
def CALL_ARGS_OFFSET : B256 := 0x1c

/-- `( V -- )`, storing `V` -- computed by `push`, e.g. `arg 2` or `[caller]`
-- at storage slot `slot`. `SSTORE` pops `(key, value)` with `key` on top, so
`push` must land first. -/
def sstoreSlot (slot : B256) (push : Line) : Line :=
  push ++ [pushB256 slot, sstore]

/-- Store a fixed selector plus `n` following ABI head words, already pushed
by `pushes`, at memory words `0..n` (word 0 the selector, right-aligned).
`pushes` is a list of `n` `Line`s, each leaving exactly one word on top. -/
def storeWord (idx : B256) (push : Line) : Line :=
  push ++ mstoreAt idx

/-- Call `caller()` -- the token, since fmint always calls a borrower directly
-- with the selector plus `n` head words already stored at memory
`[0, 4 + 32n)`, landing one 32-byte return word at `RET_WORD`.
`( -- success )`. -/
def callBack (n : B256) : Line :=
  pushList [32, RET_WORD * 32] ++    -- retSize=32 :: retOffset=0x200
  [pushB256 (4 + 32 * n)] ++         -- argsSize
  [pushB256 CALL_ARGS_OFFSET] ++     -- argsOffset
  [pushB256 0] ++                    -- value = 0
  [caller] ++                        -- address = caller() = fmint
  [Ninst.gas] ++
  [Ninst.call]

def selApprove : B256 := selector "approve" [.address, .uint256]
def selTransfer : B256 := selector "transfer" [.address, .uint256]
def selBalanceOf : B256 := selector "balanceOf" [.address]
def selTotalSupply : B256 := selector "totalSupply" []
def selFlashLoan : B256 :=
  selector "flashLoan" [.address, .address, .uint256, .dynBytes]

/-- `approve(spender, wad)` calldata at memory `[0, 68)`. `spender`/`wad` are
`Line`s so a caller value (`[caller]`) or an arithmetic one (`arg 2 ++ arg 3
++ [add]`) works interchangeably with a literal. -/
def buildApprove (spender wad : Line) : Line :=
  storeWord 0 [pushB256 selApprove] ++
  storeWord 1 spender ++
  storeWord 2 wad

/-- `transfer(dst, wad)` calldata at memory `[0, 68)`. -/
def buildTransfer (dst wad : Line) : Line :=
  storeWord 0 [pushB256 selTransfer] ++
  storeWord 1 dst ++
  storeWord 2 wad

/-- `balanceOf(guy)` calldata at memory `[0, 36)`. -/
def buildBalanceOf (guy : Line) : Line :=
  storeWord 0 [pushB256 selBalanceOf] ++
  storeWord 1 guy

/-- `totalSupply()` calldata at memory `[0, 4)`. -/
def buildTotalSupply : Line :=
  storeWord 0 [pushB256 selTotalSupply]

/-- `flashLoan(receiver, token, amount, data = "")` calldata at memory
`[0, 196)`: the four head words then an empty tail (offset `0x80`, the fifth
word after the selector; length `0`; no payload). Used for the reentrant
borrower's nested loan -- an empty `data` is enough to demonstrate depth-2
reentrancy without also re-deriving the dynamic-tail machinery. -/
def buildFlashLoanEmpty (receiver token amount : Line) : Line :=
  storeWord 0 [pushB256 selFlashLoan] ++
  storeWord 1 receiver ++
  storeWord 2 token ++
  storeWord 3 amount ++
  storeWord 4 [pushB256 0x80] ++
  storeWord 5 [pushB256 0]

/-- `keccak256(data)`, `data` being onFlashLoan's fifth argument (index 4):
follow `forwardArgTail`'s length/payload landing at words 20/21 -- clear of
the calldata-building region above -- then hash exactly `len` bytes starting
at the payload. `( -- hash )`. -/
def hashData : Line :=
  forwardArgTail 4 20 ++             -- len, payload landed at word 21
  [pushB256 (21 * 32), kec]          -- hash

/-- The shared observation prologue every non-reverting borrower opens with.
Six calldata-derived slots, then two calls back into the token to capture
`balanceOf(self)`/`totalSupply()` **mid-callback** -- the only way, under fee
≡ 0, to observe that the mint happened *before* the callback: a successful
loan's end state equals its pre-state, so only a mid-callback read is
evidence at all (evidence plan, anti-vacuity requirements). Both calls'
success flags are dropped: they call this borrower's own well-formed
requests against the token that just invoked it, so a failure there would be
an fmint defect visible in the recorded values being wrong, not in a
silently-swallowed flag. -/
def recordObservations : Line :=
  sstoreSlot OBS_SENDER [caller] ++
  sstoreSlot OBS_INITIATOR (arg 0) ++
  sstoreSlot OBS_TOKEN (arg 1) ++
  sstoreSlot OBS_AMOUNT (arg 2) ++
  sstoreSlot OBS_FEE (arg 3) ++
  sstoreSlot OBS_DATAHASH hashData ++
  ( buildBalanceOf [address] ++ callBack 1 ++ [pop] ++
    sstoreSlot OBS_BAL_SELF [pushB256 (RET_WORD * 32), mload] ) ++
  ( buildTotalSupply ++ callBack 0 ++ [pop] ++
    sstoreSlot OBS_SUPPLY [pushB256 (RET_WORD * 32), mload] )

/-- `amount + fee` from this invocation's own calldata -- the exact wad
`Blanc.Fmint.spendAllowanceThenBurn` will ask for. -/
def owedWad : Line := arg 2 ++ arg 3 ++ [add]

/-- Return `Fmint.erc3156Magic` in a `size`-byte memory range starting at
word 0 (`size = 32` for a bare one-word return, `size = 64` for the overlong
case). Memory past word 0 is whatever the prior calls left there -- garbage,
not zero, which is the point: the overlong case's tail is deliberately
unconstrained, since ERC-3156 only pins the head word. -/
def returnMagic (size : B256) : Func :=
  pushB256 Fmint.erc3156Magic ::: mstoreAt 0 +++
  returnMemoryRange 0 size

/-! ## The zoo -/

/-- **1. Compliant** -- records its observations, approves the token for
exactly `amount + fee` (benign reentrancy on the success path, deliberately:
proposal evidence plan), then returns the magic word in exactly one word.
The success path every other member is a variation or negation of. -/
def compliantBorrower : Func :=
  recordObservations +++
  (buildApprove [caller] owedWad ++ callBack 2 ++ [pop]) +++
  returnMagic 32

/-- **1b. Compliant, overlong return.** Identical, but returns 64 bytes
instead of 32. ERC-3156 pins only the head word (proposal D4 step 5,
`Blanc.Fmint.checkRetdataHead`), so a correct head with a longer payload must
still be accepted -- the "overlong with a correct head" case the evidence
plan's returndata spectrum names. -/
def compliantOverlongBorrower : Func :=
  recordObservations +++
  (buildApprove [caller] owedWad ++ callBack 2 ++ [pop]) +++
  returnMagic 64

/-- **2. Wrong magic.** Records its observations (the callback still ran and
the mint still happened -- the point of the case is that the RETURN is
wrong, not that nothing happened), then returns a word that is provably not
the magic (`erc3156Magic + 1`), and does not approve -- repayment is never
reached. -/
def wrongMagicBorrower : Func :=
  recordObservations +++
  pushB256 (Fmint.erc3156Magic + 1) ::: mstoreAt 0 +++
  returnMemoryRange 0 32

/-- **3. Reverting.** `Func.rev` alone: the callback `CALL` fails outright,
before this borrower's code does anything at all -- a clean instance of
`Blanc.Fmint.flashLoan`'s `iszero ::: .rev <?>` guard on the callback's own
success flag. No `Prog` wrapper needed at the call site since a bare `Func`
compiles standalone; see `revertingBorrowerProg` below. -/
def revertingBorrower : Func := Func.rev

-- 4. (EOA receiver) -- no Blanc program: an externally-owned account has
-- no code at all, so `CALL`ing it "succeeds" with zero return data, which
-- fails `Blanc.Fmint.flashLoan`'s `retdataShorterThan 32` guard. The zoo has
-- no entry for this member; the fixture generator gives the receiver
-- address empty `code`.

/-- **5. Passive (no approval).** Records its observations and returns the
correct magic, but never calls `approve` -- repayment then depends entirely
on whatever allowance the fixture's PRE-STATE set at
`keccak256(receiver ‖ token)`. This one `Func` covers proposal zoo member 5
("no-approval borrower", pre-state allowance left at its default zero) *and*
the evidence plan's allowance spectrum (exact / residual / insufficient /
infinite), which the fixture generator drives entirely through pre-state --
no second borrower is needed because the allowance slot is ordinary storage
the generator can set directly, exactly as the WETH suite pre-sets
balances. -/
def passiveBorrower : Func :=
  recordObservations +++
  returnMagic 32

/-- **6. Transfer-then-default.** Records its observations, then -- with a
*sufficient* pre-set allowance, so the allowance check is not what fails --
transfers its entire freshly-minted balance away to `driftAddr` before
returning the magic. `burnAndReturn`'s balance check (`rbal <? wad`) then
fails: the receiver has nothing left to burn, and the whole `flashLoan`
frame reverts, taking the transfer back with it (evidence plan zoo member
7). -/
def driftAddr : B256 := 0xd41f7

def transferAwayBorrower : Func :=
  recordObservations +++
  (buildTransfer [pushB256 driftAddr] (arg 2) ++ callBack 2 ++ [pop]) +++
  returnMagic 32

/-- **7. Reentrant, depth 2.** A storage flag (`DEPTH_SLOT`) distinguishes the
outer invocation from the one nested flash loan it triggers, since both run
the same code at the same address. On the OUTER invocation (`DEPTH_SLOT` = 0)
it: marks the flag, issues a nested `flashLoan(receiver = self, token =
caller(), amount = 1, data = "")` and requires it to succeed, then approves
and returns the magic for the OUTER amount -- exactly the compliant path.
On the INNER invocation (`DEPTH_SLOT` ≠ 0, reached only via that nested
call) it skips recursion and goes straight to the compliant path for the
INNER amount. Both mints (outer, then inner) are complete -- D5's paired
writes -- before the inner callback ever runs, and `OBS_SUPPLY`/
`OBS_BAL_SELF` are captured mid-INNER-callback, so they read a supply/balance
that already includes BOTH mints: the durable witness that flashLoan mints
before it calls out, twice over. -/
def DEPTH_SLOT : B256 := 100

def reentrantBorrower : Func :=
  recordObservations +++
  pushB256 DEPTH_SLOT ::: sload :::
  ( -- INNER (depth ≠ 0): no further recursion.
    (buildApprove [caller] owedWad ++ callBack 2 ++ [pop]) +++
    returnMagic 32
  ) <?>
  ( -- OUTER (depth = 0): mark, recurse once with a fixed small inner amount.
    pushB256 1 ::: pushB256 DEPTH_SLOT ::: sstore :::
    (buildFlashLoanEmpty [address] [caller] [pushB256 1] ++ callBack 5) +++
    iszero :::
    .rev <?>                          -- [the nested flashLoan must succeed]
    (buildApprove [caller] owedWad ++ callBack 2 ++ [pop]) +++
    returnMagic 32
  )

def compliantBorrowerProg : Prog := ⟨compliantBorrower, []⟩
def compliantOverlongBorrowerProg : Prog := ⟨compliantOverlongBorrower, []⟩
def wrongMagicBorrowerProg : Prog := ⟨wrongMagicBorrower, []⟩
def revertingBorrowerProg : Prog := ⟨revertingBorrower, []⟩
def passiveBorrowerProg : Prog := ⟨passiveBorrower, []⟩
def transferAwayBorrowerProg : Prog := ⟨transferAwayBorrower, []⟩
def reentrantBorrowerProg : Prog := ⟨reentrantBorrower, []⟩

/-- Name, program -- the SOLE source `scripts/gen-fmint-fixtures.py` uses for
"what are the borrower zoo's compiled bytes" (the `weth-selectors.json`
provenance rule, extended): no borrower's bytecode is retyped or hand-copied
anywhere else. -/
def zoo : List (String × Prog) :=
  [ ("compliant", compliantBorrowerProg),
    ("compliantOverlong", compliantOverlongBorrowerProg),
    ("wrongMagic", wrongMagicBorrowerProg),
    ("reverting", revertingBorrowerProg),
    ("passive", passiveBorrowerProg),
    ("transferAway", transferAwayBorrowerProg),
    ("reentrant", reentrantBorrowerProg) ]

end FmintBorrowers

open Jaune FmintBorrowers

-- `Bytes.toHex` (no `0x` prefix) already does exactly this -- never
-- reimplemented here.
private def hexOf (bs : Bytes) : String := "0x" ++ Bytes.toHex bs

private def outPath : System.FilePath := "scripts" / "fmint-borrowers.json"

#eval show IO Unit from do
  let mut rows : List String := []
  for (name, prog) in zoo do
    match Prog.compile prog with
    | none =>
        throw (IO.userError s!"Prog.compile for borrower {name} = none -- refusing to generate")
    | some bs =>
        rows := rows ++ [s!"  \"{name}\": \"{hexOf bs}\""]
  let body := String.intercalate ",\n" rows
  IO.FS.writeFile outPath ("{\n" ++ body ++ "\n}\n")
  IO.println s!"wrote {outPath} ({zoo.length} borrowers)"

end Blanc
