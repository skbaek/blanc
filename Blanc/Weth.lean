-- Weth.lean : proof-of-concept implementation of the Wrapped Ether (WETH) contract

import Blanc.CommonProofs

namespace Blanc

open Jaune


open Jaune.Ninst Ninst

-- events --

-- The two events WETH emits that are its own, each named once. A topic0 word
-- is the keccak of the event's ABI signature string — the same `signatureHash`
-- a function selector is built from, without the shift that narrows one to four
-- bytes. Spelling these as signature strings inlined at the log sites is how
-- the same event ends up with two spellings and, one typo later, two topics.
--
-- The other two WETH emits, `Approval` and `Transfer`, are ERC-20's rather than
-- WETH's and live in `Blanc/CommonCore.lean` beside the fragments that log
-- them.

def depositEvent : B256 := signatureHash "Deposit" [.address, .uint256]
def withdrawalEvent : B256 := signatureHash "Withdrawal" [.address, .uint256]

-- deposit() --

def logDeposit : Func :=
  callvalue ::: mstoreAt 0 +++ caller ::: -- caller || wad
  pushB256 depositEvent ::: -- depositEventSig :: caller || wad
  logWith 1 0 1 +++ -- 1 indexed topic : caller address
                    -- 1 unindexed data : deposit value
  Func.stop

def deposit : Func :=
  caller ::: sload ::: -- caller_bal
  callvalue ::: add ::: -- (call_val + caller_bal)
  caller ::: -- caller :: (call_val + caller_bal)
  sstore ::: -- caller WETH balance is now up to date
  logDeposit



-- withdraw(uint wad) --

-- assumes : args := [wad]
def logWithdraw : Func :=
  caller :::
  pushB256 withdrawalEvent ::: -- withdrawEventSig :: caller
  argCopy 0 0 1 +++ -- withdrawEventSig :: caller || wad
  logWith 1 0 1 +++ -- 1 indexed topic : caller address
                    -- 1 unindexed data : withdraw amount
  Func.stop

-- ( wad -- )
def sendToCaller : Line :=
  pushList [0, 0, 0, 0] ++ -- 0 :: 0 :: 0 :: 0 :: wad
  swap 3 :: caller :: -- caller :: wad :: 0 :: 0 :: 0 :: 0
  pushB256 0 :: -- 0 :: caller :: wad :: 0 :: 0 :: 0 :: 0
  call :: -- 'wad' amount of ethers now sent to 'caller'
  []

-- assumes : args := [wad]
def withdrawLoadCheck : Line :=
  arg 0 ++ dup 0 :: -- wad :: wad
  caller :: sload :: -- caller_bal :: wad :: wad
  dup 1 :: dup 1 :: -- caller_bal :: wad :: caller_bal :: wad :: wad
  lt :: -- (caller_bal < wad) :: caller_bal :: wad :: wad
  []

-- assumes : args := [wad]
def withdraw : Func :=
  withdrawLoadCheck +++ -- (caller_bal < wad) :: caller_bal :: wad :: wad
  .revert <?> -- [if caller balance < withdraw amount, revert]
           -- caller_bal :: wad :: wad
  sub ::: caller ::: -- caller :: (caller_bal - wad) :: wad
  sstore ::: -- wad
             -- 'wad' amount of eth subtracted from caller balance
  sendToCaller +++ -- success?
  logWithdraw <?> .revert -- you revert if flag from sendToCaller is 0, because 0 after `call` opcode means failure.



-- name() --

def name : Func :=
  pushB256 (Blanc.String.toBytes "Wrapped Ether").toB256 :::
  pushB256 152 ::: shl ::: -- "Wrapped Ether" ||
  pushList [13, 32] +++ -- 32 :: 13 :: "Wrapped Ether" ||
  mstoreAt 0 +++ -- 13 :: "Wrapped Ether" || 32
  mstoreAt 1 +++ -- "Wrapped Ether" || 32 13
  mstoreAt 2 +++ -- || 32 13 "Wrapped Ether"
  returnMemoryRange 0 96



-- symbol() --

def symbol : Func :=
  -- pushList [wethStringShift] +++ -- wethStringShift
  pushB256 (Blanc.String.toBytes "WETH").toB256 :::
  pushB256 224 ::: shl ::: -- "WETH""
  pushList [4, 32] +++ -- 32 :: 4 :: "WETH""
  mstoreAt 0 +++ -- 4 :: "WETH"" || 32
  mstoreAt 1 +++ -- "WETH" || 32 4
  mstoreAt 2 +++ -- || 32 4 "WETH""
  returnMemoryRange 0 96



-- totalSuppply() --

def totalSupply : Func :=
  address ::: balance ::: -- total_bal ||
  mstoreAt 0 +++ -- || total_bal
  returnMemoryRange 0 32



-- approve(address guy, uint wad) --

-- assumes : args = [guy, wad]
-- ( -- caller_guy_hash_valid? :: caller_guy_hash :: wad )
def prepApprove : Line :=
  caller :: mstoreAt 0 ++ -- || caller
  argCopy 1 0 1 ++ -- || caller :: guy
  arg 1 ++ pushList [64, 0] ++ -- 0 :: 64 :: wad || caller :: guy
  keccak256 :: dup 0 :: -- caller_guy_hash :: caller_guy_hash :: wad ||
  checkAddress  -- caller_guy_hash_valid? :: caller_guy_hash :: wad ||

-- arguments = [guy, wad]
def approve : Func :=
  arg 0 +++ -- guy ||
  checkNonAddress +++ -- guy_invalid? ||
  .revert <?> -- [if guy is invalid, revert]
  prepApprove +++ -- hash_valid? :: hash :: wad ||
  .revert <?> -- [ if storage location of approval amount
           --   is a valid address that may potentially
           --   collide with balance storage, revert ]
           -- hash :: wad ||
  sstore :: -- ||
  logApprove +++
  returnTrue



-- transferFrom(address src, address dst, uint wad) --

-- `transfer` itself, its four fragments, `transferFromUpdateSbal` and
-- `transferFromLog` are ERC-20's rather than WETH's and live in
-- `Blanc/CommonCore.lean`. What remains here is the pair that forks on fmint's
-- extended allowance-slot guard.

-- (wad src -- )
def updateAllowance : Func :=
  prepend [caller, dup 2, eq] <| -- (src =? caller) :: wad :: src
  returnTrue <?> -- if caller is source, do not update allowance
                 -- wad :: src
  swap 0 :: mstoreAt 0 +++ -- wad || src
  caller ::: mstoreAt 1 +++ -- wad || src :: caller
  pushList [64, 0] +++ -- 0 :: 64 :: wad || src :: caller
  keccak256 ::: -- hash :: wad
  swap 0 ::: -- wad :: hash
  dup 1 :: checkAddress +++ -- va(hash) :: wad :: hash
  .revert <?> -- if hash is a valid address, revert to prevent collision
           -- wad :: hash
  dup 1 ::: sload ::: -- amnt :: wad :: hash
  dup 0 ::: isMax +++ -- (amnt =? max) :: amnt :: wad :: hash
  returnTrue <?> -- if allowed amount is infinite, do not update allowance
                 --   (WETH9 convention: a max allowance is never decremented;
                 --    no EIP mandates it)
                 -- amnt :: wad :: hash
  dup 1 ::: dup 1 ::: lt ::: -- amnt <? wad :: amnt :: wad :: hash
  .revert <?> -- if allowed amount < transfer amount, revert
           -- amnt :: wad :: hash
  sub ::: swap 0 ::: -- hash :: (amnt - wad)
  sstore ::: returnTrue -- [allowance amount is up to date]

-- assumes : args = [src, dst, wad]
def transferFrom : Func :=
  arg 0 +++ dup 0 ::: checkNonAddress +++ -- ¬ va(src) :: src
  .revert <?> -- [if src is not a valid address, revert]
        -- src
  arg 2 +++ dup 0 ::: dup 2 ::: sload ::: -- sbal :: wad :: wad :: src
  dup 1 ::: dup 1 ::: lt ::: -- (sbal <? wad) :: sbal :: wad :: wad :: src
  .revert <?> -- if source balance < wad, then revert
        -- sbal :: wad :: wad :: src
  transferFromUpdateSbal +++ -- wad :: src
  arg 1 +++ dup 0 ::: checkNonAddress +++ -- ¬ va(dst) :: dst :: wad :: src
  .revert <?> -- [if dst is not a valid address, revert]
        -- dst :: wad :: src
  dup 0 ::: dup 2 ::: -- wad :: dst :: dst :: wad :: src
  incrWbal +++ -- [destination balance is up to date]
              -- dst :: wad :: src
  transferFromLog +++ -- wad :: src
  updateAllowance



-- main --

-- The ten functions the dispatcher routes to, in ascending selector order.
-- `deposit` is absent on purpose: it is the fallback, reached through
-- `Func.mainWith 1` below rather than through a selector.
--
-- Every entry is wrapped in the shared `nonpayable` guard
-- (`Blanc/CommonCore.lean`): deployed WETH9's recognized entry points all
-- reject nonzero call value with an empty revert, and the payable surface is
-- exactly the fallback/deposit path. The wrapping happens here, at the
-- dispatch entries, and never inside the shared `CommonCore` bodies — that
-- placement is what keeps fmint's compiled artifact unchanged.
def wethFuncs : List (B256 × Func) :=
  [ (selector "name" [], nonpayable name),                             -- 0x06fdde03
    (selector "approve" [.address, .uint256], nonpayable approve),     -- 0x095ea7b3
    (selector "totalSupply" [], nonpayable totalSupply),               -- 0x18160ddd
    (selector "transferFrom" [.address, .address, .uint256],
      nonpayable transferFrom),                                        -- 0x23b872dd
    (selector "withdraw" [.uint256], nonpayable withdraw),             -- 0x2e1a7d4d
    (selector "decimals" [], nonpayable decimals),                     -- 0x313ce567
    (selector "balanceOf" [.address], nonpayable balanceOf),           -- 0x70a08231
    (selector "symbol" [], nonpayable symbol),                         -- 0x95d89b41
    (selector "transfer" [.address, .uint256], nonpayable transfer),   -- 0xa9059cbb
    (selector "allowance" [.address, .address], nonpayable allowance) ] -- 0xdd62ed3e

-- `dispatchWith`'s ordering precondition, checked rather than commented. If a
-- maintainer inserts an eleventh function in the wrong place, this fails to
-- elaborate; before, the contract compiled cleanly and the misplaced function
-- was simply unreachable.
--
-- A failure here reports as `[Error pretty printing: maximum recursion depth
-- has been reached]` rather than as anything legible: `decide` fails, and then
-- rendering the goal has to unfold ten `String.keccak` calls. Confirmed by
-- swapping two adjacent entries above, which does fail the build. If you see
-- that message, `wethFuncs` is out of ascending selector order — the trailing
-- comment on each line is the expected value.
theorem wethFuncs_sorted : DispatchTree.sorted wethFuncs = true := by decide +kernel

-- The fork shape is now derived from the list rather than written out.
def wethTree : DispatchTree := .ofSorted wethFuncs

def weth : Prog := ⟨Func.mainWith 1 wethTree, [deposit]⟩

end Blanc
