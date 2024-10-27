-- Weth.lean : a proof-of-concept port of the Wrapped Ether (WETH) contract

import Blanc.Common



-- function signatures --

-- First 4 bytes of Keccak hash of "name()", pushed to right
def nameSig : Word :=
  String.toWord "0000000000000000000000000000000000000000000000000000000006FDDE03"

-- First 4 bytes of Keccak hash of "approve(address,uint256)", pushed to right
def approveSig : Word :=
  String.toWord "00000000000000000000000000000000000000000000000000000000095EA7B3"

-- First 4 bytes of Keccak hash of "totalSupply()", pushed to right
def totalSupplySig : Word :=
  String.toWord "0000000000000000000000000000000000000000000000000000000018160DDD"

-- First 4 bytes of Keccak hash of "transferFrom(address,address,uint256)", pushed to right
def transferFromSig : Word :=
  String.toWord "0000000000000000000000000000000000000000000000000000000023B872DD"

-- First 4 bytes of Keccak hash of "withdraw(256)", pushed to right
def withdrawSig : Word :=
  String.toWord "000000000000000000000000000000000000000000000000000000002E1A7D4D"

-- First 4 bytes of Keccak hash of "decimals()", pushed to right
def decimalsSig : Word :=
  String.toWord "00000000000000000000000000000000000000000000000000000000313CE567"

-- First 4 bytes of Keccak hash of "balanceOf(address)", pushed to right
def balanceOfSig : Word :=
  String.toWord "0000000000000000000000000000000000000000000000000000000070A08231"

-- First 4 bytes of Keccak hash of "symbol()", pushed to right
def symbolSig : Word :=
  String.toWord "0000000000000000000000000000000000000000000000000000000095D89B41"

-- First 4 bytes of Keccak hash of "transfer(address,uint256)", pushed to right
def transferSig : Word :=
  String.toWord "00000000000000000000000000000000000000000000000000000000A9059CBB"

-- First 4 bytes of Keccak hash of "deposit()", pushed to right
def depositSig : Word :=
  String.toWord "00000000000000000000000000000000000000000000000000000000D0E30DB0"

-- First 4 bytes of Keccak hash of "allowance(address,address)", pushed to right
def allowanceSig : Word :=
  String.toWord "00000000000000000000000000000000000000000000000000000000DD62ED3E"



-- event signatures --

-- Keccak hash of "Deposit(address,uint256)"
def depositEsig : Word :=
  String.toWord "e1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c"

-- Keccak hash of "Withdraw(address,uint256)"
def withdrawEsig : Word :=
  String.toWord "884edad9ce6fa2440d8a54cc123490eb96d2768479d49ff9c7366125a9424364"

-- Keccak hash of "Approval(address,address,uint256)"
def approvalEsig : Word :=
  String.toWord "8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925"

-- Keccak hash of "Transfer(address,address,uint256)"
def transferEsig : Word :=
  String.toWord "ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef"

-- Encoding of string "Wrapped Ether"
def wrappedEtherStringShift : Word :=
  String.toWord "0000000000000000000000000000000000000057726170706564204574686572"

-- Encoding of string "WETH"
def wethStringShift : Word :=
  String.toWord "0000000000000000000000000000000000000000000000000000000057455448"



open Inst

-- deposit() --

def logDeposit : Func :=
  callvalue ::: mstoreAt 0 +++ -- || wad
  caller ::: pushWord depositEsig ::: -- depositEsig :: caller || wad
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
  caller ::: pushWord withdrawEsig ::: -- withdrawEsig :: caller
  argCopy 0 0 1 +++ -- withdrawEsig :: caller || wad
  logWith 1 0 1 +++ -- 1 indexed topic : caller address
                    -- 1 unindexed data : withdraw amount
  Func.stop

-- ( wad -- )
def sendToCaller : Line :=
  pushList [0, 0, 0, 0] ++ -- 0 :: 0 :: 0 :: 0 :: wad
  swap 3 :: caller :: -- caller :: wad :: 0 :: 0 :: 0 :: 0
  push [Ox x5 x2, Ox x0 x8] (by {simp [List.length]}) :: -- 21000 :: caller :: wad :: 0 :: 0 :: 0 :: 0
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
  .rev <?> -- [if caller balance < withdraw amount, revert]
           -- caller_bal :: wad :: wad
  sub ::: caller ::: -- caller :: (caller_bal - wad) :: wad
  sstore ::: -- wad
             -- 'wad' amount of eth subtracted from caller balance
  sendToCaller +++
  logWithdraw



-- decimals() --

def decimals : Func :=
  pushWord 0x12 ::: -- 0x12 ||
  mstoreAt 0 +++ -- || 0x12
  returnMemoryRange 0 32



-- name() --

def name : Func :=
  pushWord wrappedEtherStringShift ::: -- wrappedEtherStringShift ||
  pushWord 152 ::: shl ::: -- "Wrapped Ether" ||
  pushList [13, 32] +++ -- 32 :: 13 :: "Wrapped Ether" ||
  mstoreAt 0 +++ -- 13 :: "Wrapped Ether" || 32
  mstoreAt 1 +++ -- "Wrapped Ether" || 32 13
  mstoreAt 2 +++ -- || 32 3 "Wrapped Ether"
  returnMemoryRange 0 96



-- symbol() --

def symbol : Func :=
  pushList [wethStringShift] +++ -- wethStringShift
  pushWord 224 ::: shl ::: -- "WETH""
  pushList [4, 32] +++ -- 32 :: 4 :: "WETH""
  mstoreAt 0 +++ -- 4 :: "WETH"" || 32
  mstoreAt 1 +++ -- "WETH" || 32 4
  mstoreAt 2 +++ -- || 32 4 "WETH""
  returnMemoryRange 0 96



-- balanceOf(address guy) --

def balanceOf : Func :=
  arg 0 +++ -- guy ||
  sload ::: -- guy_bal ||
  mstoreAt 0 +++ -- || guy_bal
  returnMemoryRange 0 32



-- allowance(address src, address dst) --

def allowance : Func :=
  argCopy 0 0 2 +++ -- || src dst
  pushList [64, 0] +++ -- 0 :: 64 || src dst
  kec ::: -- hash ||
  sload ::: -- allowAmnt ||
  mstoreAt 0 +++ -- || allow_amnt
  returnMemoryRange 0 32



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
  kec :: dup 0 :: -- caller_guy_hash :: caller_guy_hash :: wad ||
  checkAddress  -- caller_guy_hash_valid? :: caller_guy_hash :: wad ||

-- assumes : args = [guy, wad]
def logApprove : Line :=
  argCopy 0 1 1 ++ -- || wad
  arg 0 ++ caller :: pushWord approvalEsig :: -- approvalEsig :: caller :: guy || wad
  logWith 2 0 1 -- 2 indexed topics : caller address, approvee address
                -- 1 unindexed data : approval value


-- arguments = [guy, wad]
def approve : Func :=
  arg 0 +++ -- guy ||
  checkNonAddress +++ -- guy_invalid? ||
  .rev <?> -- [if guy is invalid, revert]
  prepApprove +++ -- hash_valid? :: hash :: wad ||
  .rev <?> -- [ if storage location of approval amount
           --   is a valid address that may potentially
           --   collide with balance storage, revert ]
           -- hash :: wad ||
  sstore :: -- ||
  logApprove +++
  returnTrue



-- transfer(address dst, uint wad) --

-- assumes : args = [dst, wad]
def logTransfer : Line :=
  argCopy 0 1 1 ++ -- || wad
  arg 0 ++ caller :: pushWord transferEsig :: -- transferEsig :: src :: dst || wad
  logWith 2 0 1 -- 2 indexed topics : source address, destination address
                -- 1 unindexed data : transfer value

-- ( wad dst -- )
def incrWbal : Line :=
  dup 1 :: -- dst :: wad :: dst
  sload :: -- dst_bal :: wad :: dst
  add :: -- (dst_bal + wad) :: dst
  swap 0 :: -- dst :: (dst_bal + wad)
  sstore :: []

-- assumes : arg = [dst, wad]
-- ( -- dst_invalid :: dst )
def transferTestDst : Line :=
  arg 0 ++ dup 0 :: -- dst :: dst
  checkNonAddress -- dst_invalid :: dst

-- assumes : arg = [_, wad]
-- ( -- caller_bal_<_wad? caller_bal wad wad )
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

-- ( caller :: caller_bal - wad :: wad :: dst -- * )
def transferCore : Func :=
  sstore ::: -- wad :: dst [caller balance up to date]
  incrWbal +++ -- [destination balance up todate]
  logTransfer +++
  returnTrue

-- assumes : arg = [dst, wad]
def transfer : Func :=
  transferTestDst +++ -- dst_invalid? :: dst
  .rev <?> -- [if dst is not a valid address, revert]
           -- dst
  transferTestLt +++ -- (caller_bal < wad) :: caller :: caller_bal - wad :: wad :: dst
  .rev <?> -- [if caller balance < transfer amount, revert]
        -- caller :: caller_bal - wad :: wad :: dst
  transferCore

-- ( sbal :: wad :: wad :: src -- wad :: src )
def transferFromUpdateSbal : Line :=
  sub :: -- (sbal - wad) :: wad :: src
  dup 2 :: -- src :: (sbal - wad) :: wad :: src
  sstore :: -- [source balance is up to date]
  []        -- wad :: src

-- ( dst :: wad :: src -- wad :: src )
def transferFromLog : Line :=
  dup 2 :: -- src :: dst :: wad :: src
  pushWord transferEsig :: -- transferEsig :: src :: dst :: wad :: src
  dup 3 :: mstoreAt 0 ++ -- transferEsig :: src :: dst :: wad :: src || wad
  logWith 2 0 1 -- [Transfer(src,dst,wad) is logged]
                -- wad :: src

-- (wad src -- )
def updateAllowance : Func :=
  prepend [caller, dup 2, eq] <| -- (src =? caller) :: wad :: src
  returnTrue <?> -- if caller is source, do not update allowance
                 -- wad :: src
  swap 0 :: mstoreAt 0 +++ -- wad || src
  caller ::: mstoreAt 1 +++ -- wad || src :: caller
  pushList [64, 0] +++ -- 0 :: 64 :: wad || src :: caller
  kec ::: -- hash :: wad
  swap 0 ::: -- wad :: hash
  dup 1 :: checkAddress +++ -- va(hash) :: wad :: hash
  .rev <?> -- if hash is a valid address, revert to prevent collision
           -- wad :: hash
  dup 1 ::: sload ::: -- amnt :: wad :: hash
  dup 0 ::: isMax +++ -- (amnt =? max) :: amnt :: wad :: hash
  returnTrue <?> -- if allowed amount is infinite (per EIP-717), do not update allowance
                 -- amnt :: wad :: hash
  dup 1 ::: dup 1 ::: lt ::: -- amnt <? wad :: amnt :: wad :: hash
  .rev <?> -- if allowed amount < transfer amount, revert
           -- amnt :: wad :: hash
  sub ::: swap 0 ::: -- hash :: (amnt - wad)
  sstore ::: returnTrue -- [allowance amount is up to date]

-- assumes : args = [src, dst, wad]
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



-- main --

def wethTree : DispatchTree :=
  .fork
  ( .fork
    ( .fork
      (.leaf nameSig name)
      (.leaf approveSig approve) )
    ( .fork
      (.leaf totalSupplySig totalSupply)
      ( .fork
        (.leaf transferFromSig transferFrom)
        (.leaf withdrawSig withdraw) ) ) )
  ( .fork
    ( .fork
      (.leaf decimalsSig decimals)
      ( .fork
        (.leaf balanceOfSig balanceOf)
        (.leaf symbolSig symbol) ) )
    ( .fork
      (.leaf transferSig transfer)
      ( .fork
        (.leaf depositSig deposit)
        (.leaf allowanceSig allowance) ) ) )

def weth : Prog := ⟨Func.main wethTree, []⟩
