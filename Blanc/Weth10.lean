-- Weth10.lean : the concrete, parameterized WETH10 runtime.
--
-- The public behavior is frozen by WETH10_COMPATIBILITY.md.  This module owns
-- code generation only; the tagged layout and deployment parameters remain in
-- Weth10Core, and the backing relation remains in Weth10Backed.

import Blanc.RevertPayload
import Blanc.Weth10Core

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace Weth10

/-! ## Runtime constants and fixed-width deployment parameters -/

def domainTypehashPreimage : String :=
  "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
def namePreimage : String := "Wrapped Ether v10"
def versionPreimage : String := "1"

def DOMAIN_TYPEHASH : B256 := Blanc.String.keccak domainTypehashPreimage
def NAME_HASH : B256 := Blanc.String.keccak namePreimage
def VERSION_HASH : B256 := Blanc.String.keccak versionPreimage

def onTokenTransferSelector : B256 :=
  selector "onTokenTransfer" [.address, .uint256, .dynBytes]
def onTokenApprovalSelector : B256 :=
  selector "onTokenApproval" [.address, .uint256, .dynBytes]
def onFlashLoanSelector : B256 :=
  selector "onFlashLoan" [.address, .address, .uint256, .uint256, .dynBytes]

/-- Deployment parameters are always encoded with `PUSH32`.  Their byte width
must not depend on the concrete chain or separator: fresh deployment patches
the corresponding fixed spans in one stable runtime template. -/
def pushDeployWord (w : B256) : Ninst :=
  Ninst.push w.toBytes (by rw [B256.length_toBytes])

def nonceTagWord : B256 := Nat.toB256 (2 ^ 254)
def allowanceTagWord : B256 := Nat.toB256 (2 ^ 255)
def allowancePayloadMask : B256 := Nat.toB256 (2 ^ 254 - 1)

/-- `(address-word -- tagged nonce key)`. -/
def tagNonceKey : Line := [pushB256 nonceTagWord, Ninst.or]

/-- Memory words 0 and 1 contain owner and spender; leave their tagged
allowance key on the stack. -/
def allowanceKeyFromMemory : Line :=
  pushList [64, 0] ++
  [kec, pushB256 allowancePayloadMask, Ninst.and,
    pushB256 allowanceTagWord, Ninst.or]

/-- Canonicalize a raw ABI address word to its low 160 bits before using it as
a balance key.  Canonical calls are unchanged; malformed input behavior is
outside the compatibility boundary, while this normalization keeps dirty
words from aliasing the tagged nonce, allowance, or flash regions. -/
def normalizeAddress : Line := pushAddressMask ++ [Ninst.not, Ninst.and]

def addressArg (k : B256) : Line := arg k ++ normalizeAddress

/-- The flash counter uses the all-ones word, emitted as `PUSH0; NOT`. -/
def pushFlashMintedSlot : Line := [pushB256 0, Ninst.not]

def returnWord (w : B256) : Func :=
  pushB256 w ::: mstoreAt 0 +++ returnMemoryRange 0 32

def returnDeployWord (w : B256) : Func :=
  pushDeployWord w ::: mstoreAt 0 +++ returnMemoryRange 0 32

/-- Solidity's nonpayable entry guard: it runs after selector dispatch and
before the endpoint body, and reverts with empty data. -/
def nonpayable (body : Func) : Func :=
  callvalue ::: iszero ::: (body <?> Func.rev)

/-! ## Stable auxiliary-table coordinates -/

-- `Func.call` indexes `main :: aux`.  This prefix is append-only: proofs and
-- compiled jumps name the same coordinates.
def fallbackSlot : Nat := 1
def flashTokenErrorSlot : Nat := 2
def individualLimitErrorSlot : Nat := 3
def totalLimitErrorSlot : Nat := 4
def flashFailedErrorSlot : Nat := 5
def allowanceErrorSlot : Nat := 6
def burnBalanceErrorSlot : Nat := 7
def expiredPermitErrorSlot : Nat := 8
def invalidPermitErrorSlot : Nat := 9
def transferBalanceErrorSlot : Nat := 10
def ethTransferErrorSlot : Nat := 11
def etherTransferErrorSlot : Nat := 12
def bubbleRevertSlot : Nat := 13
def boolReturnSlot : Nat := 14
def flashSettleSlot : Nat := 15
def transferFromCoreSlot : Nat := 16
def withdrawFromCoreSlot : Nat := 17
def flashBurnSlot : Nat := 18
def permitRecoverSlot : Nat := 19

def flashTokenError : Func := Func.revWith "WETH: flash mint only WETH10"
def individualLimitError : Func :=
  Func.revWith "WETH: individual loan limit exceeded"
def totalLimitError : Func := Func.revWith "WETH: total loan limit exceeded"
def flashFailedError : Func := Func.revWith "WETH: flash loan failed"
def allowanceError : Func := Func.revWith "WETH: request exceeds allowance"
def burnBalanceError : Func := Func.revWith "WETH: burn amount exceeds balance"
def expiredPermitError : Func := Func.revWith "WETH: Expired permit"
def invalidPermitError : Func := Func.revWith "WETH: invalid permit"
def transferBalanceError : Func :=
  Func.revWith "WETH: transfer amount exceeds balance"
def ethTransferError : Func := Func.revWith "WETH: ETH transfer failed"
def etherTransferError : Func := Func.revWith "WETH: Ether transfer failed"

/-! ## Constant and storage views -/

def callbackSuccess : Func := returnWord CALLBACK_SUCCESS
def permitTypehash : Func := returnWord PERMIT_TYPEHASH
def decimals : Func := Blanc.decimals
def balanceOfEndpoint : Func := Blanc.balanceOf

def deploymentChainId (dp : DeployParams) : Func :=
  returnDeployWord dp.deploymentChainId

def flashMinted : Func :=
  pushFlashMintedSlot +++ sload ::: mstoreAt 0 +++ returnMemoryRange 0 32

def nonces : Func :=
  arg 0 +++ tagNonceKey +++ sload ::: mstoreAt 0 +++ returnMemoryRange 0 32

def allowance : Func :=
  argCopy 0 0 2 +++ allowanceKeyFromMemory +++
  sload ::: mstoreAt 0 +++ returnMemoryRange 0 32

def totalSupply : Func :=
  selfbalance ::: pushFlashMintedSlot +++ sload ::: add :::
  mstoreAt 0 +++ returnMemoryRange 0 32

def maxFlashLoan : Func :=
  arg 0 +++ address ::: eq :::
  (pushFlashMintedSlot +++ sload :::
    pushB256 (Nat.toB256 maxFlashMinted) ::: sub :::
    mstoreAt 0 +++ returnMemoryRange 0 32) <?>
  (returnWord 0)

def flashFee : Func :=
  arg 0 +++ address ::: eq ::: iszero :::
  (.call flashTokenErrorSlot) <?>
  (returnWord 0)

def name : Func :=
  pushB256 (Blanc.String.toBytes "Wrapped Ether v10").toB256 :::
  pushB256 120 ::: shl :::
  pushList [17, 32] +++
  mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
  returnMemoryRange 0 96

def symbol : Func :=
  pushB256 (Blanc.String.toBytes "WETH10").toB256 :::
  pushB256 208 ::: shl :::
  pushList [6, 32] +++
  mstoreAt 0 +++ mstoreAt 1 +++ mstoreAt 2 +++
  returnMemoryRange 0 96

/-! ## EIP-712 domain -/

/-- `(chainId -- domainSeparator)`, clobbering memory words 0 through 4. -/
def calculateDomainSeparator : Line :=
  mstoreAt 3 ++
  [pushB256 DOMAIN_TYPEHASH] ++ mstoreAt 0 ++
  [pushB256 NAME_HASH] ++ mstoreAt 1 ++
  [pushB256 VERSION_HASH] ++ mstoreAt 2 ++
  [address] ++ mstoreAt 4 ++
  pushList [160, 0] ++ [kec]

def domainSeparator (dp : DeployParams) : Func :=
  chainid ::: dup 0 ::: pushDeployWord dp.deploymentChainId ::: eq :::
  (pop ::: returnDeployWord dp.cachedDomainSeparator) <?>
  (calculateDomainSeparator +++ mstoreAt 0 +++ returnMemoryRange 0 32)

/-! ## Payable receive and deposit paths -/

def mintCaller : Func :=
  caller ::: sload ::: callvalue ::: add ::: caller ::: sstore :::
  callvalue ::: mstoreAt 0 +++
  caller ::: pushB256 0 ::: pushB256 Blanc.transferEvent :::
  logWith 2 0 1 +++
  Func.stop

def receiveEther : Func := mintCaller
def deposit : Func := mintCaller

def mintToPrefix : Line :=
  addressArg 0 ++ [sload, callvalue, add] ++ addressArg 0 ++
  [sstore, callvalue] ++ mstoreAt 0 ++ addressArg 0 ++
  [pushB256 0, pushB256 Blanc.transferEvent] ++
  logWith 2 0 1

def depositTo : Func := mintToPrefix +++ Func.stop

/-! ## Transfer, withdrawal, and call-free mutation helpers -/

/-- `(to :: value :: from -- value :: from)`. -/
def emitTransfer : Line := Blanc.transferFromLog

/-- `(spender :: value :: owner -- value :: owner)`. -/
def emitApproval : Line :=
  [dup 2, pushB256 Blanc.approvalEvent, dup 3] ++
  mstoreAt 0 ++ logWith 2 0 1

/-- Load caller balance and calldata amount `k` as
`balance :: value :: caller`. -/
def loadCallerBalanceAmount (k : B256) : Line :=
  [caller, dup 0, sload] ++ arg k ++ [swap 0]

/-- `(balance :: value :: owner -- failed? :: balance :: value :: owner)`. -/
def balanceTooSmall : Line := [dup 1, dup 1, lt]

/-- `(balance :: value :: owner -- )`, under the preceding balance check. -/
def debitLoadedBalance : Line := [sub, swap 0, sstore]

/-- `(value -- success?)`: zero-length value call to the caller, forwarding
the frame's remaining gas subject to EIP-150. -/
def sendValueToCaller : Line :=
  pushList [0, 0, 0, 0] ++ [swap 3, caller, gas, call]

/-- `(value -- success?)`: zero-length value call to address argument `k`. -/
def sendValueToArg (k : B256) : Line :=
  pushList [0, 0, 0, 0] ++ [swap 3] ++ arg k ++ [gas, call]

def transferNonzeroThen (next : Func) : Func :=
  loadCallerBalanceAmount 1 +++ balanceTooSmall +++
  (.call transferBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    addressArg 0 +++ dup 0 ::: sload ::: arg 1 +++ add ::: swap 0 ::: sstore :::
    caller ::: arg 1 +++ addressArg 0 +++ emitTransfer +++
    next)

def transferZeroThen (next : Func) : Func :=
  loadCallerBalanceAmount 1 +++ balanceTooSmall +++
  (.call burnBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    caller ::: arg 1 +++ pushB256 0 ::: emitTransfer +++
    swap 0 ::: pop :::
    sendValueToCaller +++ iszero :::
    (.call ethTransferErrorSlot) <?>
    next)

def transferThen (next : Func) : Func :=
  arg 0 +++ iszero :::
  (transferZeroThen next <?> transferNonzeroThen next)

def transfer : Func := transferThen returnTrue

def withdraw : Func :=
  loadCallerBalanceAmount 0 +++ balanceTooSmall +++
  (.call burnBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    caller ::: arg 0 +++ pushB256 0 ::: emitTransfer +++
    swap 0 ::: pop :::
    sendValueToCaller +++ iszero :::
    (.call ethTransferErrorSlot) <?>
    Func.stop)

def withdrawTo : Func :=
  loadCallerBalanceAmount 1 +++ balanceTooSmall +++
  (.call burnBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    caller ::: arg 1 +++ pushB256 0 ::: emitTransfer +++
    swap 0 ::: pop :::
    sendValueToArg 0 +++ iszero :::
    (.call ethTransferErrorSlot) <?>
    Func.stop)

/-- Load balance of address argument `owner` and calldata amount `amount` as
`balance :: value :: owner`. -/
def loadArgBalanceAmount (owner amount : B256) : Line :=
  addressArg owner ++ [dup 0, sload] ++ arg amount ++ [swap 0]

def transferFromNonzero : Func :=
  loadArgBalanceAmount 0 2 +++ balanceTooSmall +++
  (.call transferBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    addressArg 1 +++ dup 0 ::: sload ::: arg 2 +++ add ::: swap 0 ::: sstore :::
    addressArg 0 +++ arg 2 +++ addressArg 1 +++ emitTransfer +++
    returnTrue)

def transferFromZero : Func :=
  loadArgBalanceAmount 0 2 +++ balanceTooSmall +++
  (.call burnBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    addressArg 0 +++ arg 2 +++ pushB256 0 ::: emitTransfer +++
    swap 0 ::: pop :::
    sendValueToCaller +++ iszero :::
    (.call ethTransferErrorSlot) <?>
    returnTrue)

def transferFromCore : Func :=
  arg 1 +++ iszero ::: (transferFromZero <?> transferFromNonzero)

def withdrawFromCore : Func :=
  loadArgBalanceAmount 0 2 +++ balanceTooSmall +++
  (.call burnBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    addressArg 0 +++ arg 2 +++ pushB256 0 ::: emitTransfer +++
    swap 0 ::: pop :::
    sendValueToArg 1 +++ iszero :::
    (.call etherTransferErrorSlot) <?>
    Func.stop)

/-- Spend finite `allowance[from][caller]`, or preserve an infinite allowance,
then tail-jump to `nextSlot`.  The `from == caller` branch bypasses even the
allowance read. -/
def spendCallerAllowanceThen (amount : B256) (nextSlot : Nat) : Func :=
  arg 0 +++ caller ::: eq :::
  (.call nextSlot) <?>
  (arg 0 +++ mstoreAt 0 +++ caller ::: mstoreAt 1 +++
    allowanceKeyFromMemory +++ dup 0 ::: sload ::: dup 0 ::: isMax +++
    (pop ::: pop ::: .call nextSlot) <?>
    (arg amount +++ swap 0 ::: balanceTooSmall +++
      (.call allowanceErrorSlot) <?>
      (sub ::: dup 0 ::: swap 1 ::: sstore :::
        arg 0 +++ swap 0 ::: caller ::: emitApproval +++
        pop ::: pop ::: .call nextSlot)))

def transferFrom : Func := spendCallerAllowanceThen 2 transferFromCoreSlot

def withdrawFrom : Func := spendCallerAllowanceThen 2 withdrawFromCoreSlot

/-! ## Call-free state mutation -/

def approvePrefix : Line :=
  [caller] ++ mstoreAt 0 ++
  argCopy 1 0 1 ++
  allowanceKeyFromMemory ++
  arg 1 ++ [swap 0, sstore] ++
  Blanc.logApprove

def approve : Func := approvePrefix +++ returnTrue

/-! ## ERC-677-style Boolean callbacks -/

def callbackArgsOffset : B256 := 0x1c

/-- `(value -- )`, writing selector/caller/value/dynamic-offset words 0..3. -/
def storeTokenCallbackHead (sel : B256) : Line :=
  [pushB256 sel] ++ mstoreAt 0 ++
  [caller] ++ mstoreAt 1 ++
  mstoreAt 2 ++
  [pushB256 0x60] ++ mstoreAt 3

/-- `(dataLen -- callback calldata size)`. -/
def tokenCallbackArgsSize : Line :=
  [pushB256 31, add, pushB256 31, Ninst.not, Ninst.and,
    pushB256 0x84, add]

/-- Common Solidity-0.7 Boolean return decoder.  A failed child call bubbles
its full returndata and a short return empty-reverts.  The first full word uses
the deployed runtime's truthiness rule: zero becomes ABI `false` and every
nonzero value becomes canonical ABI `true`. -/
def boolReturn : Func :=
  iszero :::
  (.call bubbleRevertSlot) <?>
  (retdataShorterThan 32 +++
    Func.rev <?>
    (pushList [32, 0, 0] +++ retdatacopy :::
      pushB256 0 ::: mload :::
      iszero ::: iszero :::
      mstoreAt 0 +++ returnMemoryRange 0 32))

def bubbleRevert : Func := Func.revReturnData

/-- Typed zero-value callback with signature `sel(address,uint256,bytes)`.
The source state/log prefix has already committed within the current frame.
Solidity's code-existence check happens before `CALL`; a codeless target emits
no child call and empty-reverts. -/
def callBoolCallback (sel : B256) (target dataArg : B256)
    (value : Line) : Func :=
  arg target +++ dup 0 ::: extcodesize ::: iszero :::
  Func.rev <?>
  (pop :::
    value +++ storeTokenCallbackHead sel +++
    pushList [0, 0] +++
    forwardArgTail dataArg 4 +++ tokenCallbackArgsSize +++
    pushB256 callbackArgsOffset ::: pushB256 0 :::
    arg target +++ gas ::: call :::
    .call boolReturnSlot)

def depositToAndCall : Func :=
  mintToPrefix +++
  callBoolCallback onTokenTransferSelector 0 1 [callvalue]

def approveAndCall : Func :=
  approvePrefix +++
  callBoolCallback onTokenApprovalSelector 0 2 (arg 1)

def transferAndCall : Func :=
  transferThen <|
    callBoolCallback onTokenTransferSelector 0 2 (arg 1)

/-! ## ERC-3156 flash minting -/

def maxUint112 : B256 := Nat.toB256 maxFlashMinted

/-- `(amount -- )`, writing the five static callback heads after the selector.
The dynamic `data` offset is relative to the argument area, hence `0xa0`. -/
def storeFlashCallbackHead : Line :=
  [pushB256 onFlashLoanSelector] ++ mstoreAt 0 ++
  [caller] ++ mstoreAt 1 ++
  [address] ++ mstoreAt 2 ++
  mstoreAt 3 ++
  [pushB256 0] ++ mstoreAt 4 ++
  [pushB256 0xa0] ++ mstoreAt 5

/-- `(dataLen -- callback calldata size)`. -/
def flashCallbackArgsSize : Line :=
  [pushB256 31, add, pushB256 31, Ninst.not, Ninst.and,
    pushB256 0xc4, add]

/-- Starting from `reduced`, emit the finite-allowance
`Approval(receiver, address(this), reduced)` and clear the stack. -/
def emitFlashApproval : Line :=
  [dup 0] ++ mstoreAt 0 ++
  [address] ++ arg 0 ++ [pushB256 Blanc.approvalEvent] ++
  logWith 2 0 1 ++ [pop]

/-- Final flash settlement after the callback and allowance phase.  It reloads
the receiver's post-callback balance, burns, emits, decrements `flashMinted`
unchecked, and returns true. -/
def flashBurn : Func :=
  loadArgBalanceAmount 0 2 +++ balanceTooSmall +++
  (.call burnBalanceErrorSlot) <?>
  (debitLoadedBalance +++
    addressArg 0 +++ arg 2 +++ pushB256 0 ::: emitTransfer +++
    pop ::: pop :::
    pushFlashMintedSlot +++ sload ::: arg 2 +++ swap 0 ::: sub :::
    pushFlashMintedSlot +++ sstore :::
    returnTrue)

/-- Post-callback allowance phase.  Both max and finite arms tail-jump to the
single burn continuation so its ordering cannot drift between the arms. -/
def flashSettle : Func :=
  addressArg 0 +++ mstoreAt 0 +++ address ::: mstoreAt 1 +++
  allowanceKeyFromMemory +++ dup 0 ::: sload ::: dup 0 ::: isMax +++
  (pop ::: pop ::: .call flashBurnSlot) <?>
  (arg 2 +++ swap 0 ::: balanceTooSmall +++
    (.call allowanceErrorSlot) <?>
    (sub ::: dup 0 ::: swap 1 ::: sstore :::
      emitFlashApproval +++ .call flashBurnSlot))

def flashLoan : Func :=
  arg 1 +++ address ::: eq ::: iszero :::
  (.call flashTokenErrorSlot) <?>
  (arg 2 +++ dup 0 ::: pushB256 maxUint112 ::: lt :::
    (.call individualLimitErrorSlot) <?>
    (pushFlashMintedSlot +++ sload ::: dup 1 ::: add :::
      pushFlashMintedSlot +++ sstore :::
      pushFlashMintedSlot +++ sload ::: dup 0 :::
      pushB256 maxUint112 ::: lt :::
      (.call totalLimitErrorSlot) <?>
      (pop :::
        addressArg 0 +++ dup 0 ::: sload ::: dup 2 ::: add :::
        dup 1 ::: sstore ::: swap 0 :::
        dup 0 ::: mstoreAt 0 +++
        dup 1 ::: pushB256 0 ::: pushB256 Blanc.transferEvent :::
        logWith 2 0 1 +++
        dup 1 ::: extcodesize ::: iszero :::
        Func.rev <?>
        (dup 0 ::: storeFlashCallbackHead +++
          pushList [0, 0] +++
          forwardArgTail 3 6 +++ flashCallbackArgsSize +++
          pushB256 callbackArgsOffset ::: pushB256 0 :::
          dup 6 ::: gas ::: call ::: iszero :::
          (.call bubbleRevertSlot) <?>
          (retdataShorterThan 32 +++
            Func.rev <?>
            (checkRetdataHead CALLBACK_SUCCESS 0 +++ iszero :::
              (.call flashFailedErrorSlot) <?>
              (pop ::: pop ::: .call flashSettleSlot)))))))

/-! ## ERC-2612 permit -/

def eip712PrefixWord : B256 := Nat.toB256 (0x1901 * 2 ^ 240)

/-- Consume `domain :: hashStruct` and leave the EIP-712 digest. -/
def permitDigest : Line :=
  [swap 0, pushB256 34, mstore,
    pushB256 eip712PrefixWord] ++ mstoreAt 0 ++
  [pushB256 2, mstore] ++ pushList [66, 0] ++ [kec]

/-- Call precompile 1 exactly as Solidity's `ecrecover` builtin does.  The
output word is pre-zeroed because precompile failure returns address zero. -/
def recoverPermitSigner : Line :=
  mstoreAt 0 ++
  arg 4 ++ mstoreAt 1 ++
  arg 5 ++ mstoreAt 2 ++
  arg 6 ++ mstoreAt 3 ++
  [pushB256 0] ++ mstoreAt 4 ++
  pushList [32, 128, 128, 0, 1] ++ [gas, statcall, pop,
    pushB256 128, mload]

def approvePermit : Func :=
  argCopy 0 0 2 +++ allowanceKeyFromMemory +++
  arg 2 +++ swap 0 ::: sstore :::
  arg 2 +++ mstoreAt 0 +++
  arg 1 +++ arg 0 +++ pushB256 Blanc.approvalEvent :::
  logWith 2 0 1 +++
  Func.stop

def permitRecover : Func :=
  permitDigest +++ recoverPermitSigner +++
  dup 0 ::: iszero :::
  (.call invalidPermitErrorSlot) <?>
  (arg 0 +++ eq ::: iszero :::
    (.call invalidPermitErrorSlot) <?>
    approvePermit)

def permit (dp : DeployParams) : Func :=
  arg 3 +++ timestamp ::: gt :::
  (.call expiredPermitErrorSlot) <?>
  (chainid :::
    addressArg 0 +++ dup 0 ::: tagNonceKey +++ dup 0 ::: sload :::
    dup 0 ::: mstoreAt 4 +++ pushB256 1 ::: add ::: swap 0 ::: sstore :::
    pop :::
    pushB256 PERMIT_TYPEHASH ::: mstoreAt 0 +++
    argCopy 1 0 3 +++ arg 3 +++ mstoreAt 5 +++
    pushList [192, 0] +++ kec :::
    dup 1 ::: pushDeployWord dp.deploymentChainId ::: eq :::
    (swap 0 ::: pop ::: pushDeployWord dp.cachedDomainSeparator :::
      .call permitRecoverSlot) <?>
    (swap 0 ::: calculateDomainSeparator +++ .call permitRecoverSlot))

/-- Dispatcher misses reach this slot.  Only truly empty calldata is receive;
an unknown nonempty selector is an empty-data revert. -/
def receiveOrRevert : Func :=
  calldatasize ::: iszero ::: (receiveEther <?> Func.rev)

/-! ## Complete runtime program -/

/-- The 27 deployed selectors in strict ascending order.  Payability is local
to each leaf so a recognized nonpayable selector rejects value before its
source-level guards, while the three deposit selectors remain payable. -/
def weth10Funcs (dp : DeployParams) : List (B256 × Func) :=
  [ (selector "name" [], nonpayable name),
    (selector "approve" [.address, .uint256], nonpayable approve),
    (selector "totalSupply" [], nonpayable totalSupply),
    (selector "withdrawTo" [.address, .uint256], nonpayable withdrawTo),
    (selector "transferFrom" [.address, .address, .uint256],
      nonpayable transferFrom),
    (selector "withdraw" [.uint256], nonpayable withdraw),
    (selector "PERMIT_TYPEHASH" [], nonpayable permitTypehash),
    (selector "decimals" [], nonpayable decimals),
    (selector "DOMAIN_SEPARATOR" [], nonpayable (domainSeparator dp)),
    (selector "transferAndCall" [.address, .uint256, .dynBytes],
      nonpayable transferAndCall),
    (selector "flashLoan" [.address, .address, .uint256, .dynBytes],
      nonpayable flashLoan),
    (selector "depositToAndCall" [.address, .dynBytes], depositToAndCall),
    (selector "maxFlashLoan" [.address], nonpayable maxFlashLoan),
    (selector "balanceOf" [.address], nonpayable balanceOfEndpoint),
    (selector "nonces" [.address], nonpayable nonces),
    (selector "CALLBACK_SUCCESS" [], nonpayable callbackSuccess),
    (selector "flashMinted" [], nonpayable flashMinted),
    (selector "withdrawFrom" [.address, .address, .uint256],
      nonpayable withdrawFrom),
    (selector "symbol" [], nonpayable symbol),
    (selector "transfer" [.address, .uint256], nonpayable transfer),
    (selector "depositTo" [.address], depositTo),
    (selector "approveAndCall" [.address, .uint256, .dynBytes],
      nonpayable approveAndCall),
    (selector "deploymentChainId" [], nonpayable (deploymentChainId dp)),
    (selector "deposit" [], deposit),
    (selector "permit"
      [.address, .address, .uint256, .uint256, .uint 8, .bytes 32, .bytes 32],
      nonpayable (permit dp)),
    (selector "flashFee" [.address, .uint256], nonpayable flashFee),
    (selector "allowance" [.address, .address], nonpayable allowance) ]

theorem weth10Funcs_sorted (dp : DeployParams) :
    DispatchTree.sorted (weth10Funcs dp) = true := by
  change DispatchTree.sorted (weth10Funcs ⟨0, 0⟩) = true
  decide +kernel

def weth10Tree (dp : DeployParams) : DispatchTree :=
  .ofSorted (weth10Funcs dp)

/-! ## Parameter-independent compiler shape

The compiler erases instruction contents when deciding success, but asking the
elaborator to compare the two complete 6 KB program shapes definitionally is
needlessly expensive.  The small erasure below follows the dispatcher tree and
lets the proof compare the 27 leaves before rebuilding that tree. -/

private inductive DispatchCompileShape : Type
  | leaf (selector : B256) (body : Func.CompileShape)
  | fork (left right : DispatchCompileShape)

private def dispatchCompileShape : DispatchTree → DispatchCompileShape
  | .leaf w p => .leaf w p.compileShape
  | .fork l r => .fork (dispatchCompileShape l) (dispatchCompileShape r)

private def dispatchEntryShapes (xs : List (B256 × Func)) :
    List (B256 × Func.CompileShape) :=
  xs.map fun wp => (wp.1, wp.2.compileShape)

private theorem dispatchCompileShape_build_eq
    {xs ys : List (B256 × Func)}
    (h : dispatchEntryShapes xs = dispatchEntryShapes ys) (fuel : Nat) :
    dispatchCompileShape (DispatchTree.build fuel xs) =
      dispatchCompileShape (DispatchTree.build fuel ys) := by
  induction fuel generalizing xs ys with
  | zero =>
      cases xs with
      | nil =>
          cases ys <;>
            simp [dispatchEntryShapes, DispatchTree.build,
              dispatchCompileShape] at h ⊢
      | cons x xs =>
          cases xs with
          | nil =>
              cases ys with
              | nil => simp [dispatchEntryShapes] at h
              | cons y ys =>
                  cases ys with
                  | nil =>
                      simp [dispatchEntryShapes, DispatchTree.build,
                        dispatchCompileShape] at h ⊢
                      exact h
                  | cons y' ys =>
                      simp [dispatchEntryShapes] at h
          | cons x' xs =>
              cases ys with
              | nil => simp [dispatchEntryShapes] at h
              | cons y ys =>
                  cases ys with
                  | nil => simp [dispatchEntryShapes] at h
                  | cons y' ys =>
                      simpa [dispatchEntryShapes, DispatchTree.build,
                        dispatchCompileShape] using congrArg List.head? h
  | succ fuel ih =>
      cases xs with
      | nil =>
          cases ys <;>
            simp [dispatchEntryShapes, DispatchTree.build,
              dispatchCompileShape] at h ⊢
      | cons x xs =>
          cases xs with
          | nil =>
              cases ys with
              | nil => simp [dispatchEntryShapes] at h
              | cons y ys =>
                  cases ys with
                  | nil =>
                      simp [dispatchEntryShapes, DispatchTree.build,
                        dispatchCompileShape] at h ⊢
                      exact h
                  | cons y' ys =>
                      simp [dispatchEntryShapes] at h
          | cons x' xs =>
              cases ys with
              | nil => simp [dispatchEntryShapes] at h
              | cons y ys =>
                  cases ys with
                  | nil => simp [dispatchEntryShapes] at h
                  | cons y' ys =>
                      have hlen : xs.length = ys.length := by
                        simpa [dispatchEntryShapes] using
                          congrArg List.length h
                      simp only [DispatchTree.build, dispatchCompileShape,
                        List.length_cons]
                      rw [← hlen]
                      congr 1
                      · apply ih
                        simpa [dispatchEntryShapes] using
                          congrArg
                            (List.take
                              (((x :: x' :: xs).length + 1) / 2)) h
                      · apply ih
                        simpa [dispatchEntryShapes] using
                          congrArg
                            (List.drop
                              (((x :: x' :: xs).length + 1) / 2)) h

private theorem leftmostFsig_eq_of_dispatchCompileShape
    {t t' : DispatchTree}
    (h : dispatchCompileShape t = dispatchCompileShape t') :
    leftmostFsig t = leftmostFsig t' := by
  induction t generalizing t' with
  | leaf w p =>
      cases t' with
      | leaf w' p' =>
          have hw :=
            congrArg (fun s =>
                match s with
                | DispatchCompileShape.leaf w _ => w
                | DispatchCompileShape.fork _ _ => 0) h
          simpa [dispatchCompileShape, leftmostFsig] using hw
      | fork _ _ => simp [dispatchCompileShape] at h
  | fork l r ihl ihr =>
      cases t' with
      | leaf _ _ => simp [dispatchCompileShape] at h
      | fork l' r' =>
          simp only [dispatchCompileShape,
            DispatchCompileShape.fork.injEq] at h
          exact ihl (t' := l') h.1

private theorem dispatchWith_compileShape_eq
    {t t' : DispatchTree}
    (h : dispatchCompileShape t = dispatchCompileShape t') (k : Nat) :
    (dispatchWith k t).compileShape =
      (dispatchWith k t').compileShape := by
  induction t generalizing t' with
  | leaf w p =>
      cases t' with
      | leaf w' p' =>
          simp only [dispatchCompileShape,
            DispatchCompileShape.leaf.injEq] at h
          simp [dispatchWith, Func.compileShape, h.1, h.2]
      | fork _ _ => simp [dispatchCompileShape] at h
  | fork l r ihl ihr =>
      cases t' with
      | leaf _ _ => simp [dispatchCompileShape] at h
      | fork l' r' =>
          simp only [dispatchCompileShape,
            DispatchCompileShape.fork.injEq] at h
          have hw := leftmostFsig_eq_of_dispatchCompileShape h.2
          simp [dispatchWith, Func.compileShape, hw, ihl h.1, ihr h.2]

private theorem weth10EntryShapes_eq (dp : DeployParams) :
    dispatchEntryShapes (weth10Funcs dp) =
      dispatchEntryShapes (weth10Funcs ⟨0, 0⟩) := by
  rfl

private theorem weth10Tree_compileShape_eq (dp : DeployParams) :
    dispatchCompileShape (weth10Tree dp) =
      dispatchCompileShape (weth10Tree ⟨0, 0⟩) := by
  unfold weth10Tree DispatchTree.ofSorted
  have hlen :
      (weth10Funcs dp).length = (weth10Funcs ⟨0, 0⟩).length := by
    simpa [dispatchEntryShapes] using
      congrArg List.length (weth10EntryShapes_eq dp)
  rw [← hlen]
  exact dispatchCompileShape_build_eq (weth10EntryShapes_eq dp) _

private theorem prepend_compileShape_eq (l : Line) {p q : Func}
    (h : p.compileShape = q.compileShape) :
    (l +++ p).compileShape = (l +++ q).compileShape := by
  induction l with
  | nil => exact h
  | cons i l ih => simp [prepend, Func.compileShape, ih]

def weth10Main (dp : DeployParams) : Func :=
  calldatasize ::: iszero :::
  (receiveEther <?> (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))

def weth10Aux : List Func :=
  [ Func.rev,
    flashTokenError,
    individualLimitError,
    totalLimitError,
    flashFailedError,
    allowanceError,
    burnBalanceError,
    expiredPermitError,
    invalidPermitError,
    transferBalanceError,
    ethTransferError,
    etherTransferError,
    bubbleRevert,
    boolReturn,
    flashSettle,
    transferFromCore,
    withdrawFromCore,
    flashBurn,
    permitRecover ]

def weth10 (dp : DeployParams) : Prog :=
  ⟨weth10Main dp, weth10Aux⟩

private theorem weth10Main_compileShape_eq (dp : DeployParams) :
    (weth10Main dp).compileShape =
      (weth10Main ⟨0, 0⟩).compileShape := by
  have hd :=
    dispatchWith_compileShape_eq (weth10Tree_compileShape_eq dp) fallbackSlot
  have hp := prepend_compileShape_eq fsig hd
  simp [weth10Main, Func.compileShape, hp]

private theorem weth10_compileShape_eq (dp : DeployParams) :
    (weth10 dp).compileShape = (weth10 ⟨0, 0⟩).compileShape := by
  simp [weth10, Prog.compileShape, weth10Main_compileShape_eq dp]

/-- Deployment parameters alter fixed-width pushed words, but never the
compiler-relevant shape of the complete runtime program. -/
theorem weth10_compileShape_eq_zero (dp : DeployParams) :
    (weth10 dp).compileShape = (weth10 ⟨0, 0⟩).compileShape :=
  weth10_compileShape_eq dp

private theorem weth10CompilesZero :
    Prog.compiles (weth10 ⟨0, 0⟩) = true := by
  decide +kernel

/-- Fixed-width deployment words do not affect compiler success. -/
theorem weth10_compiles (dp : DeployParams) :
    Prog.compiles (weth10 dp) = true := by
  rw [Prog.compiles_eq_of_compileShape (weth10_compileShape_eq dp)]
  exact weth10CompilesZero

end Weth10

end Blanc
