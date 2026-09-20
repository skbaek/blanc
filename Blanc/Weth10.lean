-- Weth10.lean : the concrete, parameterized WETH10 runtime.
--
-- The public behavior is frozen by WETH10_COMPATIBILITY.md.  This module owns
-- code generation only; the tagged layout and deployment parameters remain in
-- Weth10Core, and the backing relation remains in Weth10Backed.

import Blanc.RevertPayload
import Blanc.Weth10Core
import Blanc.Weth10TemplateCode

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
  [keccak256, pushB256 allowancePayloadMask, Ninst.and,
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

def flashTokenError : Func := Func.revertWith "WETH: flash mint only WETH10"
def individualLimitError : Func :=
  Func.revertWith "WETH: individual loan limit exceeded"
def totalLimitError : Func := Func.revertWith "WETH: total loan limit exceeded"
def flashFailedError : Func := Func.revertWith "WETH: flash loan failed"
def allowanceError : Func := Func.revertWith "WETH: request exceeds allowance"
def burnBalanceError : Func := Func.revertWith "WETH: burn amount exceeds balance"
def expiredPermitError : Func := Func.revertWith "WETH: Expired permit"
def invalidPermitError : Func := Func.revertWith "WETH: invalid permit"
def transferBalanceError : Func :=
  Func.revertWith "WETH: transfer amount exceeds balance"
def ethTransferError : Func := Func.revertWith "WETH: ETH transfer failed"
def etherTransferError : Func := Func.revertWith "WETH: Ether transfer failed"

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
  pushList [160, 0] ++ [keccak256]

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
  (returnDataShorterThan 32 +++
    Func.revert <?>
    (pushList [32, 0, 0] +++ returndatacopy :::
      pushB256 0 ::: mload :::
      iszero ::: iszero :::
      mstoreAt 0 +++ returnMemoryRange 0 32))

def bubbleRevert : Func := Func.revertReturnData

/-- Typed zero-value callback with signature `sel(address,uint256,bytes)`.
The source state/log prefix has already committed within the current frame.
Solidity's code-existence check happens before `CALL`; a codeless target emits
no child call and empty-reverts. -/
def callBoolCallback (sel : B256) (target dataArg : B256)
    (value : Line) : Func :=
  arg target +++ dup 0 ::: extcodesize ::: iszero :::
  Func.revert <?>
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
        Func.revert <?>
        (dup 0 ::: storeFlashCallbackHead +++
          pushList [0, 0] +++
          forwardArgTail 3 6 +++ flashCallbackArgsSize +++
          pushB256 callbackArgsOffset ::: pushB256 0 :::
          dup 6 ::: gas ::: call ::: iszero :::
          (.call bubbleRevertSlot) <?>
          (returnDataShorterThan 32 +++
            Func.revert <?>
            (checkReturnDataHead CALLBACK_SUCCESS 0 +++ iszero :::
              (.call flashFailedErrorSlot) <?>
              (pop ::: pop ::: .call flashSettleSlot)))))))

/-! ## ERC-2612 permit -/

def eip712PrefixWord : B256 := Nat.toB256 (0x1901 * 2 ^ 240)

/-- Consume `domain :: hashStruct` and leave the EIP-712 digest. -/
def permitDigest : Line :=
  [swap 0, pushB256 34, mstore,
    pushB256 eip712PrefixWord] ++ mstoreAt 0 ++
  [pushB256 2, mstore] ++ pushList [66, 0] ++ [keccak256]

/-- Call precompile 1 exactly as Solidity's `ecrecover` builtin does.  The
output word is pre-zeroed because precompile failure returns address zero. -/
def recoverPermitSigner : Line :=
  mstoreAt 0 ++
  arg 4 ++ mstoreAt 1 ++
  arg 5 ++ mstoreAt 2 ++
  arg 6 ++ mstoreAt 3 ++
  [pushB256 0] ++ mstoreAt 4 ++
  pushList [32, 128, 128, 0, 1] ++ [gas, staticcall, pop,
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
    pushList [192, 0] +++ keccak256 :::
    dup 1 ::: pushDeployWord dp.deploymentChainId ::: eq :::
    (swap 0 ::: pop ::: pushDeployWord dp.cachedDomainSeparator :::
      .call permitRecoverSlot) <?>
    (swap 0 ::: calculateDomainSeparator +++ .call permitRecoverSlot))

/-- Dispatcher misses reach this slot.  Only truly empty calldata is receive;
an unknown nonempty selector is an empty-data revert. -/
def receiveOrRevert : Func :=
  calldatasize ::: iszero ::: (receiveEther <?> Func.revert)

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

private theorem pushDeployWord_size (w : B256) :
    (pushDeployWord w).size = 33 := by
  simp [pushDeployWord, Ninst.size, B256.length_toBytes]

private theorem domainSeparator_compileShape_eq (dp : DeployParams) :
    (nonpayable (domainSeparator dp)).compileShape =
      (nonpayable
        (domainSeparator (⟨0, 0⟩ : DeployParams))).compileShape := by
  simp [nonpayable, domainSeparator, Func.compileShape,
    pushDeployWord_size, returnDeployWord]

private theorem deploymentChainId_compileShape_eq (dp : DeployParams) :
    (nonpayable (deploymentChainId dp)).compileShape =
      (nonpayable
        (deploymentChainId (⟨0, 0⟩ : DeployParams))).compileShape := by
  simp [nonpayable, deploymentChainId, returnDeployWord, Func.compileShape,
    pushDeployWord_size]

private theorem permit_compileShape_eq (dp : DeployParams) :
    (nonpayable (permit dp)).compileShape =
      (nonpayable (permit (⟨0, 0⟩ : DeployParams))).compileShape := by
  simp [nonpayable, permit, Func.compileShape, arg, addressArg,
    normalizeAddress, tagNonceKey, mstoreAt, argCopy, pushList,
    calculateDomainSeparator, cdl, cdc, pushAddressMask, prepend,
    pushDeployWord_size]

private theorem weth10EntryShapes_eq (dp : DeployParams) :
    dispatchEntryShapes (weth10Funcs dp) =
      dispatchEntryShapes (weth10Funcs ⟨0, 0⟩) := by
  simp only [dispatchEntryShapes, weth10Funcs, List.map,
    domainSeparator_compileShape_eq dp,
    deploymentChainId_compileShape_eq dp,
    permit_compileShape_eq dp]

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

def weth10Main (dp : DeployParams) : Func :=
  calldatasize ::: iszero :::
  (receiveEther <?> (fsig +++ dispatchWith fallbackSlot (weth10Tree dp)))

def weth10Aux : List Func :=
  [ Func.revert,
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
  have hp := Func.compileShape_prepend_congr fsig hd
  simp [weth10Main, Func.compileShape, hp]

private theorem weth10_compileShape_eq (dp : DeployParams) :
    (weth10 dp).compileShape = (weth10 ⟨0, 0⟩).compileShape := by
  simp [weth10, Prog.compileShape, weth10Main_compileShape_eq dp]

/-- Deployment parameters alter fixed-width pushed words, but never the
compiler-relevant shape of the complete runtime program. -/
theorem weth10_compileShape_eq_zero (dp : DeployParams) :
    (weth10 dp).compileShape = (weth10 ⟨0, 0⟩).compileShape :=
  weth10_compileShape_eq dp

/-- The zero-parameter template's direct full kernel evaluation of the WETH10
compiler.  The structural success witness below decides compilation without
constructing bytes; `weth10RuntimeTemplate`'s identity in
`Blanc/Weth10Deploy.lean` derives from this template witness. -/
private theorem weth10CompilesZero :
    Prog.compiles (weth10 ⟨0, 0⟩) = true := by
  decide +kernel

private theorem weth10TemplateCode_compile_of_emit
    (h : (weth10 ⟨0, 0⟩).emitUnchecked = weth10TemplateCode) :
    Prog.compile (weth10 ⟨0, 0⟩) = some weth10TemplateCode := by
  have hc := Prog.compile_eq_some_getD_of_compiles
    (weth10 ⟨0, 0⟩) weth10CompilesZero
  exact hc.trans
    (congrArg some ((Prog.compile_eq_emitUnchecked hc).trans h))

private def weth10ZeroTable : List (Nat × Func) :=
  table 0 ((weth10 ⟨0, 0⟩).main :: (weth10 ⟨0, 0⟩).aux)

private theorem weth10ZeroTable_locations :
    weth10ZeroTable.map Prod.fst =
      [0, 4001, 4005, 4115, 4261, 4403, 4513, 4655,
       4801, 4911, 5021, 5167, 5277, 5387, 5395, 5433,
       5607, 5852, 5962, 6070] := by
  decide +kernel

private theorem boolReturn_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5396 boolReturn =
      (weth10TemplateCode.drop 5396).take 37 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem permitRecover_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 6071 permitRecover =
      (weth10TemplateCode.drop 6071).take 242 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem weth10Main_size : compsize (weth10Main ⟨0, 0⟩) = 4000 := by
  decide +kernel

private theorem weth10Aux_sizes :
    weth10Aux.map compsize = [3, 109, 145, 141, 109, 141, 145, 109, 109, 145, 109, 109, 7, 37, 173, 244, 109, 107, 242] := by
  decide +kernel

private theorem revert_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4002 Func.revert =
      (weth10TemplateCode.drop 4002).take 3 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem flashTokenError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4006 flashTokenError =
      (weth10TemplateCode.drop 4006).take 109 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem individualLimitError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4116 individualLimitError =
      (weth10TemplateCode.drop 4116).take 145 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem totalLimitError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4262 totalLimitError =
      (weth10TemplateCode.drop 4262).take 141 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem flashFailedError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4404 flashFailedError =
      (weth10TemplateCode.drop 4404).take 109 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem allowanceError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4514 allowanceError =
      (weth10TemplateCode.drop 4514).take 141 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem burnBalanceError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4656 burnBalanceError =
      (weth10TemplateCode.drop 4656).take 145 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem expiredPermitError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4802 expiredPermitError =
      (weth10TemplateCode.drop 4802).take 109 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem invalidPermitError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 4912 invalidPermitError =
      (weth10TemplateCode.drop 4912).take 109 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem transferBalanceError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5022 transferBalanceError =
      (weth10TemplateCode.drop 5022).take 145 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem ethTransferError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5168 ethTransferError =
      (weth10TemplateCode.drop 5168).take 109 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem etherTransferError_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5278 etherTransferError =
      (weth10TemplateCode.drop 5278).take 109 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem bubbleRevert_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5388 bubbleRevert =
      (weth10TemplateCode.drop 5388).take 7 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem flashSettle_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5434 flashSettle =
      (weth10TemplateCode.drop 5434).take 173 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem transferFromCore_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5608 transferFromCore =
      (weth10TemplateCode.drop 5608).take 244 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem withdrawFromCore_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5853 withdrawFromCore =
      (weth10TemplateCode.drop 5853).take 109 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem flashBurn_emit_zero :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 5963 flashBurn =
      (weth10TemplateCode.drop 5963).take 107 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem weth10ZeroTable_eq :
    weth10ZeroTable =
      [(0, weth10Main ⟨0, 0⟩),
      (4001, Func.revert),
      (4005, flashTokenError),
      (4115, individualLimitError),
      (4261, totalLimitError),
      (4403, flashFailedError),
      (4513, allowanceError),
      (4655, burnBalanceError),
      (4801, expiredPermitError),
      (4911, invalidPermitError),
      (5021, transferBalanceError),
      (5167, ethTransferError),
      (5277, etherTransferError),
      (5387, bubbleRevert),
      (5395, boolReturn),
      (5433, flashSettle),
      (5607, transferFromCore),
      (5852, withdrawFromCore),
      (5962, flashBurn),
      (6070, permitRecover)] := by
  have hs := weth10Aux_sizes
  simp only [weth10Aux, List.map_cons, List.map_nil, List.cons.injEq] at hs
  rcases hs with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    h12, h13, h14, h15, h16, h17, h18, _⟩
  simp only [weth10ZeroTable, weth10, weth10Aux, table, weth10Main_size,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17, Nat.reduceAdd]

private def weth10TreeSlice (fuel start count : Nat) : DispatchTree :=
  DispatchTree.build fuel (((weth10Funcs ⟨0, 0⟩).drop start).take count)

private theorem weth10Tree_quarters :
    weth10Tree ⟨0, 0⟩ =
      .fork (.fork (weth10TreeSlice 25 0 7) (weth10TreeSlice 25 7 7))
        (.fork (weth10TreeSlice 25 14 7) (weth10TreeSlice 25 21 6)) := by
  rfl

private theorem dispatch0_7_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 3112
      (dispatchWith fallbackSlot (weth10TreeSlice 25 0 7)) =
      (weth10TemplateCode.drop 3112).take 839 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem dispatch7_7_size :
    compsize (dispatchWith fallbackSlot (weth10TreeSlice 25 7 7)) = 1307 := by
  decide +kernel

private theorem dispatch7_7_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 1804
      (dispatchWith fallbackSlot (weth10TreeSlice 25 7 7)) =
      (weth10TemplateCode.drop 1804).take 1307 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem dispatch14_7_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 970
      (dispatchWith fallbackSlot (weth10TreeSlice 25 14 7)) =
      (weth10TemplateCode.drop 970).take 822 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem dispatch21_6_size :
    compsize (dispatchWith fallbackSlot (weth10TreeSlice 25 21 6)) = 935 := by
  decide +kernel

private theorem dispatch21_6_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 34
      (dispatchWith fallbackSlot (weth10TreeSlice 25 21 6)) =
      (weth10TemplateCode.drop 34).take 935 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem dispatchLeft_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 1793
      (dispatchWith fallbackSlot
        (.fork (weth10TreeSlice 25 0 7) (weth10TreeSlice 25 7 7))) =
      (weth10TemplateCode.drop 1793).take 2158 := by
  rw [dispatchWith, Func.emitUnchecked, Func.emitUnchecked,
    Func.emitUnchecked, Func.emitUnchecked]
  have hp : (pushB256 (leftmostFsig (weth10TreeSlice 25 7 7))).size = 5 := by
    decide +kernel
  rw [hp]
  simp only [Ninst.size, dispatch7_7_size, Nat.reduceAdd]
  rw [dispatch7_7_emit, dispatch0_7_emit]
  decide +kernel

private theorem dispatchRight_size :
    compsize (dispatchWith fallbackSlot
      (.fork (weth10TreeSlice 25 14 7) (weth10TreeSlice 25 21 6))) = 1769 := by
  decide +kernel

private theorem dispatchRight_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 23
      (dispatchWith fallbackSlot
        (.fork (weth10TreeSlice 25 14 7) (weth10TreeSlice 25 21 6))) =
      (weth10TemplateCode.drop 23).take 1769 := by
  rw [dispatchWith, Func.emitUnchecked, Func.emitUnchecked,
    Func.emitUnchecked, Func.emitUnchecked]
  have hp : (pushB256 (leftmostFsig (weth10TreeSlice 25 21 6))).size = 5 := by
    decide +kernel
  rw [hp]
  simp only [Ninst.size, dispatch21_6_size, Nat.reduceAdd]
  rw [dispatch21_6_emit, dispatch14_7_emit]
  decide +kernel

private theorem dispatchFull_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 12
      (dispatchWith fallbackSlot (weth10Tree ⟨0, 0⟩)) =
      (weth10TemplateCode.drop 12).take 3939 := by
  rw [weth10Tree_quarters, dispatchWith, Func.emitUnchecked, Func.emitUnchecked,
    Func.emitUnchecked, Func.emitUnchecked]
  have hp : (pushB256 (leftmostFsig (.fork (weth10TreeSlice 25 14 7) (weth10TreeSlice 25 21 6)))).size = 5 := by
    decide +kernel
  rw [hp]
  simp only [Ninst.size, dispatchRight_size, Nat.reduceAdd]
  rw [dispatchRight_emit, dispatchLeft_emit]
  decide +kernel

private theorem receiveEther_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 3952 receiveEther =
      (weth10TemplateCode.drop 3952).take 49 := by
  rw [weth10ZeroTable_locations]
  decide +kernel

private theorem dispatchPrefixed_size :
    compsize (fsig +++ dispatchWith fallbackSlot (weth10Tree ⟨0, 0⟩)) = 3944 := by
  decide +kernel

private theorem dispatchPrefixed_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 7
      (fsig +++ dispatchWith fallbackSlot (weth10Tree ⟨0, 0⟩)) =
      (weth10TemplateCode.drop 7).take 3944 := by
  change ([0x5f, 0x35, 0x60, 0xe0, 0x1c] : Bytes) ++
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 12
      (dispatchWith fallbackSlot (weth10Tree ⟨0, 0⟩)) = _
  rw [dispatchFull_emit]
  decide +kernel

private theorem weth10Main_emit :
    Func.emitUnchecked (weth10ZeroTable.map Prod.fst) 1 (weth10Main ⟨0, 0⟩) =
      (weth10TemplateCode.drop 1).take 4000 := by
  rw [weth10Main, Func.emitUnchecked, Func.emitUnchecked, Func.emitUnchecked]
  simp only [Ninst.size, dispatchPrefixed_size, Nat.reduceAdd]
  rw [dispatchPrefixed_emit, receiveEther_emit]
  decide +kernel

private theorem template_join_19 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 6071).take 242) ++
      weth10TemplateCode.drop 6313 = weth10TemplateCode.drop 6070 := by
  have hj : (weth10TemplateCode.drop 6071).take 242 ++
      weth10TemplateCode.drop 6313 = weth10TemplateCode.drop 6071 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 242 (weth10TemplateCode.drop 6071)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 6070).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 6070)

private theorem template_join_18 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5963).take 107) ++
      weth10TemplateCode.drop 6070 = weth10TemplateCode.drop 5962 := by
  have hj : (weth10TemplateCode.drop 5963).take 107 ++
      weth10TemplateCode.drop 6070 = weth10TemplateCode.drop 5963 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 107 (weth10TemplateCode.drop 5963)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5962).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5962)

private theorem template_join_17 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5853).take 109) ++
      weth10TemplateCode.drop 5962 = weth10TemplateCode.drop 5852 := by
  have hj : (weth10TemplateCode.drop 5853).take 109 ++
      weth10TemplateCode.drop 5962 = weth10TemplateCode.drop 5853 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (weth10TemplateCode.drop 5853)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5852).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5852)

private theorem template_join_16 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5608).take 244) ++
      weth10TemplateCode.drop 5852 = weth10TemplateCode.drop 5607 := by
  have hj : (weth10TemplateCode.drop 5608).take 244 ++
      weth10TemplateCode.drop 5852 = weth10TemplateCode.drop 5608 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 244 (weth10TemplateCode.drop 5608)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5607).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5607)

private theorem template_join_15 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5434).take 173) ++
      weth10TemplateCode.drop 5607 = weth10TemplateCode.drop 5433 := by
  have hj : (weth10TemplateCode.drop 5434).take 173 ++
      weth10TemplateCode.drop 5607 = weth10TemplateCode.drop 5434 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 173 (weth10TemplateCode.drop 5434)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5433).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5433)

private theorem template_join_14 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5396).take 37) ++
      weth10TemplateCode.drop 5433 = weth10TemplateCode.drop 5395 := by
  have hj : (weth10TemplateCode.drop 5396).take 37 ++
      weth10TemplateCode.drop 5433 = weth10TemplateCode.drop 5396 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 37 (weth10TemplateCode.drop 5396)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5395).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5395)

private theorem template_join_13 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5388).take 7) ++
      weth10TemplateCode.drop 5395 = weth10TemplateCode.drop 5387 := by
  have hj : (weth10TemplateCode.drop 5388).take 7 ++
      weth10TemplateCode.drop 5395 = weth10TemplateCode.drop 5388 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 7 (weth10TemplateCode.drop 5388)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5387).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5387)

private theorem template_join_12 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5278).take 109) ++
      weth10TemplateCode.drop 5387 = weth10TemplateCode.drop 5277 := by
  have hj : (weth10TemplateCode.drop 5278).take 109 ++
      weth10TemplateCode.drop 5387 = weth10TemplateCode.drop 5278 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (weth10TemplateCode.drop 5278)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5277).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5277)

private theorem template_join_11 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5168).take 109) ++
      weth10TemplateCode.drop 5277 = weth10TemplateCode.drop 5167 := by
  have hj : (weth10TemplateCode.drop 5168).take 109 ++
      weth10TemplateCode.drop 5277 = weth10TemplateCode.drop 5168 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (weth10TemplateCode.drop 5168)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5167).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5167)

private theorem template_join_10 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 5022).take 145) ++
      weth10TemplateCode.drop 5167 = weth10TemplateCode.drop 5021 := by
  have hj : (weth10TemplateCode.drop 5022).take 145 ++
      weth10TemplateCode.drop 5167 = weth10TemplateCode.drop 5022 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 145 (weth10TemplateCode.drop 5022)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 5021).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 5021)

private theorem template_join_9 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4912).take 109) ++
      weth10TemplateCode.drop 5021 = weth10TemplateCode.drop 4911 := by
  have hj : (weth10TemplateCode.drop 4912).take 109 ++
      weth10TemplateCode.drop 5021 = weth10TemplateCode.drop 4912 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (weth10TemplateCode.drop 4912)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4911).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4911)

private theorem template_join_8 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4802).take 109) ++
      weth10TemplateCode.drop 4911 = weth10TemplateCode.drop 4801 := by
  have hj : (weth10TemplateCode.drop 4802).take 109 ++
      weth10TemplateCode.drop 4911 = weth10TemplateCode.drop 4802 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (weth10TemplateCode.drop 4802)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4801).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4801)

private theorem template_join_7 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4656).take 145) ++
      weth10TemplateCode.drop 4801 = weth10TemplateCode.drop 4655 := by
  have hj : (weth10TemplateCode.drop 4656).take 145 ++
      weth10TemplateCode.drop 4801 = weth10TemplateCode.drop 4656 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 145 (weth10TemplateCode.drop 4656)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4655).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4655)

private theorem template_join_6 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4514).take 141) ++
      weth10TemplateCode.drop 4655 = weth10TemplateCode.drop 4513 := by
  have hj : (weth10TemplateCode.drop 4514).take 141 ++
      weth10TemplateCode.drop 4655 = weth10TemplateCode.drop 4514 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 141 (weth10TemplateCode.drop 4514)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4513).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4513)

private theorem template_join_5 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4404).take 109) ++
      weth10TemplateCode.drop 4513 = weth10TemplateCode.drop 4403 := by
  have hj : (weth10TemplateCode.drop 4404).take 109 ++
      weth10TemplateCode.drop 4513 = weth10TemplateCode.drop 4404 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (weth10TemplateCode.drop 4404)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4403).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4403)

private theorem template_join_4 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4262).take 141) ++
      weth10TemplateCode.drop 4403 = weth10TemplateCode.drop 4261 := by
  have hj : (weth10TemplateCode.drop 4262).take 141 ++
      weth10TemplateCode.drop 4403 = weth10TemplateCode.drop 4262 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 141 (weth10TemplateCode.drop 4262)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4261).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4261)

private theorem template_join_3 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4116).take 145) ++
      weth10TemplateCode.drop 4261 = weth10TemplateCode.drop 4115 := by
  have hj : (weth10TemplateCode.drop 4116).take 145 ++
      weth10TemplateCode.drop 4261 = weth10TemplateCode.drop 4116 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 145 (weth10TemplateCode.drop 4116)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4115).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4115)

private theorem template_join_2 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4006).take 109) ++
      weth10TemplateCode.drop 4115 = weth10TemplateCode.drop 4005 := by
  have hj : (weth10TemplateCode.drop 4006).take 109 ++
      weth10TemplateCode.drop 4115 = weth10TemplateCode.drop 4006 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (weth10TemplateCode.drop 4006)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4005).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4005)

private theorem template_join_1 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 4002).take 3) ++
      weth10TemplateCode.drop 4005 = weth10TemplateCode.drop 4001 := by
  have hj : (weth10TemplateCode.drop 4002).take 3 ++
      weth10TemplateCode.drop 4005 = weth10TemplateCode.drop 4002 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 3 (weth10TemplateCode.drop 4002)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 4001).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 4001)

private theorem template_join_0 :
    ((0x5b : UInt8) :: (weth10TemplateCode.drop 1).take 4000) ++
      weth10TemplateCode.drop 4001 = weth10TemplateCode.drop 0 := by
  have hj : (weth10TemplateCode.drop 1).take 4000 ++
      weth10TemplateCode.drop 4001 = weth10TemplateCode.drop 1 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4000 (weth10TemplateCode.drop 1)
  rw [List.cons_append, hj]
  have hm : (weth10TemplateCode.drop 0).take 1 = [(0x5b : UInt8)] := by
    decide +kernel
  simpa only [hm, List.drop_drop, Nat.reduceAdd, List.cons_append, List.nil_append]
    using List.take_append_drop 1 (weth10TemplateCode.drop 0)

private theorem weth10TemplateCode_emit :
    (weth10 ⟨0, 0⟩).emitUnchecked = weth10TemplateCode := by
  change Table.emitUnchecked (weth10ZeroTable.map Prod.fst) weth10ZeroTable = _
  conv_lhs => arg 2; rw [weth10ZeroTable_eq]
  simp only [Table.emitUnchecked, Nat.reduceAdd]
  rw [weth10Main_emit,
    revert_emit_zero,
    flashTokenError_emit_zero,
    individualLimitError_emit_zero,
    totalLimitError_emit_zero,
    flashFailedError_emit_zero,
    allowanceError_emit_zero,
    burnBalanceError_emit_zero,
    expiredPermitError_emit_zero,
    invalidPermitError_emit_zero,
    transferBalanceError_emit_zero,
    ethTransferError_emit_zero,
    etherTransferError_emit_zero,
    bubbleRevert_emit_zero,
    boolReturn_emit_zero,
    flashSettle_emit_zero,
    transferFromCore_emit_zero,
    withdrawFromCore_emit_zero,
    flashBurn_emit_zero,
    permitRecover_emit_zero]
  have hmarker : Jinst.jumpdest.toUInt8 = (0x5b : UInt8) := by decide +kernel
  simp only [hmarker]
  have he : weth10TemplateCode.drop 6313 = [] := by decide +kernel
  rw [← he]
  rw [template_join_19,
    template_join_18,
    template_join_17,
    template_join_16,
    template_join_15,
    template_join_14,
    template_join_13,
    template_join_12,
    template_join_11,
    template_join_10,
    template_join_9,
    template_join_8,
    template_join_7,
    template_join_6,
    template_join_5,
    template_join_4,
    template_join_3,
    template_join_2,
    template_join_1,
    template_join_0]
  rfl

theorem weth10TemplateCode_compile :
    Prog.compile (weth10 ⟨0, 0⟩) = some weth10TemplateCode := by
  exact weth10TemplateCode_compile_of_emit weth10TemplateCode_emit

/-- Fixed-width deployment words do not affect compiler success. -/
theorem weth10_compiles (dp : DeployParams) :
    Prog.compiles (weth10 dp) = true := by
  rw [Prog.compiles_eq_of_compileShape (weth10_compileShape_eq dp)]
  exact weth10CompilesZero

end Weth10

end Blanc
