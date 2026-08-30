import Blanc.LinearDispatch
import Blanc.AddressSlot
import Blanc.ProxyPairOssifiableSurface
import Blanc.ProxyPairProgram

/-!
# Lido OssifiableProxy runtime baseline

This module is the executable, linear-dispatch baseline for the seven named
`OssifiableProxy` endpoints.  Selector misses, including empty calldata, enter
the same whole-calldata/whole-returndata forwarding body as the selector-free
proxy.  Each selector hit performs Solidity's nonpayable check before its ABI
decoder and endpoint body.

The module deliberately contains no constructor and no execution theorem.  Its
small decoder helpers are private and product-specific; the public surface is
the stable auxiliary layout, runtime program, and compiled artifact witness.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Stable auxiliary coordinates -/

def fallbackSlot : Nat := 1
def getAdminSlot : Nat := 2
def getImplementationSlot : Nat := 3
def getIsOssifiedSlot : Nat := 4
def ossifySlot : Nat := 5
def changeAdminSlot : Nat := 6
def upgradeToSlot : Nat := 7
def upgradeToAndCallSlot : Nat := 8
def emptyRevertSlot : Nat := 9
def notAdminErrorSlot : Nat := 10
def proxyIsOssifiedErrorSlot : Nat := 11
def zeroAdminErrorSlot : Nat := 12
def noCodeImplementationErrorSlot : Nat := 13
def emptyDelegatecallErrorSlot : Nat := 14
def allocationPanicSlot : Nat := 15

/-! ## Private scratch and ABI-decoder vocabulary -/

private def implementationWord : B256 := 0
private def setupLengthWord : B256 := 1
private def forceCallWord : B256 := 2
private def setupOffsetWord : B256 := 3

/-- The setup bytes are copied away from the four scratch words above. -/
private def setupMemoryBase : B256 := 0x80

private def abiMaxUint64 : B256 := 0xffffffffffffffff

private def loadScratchWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

/-- Canonicalize a word known to have an address in its low 160 bits. -/
private def cleanAddressWord : Line :=
  pushAddressMask ++ [Ninst.not, Ninst.and]

private def returnTopWord : Func :=
  mstoreAt 0 +++ returnMemoryRange 0 32

/-- Solidity-0.8.9 static-address decoding: a complete head is required, dirty
high bits revert empty, and arbitrary trailing calldata remains accepted. -/
private def decodeAddressArg0 (body : Func) : Func :=
  pushB256 36 ::: calldatasize ::: lt :::
  ((.call emptyRevertSlot) <?>
    (arg 0 +++ checkNonAddress +++
      ((.call emptyRevertSlot) <?> body)))

/-- Solidity-0.8.9 decoding for `(address,bytes,bool)`.

Offsets are relative to the first argument head byte (calldata byte four).
They need not be canonical or word aligned.  The decoder checks the three-word
head, the address and bool cleanups, the compiler's uint64 bounds for dynamic
offset and length, the complete length word, and every payload byte.  It does
not require canonical tail placement or reject trailing bytes.  The raw bytes
are copied to `setupMemoryBase`; ABI padding is not part of the delegated input.
-/
private def decodeUpgradeToAndCall (body : Func) : Func :=
  pushB256 100 ::: calldatasize ::: lt :::
  ((.call emptyRevertSlot) <?>
    (-- address head: reject dirty high bits, then retain the canonical word
     arg 0 +++ checkNonAddress +++
     ((.call emptyRevertSlot) <?>
       (arg 0 +++ mstoreAt implementationWord +++
        -- dynamic offset is compiler-bounded to uint64
        pushB256 abiMaxUint64 ::: arg 1 +++ gt :::
        ((.call emptyRevertSlot) <?>
          (arg 1 +++ mstoreAt setupOffsetWord +++
           -- byte 4 + offset must contain a complete length word
           loadScratchWord setupOffsetWord +++ pushB256 36 ::: add :::
             calldatasize ::: lt :::
           ((.call emptyRevertSlot) <?>
             (loadScratchWord setupOffsetWord +++ pushB256 4 ::: add :::
                calldataload ::: mstoreAt setupLengthWord +++
              -- dynamic length is compiler-bounded to uint64
              pushB256 abiMaxUint64 ::: loadScratchWord setupLengthWord +++
                gt :::
              ((.call allocationPanicSlot) <?>
                (-- require every payload byte, without requiring tail padding
                 loadScratchWord setupOffsetWord +++ pushB256 36 ::: add :::
                   loadScratchWord setupLengthWord +++ add :::
                   calldatasize ::: lt :::
                 ((.call emptyRevertSlot) <?>
                   (-- Match solc's decoder order: copy the declared payload
                    -- before validating the trailing bool head.
                    loadScratchWord setupLengthWord +++
                    loadScratchWord setupOffsetWord +++ pushB256 36 ::: add :::
                    pushB256 setupMemoryBase ::: calldatacopy :::
                    -- bool must be exactly zero or one
                    arg 2 +++ dup 0 ::: iszero ::: iszero ::: eq :::
                    ((arg 2 +++ mstoreAt forceCallWord +++ body) <?>
                      (.call emptyRevertSlot))))))))))))))

/-! ## Authorization and exact revert payloads -/

/-- Match the source modifier's precedence: an all-zero admin reports
`ProxyIsOssified`; only a live, different admin reports `NotAdmin`. -/
private def onlyActiveAdmin (body : Func) : Func :=
  [pushB256 adminSlotLit, sload] +++ cleanAddressWord +++
  (dup 0 ::: iszero :::
    ((.call proxyIsOssifiedErrorSlot) <?>
      (caller ::: eq :::
        (body <?> (.call notAdminErrorSlot)))))

def notAdminError : Func :=
  Func.revData notAdminErrorData

def proxyIsOssifiedError : Func :=
  Func.revData proxyIsOssifiedErrorData

def zeroAdminError : Func :=
  Func.revData zeroAdminErrorData

def noCodeImplementationError : Func :=
  Func.revData noCodeImplementationErrorData

def emptyDelegatecallError : Func :=
  Func.revData emptyDelegatecallErrorData

/-! ## Getter bodies -/

def getAdmin : Func :=
  [pushB256 adminSlotLit, sload] +++ cleanAddressWord +++ returnTopWord

def getImplementation : Func :=
  [pushB256 implementationSlotLit, sload] +++ cleanAddressWord +++ returnTopWord

def getIsOssified : Func :=
  [pushB256 adminSlotLit, sload] +++ cleanAddressWord +++
    (iszero ::: returnTopWord)

/-! ## Admin and implementation mutation bodies -/

/-- `_changeAdmin`: the source emits before `_setAdmin` performs its zero
check.  Ordinary revert settlement removes that raw log on the zero arm. -/
private def changeAdminBody : Func :=
  [pushB256 adminSlotLit, sload] +++ cleanAddressWord +++ mstoreAt 0 +++
  arg 0 +++ mstoreAt 1 +++
  pushB256 adminChangedEventTopic ::: logWith 0 0 2 +++
  arg 0 +++ iszero :::
  ((.call zeroAdminErrorSlot) <?>
    (arg 0 +++ storeAddressWordAt adminSlotLit +++ Func.stop))

def changeAdmin : Func :=
  decodeAddressArg0 (onlyActiveAdmin changeAdminBody)

/-- Store and announce a checked implementation, then run `continuation`.
The retained implementation word supplies both `SSTORE` and the indexed log,
so same-value upgrades still perform both source actions. -/
private def upgradeImplementation (continuation : Func) : Func :=
  arg 0 +++ dup 0 ::: extcodesize ::: iszero :::
  ((.call noCodeImplementationErrorSlot) <?>
    (dup 0 ::: storeAddressWordAt implementationSlotLit +++
     pushB256 upgradedEventTopic ::: logWith 1 0 0 +++
     continuation))

def upgradeTo : Func :=
  decodeAddressArg0 (onlyActiveAdmin (upgradeImplementation Func.stop))

/-- Delegate the exact decoded setup bytes.  A nonempty child failure bubbles
verbatim; an empty child failure uses OpenZeppelin's inherited fallback string.
Successful setup returndata is intentionally discarded by `STOP`. -/
private def delegateSetup : Func :=
  pushB256 0 :::
  pushB256 0 :::
  loadScratchWord setupLengthWord +++
  pushB256 setupMemoryBase :::
  loadScratchWord implementationWord +++
  gas :::
  delcall :::
  (Func.stop <?>
    (retdatasize :::
      (Func.revReturnData <?> (.call emptyDelegatecallErrorSlot))))

/-- Skip only when both the decoded byte length and `forceCall_` are zero. -/
private def afterUpgradeToAndCall : Func :=
  loadScratchWord setupLengthWord +++
  (delegateSetup <?>
    (loadScratchWord forceCallWord +++
      (delegateSetup <?> Func.stop)))

def upgradeToAndCall : Func :=
  decodeUpgradeToAndCall
    (onlyActiveAdmin (upgradeImplementation afterUpgradeToAndCall))

/-- Ossification writes zero directly, then emits the source-ordered pair of
events.  It intentionally does not call `_changeAdmin`, whose zero guard would
reject this terminal transition. -/
private def ossifyBody : Func :=
  [pushB256 adminSlotLit, sload] +++ cleanAddressWord +++ mstoreAt 0 +++
  pushB256 0 ::: storeAddressWordAt adminSlotLit +++
  pushB256 0 ::: mstoreAt 1 +++
  pushB256 adminChangedEventTopic ::: logWith 0 0 2 +++
  pushB256 proxyOssifiedEventTopic ::: logWith 0 0 0 +++
  Func.stop

def ossify : Func :=
  onlyActiveAdmin ossifyBody

/-! ## Linear dispatcher and compiler artifact -/

def runtimeBaselineEntries : List (B256 × Func) :=
  [ (proxyGetAdminSelector, nonpayable (.call getAdminSlot)),
    (proxyGetImplementationSelector, nonpayable (.call getImplementationSlot)),
    (proxyGetIsOssifiedSelector, nonpayable (.call getIsOssifiedSlot)),
    (proxyOssifySelector, nonpayable (.call ossifySlot)),
    (proxyChangeAdminSelector, nonpayable (.call changeAdminSlot)),
    (proxyUpgradeToSelector, nonpayable (.call upgradeToSlot)),
    (proxyUpgradeToAndCallSelector, nonpayable (.call upgradeToAndCallSlot)) ]

theorem runtimeBaselineEntries_selectors :
    runtimeBaselineEntries.map Prod.fst = runtimeSelectors := by
  rfl

def runtimeBaselineAux : List Func :=
  [ proxyFallback,
    getAdmin,
    getImplementation,
    getIsOssified,
    ossify,
    changeAdmin,
    upgradeTo,
    upgradeToAndCall,
    Func.rev,
    notAdminError,
    proxyIsOssifiedError,
    zeroAdminError,
    noCodeImplementationError,
    emptyDelegatecallError,
    Func.revData allocationPanicData ]

theorem runtimeBaselineAux_length : runtimeBaselineAux.length = 15 := by
  rfl

def runtimeBaselineMain : Func :=
  fsig +++ linearDispatchWith fallbackSlot runtimeBaselineEntries

def runtimeBaseline : Prog :=
  ⟨runtimeBaselineMain, runtimeBaselineAux⟩

def runtimeBaselineBytes : Bytes :=
  (Prog.compile runtimeBaseline).getD []

def runtimeBaselineCode : ByteArray :=
  ByteArray.mk runtimeBaselineBytes.toArray

theorem runtimeBaseline_compiles : runtimeBaseline.compiles = true := by
  decide +kernel

theorem runtimeBaseline_compile :
    Prog.compile runtimeBaseline = some runtimeBaselineBytes :=
  Prog.compile_eq_some_getD_of_compiles _ runtimeBaseline_compiles

/-- Exact structural byte length.  The reducible right-hand side evaluates to
the numeric artifact length without rebuilding compiler output. -/
def runtimeBaselineByteLength : Nat :=
  ((runtimeBaseline.main :: runtimeBaseline.aux).map
    fun f => 1 + compsize f).sum

theorem runtimeBaselineBytes_length :
    runtimeBaselineBytes.length = runtimeBaselineByteLength := by
  exact Prog.length_compile runtimeBaseline_compile

end Blanc.ProxyPair
