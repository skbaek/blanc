import Blanc.ProxyPairOssifiableProgram

/-!
# Lido OssifiableProxy creation-template baseline

The compiled `Prog` in this module is the executable prefix of a complete
creation input.  The full image is

`creationBaselineBytes ++ runtimeBaselineBytes ++ constructorArgs`.

Constructor arguments are therefore decoded with `CODECOPY`, not calldata
instructions.  The source order is the one fixed by Solidity inheritance:
`ERC1967Proxy` validates and installs the implementation, emits `Upgraded`, and
optionally runs setup; only after setup returns does `OssifiableProxy` read the
admin slot, emit `AdminChanged`, validate the requested admin, and store it.

No deployment execution theorem is owned here.  Later proof modules can use
the generic appended-code and CREATE-message infrastructure without making
this executable owner depend on another contract family.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Private table coordinates and memory layout -/

private def constructorEmptyRevertSlot : Nat := 1
private def constructorNoCodeImplementationErrorSlot : Nat := 2
private def constructorEmptyDelegatecallErrorSlot : Nat := 3
private def constructorZeroAdminErrorSlot : Nat := 4
private def constructorAfterSetupSlot : Nat := 5
private def constructorDelegateSetupSlot : Nat := 6
private def constructorAllocationPanicSlot : Nat := 7

private def constructorImplementationWord : B256 := 0
private def constructorRequestedAdminWord : B256 := 1
private def constructorDataOffsetWord : B256 := 2
private def constructorDataPointerWord : B256 := 3
private def constructorDataLengthWord : B256 := 4
private def constructorPreviousAdminWord : B256 := 5
private def constructorEventAdminWord : B256 := 6

/-- Setup bytes begin above every scalar/event scratch word. -/
private def constructorSetupMemoryBase : B256 := 0x100

private def constructorAbiMaxUint64 : B256 := 0xffffffffffffffff

private def constructorLoadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

private def constructorCleanAddressWord : Line :=
  pushAddressMask ++ [Ninst.not, Ninst.and]

/-- Layout coordinates are emitted at a fixed width.  The provisional and final
constructor passes therefore have identical compiler shape even though their
embedded offsets differ. -/
private def pushCreationCoordinate (value : Nat) : Ninst :=
  Ninst.push (Nat.toB256 value).toBytes (by rw [B256.length_toBytes])

/-! ## Strict appended-argument decoder -/

/-- Decode appended `(address,address,bytes)` constructor arguments.

The offset is relative to the first constructor head byte.  Solidity 0.8.9
accepts noncanonical and unaligned in-bounds offsets, as well as trailing code
bytes.  It rejects dirty address heads, offsets or lengths above `uint64.max`,
an incomplete dynamic length word, and a payload extending past `CODESIZE`.
Only the declared payload bytes are copied; ABI padding is not delegated.
-/
private def decodeConstructorArguments (argsOffset : Nat) (body : Func) : Func :=
  -- A complete three-word head must be appended after the runtime.
  pushCreationCoordinate (argsOffset + 96) ::: codesize ::: lt :::
  ((.call constructorEmptyRevertSlot) <?>
    (pushB256 96 ::: pushCreationCoordinate argsOffset ::: pushB256 0 :::
       codecopy :::
     -- implementation_ and admin_ are strict Solidity address words.
     constructorLoadWord constructorImplementationWord +++ checkNonAddress +++
     ((.call constructorEmptyRevertSlot) <?>
       (constructorLoadWord constructorRequestedAdminWord +++ checkNonAddress +++
        ((.call constructorEmptyRevertSlot) <?>
          (-- Dynamic offsets follow Solidity's uint64-bounded decoder path.
           pushB256 constructorAbiMaxUint64 :::
             constructorLoadWord constructorDataOffsetWord +++ gt :::
           ((.call constructorEmptyRevertSlot) <?>
             (constructorLoadWord constructorDataOffsetWord +++
                pushCreationCoordinate argsOffset ::: add :::
                mstoreAt constructorDataPointerWord +++
              -- The dynamic length word must be complete.
              constructorLoadWord constructorDataPointerWord +++ pushB256 32 :::
                add ::: codesize ::: lt :::
              ((.call constructorEmptyRevertSlot) <?>
                (pushB256 32 :::
                   constructorLoadWord constructorDataPointerWord +++
                   pushB256 (constructorDataLengthWord * 32) ::: codecopy :::
                 pushB256 constructorAbiMaxUint64 :::
                   constructorLoadWord constructorDataLengthWord +++ gt :::
                 ((.call constructorAllocationPanicSlot) <?>
                   (-- Require every declared payload byte; trailing bytes pass.
                    constructorLoadWord constructorDataPointerWord +++
                      pushB256 32 ::: add :::
                      constructorLoadWord constructorDataLengthWord +++ add :::
                      codesize ::: lt :::
                    ((.call constructorEmptyRevertSlot) <?>
                      (constructorLoadWord constructorDataLengthWord +++
                       constructorLoadWord constructorDataPointerWord +++
                         pushB256 32 ::: add :::
                       pushB256 constructorSetupMemoryBase ::: codecopy :::
                       body))))))))))))))

/-! ## Exact source-order constructor bodies -/

private def constructorNoCodeImplementationError : Func :=
  Func.revData noCodeImplementationErrorData

private def constructorEmptyDelegatecallError : Func :=
  Func.revData emptyDelegatecallErrorData

private def constructorZeroAdminError : Func :=
  Func.revData zeroAdminErrorData

private def constructorAllocationPanic : Func :=
  Func.revData allocationPanicData

/-- Continue after optional setup.  The previous admin is read here rather than
before the delegatecall, so setup may mutate either ERC-1967 slot exactly as it
can in the Solidity constructor. -/
private def constructorAfterSetup
    (runtimeOffset runtimeLength : Nat) : Func :=
  [pushB256 adminSlotLit, sload] +++ constructorCleanAddressWord +++
    mstoreAt constructorPreviousAdminWord +++
  constructorLoadWord constructorRequestedAdminWord +++
    mstoreAt constructorEventAdminWord +++
  pushB256 adminChangedEventTopic :::
    logWith 0 constructorPreviousAdminWord 2 +++
  -- `_changeAdmin` emits before `_setAdmin` rejects the zero address.
  constructorLoadWord constructorRequestedAdminWord +++ iszero :::
  ((.call constructorZeroAdminErrorSlot) <?>
    (constructorLoadWord constructorRequestedAdminWord +++
       storeAddressWordAt adminSlotLit +++
     -- Return the exact already-compiled runtime appended after this prefix.
     pushCreationCoordinate runtimeLength :::
       pushCreationCoordinate runtimeOffset ::: pushB256 0 ::: codecopy :::
     pushCreationCoordinate runtimeLength ::: pushB256 0 ::: Func.ret))

/-- Delegate the exact decoded setup bytes.  Successful returndata is discarded;
failed nonempty returndata bubbles verbatim, while an empty failure receives the
inherited OpenZeppelin fallback string. -/
private def constructorDelegateSetup : Func :=
  pushB256 0 :::
  pushB256 0 :::
  constructorLoadWord constructorDataLengthWord +++
  pushB256 constructorSetupMemoryBase :::
  constructorLoadWord constructorImplementationWord +++
  gas :::
  delcall :::
  ((.call constructorAfterSetupSlot) <?>
    (retdatasize :::
      (Func.revReturnData <?>
        (.call constructorEmptyDelegatecallErrorSlot))))

/-- `_upgradeToAndCall(implementation_, data_, false)`: validate code, store,
emit `Upgraded`, and skip setup exactly when the decoded byte length is zero. -/
private def constructorInitializeImplementation : Func :=
  constructorLoadWord constructorImplementationWord +++
    dup 0 ::: extcodesize ::: iszero :::
  ((.call constructorNoCodeImplementationErrorSlot) <?>
    (dup 0 ::: storeAddressWordAt implementationSlotLit +++
     pushB256 upgradedEventTopic ::: logWith 1 0 0 +++
     constructorLoadWord constructorDataLengthWord +++
     ((.call constructorDelegateSetupSlot) <?>
       (.call constructorAfterSetupSlot))))

private def constructorProgram
    (runtimeOffset argsOffset runtimeLength : Nat) : Prog :=
  { main :=
      callvalue ::: iszero :::
        (decodeConstructorArguments argsOffset
          constructorInitializeImplementation <?>
          (.call constructorEmptyRevertSlot))
    aux :=
      [ Func.rev,
        constructorNoCodeImplementationError,
        constructorEmptyDelegatecallError,
        constructorZeroAdminError,
        constructorAfterSetup runtimeOffset runtimeLength,
        constructorDelegateSetup,
        constructorAllocationPanic ] }

/-! ## Two-pass executable layout and compiler artifact -/

/-- The first pass determines the prefix length.  Fixed-width coordinate pushes
make that length independent of the provisional embedded offsets. -/
private def provisionalCreationBaselineBytes : Bytes :=
  (Prog.compile
    (constructorProgram 0 0 runtimeBaselineBytes.length)).getD []

/-- Compiler-derived location at which `runtimeBaselineBytes` begins. -/
def creationBaselineByteLength : Nat :=
  provisionalCreationBaselineBytes.length

/-- Exact constructor `Prog` whose code is the creation-template prefix. -/
def creationBaseline : Prog :=
  constructorProgram creationBaselineByteLength
    (creationBaselineByteLength + runtimeBaselineBytes.length)
    runtimeBaselineBytes.length

def creationBaselineBytes : Bytes :=
  (Prog.compile creationBaseline).getD []

def creationBaselineCode : ByteArray :=
  ByteArray.mk creationBaselineBytes.toArray

theorem creationBaseline_compiles : creationBaseline.compiles = true := by
  decide +kernel

theorem creationBaseline_compile :
    Prog.compile creationBaseline = some creationBaselineBytes :=
  Prog.compile_eq_some_getD_of_compiles _ creationBaseline_compiles

/-- Exact two-pass fixed point and compiled-prefix length witness. -/
theorem creationBaselineBytes_length :
    creationBaselineBytes.length = creationBaselineByteLength := by
  decide +kernel

/-! ## Product-owned constructor proof surface

The executable helpers above stay private implementation details.  These thin
aliases are the deliberately small public surface used by the constructor
proof: they name phase boundaries without duplicating the constructor or
exporting its scratch-table implementation as general Blanc vocabulary. -/

/-- The exact function table used by creation-code phase proofs. -/
def ossifiableConstructorFunctions
    (runtimeOffset runtimeLength : Nat) : List Func :=
  (constructorProgram runtimeOffset
      (runtimeOffset + runtimeLength) runtimeLength).main ::
    (constructorProgram runtimeOffset
      (runtimeOffset + runtimeLength) runtimeLength).aux

/-- Strict appended-argument decoding followed by `body`. -/
def ossifiableConstructorDecode (argsOffset : Nat) (body : Func) : Func :=
  decodeConstructorArguments argsOffset body

/-- Implementation validation/write/`Upgraded`, including the setup split. -/
def ossifiableConstructorInitializeImplementation : Func :=
  constructorInitializeImplementation

/-- Nonempty setup delegatecall and failure normalization. -/
def ossifiableConstructorDelegateSetup : Func :=
  constructorDelegateSetup

/-- Post-setup admin read/log/check/write and runtime return. -/
def ossifiableConstructorAfterSetup
    (runtimeOffset runtimeLength : Nat) : Func :=
  constructorAfterSetup runtimeOffset runtimeLength

/-- The complete constructor program with named proof-facing coordinates. -/
def ossifiableConstructorProgram
    (runtimeOffset argsOffset runtimeLength : Nat) : Prog :=
  constructorProgram runtimeOffset argsOffset runtimeLength

/-- Fixed-width creation-coordinate push used by the constructor compiler. -/
def ossifiablePushCreationCoordinate (value : Nat) : Ninst :=
  pushCreationCoordinate value

@[simp] theorem ossifiablePushCreationCoordinate_shape (value : Nat) :
    ossifiablePushCreationCoordinate value =
      Ninst.push (Nat.toB256 value).toBytes (by rw [B256.length_toBytes]) := by
  rfl

@[simp] theorem ossifiableConstructorAfterSetupSlot_eq :
    constructorAfterSetupSlot = 5 := rfl

@[simp] theorem ossifiableConstructorDelegateSetupSlot_eq :
    constructorDelegateSetupSlot = 6 := rfl

@[simp] theorem ossifiableConstructorZeroAdminErrorSlot_eq :
    constructorZeroAdminErrorSlot = 4 := rfl

@[simp] theorem ossifiableConstructorFunctions_emptyRevert
    (runtimeOffset runtimeLength : Nat) :
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)[1]? =
      some Func.rev := by
  rfl

@[simp] theorem ossifiableConstructorFunctions_noCode
    (runtimeOffset runtimeLength : Nat) :
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)[2]? =
      some (Func.revData noCodeImplementationErrorData) := by
  rfl

@[simp] theorem ossifiableConstructorFunctions_emptyDelegatecall
    (runtimeOffset runtimeLength : Nat) :
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)[3]? =
      some (Func.revData emptyDelegatecallErrorData) := by
  rfl

@[simp] theorem ossifiableConstructorFunctions_zeroAdmin
    (runtimeOffset runtimeLength : Nat) :
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)[4]? =
      some (Func.revData zeroAdminErrorData) := by
  rfl

@[simp] theorem ossifiableConstructorFunctions_afterSetup
    (runtimeOffset runtimeLength : Nat) :
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)[5]? =
      some (ossifiableConstructorAfterSetup runtimeOffset runtimeLength) := by
  rfl

@[simp] theorem ossifiableConstructorFunctions_delegateSetup
    (runtimeOffset runtimeLength : Nat) :
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)[6]? =
      some ossifiableConstructorDelegateSetup := by
  rfl

@[simp] theorem ossifiableConstructorFunctions_allocationPanic
    (runtimeOffset runtimeLength : Nat) :
    (ossifiableConstructorFunctions runtimeOffset runtimeLength)[7]? =
      some (Func.revData allocationPanicData) := by
  rfl

theorem ossifiableConstructorInitializeImplementation_shape :
    ossifiableConstructorInitializeImplementation =
      [pushB256 0, mload] +++
        dup 0 ::: extcodesize ::: iszero :::
        ((.call 2) <?>
          (dup 0 ::: storeAddressWordAt implementationSlotLit +++
            pushB256 upgradedEventTopic ::: logWith 1 0 0 +++
            [pushB256 128, mload] +++
            ((.call 6) <?> (.call 5)))) := by
  rfl

theorem ossifiableConstructorDelegateSetup_shape :
    ossifiableConstructorDelegateSetup =
      pushB256 0 :::
        pushB256 0 :::
        [pushB256 128, mload] +++
        pushB256 0x100 :::
        [pushB256 0, mload] +++
        gas :::
        delcall :::
        ((.call 5) <?>
          (retdatasize :::
            (Func.revReturnData <?> (.call 3)))) := by
  rfl

theorem ossifiableConstructorAfterSetup_shape
    (runtimeOffset runtimeLength : Nat) :
    ossifiableConstructorAfterSetup runtimeOffset runtimeLength =
      [pushB256 adminSlotLit, sload] +++
        (pushAddressMask +++
          (Ninst.not ::: Ninst.and :::
            mstoreAt 5 +++
            [pushB256 32, mload] +++ mstoreAt 6 +++
            pushB256 adminChangedEventTopic ::: logWith 0 5 2 +++
            [pushB256 32, mload] +++ iszero :::
            ((.call 4) <?>
              ([pushB256 32, mload] +++
                storeAddressWordAt adminSlotLit +++
                ossifiablePushCreationCoordinate runtimeLength :::
                  ossifiablePushCreationCoordinate runtimeOffset :::
                  pushB256 0 ::: codecopy :::
                ossifiablePushCreationCoordinate runtimeLength :::
                  pushB256 0 ::: Func.ret)))) := by
  rfl

theorem creationBaseline_eq_constructorProgram :
    creationBaseline =
      ossifiableConstructorProgram creationBaselineByteLength
        (creationBaselineByteLength + runtimeBaselineBytes.length)
        runtimeBaselineBytes.length := by
  rfl

theorem ossifiableConstructorProgram_main_shape
    (runtimeOffset argsOffset runtimeLength : Nat) :
    (ossifiableConstructorProgram runtimeOffset argsOffset runtimeLength).main =
      callvalue ::: iszero :::
        (ossifiableConstructorDecode argsOffset
          ossifiableConstructorInitializeImplementation <?> (.call 1)) := by
  rfl

/-! ## Complete creation-input helpers -/

/-- Prefix plus the exact runtime returned by a successful constructor. -/
def ossifiableCreationTemplate : Bytes :=
  creationBaselineBytes ++ runtimeBaselineBytes

/-- Canonical ABI tuple `(implementation_, admin_, data_)`, with the dynamic
tail at offset `0x60` from the constructor argument area's first byte. -/
def abiEncodeOssifiableConstructorArgs
    (implementation admin : Adr) (data : Bytes) : Bytes :=
  implementation.toB256.toBytes ++
    admin.toB256.toBytes ++
    (96 : B256).toBytes ++
    abiBytesTail data

def ossifiableFullCreateInput
    (implementation admin : Adr) (data : Bytes) : Bytes :=
  ossifiableCreationTemplate ++
    abiEncodeOssifiableConstructorArgs implementation admin data

/-- Canonical complete CREATE input for the empty-setup constructor tuple. -/
def ossifiableEmptyDataCreateInput
    (implementation admin : Adr) : Bytes :=
  ossifiableFullCreateInput implementation admin []

end Blanc.ProxyPair
