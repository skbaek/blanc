import Blanc.LidoTriggerableWithdrawalsGatewayCode

/-!
Creation artifact for the production Lido Triggerable Withdrawals Gateway
port.

The constructor decodes the complete five-word static ABI suffix, validates it
in Solidity source order, patches the compiler-derived locator words in the
parameter-neutral runtime, initializes the projected enumerable-admin and
exit-limit state, emits the two constructor events, and returns the patched
runtime.  These are identities of the Blanc family; they do not claim byte
identity with Solidity initcode or runtime.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway

structure ConstructorArgs where
  admin : B256
  locator : B256
  maxExitRequestsLimit : B256
  exitsPerFrame : B256
  frameDurationInSec : B256
deriving DecidableEq

def ConstructorArgs.toDeployParams (args : ConstructorArgs) : DeployParams :=
  ⟨args.locator⟩

def constructorArgumentBytes : Nat := 5 * 32
def eip3860InitcodeLimit : Nat := 49152

private def constructorRuntimeBase : Nat := constructorArgumentBytes

/-- Full-width layout words keep the provisional and final constructor passes
compiler-shape identical without silently truncating future large artifacts. -/
private def pushLayoutNat (value : Nat) : Ninst :=
  pushDeployWord (Nat.toB256 value)

private def loadArgumentIndex (index : Nat) : Line :=
  [pushDeployWord (Nat.toB256 (32 * index)), mload]

private def storeByteOffset (offset : Nat) : Line :=
  [pushDeployWord (Nat.toB256 offset), mstore]

private def constructorError (name : String) : Func :=
  Func.revSelector (customErrorData name) (by
    simp [customErrorData, B256.length_toBytes])

private def patchLocatorLine (runtimeBase : Nat) : Line :=
  locatorWordOffsets.flatMap fun offset =>
    loadArgumentIndex 1 ++ storeByteOffset (runtimeBase + offset)

private def initializeAdminRole : Line :=
  -- Memory words zero and one become the role/account key throughout this
  -- sequence; word two is the zero-based global enumeration index.
  [pushB256 defaultAdminRole] ++ mstoreAt 0 ++
  loadArgumentIndex 0 ++ mstoreAt 1 ++
  [pushB256 0] ++ mstoreAt 2 ++
  [pushB256 1] ++ roleKeyFromMemory roleLookupIndexRegion ++ [sstore] ++
  mloadWord 0 ++ roleKeyFromMemory roleLookupRoleRegion ++ [sstore] ++
  mloadWord 1 ++ roleKeyFromMemory roleLookupAccountRegion ++ [sstore] ++
  mloadWord 0 ++ enumKeyFromMemory enumRoleRegion ++ [sstore] ++
  mloadWord 1 ++ enumKeyFromMemory enumAccountRegion ++ [sstore] ++
  [pushB256 1, pushB256 roleRecordLengthSlot, sstore] ++
  emitRoleGranted

private def initializeExitRequestLimit : Line :=
  loadArgumentIndex 2 ++ [pushB256 maxExitRequestsLimitSlot, sstore] ++
  loadArgumentIndex 2 ++ [pushB256 prevExitRequestsLimitSlot, sstore] ++
  [timestamp, pushB256 (Nat.toB256 (2 ^ 32 - 1)), and,
    pushB256 prevTimestampSlot, sstore] ++
  loadArgumentIndex 4 ++ [pushB256 frameDurationInSecSlot, sstore] ++
  loadArgumentIndex 3 ++ [pushB256 exitsPerFrameSlot, sstore] ++
  loadArgumentIndex 2 ++ mstoreAt 2 ++
  loadArgumentIndex 3 ++ mstoreAt 3 ++
  loadArgumentIndex 4 ++ mstoreAt 4 ++
  [pushB256 (signatureHash "ExitRequestsLimitSet"
    [.uint256, .uint256, .uint256])] ++
  logWith 0 2 3

private def constructorBody
    (runtimeOffset argsOffset runtimeLength : Nat) : Func :=
  -- Solidity's static decoder requires the complete five-word head while
  -- accepting any trailing creation data.
  pushLayoutNat (argsOffset + constructorArgumentBytes) ::: codesize ::: lt :::
  ((.call 1) <?>
    (pushLayoutNat constructorArgumentBytes ::: pushLayoutNat argsOffset :::
      pushLayoutNat 0 ::: codecopy :::
      -- ABI address words are canonical before source-level checks.
      loadArgumentIndex 0 +++ checkNonAddress +++
      ((.call 1) <?>
        (loadArgumentIndex 1 +++ checkNonAddress +++
          ((.call 1) <?>
            (loadArgumentIndex 0 +++ iszero :::
              ((.call 2) <?>
                -- `_setExitRequestLimit` validations, in source order.
                ([pushB256 (Nat.toB256 (2 ^ 32 - 1))] ++
                    loadArgumentIndex 2 ++ [gt]) +++
                ((.call 3) <?>
                  (([pushB256 (Nat.toB256 (2 ^ 32 - 1))] ++
                      loadArgumentIndex 4 ++ [gt]) +++
                    ((.call 4) <?>
                      (loadArgumentIndex 2 ++ loadArgumentIndex 3 ++ [gt]) +++
                      ((.call 5) <?>
                        (loadArgumentIndex 4 +++ iszero :::
                          ((.call 6) <?>
                            (pushLayoutNat runtimeLength :::
                              pushLayoutNat runtimeOffset :::
                              pushLayoutNat constructorRuntimeBase :::
                              codecopy :::
                              (patchLocatorLine constructorRuntimeBase ++
                                initializeAdminRole ++
                                initializeExitRequestLimit ++
                                [pushLayoutNat runtimeLength,
                                  pushLayoutNat constructorRuntimeBase]) +++
                              Func.ret))))))))))))))

private def constructorProgram
    (runtimeOffset argsOffset runtimeLength : Nat) : Prog :=
  { main := callvalue ::: iszero :::
      (constructorBody runtimeOffset argsOffset runtimeLength <?> .call 1)
    aux := [Func.rev,
      constructorError "AdminCannotBeZero",
      constructorError "TooLargeMaxExitRequestsLimit",
      constructorError "TooLargeFrameDuration",
      constructorError "TooLargeExitsPerFrame",
      constructorError "ZeroFrameDuration"] }

private def provisionalConstructorPrefix : Bytes :=
  (Prog.compile
    (constructorProgram 0 0 runtimeTemplateCode.length)).getD []

/-- Exact source program compiled into the creation prefix. -/
def lidoTwgConstructorProgram : Prog :=
  let prefixLength := provisionalConstructorPrefix.length
  constructorProgram prefixLength
    (prefixLength + runtimeTemplateCode.length)
    runtimeTemplateCode.length

def lidoTwgInitPrefix : Bytes :=
  (Prog.compile lidoTwgConstructorProgram).getD []

/-- Parameter-neutral Blanc creation-code template. -/
def lidoTwgCreationTemplate : Bytes :=
  lidoTwgInitPrefix ++ runtimeTemplateCode

def abiEncodeConstructorArgs (args : ConstructorArgs) : Bytes :=
  args.admin.toBytes ++ args.locator.toBytes ++
    args.maxExitRequestsLimit.toBytes ++ args.exitsPerFrame.toBytes ++
    args.frameDurationInSec.toBytes

/-- Complete CREATE input: constructor prefix, runtime template, and full ABI
constructor suffix. -/
def lidoTwgFullCreateInput (args : ConstructorArgs) : Bytes :=
  lidoTwgCreationTemplate ++ abiEncodeConstructorArgs args

theorem abiEncodeConstructorArgs_length (args : ConstructorArgs) :
    (abiEncodeConstructorArgs args).length = constructorArgumentBytes := by
  simp [abiEncodeConstructorArgs, constructorArgumentBytes,
    B256.length_toBytes]

theorem creation_template_runtime_suffix :
    lidoTwgCreationTemplate.drop lidoTwgInitPrefix.length =
      runtimeTemplateCode := by
  simp [lidoTwgCreationTemplate]

theorem full_create_input_length (args : ConstructorArgs) :
    (lidoTwgFullCreateInput args).length =
      lidoTwgCreationTemplate.length + constructorArgumentBytes := by
  simp [lidoTwgFullCreateInput, abiEncodeConstructorArgs_length]

/-- Constructor writes are classified one-for-one.  Internal `Func.call`
table edges are not external EVM calls. -/
def constructorPersistentWriteInventory :
    List (SourceSite × PersistentWriteClass) :=
  [ (⟨"constructor.admin.lookupIndex", 0⟩, .roleIndex),
    (⟨"constructor.admin.lookupRole", 1⟩, .roleRecord),
    (⟨"constructor.admin.lookupAccount", 2⟩, .roleRecord),
    (⟨"constructor.admin.enumRole", 3⟩, .enumeration),
    (⟨"constructor.admin.enumAccount", 4⟩, .enumeration),
    (⟨"constructor.admin.recordLength", 5⟩, .roleMembership),
    (⟨"constructor.limit.maximum", 6⟩, .limit),
    (⟨"constructor.limit.previous", 7⟩, .limit),
    (⟨"constructor.limit.timestamp", 8⟩, .limit),
    (⟨"constructor.limit.frameDuration", 9⟩, .limit),
    (⟨"constructor.limit.exitsPerFrame", 10⟩, .limit) ]

def constructorExternalCallInventory :
    List (SourceSite × ExternalCallClass) := []

end LidoTriggerableWithdrawalsGateway
end Blanc
