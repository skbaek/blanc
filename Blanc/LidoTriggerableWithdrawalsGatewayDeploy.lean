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

private def constructorArgumentWords : Nat := constructorArgumentBytes / 32
private def constructorArgumentCacheBase : Nat := constructorArgumentWords
private def constructorAdminScratchBase : Nat :=
  constructorArgumentCacheBase + constructorArgumentWords
private def constructorLimitEventScratchBase : Nat :=
  constructorAdminScratchBase + 3

private def cachedArgumentWord (index : Nat) : Nat :=
  constructorArgumentCacheBase + index

private def loadCachedArgumentIndex (index : Nat) : Line :=
  mloadWord (Nat.toB256 (cachedArgumentWord index))

private def cacheConstructorArguments : Line :=
  (List.range constructorArgumentWords).flatMap fun index =>
    loadArgumentIndex index ++
      mstoreAt (Nat.toB256 (cachedArgumentWord index))

private def storeByteOffset (offset : Nat) : Line :=
  [pushDeployWord (Nat.toB256 offset), mstore]

private def constructorError (name : String) : Func :=
  Func.revertSelector (customErrorData name) (by
    simp [customErrorData, B256.length_toBytes])

private def patchLocatorLine (runtimeBase : Nat) : Line :=
  locatorWordOffsets.flatMap fun offset =>
    loadArgumentIndex 1 ++ storeByteOffset (runtimeBase + offset)

private def initializeAdminRole : Line :=
  -- Keep the decoded ABI head at words zero through four intact for the
  -- locator patch.  Constructor-only key/event scratch lives above the
  -- cached five-word argument copy and is overwritten by the runtime copy.
  let roleWord := constructorAdminScratchBase
  let accountWord := constructorAdminScratchBase + 1
  let indexWord := constructorAdminScratchBase + 2
  [pushB256 defaultAdminRole] ++ mstoreAt (Nat.toB256 roleWord) ++
  loadCachedArgumentIndex 0 ++ mstoreAt (Nat.toB256 accountWord) ++
  [pushB256 0] ++ mstoreAt (Nat.toB256 indexWord) ++
  [pushB256 1] ++
    roleKeyFromMemoryAt roleWord accountWord roleLookupIndexRegion ++ [sstore] ++
  mloadWord (Nat.toB256 roleWord) ++
    roleKeyFromMemoryAt roleWord accountWord roleLookupRoleRegion ++ [sstore] ++
  mloadWord (Nat.toB256 accountWord) ++
    roleKeyFromMemoryAt roleWord accountWord roleLookupAccountRegion ++ [sstore] ++
  mloadWord (Nat.toB256 roleWord) ++
    enumKeyFromMemoryAt indexWord enumRoleRegion ++ [sstore] ++
  mloadWord (Nat.toB256 accountWord) ++
    enumKeyFromMemoryAt indexWord enumAccountRegion ++ [sstore] ++
  [pushB256 1, pushB256 roleRecordLengthSlot, sstore] ++
  [caller] ++ mloadWord (Nat.toB256 accountWord) ++
    mloadWord (Nat.toB256 roleWord) ++
    [pushB256 (signatureHash "RoleGranted" [.bytes 32, .address, .address])] ++
    logWith 3 0 0

private def initializeExitRequestLimit : Line :=
  loadCachedArgumentIndex 2 ++ [pushB256 maxExitRequestsLimitSlot, sstore] ++
  loadCachedArgumentIndex 2 ++ [pushB256 prevExitRequestsLimitSlot, sstore] ++
  [timestamp, pushB256 (Nat.toB256 (2 ^ 32 - 1)), and,
    pushB256 prevTimestampSlot, sstore] ++
  loadCachedArgumentIndex 4 ++ [pushB256 frameDurationInSecSlot, sstore] ++
  loadCachedArgumentIndex 3 ++ [pushB256 exitsPerFrameSlot, sstore] ++
  loadCachedArgumentIndex 2 ++
    mstoreAt (Nat.toB256 constructorLimitEventScratchBase) ++
  loadCachedArgumentIndex 3 ++
    mstoreAt (Nat.toB256 (constructorLimitEventScratchBase + 1)) ++
  loadCachedArgumentIndex 4 ++
    mstoreAt (Nat.toB256 (constructorLimitEventScratchBase + 2)) ++
  [pushB256 (signatureHash "ExitRequestsLimitSet"
    [.uint256, .uint256, .uint256])] ++
  logWith 0 (Nat.toB256 constructorLimitEventScratchBase) 3

private def constructorBody
    (runtimeOffset argsOffset runtimeLength : Nat) : Func :=
  -- Solidity's static decoder requires the complete five-word head while
  -- accepting any trailing creation data.
  pushLayoutNat (argsOffset + constructorArgumentBytes) ::: codesize ::: lt :::
  ((.call 1) <?>
    (pushLayoutNat constructorArgumentBytes ::: pushLayoutNat argsOffset :::
      pushLayoutNat 0 ::: codecopy :::
      cacheConstructorArguments +++
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
                            ((initializeAdminRole ++
                                initializeExitRequestLimit ++
                                [pushLayoutNat runtimeLength,
                                  pushLayoutNat runtimeOffset,
                                  pushLayoutNat constructorRuntimeBase,
                                  codecopy] ++
                                patchLocatorLine constructorRuntimeBase ++
                                [pushLayoutNat runtimeLength,
                                  pushLayoutNat constructorRuntimeBase]) +++
                              Func.return_))))))))))))))

private def constructorProgram
    (runtimeOffset argsOffset runtimeLength : Nat) : Prog :=
  { main := callvalue ::: iszero :::
      (constructorBody runtimeOffset argsOffset runtimeLength <?> .call 1)
    aux := [Func.revert,
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
  CreationArtifact.finalizedConstructorProgram constructorProgram
    provisionalConstructorPrefix runtimeTemplateCode

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
