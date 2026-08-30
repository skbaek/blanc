import Blanc.ProxyPairOssifiableDeploy
import Blanc.CompiledWalkInversion
import Blanc.DelegatecallEnvelope

/-!
# OssifiableProxy constructor phase specifications

This module deliberately separates three layers:

* a total, pure specification of the strict appended-code ABI decoder;
* exact source-shape and compiled-branch facts for the product constructor;
* effect certificates which later whole-constructor proofs must derive from
  the actual execution.

In particular, the nonempty setup boundary contains an actual
`DelegatedChildCertificate` for the exact child derived from a
`DelegatecallSpawnDescriptor`.  It does not assume the outer constructor's
final storage, logs, output, or status.
-/

namespace Blanc.ProxyPair

open Jaune

/-! ## Strict appended-code decoder specification -/

/-- The three observable decoder exits used by the Solidity 0.8.9-shaped
constructor.  Malformed words use the empty-revert table entry; only a dynamic
length above `uint64.max` uses the allocation-panic payload. -/
inductive OssifiableConstructorDecodeResult where
  | accepted (implementation requestedAdmin : B256) (setupData : Bytes)
  | emptyRevert
  | allocationPanic
  deriving DecidableEq

def ossifiableConstructorAbiMaxUint64 : B256 := 0xffffffffffffffff

/-- A `CODECOPY`/`MLOAD` word, including right-zero padding.  Decoder guards
ensure the uses below never rely on padding for an accepted input. -/
def ossifiableConstructorCodeWord (code : Bytes) (offset : Nat) : B256 :=
  Bytes.toB256 (code.sliceD offset 32 0)

/-- The dynamic pointer is EVM-word addition, exactly as in the executable
decoder.  The accepted deployment coordinates make the subsequent `.toNat`
nonwrapping; the pure specification keeps the word operation visible. -/
def ossifiableConstructorDataPointer
    (argsOffset : Nat) (relativeOffset : B256) : B256 :=
  relativeOffset + Nat.toB256 argsOffset

def ossifiableConstructorDataStart
    (argsOffset : Nat) (relativeOffset : B256) : B256 :=
  ossifiableConstructorDataPointer argsOffset relativeOffset + 32

def ossifiableConstructorDataEnd
    (argsOffset : Nat) (relativeOffset length : B256) : B256 :=
  ossifiableConstructorDataStart argsOffset relativeOffset + length

/-- Total decoder model in the exact guard order of
`ossifiableConstructorDecode`.

The initial head and all later bounds are checked against the complete CREATE
code image.  Noncanonical and unaligned in-bounds offsets, plus trailing code
bytes, remain accepted. -/
def ossifiableConstructorDecodeSpec
    (code : Bytes) (argsOffset : Nat) : OssifiableConstructorDecodeResult :=
  if code.length < argsOffset + 96 then
    .emptyRevert
  else
    let implementation := ossifiableConstructorCodeWord code argsOffset
    if addressMask &&& implementation ≠ 0 then
      .emptyRevert
    else
      let requestedAdmin :=
        ossifiableConstructorCodeWord code (argsOffset + 32)
      if addressMask &&& requestedAdmin ≠ 0 then
        .emptyRevert
      else
        let relativeOffset :=
          ossifiableConstructorCodeWord code (argsOffset + 64)
        if ossifiableConstructorAbiMaxUint64 < relativeOffset then
          .emptyRevert
        else
          let pointer :=
            ossifiableConstructorDataPointer argsOffset relativeOffset
          if code.length < (pointer + 32).toNat then
            .emptyRevert
          else
            let length := ossifiableConstructorCodeWord code pointer.toNat
            if ossifiableConstructorAbiMaxUint64 < length then
              .allocationPanic
            else
              let start := pointer + 32
              let finish := start + length
              if code.length < finish.toNat then
                .emptyRevert
              else
                .accepted implementation requestedAdmin
                  (code.sliceD start.toNat length.toNat 0)

theorem ossifiableConstructorDecodeSpec_shortHead
    {code : Bytes} {argsOffset : Nat}
    (short : code.length < argsOffset + 96) :
    ossifiableConstructorDecodeSpec code argsOffset = .emptyRevert := by
  simp [ossifiableConstructorDecodeSpec, short]

theorem ossifiableConstructorDecodeSpec_dirtyImplementation
    {code : Bytes} {argsOffset : Nat}
    (head : argsOffset + 96 ≤ code.length)
    (dirty : addressMask &&&
      ossifiableConstructorCodeWord code argsOffset ≠ 0) :
    ossifiableConstructorDecodeSpec code argsOffset = .emptyRevert := by
  simp [ossifiableConstructorDecodeSpec, Nat.not_lt.mpr head, dirty]

theorem ossifiableConstructorDecodeSpec_dirtyAdmin
    {code : Bytes} {argsOffset : Nat}
    (head : argsOffset + 96 ≤ code.length)
    (implementationClean : addressMask &&&
      ossifiableConstructorCodeWord code argsOffset = 0)
    (adminDirty : addressMask &&&
      ossifiableConstructorCodeWord code (argsOffset + 32) ≠ 0) :
    ossifiableConstructorDecodeSpec code argsOffset = .emptyRevert := by
  simp [ossifiableConstructorDecodeSpec, Nat.not_lt.mpr head,
    implementationClean, adminDirty]

theorem ossifiableConstructorDecodeSpec_largeOffset
    {code : Bytes} {argsOffset : Nat}
    (head : argsOffset + 96 ≤ code.length)
    (implementationClean : addressMask &&&
      ossifiableConstructorCodeWord code argsOffset = 0)
    (adminClean : addressMask &&&
      ossifiableConstructorCodeWord code (argsOffset + 32) = 0)
    (large : ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code (argsOffset + 64)) :
    ossifiableConstructorDecodeSpec code argsOffset = .emptyRevert := by
  simp [ossifiableConstructorDecodeSpec, Nat.not_lt.mpr head,
    implementationClean, adminClean, large]

theorem ossifiableConstructorDecodeSpec_incompleteLength
    {code : Bytes} {argsOffset : Nat}
    (head : argsOffset + 96 ≤ code.length)
    (implementationClean : addressMask &&&
      ossifiableConstructorCodeWord code argsOffset = 0)
    (adminClean : addressMask &&&
      ossifiableConstructorCodeWord code (argsOffset + 32) = 0)
    (offsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code (argsOffset + 64))
    (short : code.length <
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64)) + 32).toNat) :
    ossifiableConstructorDecodeSpec code argsOffset = .emptyRevert := by
  simp [ossifiableConstructorDecodeSpec, Nat.not_lt.mpr head,
    implementationClean, adminClean, offsetBound, short]

theorem ossifiableConstructorDecodeSpec_largeLength
    {code : Bytes} {argsOffset : Nat}
    (head : argsOffset + 96 ≤ code.length)
    (implementationClean : addressMask &&&
      ossifiableConstructorCodeWord code argsOffset = 0)
    (adminClean : addressMask &&&
      ossifiableConstructorCodeWord code (argsOffset + 32) = 0)
    (offsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code (argsOffset + 64))
    (lengthComplete :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64)) + 32).toNat
        ≤ code.length)
    (large : ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat) :
    ossifiableConstructorDecodeSpec code argsOffset = .allocationPanic := by
  simp [ossifiableConstructorDecodeSpec, Nat.not_lt.mpr head,
    implementationClean, adminClean, offsetBound,
    Nat.not_lt.mpr lengthComplete, large]

theorem ossifiableConstructorDecodeSpec_payloadOutOfBounds
    {code : Bytes} {argsOffset : Nat}
    (head : argsOffset + 96 ≤ code.length)
    (implementationClean : addressMask &&&
      ossifiableConstructorCodeWord code argsOffset = 0)
    (adminClean : addressMask &&&
      ossifiableConstructorCodeWord code (argsOffset + 32) = 0)
    (offsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code (argsOffset + 64))
    (lengthComplete :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64)) + 32).toNat
        ≤ code.length)
    (lengthBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat)
    (payloadShort : code.length <
      (ossifiableConstructorDataEnd argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64))
        (ossifiableConstructorCodeWord code
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat)).toNat) :
    ossifiableConstructorDecodeSpec code argsOffset = .emptyRevert := by
  have payloadShort' : code.length <
      (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord code (argsOffset + 64)) + 32 +
        ossifiableConstructorCodeWord code
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat).toNat := by
    simpa only [ossifiableConstructorDataEnd,
      ossifiableConstructorDataStart] using payloadShort
  simp [ossifiableConstructorDecodeSpec, Nat.not_lt.mpr head,
    implementationClean, adminClean, offsetBound,
    Nat.not_lt.mpr lengthComplete, lengthBound,
    payloadShort']

theorem ossifiableConstructorDecodeSpec_accepted
    {code : Bytes} {argsOffset : Nat}
    (head : argsOffset + 96 ≤ code.length)
    (implementationClean : addressMask &&&
      ossifiableConstructorCodeWord code argsOffset = 0)
    (adminClean : addressMask &&&
      ossifiableConstructorCodeWord code (argsOffset + 32) = 0)
    (offsetBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code (argsOffset + 64))
    (lengthComplete :
      (ossifiableConstructorDataPointer argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64)) + 32).toNat
        ≤ code.length)
    (lengthBound : ¬ ossifiableConstructorAbiMaxUint64 <
      ossifiableConstructorCodeWord code
        (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat)
    (payloadComplete :
      (ossifiableConstructorDataEnd argsOffset
        (ossifiableConstructorCodeWord code (argsOffset + 64))
        (ossifiableConstructorCodeWord code
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat)).toNat
        ≤ code.length) :
    ossifiableConstructorDecodeSpec code argsOffset =
      .accepted
        (ossifiableConstructorCodeWord code argsOffset)
        (ossifiableConstructorCodeWord code (argsOffset + 32))
        (code.sliceD
          (ossifiableConstructorDataStart argsOffset
            (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat
          (ossifiableConstructorCodeWord code
            (ossifiableConstructorDataPointer argsOffset
              (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat).toNat
          0) := by
  have payloadComplete' :
      (ossifiableConstructorDataPointer argsOffset
          (ossifiableConstructorCodeWord code (argsOffset + 64)) + 32 +
        ossifiableConstructorCodeWord code
          (ossifiableConstructorDataPointer argsOffset
            (ossifiableConstructorCodeWord code (argsOffset + 64))).toNat).toNat
        ≤ code.length := by
    simpa only [ossifiableConstructorDataEnd,
      ossifiableConstructorDataStart] using payloadComplete
  simp [ossifiableConstructorDecodeSpec, Nat.not_lt.mpr head,
    implementationClean, adminClean, offsetBound,
    Nat.not_lt.mpr lengthComplete, lengthBound,
    payloadComplete', ossifiableConstructorDataStart]

/-! ## Implementation validation and ordered installation effect -/

inductive OssifiableImplementationValidation where
  | noCode
  | accepted
  deriving DecidableEq, Repr

def ossifiableImplementationValidation
    (code : ByteArray) : OssifiableImplementationValidation :=
  if code.size = 0 then .noCode else .accepted

@[simp] theorem ossifiableImplementationValidation_noCode
    {code : ByteArray} (h : code.size = 0) :
    ossifiableImplementationValidation code = .noCode := by
  simp [ossifiableImplementationValidation, h]

@[simp] theorem ossifiableImplementationValidation_accepted
    {code : ByteArray} (h : code.size ≠ 0) :
    ossifiableImplementationValidation code = .accepted := by
  simp [ossifiableImplementationValidation, h]

/-- The exact raw word produced by Solidity address assignment. -/
def ossifiableConstructorAddressWrite
    (raw : B256) (newAddress : Adr) : B256 :=
  (addressMask &&& raw) ||| newAddress.toB256

/-- The exact low-160-bit word observed by an address-typed read. -/
def ossifiableConstructorAddressRead (raw : B256) : B256 :=
  (~~~ addressMask) &&& raw

/-- Product-owned phase spec.  A later executable proof supplies this witness
after the `EXTCODESIZE` accepting arm; the fields state the exact address-slot
write and single appended `Upgraded` log, without suppressing same-value
installation. -/
structure OssifiableConstructorImplementationEffect
    (proxy implementation : Adr) (implementationCode : ByteArray)
    (rawBefore rawAfter : B256) (logsBefore logsAfter : List Log) : Prop where
  codeNonempty : implementationCode.size ≠ 0
  implementationWrite :
    rawAfter = ossifiableConstructorAddressWrite rawBefore implementation
  upgradedAppended :
    logsAfter = logsBefore ++ [upgradedLog proxy implementation]

theorem ossifiableConstructorImplementationEffect_intro
    (proxy implementation : Adr) (implementationCode : ByteArray)
    (rawBefore : B256) (logsBefore : List Log)
    (codeNonempty : implementationCode.size ≠ 0) :
    OssifiableConstructorImplementationEffect proxy implementation
      implementationCode rawBefore
      (ossifiableConstructorAddressWrite rawBefore implementation)
      logsBefore (logsBefore ++ [upgradedLog proxy implementation]) := by
  exact ⟨codeNonempty, rfl, rfl⟩

/-! ## Empty/nonempty setup split -/

/-- A zero decoded byte length takes the fall-through `afterSetup` arm.  This
is a theorem about the actual gas-exact compiled branch, not a comment about
the surface notation (whose arguments are intentionally reversed). -/
theorem ossifiableConstructorEmptySetup_selectsAfterSetup
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {tail : Stack}
    (stack : (0 : B256) :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      ((.call 6) <?> (.call 5)) out) :
    ∃ armPre,
      Devm.PopBurnBy [0] (gVerylow + gHigh) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre (.call 5) out ∧
      tail <<+ armPre.stack := by
  exact Func.RunCompiledTo.zero_branch_of_prefix stack run

/-- Conversely, a nonzero decoded byte length takes the delegate-setup arm. -/
theorem ossifiableConstructorNonemptySetup_selectsDelegateSetup
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {length : B256} {tail : Stack}
    (nonempty : length ≠ 0)
    (stack : length :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      ((.call 6) <?> (.call 5)) out) :
    ∃ armPre branchWord,
      branchWord ≠ 0 ∧
      Devm.PopBurnBy [branchWord]
        (gVerylow + gHigh + gJumpdest) pre armPre ∧
      Func.RunCompiledTo fs sevm armPre (.call 6) out ∧
      tail <<+ armPre.stack := by
  exact Func.RunCompiledTo.succ_branch_of_prefix nonempty stack run

/-! ## Actual delegated-child certificate for nonempty setup -/

/-- Certificate at the constructor's nonempty setup boundary.  `spawn` fixes
the real EIP-150/depth/access/memory-derived child; `childCertificate` retains
that child's actual recursive execution.  No outer observation is a field. -/
structure OssifiableConstructorSetupCertificate
    (sevm : Sevm) (callPre : Devm) (out : MessageResult) where
  implementation : Adr
  setupData : Bytes
  setupData_nonempty : setupData ≠ []
  spawn : DelegatecallSpawnDescriptor sevm callPre
  codeWord_eq : spawn.codeWord = implementation.toB256
  inputOffsetWord_eq : spawn.inputOffsetWord = 0x100
  inputSizeWord_eq : spawn.inputSizeWord = Nat.toB256 setupData.length
  outputOffsetWord_eq : spawn.outputOffsetWord = 0
  outputSizeWord_eq : spawn.outputSizeWord = 0
  childMessage : Msg
  childMessage_eq : childMessage = spawn.child
  childData_eq : childMessage.data = setupData
  childCertificate : DelegatedChildCertificate childMessage out

theorem OssifiableConstructorSetupCertificate.child_process
    {sevm : Sevm} {callPre : Devm} {out : MessageResult}
    (certificate :
      OssifiableConstructorSetupCertificate sevm callPre out) :
    ProcessMessage certificate.childMessage
      certificate.childCertificate.trace.slot out :=
  certificate.childCertificate.process

@[simp] theorem OssifiableConstructorSetupCertificate.child_currentTarget
    {sevm : Sevm} {callPre : Devm} {out : MessageResult}
    (certificate :
      OssifiableConstructorSetupCertificate sevm callPre out) :
    certificate.childMessage.currentTarget = sevm.currentTarget := by
  rw [certificate.childMessage_eq]
  exact certificate.spawn.child_currentTarget

@[simp] theorem OssifiableConstructorSetupCertificate.child_transfer
    {sevm : Sevm} {callPre : Devm} {out : MessageResult}
    (certificate :
      OssifiableConstructorSetupCertificate sevm callPre out) :
    certificate.childMessage.shouldTransferValue = false := by
  rw [certificate.childMessage_eq]
  exact certificate.spawn.child_transfer

/-! ## Post-setup admin read/log/write specification -/

/-- Event emitted from the exact cleaned post-setup slot word. -/
def ossifiableConstructorAdminChangedLog
    (proxy : Adr) (postSetupRaw : B256) (requestedAdmin : Adr) : Log :=
  ⟨proxy, [adminChangedEventTopic],
    (ossifiableConstructorAddressRead postSetupRaw).toBytes ++
      requestedAdmin.toB256.toBytes⟩

/-- Product-owned spec of `_changeAdmin` after optional setup.  Crucially,
`postSetupRaw` is supplied after the child returns, and both the emitted
previous admin and the upper 96 bits of the write are derived from that word.
The requested-zero case is intentionally excluded here: it has already
emitted the log but must revert rather than produce this success effect. -/
structure OssifiableConstructorAdminEffect
    (proxy requestedAdmin : Adr) (postSetupRaw rawAfter : B256)
    (logsBefore logsAfter : List Log) : Prop where
  requestedNonzero : requestedAdmin ≠ 0
  adminWrite :
    rawAfter =
      ossifiableConstructorAddressWrite postSetupRaw requestedAdmin
  adminChangedAppended :
    logsAfter = logsBefore ++
      [ossifiableConstructorAdminChangedLog
        proxy postSetupRaw requestedAdmin]

theorem ossifiableConstructorAdminEffect_intro
    (proxy requestedAdmin : Adr) (postSetupRaw : B256)
    (logsBefore : List Log) (requestedNonzero : requestedAdmin ≠ 0) :
    OssifiableConstructorAdminEffect proxy requestedAdmin postSetupRaw
      (ossifiableConstructorAddressWrite postSetupRaw requestedAdmin)
      logsBefore
      (logsBefore ++
        [ossifiableConstructorAdminChangedLog
          proxy postSetupRaw requestedAdmin]) := by
  exact ⟨requestedNonzero, rfl, rfl⟩

/-- Dirty high bits from the post-setup raw word are present verbatim in the
constructor's write formula; they are not replaced by a full-word SSTORE. -/
theorem ossifiableConstructorAdminWrite_preservesDirtyUpper_formula
    (postSetupRaw : B256) (requestedAdmin : Adr) :
    ossifiableConstructorAddressWrite postSetupRaw requestedAdmin =
      (addressMask &&& postSetupRaw) ||| requestedAdmin.toB256 := by
  rfl

/-- The event reads the post-setup word and cleans it before encoding. -/
@[simp] theorem ossifiableConstructorAdminChangedLog_data
    (proxy : Adr) (postSetupRaw : B256) (requestedAdmin : Adr) :
    (ossifiableConstructorAdminChangedLog
      proxy postSetupRaw requestedAdmin).data =
      (ossifiableConstructorAddressRead postSetupRaw).toBytes ++
        requestedAdmin.toB256.toBytes := by
  rfl

@[simp] theorem ossifiableConstructorAdminChangedLog_topics
    (proxy : Adr) (postSetupRaw : B256) (requestedAdmin : Adr) :
    (ossifiableConstructorAdminChangedLog
      proxy postSetupRaw requestedAdmin).topics =
      [adminChangedEventTopic] := by
  rfl

end Blanc.ProxyPair
