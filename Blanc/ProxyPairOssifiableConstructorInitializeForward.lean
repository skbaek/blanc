import Blanc.ProxyPairOssifiableConstructorForward

/-!
# OssifiableProxy constructor implementation initialization

This module constructs the canonical successful implementation-initialization
walk after the constructor decoder has produced the five-word memory image.
The implementation has code, both proxy slots start cold and zero, and the
optional setup payload is empty.  The walk validates the implementation,
installs its packed address, emits `Upgraded`, and enters the already-proved
post-setup admin/runtime path.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

private theorem initialize_addAccessedAddress_setMach_setMach
    (base : Devm) (mach mach' : Mach) (address : Adr) :
    (addAccessedAddress (base.setMach mach) address).setMach mach' =
      (addAccessedAddress base address).setMach mach' := rfl

private theorem initialize_addAccessedAddress_getStorVal
    (base : Devm) (address target : Adr) (key : B256) :
    (addAccessedAddress base address).getStorVal target key =
      base.getStorVal target key := rfl

private theorem initialize_addAccessedStorageKey_getStorVal
    (base : Devm) (address : Adr) (key : B256) (target : Adr)
    (targetKey : B256) :
    (addAccessedStorageKey base address key).getStorVal target targetKey =
      base.getStorVal target targetKey := rfl

private theorem initialize_withRefundCounter_getStorVal
    (base : Devm) (refund : Int) (target : Adr) (key : B256) :
    (base.withRefundCounter refund).getStorVal target key =
      base.getStorVal target key := rfl

private theorem initialize_addLog_getStorVal
    (base : Devm) (entry : Log) (target : Adr) (key : B256) :
    (base.addLog entry).getStorVal target key =
      base.getStorVal target key := rfl

private theorem initialize_setStorVal_getStorVal_ne
    (base : Devm) (target : Adr) {writtenKey readKey : B256}
    (value : B256) (hne : writtenKey ≠ readKey) :
    (base.setStorVal target writtenKey value).getStorVal target readKey =
      base.getStorVal target readKey := by
  show (_root_.Blanc.Devm.getStor
      (base.setStorVal target writtenKey value) target).get readKey =
    (_root_.Blanc.Devm.getStor base target).get readKey
  rw [setStorVal_getStor_self, Stor.get_set_ne _ hne]

private theorem initialize_not_mem_hashSet_insert
    {α : Type _} [BEq α] [Hashable α] [LawfulBEq α]
    {s : Std.HashSet α} {x p : α}
    (h : p ∉ s) (hne : x ≠ p) : p ∉ s.insert x := by
  intro hmem
  rcases Std.HashSet.mem_insert.mp hmem with he | hx
  · exact hne (eq_of_beq he)
  · exact h hx

private def initializeAfterSetupCall : Func := .call 5

private def initializeSetupBranch : Func :=
  (.call 6) <?> initializeAfterSetupCall

private def initializeLoadLength : Func :=
  [pushB256 128, mload] +++ initializeSetupBranch

private def initializeLog : Func :=
  pushB256 upgradedEventTopic ::: logWith 1 0 0 +++ initializeLoadLength

private def initializeSstore : Func :=
  pushB256 implementationSlotLit ::: sstore ::: initializeLog

private def initializeMerge : Func :=
  Ninst.and ::: Ninst.or ::: initializeSstore

private def initializeHighMask : Func :=
  pushB256 0 ::: Ninst.not ::: pushB256 160 ::: shl ::: initializeMerge

private def initializePackedStore : Func :=
  pushB256 implementationSlotLit ::: sload ::: initializeHighMask

private def initializeAccepted : Func :=
  dup 0 ::: initializePackedStore

/-- Execute the canonical empty-setup initialization path from the decoded
five-word constructor image.  The theorem includes the implementation code
guard, the exact warm `SSTORE`, the `Upgraded` log, and the complete post-setup
admin/runtime walk. -/
theorem ossifiableConstructorInitializeImplementation_zeroSetup_runCompiled
    {sevm : Sevm} {base : Devm}
    {memory : Mem} {image runtimeBytes : Bytes}
    {implementation requestedAdmin : Adr} {G : Nat}
    (hwf : Mem.Wf memory)
    (hreads : Mem.Reads memory image)
    (himplementation : Bytes.toB256 (image.sliceD 0 32 0) =
      implementation.toB256)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (hlength : Bytes.toB256 (image.sliceD 128 32 0) = 0)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hcodeSizeNonzero :
      (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold : (sevm.currentTarget, implementationSlotLit) ∉
      base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hsize : memory.size = 160)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : 200000 ≤ G) :
    ∃ post,
      Func.RunCompiled (ossifiableConstructorFunctions 1250 2197) sevm
        (base.setMach ⟨[], memory, G⟩)
        ossifiableConstructorInitializeImplementation post ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor base sevm.currentTarget).set implementationSlotLit
          implementation.toB256).set adminSlotLit requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [rawUpgradedLog sevm.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget 0
          requestedAdmin] ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 49897 ∧
      post.error = base.error := by
  have hmemory0 : (memory.read 0 32).2 = memory := by
    apply Mem.read_snd_eq_self
    rw [hsize]
    decide
  have hmemory128 : (memory.read 128 32).2 = memory := by
    apply Mem.read_snd_eq_self
    rw [hsize]
    decide
  have hreadZero : memory.read 0 0 = ([], memory) := by
    simp [Mem.read, Mem.extend, memExtSize]
    rfl
  have halign : memory.size % 32 = 0 := by
    rw [hsize]
  have hzeroWindow : 0 + 0 ≤ memory.size := by omega
  have himplementationWordNonzero : implementation.toB256 ≠ 0 := by
    intro hzero
    apply himplementationNonzero
    apply Adr.toB256_inj
    rw [hzero]
    decide
  have hzeroImplementation : (0 : B256) ≠ implementation.toB256 :=
    Ne.symm himplementationWordNonzero
  have hrefund (rc : Int) :
      sstoreNewRefundCounter implementation.toB256 0 0 rc = rc := by
    simp [sstoreNewRefundCounter, hzeroImplementation,
      himplementationWordNonzero]
  have hnew :
      ((((fun x y : B256 => y <<< x.toNat) 160
        ((fun x : B256 => ~~~x) 0)).and 0).or implementation.toB256) =
        implementation.toB256 := by
    exact b256_and_zero_or _ _
  let initializationLog : Log :=
    ⟨sevm.currentTarget, [upgradedEventTopic, implementation.toB256], []⟩
  let initializedBase : Devm :=
    ((((addAccessedStorageKey (addAccessedAddress base implementation)
          sevm.currentTarget implementationSlotLit).withRefundCounter
        base.refundCounter).setStorVal sevm.currentTarget
      implementationSlotLit implementation.toB256).addLog initializationLog)
  have hadminRawInitialized :
      initializedBase.getStorVal sevm.currentTarget adminSlotLit = 0 := by
    have hslots : implementationSlotLit ≠ adminSlotLit := by decide
    unfold initializedBase
    rw [initialize_addLog_getStorVal]
    rw [initialize_setStorVal_getStorVal_ne
      (writtenKey := implementationSlotLit) (readKey := adminSlotLit)
      _ sevm.currentTarget implementation.toB256 hslots]
    rw [initialize_withRefundCounter_getStorVal,
      initialize_addAccessedStorageKey_getStorVal,
      initialize_addAccessedAddress_getStorVal]
    exact hadminRaw
  have hadminColdInitialized :
      (sevm.currentTarget, adminSlotLit) ∉
        initializedBase.accessedStorageKeys := by
    change (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys.insert
        (sevm.currentTarget, implementationSlotLit)
    apply initialize_not_mem_hashSet_insert hadminCold
    intro hp
    have hk := congrArg Prod.snd hp
    exact (by decide : implementationSlotLit ≠ adminSlotLit) hk
  have htail := ossifiableConstructorAfterSetup_zeroAdmin_forward_exact
    (fs := ossifiableConstructorFunctions 1250 2197)
    (sevm := sevm) (base := initializedBase) (memory := memory)
    (image := image) (runtimeBytes := runtimeBytes)
    (requestedAdmin := requestedAdmin) (G := G - 25913)
    hwf hreads hrequested hrequestedNonzero hadminRawInitialized
    hadminOriginal hadminColdInitialized hsize hstatic hcode
    hruntimeLength hruntimeNonempty
    (ossifiableConstructorFunctions_zeroAdmin 1250 2197) (by omega)
  rcases htail with
    ⟨post, htailRun, htailStorage, htailLogs, htailOutput, htailGas,
      htailError⟩
  refine ⟨post, ?_, ?_, ?_, htailOutput, ?_, ?_⟩
  · rw [ossifiableConstructorInitializeImplementation_shape]
    func_run (2) [3]
    · exact Devm.extCost_add_of_size (a := gVerylow) hsize (by decide)
    simp only [show (0 : B256).toNat = 0 by rfl]
    rw [Mem.Reads.read hreads, himplementation, hmemory0]
    func_run (4) [0]
    · simpa only [Devm.setMach_accessedAddresses, toAdr_toB256]
        using haddressCold
    · simp only [Devm.getCode_setMach, toAdr_toB256, B256.eqCheck,
        hcodeSizeNonzero, ↓reduceIte]
    simp only [initialize_addAccessedAddress_setMach_setMach, toAdr_toB256]
    change Func.RunCompiled (ossifiableConstructorFunctions 1250 2197) sevm _
      initializeAccepted _
    unfold initializeAccepted
    func_run (1)
    unfold initializePackedStore
    apply Func.RunCompiled.next
    · apply Ninst.runCompiled_pushB256 (c := 3) (G := G - 2630)
      · decide +kernel
      · simp only [Devm.gasLeft_setMach]
        omega
      · simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega
    func_run (1)
    simp only [Devm.addAccessedStorageKey_setMach_setMach,
      Devm.getStorVal_setMach, initialize_addAccessedAddress_getStorVal,
      Devm.memory_setMach, Devm.stack_setMach]
    rw [himplementationRaw]
    unfold initializeHighMask
    func_run (4)
    unfold initializeMerge
    func_run (2)
    unfold initializeSstore
    have hwarmImplementation :
        (sevm.currentTarget, implementationSlotLit) ∈
          (addAccessedStorageKey (addAccessedAddress base implementation)
            sevm.currentTarget implementationSlotLit).accessedStorageKeys :=
      Std.HashSet.mem_insert_self
    func_run (2) [20000]
    · simp only [Devm.getStorVal_setMach,
        initialize_addAccessedStorageKey_getStorVal,
        initialize_addAccessedAddress_getStorVal, himplementationRaw,
        himplementationOriginal, hnew]
      rw [sstoreValueCost,
        if_pos ⟨rfl, fun h => himplementationWordNonzero h.symm⟩,
        if_pos rfl]
      norm_num [gasStorageSet]
    simp only [hnew, Devm.getStorVal_setMach,
      initialize_addAccessedStorageKey_getStorVal,
      initialize_addAccessedAddress_getStorVal, himplementationRaw,
      himplementationOriginal]
    unfold initializeLog
    func_run (4) [1125]
    · simp only [show ((0 : B256) * 32).toNat = 0 by decide]
      rw [Devm.extCost_zero_of_le halign hzeroWindow]
      norm_num [gLog, gLogdata, gLogtopic]
    simp only [show ((0 : B256) * 32).toNat = 0 by decide]
    rw [hreadZero]
    change Func.RunCompiled (ossifiableConstructorFunctions 1250 2197) sevm _
      initializeLoadLength _
    unfold initializeLoadLength
    func_run (2) [3]
    · exact Devm.extCost_add_of_size hsize (by decide)
    simp only [show (128 : B256).toNat = 128 by decide]
    rw [Mem.Reads.read hreads, hlength, hmemory128]
    unfold initializeSetupBranch
    func_run (1)
    unfold initializeAfterSetupCall
    func_run (1)
    rw [hrefund]
    change Func.RunCompiled (ossifiableConstructorFunctions 1250 2197) sevm
      (initializedBase.setMach ⟨[], memory, G - 25913⟩)
      (ossifiableConstructorAfterSetup 1250 2197) post
    exact htailRun
  · rw [htailStorage]
    unfold initializedBase
    rw [Devm.addLog_getStor, setStorVal_getStor_self,
      Devm.withRefundCounter_getStor, addAccessedStorageKey_getStor]
    rfl
  · rw [htailLogs]
    unfold initializedBase initializationLog rawUpgradedLog
    rfl
  · rw [htailGas]
    omega
  · calc
      post.error = initializedBase.error := htailError
      _ = base.error := rfl

end Blanc.ProxyPair
