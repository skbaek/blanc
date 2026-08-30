import Blanc.ProxyPairOssifiableConstructorNonempty
import Blanc.MessageExecution

namespace Blanc.ProxyPair.OssifiableBothSlotFixture

open Jaune
open Jaune.Ninst Blanc.Ninst

def implementation : Adr :=
  Nat.toAdr 0x6f6541c2203196feedd14cd2c09550da1cbeda31

def requestedAdmin : Adr :=
  Nat.toAdr 0x8ea83ad72396f1e0cd2f8e72b1461db8eb6af7b5

def postSetupImplementation : Adr :=
  Nat.toAdr 0x3333333333333333333333333333333333333333

def postSetupAdmin : Adr :=
  Nat.toAdr 0x6813eb9362372eef6200f3b1dbc3f819671cba69

def target : Adr :=
  Nat.toAdr 0x889edc2edab5f40e902b864ad4d7ade8e412f9b1

def setupData : Bytes :=
  [0x4f, 0x53, 0x53, 0x49, 0x46, 0x49, 0x41, 0x42,
   0x4c, 0x45, 0x5f, 0x50, 0x52, 0x4f, 0x58, 0x59,
   0x5f, 0x53, 0x45, 0x54, 0x55, 0x50, 0x5f, 0x56,
   0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- The frozen differential fixture bytecode: write a new implementation word,
then a new admin word, and return successfully with empty returndata. -/
def implementationBytes : Bytes := [
  0x73, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
  0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x33,
  0x33, 0x33, 0x33, 0x33, 0x33, 0x7f, 0x36, 0x08,
  0x94, 0xa1, 0x3b, 0xa1, 0xa3, 0x21, 0x06, 0x67,
  0xc8, 0x28, 0x49, 0x2d, 0xb9, 0x8d, 0xca, 0x3e,
  0x20, 0x76, 0xcc, 0x37, 0x35, 0xa9, 0x20, 0xa3,
  0xca, 0x50, 0x5d, 0x38, 0x2b, 0xbc, 0x55, 0x73,
  0x68, 0x13, 0xeb, 0x93, 0x62, 0x37, 0x2e, 0xef,
  0x62, 0x00, 0xf3, 0xb1, 0xdb, 0xc3, 0xf8, 0x19,
  0x67, 0x1c, 0xba, 0x69, 0x7f, 0xb5, 0x31, 0x27,
  0x68, 0x4a, 0x56, 0x8b, 0x31, 0x73, 0xae, 0x13,
  0xb9, 0xf8, 0xa6, 0x01, 0x6e, 0x24, 0x3e, 0x63,
  0xb6, 0xe8, 0xee, 0x11, 0x78, 0xd6, 0xa7, 0x17,
  0x85, 0x0b, 0x5d, 0x61, 0x03, 0x55, 0x60, 0x00,
  0x60, 0x00, 0xf3]

def implementationCode : ByteArray :=
  ByteArray.mk implementationBytes.toArray

def push1Zero : Ninst := Ninst.push [0] (by decide)

def setupMain : Func :=
  pushB256 postSetupImplementation.toB256 :::
    pushB256 implementationSlotLit ::: sstore :::
    pushB256 postSetupAdmin.toB256 :::
    pushB256 adminSlotLit ::: sstore :::
    push1Zero ::: push1Zero ::: Func.last .ret

theorem setupMain_compile :
    Func.compile [] 0 setupMain = some implementationCode.toList := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

theorem setupMain_noCalls : setupMain.NoCalls := by
  simp [setupMain, Func.NoCalls]

def setupBodyGas : Nat := 22218

private theorem getStorVal_setStorVal_ne
    (d : Devm) (owner : Adr) (writtenKey readKey value : B256)
    (hne : writtenKey ≠ readKey) :
    (d.setStorVal owner writtenKey value).getStorVal owner readKey =
      d.getStorVal owner readKey := by
  show ((Devm.getStor (d.setStorVal owner writtenKey value) owner).get
    readKey) = _
  rw [setStorVal_getStor_self, Stor.get_set_ne _ hne]
  rfl

private theorem getStorVal_withRefundCounter
    (d : Devm) (refund : Int) (owner : Adr) (key : B256) :
    (d.withRefundCounter refund).getStorVal owner key =
      d.getStorVal owner key := by
  rfl

private theorem getStorVal_sstoreBase_ne
    (d : Devm) (owner : Adr) (writtenKey readKey value : B256)
    (refund : Int) (hne : writtenKey ≠ readKey) :
    ((((addAccessedStorageKey d owner writtenKey).withRefundCounter refund
      ).setStorVal owner writtenKey value).getStorVal owner readKey) =
        d.getStorVal owner readKey := by
  unfold Devm.getStorVal Devm.getAcct
  rw [Devm.sstoreBase_state]
  simp only [State.setStorVal, State.get_set_self]
  rw [Stor.get_set_ne _ hne]

theorem setupMain_runCompiledTo
    (fs : List Func) (sevm : Sevm) (base : Devm) (G : Nat)
    (hstatic : sevm.isStatic = false)
    (himplementationWarm :
      (sevm.currentTarget, implementationSlotLit) ∈
        base.accessedStorageKeys)
    (hadminCold :
      (sevm.currentTarget, adminSlotLit) ∉ base.accessedStorageKeys)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCurrent :
      base.getStorVal sevm.currentTarget implementationSlotLit =
        implementation.toB256)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCurrent :
      base.getStorVal sevm.currentTarget adminSlotLit = 0) :
    ∃ post,
      Func.RunCompiledTo fs sevm
        (base.setMach ⟨[], Mem.empty, G + setupBodyGas⟩)
        setupMain (.ok post) ∧
      post.error = base.error ∧
      post.output = [] ∧
      post.gasLeft = G ∧
      post.getStorVal sevm.currentTarget implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal sevm.currentTarget adminSlotLit =
        postSetupAdmin.toB256 ∧
      post.logs = base.logs ∧
      post.accessedStorageKeys =
        base.accessedStorageKeys.insert
          (sevm.currentTarget, adminSlotLit) := by
  apply Exists.intro
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold setupMain setupBodyGas push1Zero
    func_run [100, 22100]
    · simp only [Devm.getStorVal_setMach]
      rw [himplementationOriginal, himplementationCurrent]
      decide
    · simp only [Devm.getStorVal_setMach,
        getStorVal_setStorVal_ne _ _ _ _ _
          (show implementationSlotLit ≠ adminSlotLit by decide),
        getStorVal_withRefundCounter]
      rw [hadminOriginal, hadminCurrent]
      decide
    · apply Func.runCompiledTo_ret_word (i := 0) (sz := 0) (s := [])
        (e := 0) (G := G) (out := [])
      · rfl
      · exact Devm.extCost_empty_window
      · simp only [Devm.gasLeft_setMach]
        omega
      · rw [show B256.toNat (0 : B256) = 0 by decide]
        exact congrArg Prod.fst Devm.memRead_zero
  · simp only [Devm.withOutput_error, Devm.memRead_error,
      Devm.setMach_error, Devm.sstoreBase_error]
    rfl
  · rfl
  · rfl
  · simp only [Devm.retPost_getStorVal, Devm.getStorVal_setMach,
      getStorVal_sstoreBase_ne _ _ _ _ _ _
        (show adminSlotLit ≠ implementationSlotLit by decide),
      Devm.getStorVal_setStorVal_self]
  · simp only [Devm.retPost_getStorVal, Devm.getStorVal_setMach,
      Devm.getStorVal_setStorVal_self]
  · simp only [Devm.withOutput_logs, Devm.memRead_logs,
      Devm.setMach_logs, Devm.sstoreBase_logs]
    rfl
  · simp only [Devm.retPost_accessedStorageKeys,
      Devm.setMach_accessedStorageKeys,
      Devm.sstoreBase_accessedStorageKeys]
    simp only [Devm.setMach_accessedStorageKeys,
      Devm.sstoreWarmBase_accessedStorageKeys]

/-! ## Closed proxy-storage child world -/

def originalState : State :=
  State.set (.empty : State) implementation
    { Acct.nil with code := implementationCode }

def currentState : State :=
  State.set originalState target
    { Acct.nil with
      stor := Stor.empty.set implementationSlotLit implementation.toB256 }

def warmKeys : Std.HashSet (Adr × B256) :=
  Std.HashSet.emptyWithCapacity.insert (target, implementationSlotLit)

def benv : Benv :=
  { (default : Benv) with
    state := currentState
    stat :=
      { (default : BenvStat) with
        rules := pragueRules
        origState := originalState } }

def message : Msg :=
  { (default : Msg) with
    benv := benv
    caller := target
    target := some target
    currentTarget := target
    gas := 1000 + setupBodyGas
    value := 0
    data := setupData
    codeAddress := some implementation
    code := implementationCode
    depth := 1023
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := warmKeys
    disablePrecompiles := true }

private theorem originalState_target_implementation_zero :
    (originalState.get target).stor.get implementationSlotLit = 0 := by
  unfold originalState
  rw [State.get_set_ne _ (show implementation ≠ target by decide) _]
  rfl

private theorem originalState_target_admin_zero :
    (originalState.get target).stor.get adminSlotLit = 0 := by
  unfold originalState
  rw [State.get_set_ne _ (show implementation ≠ target by decide) _]
  rfl

private theorem currentState_target_implementation :
    (currentState.get target).stor.get implementationSlotLit =
      implementation.toB256 := by
  unfold currentState
  rw [State.get_set_self]
  exact Stor.get_set_self _ _ _

private theorem currentState_target_admin_zero :
    (currentState.get target).stor.get adminSlotLit = 0 := by
  unfold currentState
  rw [State.get_set_self]
  change (Stor.empty.set implementationSlotLit implementation.toB256).get
    adminSlotLit = 0
  rw [Stor.get_set_ne _
    (show implementationSlotLit ≠ adminSlotLit by decide)]
  rfl

/-- Closed execution of the exact frozen setup child in proxy storage
context.  Both ERC-1967 slots are changed and the child returns cleanly with
empty returndata and no log. -/
theorem message_success :
    ∃ post,
      processMessage message = .ok post ∧
      post.error = .none ∧
      post.output = [] ∧
      post.getStorVal target implementationSlotLit =
        postSetupImplementation.toB256 ∧
      post.getStorVal target adminSlotLit = postSetupAdmin.toB256 ∧
      post.logs = [] := by
  obtain ⟨post, walk, error, output, gas, implementationSlot,
      adminSlot, logs, _keys⟩ :=
    setupMain_runCompiledTo [] (initSevm message) (initDevm message) 1000
      (by rfl)
      (by
        change (target, implementationSlotLit) ∈ warmKeys
        exact Std.HashSet.mem_insert_self)
      (by
        change (target, adminSlotLit) ∉ warmKeys
        simp only [warmKeys, Std.HashSet.mem_insert,
          Std.HashSet.not_mem_emptyWithCapacity, or_false, beq_iff_eq,
          Prod.mk.injEq, true_and]
        exact (show implementationSlotLit ≠ adminSlotLit by decide))
      (by
        change (originalState.get target).stor.get implementationSlotLit = 0
        exact originalState_target_implementation_zero)
      (by
        change (currentState.get target).stor.get implementationSlotLit =
          implementation.toB256
        exact currentState_target_implementation)
      (by
        change (originalState.get target).stor.get adminSlotLit = 0
        exact originalState_target_admin_zero)
      (by
        change (currentState.get target).stor.get adminSlotLit = 0
        exact currentState_target_admin_zero)
  have raw : exec (initEvm message) = .ok post := by
    apply Func.exec_of_runCompiled_prefix
        (l := []) (FS := []) (p := setupMain)
        (pfx := implementationBytes) (sfx := [])
    · exact Func.RunCompiled.of_runCompiledTo_ok walk
    · exact setupMain_noCalls
    · simpa only [implementationCode, ByteArray.toList_eq_toList_data]
        using setupMain_compile
    · simp only [initSevm, message, implementationCode,
        ByteArray.toList_eq_toList_data, List.append_nil]
  have settled : processMessage message = .ok post := by
    apply MessageExecution.processMessage_clean_of_exec
    · rfl
    · rfl
    · exact raw
    · simpa [initDevm, Devm.error] using error
  exact ⟨post, settled, by simpa [initDevm, Devm.error] using error, output,
    implementationSlot, adminSlot,
      by simpa [initDevm, Devm.logs] using logs⟩

end Blanc.ProxyPair.OssifiableBothSlotFixture
