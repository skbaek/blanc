import Blanc.ProxyPairOssifiableDeploymentMessage

/-!
# OssifiableProxy concrete empty-setup CREATE fixture

This module instantiates the direct CREATE theorem at explicit selected rules.
The implementation contains `PUSH0; PUSH0; REVERT`, so the empty setup
path is biting: an accidental delegatecall would fail the deployment.
-/

namespace Blanc.ProxyPair.OssifiableCreateFixture

open Jaune

def implementation : Adr :=
  Nat.toAdr 0x6f6541c2203196feedd14cd2c09550da1cbeda31

def admin : Adr :=
  Nat.toAdr 0x8ea83ad72396f1e0cd2f8e72b1461db8eb6af7b5

def target : Adr :=
  Nat.toAdr 0x889edc2edab5f40e902b864ad4d7ade8e412f9b1

def creator : Adr := Nat.toAdr 1

/-- `PUSH0; PUSH0; REVERT`, deliberately hostile to accidental setup calls. -/
def implementationCode : ByteArray :=
  ByteArray.mk [0x5f, 0x5f, 0xfd].toArray

def state : State :=
  let withImplementation := State.set (.empty : State) implementation
    { Acct.nil with code := implementationCode }
  State.set withImplementation creator
    { Acct.nil with bal := 1000000000000000000 }

def benv (rules : ForkRules) : Benv :=
  { (default : Benv) with
    state := state
    stat :=
      { (default : BenvStat) with
        rules := rules
        origState := state } }

def createCode : ByteArray :=
  ByteArray.mk
    (ossifiableEmptyDataCreateInput implementation admin).toArray

private theorem byteArrayMk_toList (bytes : Bytes) :
    (ByteArray.mk bytes.toArray).toList = bytes := by
  rw [ByteArray.toList_eq_toList_data]

def message (rules : ForkRules) : Msg :=
  { (default : Msg) with
    benv := benv rules
    caller := creator
    target := none
    currentTarget := target
    gas := 1000000
    value := 0
    data := []
    codeAddress := none
    code := createCode
    depth := 0
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := false }

@[simp] theorem message_code (rules : ForkRules) :
    (message rules).code.toList =
      ossifiableEmptyDataCreateInput implementation admin := by
  change createCode.toList = _
  exact byteArrayMk_toList _

@[simp] theorem implementation_code :
    state.getCode implementation = implementationCode := by
  unfold state State.getCode
  rw [State.get_set_ne _
    (show creator ≠ implementation by decide) _]
  rw [State.get_set_self]

private theorem target_fresh : state.get target = Acct.nil := by
  unfold state
  rw [State.get_set_ne _ (show creator ≠ target by decide) _]
  rw [State.get_set_ne _ (show implementation ≠ target by decide) _]
  rfl

/-- Closed concrete CREATE certificate for the frozen implementation/admin
tuple and explicit one-million-gas selected-rule message. -/
theorem message_success (rules : ForkRules)
    (hmax : 2188 ≤ rules.code.maxCodeSize) :
    ∃ post, OssifiableEmptySetupCreateResult
      (message rules) implementation admin post := by
  apply processCreateMessage_ossifiable_emptySetup_success
      (message rules) implementation admin
  · rfl
  · rfl
  · exact message_code rules
  · decide
  · decide
  · rw [show (message rules).benv.state = state by rfl, implementation_code]
    decide
  · change implementation ∉ Std.HashSet.emptyWithCapacity
    exact Std.HashSet.not_mem_emptyWithCapacity
  · change (state.get target).stor.get implementationSlotLit = 0
    rw [target_fresh]
    rfl
  · change (target, implementationSlotLit) ∉
      Std.HashSet.emptyWithCapacity
    exact Std.HashSet.not_mem_emptyWithCapacity
  · change (state.get target).stor.get adminSlotLit = 0
    rw [target_fresh]
    rfl
  · change (target, adminSlotLit) ∉ Std.HashSet.emptyWithCapacity
    exact Std.HashSet.not_mem_emptyWithCapacity
  · rfl
  · norm_num [ossifiableCreateMessageGas, message]
  · exact hmax

end Blanc.ProxyPair.OssifiableCreateFixture
