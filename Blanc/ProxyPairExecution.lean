import Blanc.ProxyPairProgram
import Blanc.ProxyPairImplementation

/-!
# A concrete installed proxy/implementation pair

This module fixes one pair of accounts and runs the selector-free proxy at the
two 32-byte guard words.  The execution theorems below are deliberately local
to this fixture; no shared execution or settlement helper is introduced here.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Installed pair -/

def proxyAdr : Adr := 0x00000000000000000000000000000000000a0001

def implAdr : Adr := 0x00000000000000000000000000000000000b0002

def callerAdr : Adr := 0x00000000000000000000000000000000000c0003

theorem proxyAdr_ne_implAdr : proxyAdr ≠ implAdr := by decide

def proxyAcct : Acct :=
  { Acct.nil with
    stor := Stor.empty.set implementationSlot implAdr.toB256
    code := proxyCode }

def implAcct : Acct := { Acct.nil with code := implGuardedCode }

def pairState : State :=
  State.set (State.set (.empty : State) implAdr implAcct) proxyAdr proxyAcct

theorem pairState_proxyAcct : pairState.get proxyAdr = proxyAcct := by
  rw [pairState, State.get_set_self]

theorem pairState_implAcct : pairState.get implAdr = implAcct := by
  rw [pairState, State.get_set_ne _ proxyAdr_ne_implAdr, State.get_set_self]

theorem pairState_proxyCode : (pairState.get proxyAdr).code = proxyCode := by
  rw [pairState_proxyAcct]
  rfl

theorem pairState_implCode : (pairState.get implAdr).code = implGuardedCode := by
  rw [pairState_implAcct]
  rfl

theorem pairState_proxySlot :
    (pairState.get proxyAdr).stor.get implementationSlot = implAdr.toB256 := by
  rw [pairState_proxyAcct]
  unfold proxyAcct
  rw [implementationSlot_val]
  rw [Stor.get_set_self]

theorem pairState_implSlot_zero :
    (pairState.get implAdr).stor.get implSlot = 0 := by
  rw [pairState_implAcct]
  rfl

theorem pairState_proxyImplSlot_zero :
    (pairState.get proxyAdr).stor.get implSlot = 0 := by
  rw [pairState_proxyAcct]
  unfold proxyAcct
  rw [Stor.get_set_ne _ implSlot_ne_implementationSlot.symm]
  simp [Stor.empty, Stor.get]

/-! ## The two fixed messages -/

def successData : Bytes := (1 : B256).toBytes

def revertData : Bytes := (0 : B256).toBytes

theorem successData_length : successData.length = 32 := by
  simp [successData, B256.length_toBytes]

theorem revertData_length : revertData.length = 32 := by
  simp [revertData, B256.length_toBytes]

def pairBenv : Benv :=
  { (default : Benv) with
    state := pairState
    stat := { (default : BenvStat) with origState := pairState } }

/-! ## The cold call split -/

theorem proxy_call_gas_split :
    calculateMsgCallGas 0 25095 25095 0 gasColdAccountAccess =
      (24744, 22144) := by
  decide

theorem pairBenv_impl_not_precompile :
    pairBenv.stat.rules.isPrecomp implAdr = false := by decide

/-! ## Entry and child messages -/

def proxyMsgSuccess : Msg :=
  { (default : Msg) with
    benv := pairBenv
    caller := callerAdr
    target := some proxyAdr
    currentTarget := proxyAdr
    gas := 27224
    value := 0
    data := successData
    codeAddress := some proxyAdr
    code := proxyCode
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := true }

def proxyMsgRevert : Msg :=
  { proxyMsgSuccess with data := revertData }

theorem proxyMsgSuccess_code : proxyMsgSuccess.code = proxyCode := rfl

theorem proxyMsgRevert_code : proxyMsgRevert.code = proxyCode := rfl

theorem proxyMsgSuccess_data : proxyMsgSuccess.data = successData := rfl

theorem proxyMsgRevert_data : proxyMsgRevert.data = revertData := rfl

theorem proxyMsgSuccess_gas : proxyMsgSuccess.gas = 27224 := rfl

theorem proxyMsgRevert_gas : proxyMsgRevert.gas = 27224 := rfl

theorem proxyMsgSuccess_target : proxyMsgSuccess.currentTarget = proxyAdr := rfl

theorem proxyMsgRevert_target : proxyMsgRevert.currentTarget = proxyAdr := rfl

theorem proxyMsgSuccess_caller : proxyMsgSuccess.caller = callerAdr := rfl

theorem proxyMsgRevert_caller : proxyMsgRevert.caller = callerAdr := rfl

end Blanc.ProxyPair
