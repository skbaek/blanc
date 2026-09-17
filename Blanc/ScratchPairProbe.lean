import Blanc.Composition.ProrataWethVaultBoundary
import Blanc.Composition.ProrataWethVaultEffects

namespace Blanc.ScratchPairProbe

open Jaune
open Blanc.Composition.ProrataWethVault

def vault : Adr := 0x0000000000000000000000000000000000000001
def owner : Adr := 0x0000000000000000000000000000000000000002
def recipient : Adr := 0x0000000000000000000000000000000000000003
def literalWethAccount : Adr := 0x0000000000000000000000000000000000001000
def wad : B256 := 0x2a

def calldata : Bytes :=
  [0x23, 0xb8, 0x72, 0xdd,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x02,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2a]

theorem probe_calldata_length : calldata.length = 100 := by
  decide +kernel

def gasWord : B256 := 1000000
def inputOffset : B256 := 0
def inputSize : B256 := 100
def outputOffset : B256 := 0
def outputSize : B256 := 0
def rest : List B256 := []

def allowanceKey : B256 :=
  (owner.toB256.toBytes ++ vault.toB256.toBytes).keccak
def wethStor : Stor :=
  (Stor.empty.set owner.toB256 100).set allowanceKey B256.max

def vaultAcct : Acct :=
  { Acct.nil with code := Blanc.prorataWethVaultCode.toByteArray }
def wethAcct : Acct :=
  { Acct.nil with code := Blanc.wethCode.toByteArray, stor := wethStor }

def state : State :=
  State.set (State.set (.empty : State) vault vaultAcct)
    literalWethAccount wethAcct

def benv : Benv :=
  { (default : Benv) with
    state := state
    stat := { (default : BenvStat) with origState := state } }

def msg : Msg :=
  { (default : Msg) with
    benv := benv
    caller := owner
    target := some vault
    currentTarget := vault
    gas := 1000000
    value := 0
    data := calldata
    codeAddress := some vault
    code := Blanc.prorataWethVaultCode.toByteArray
    depth := 1
    shouldTransferValue := false
    isStatic := false
    accessedAddresses := .emptyWithCapacity
    accessedStorageKeys := .emptyWithCapacity
    disablePrecompiles := true }

def sevm : Sevm := initSevm msg
def memory : Mem := ⟨calldata.toArray, 100⟩
def pre : Devm :=
  (initDevm msg).setMach
    ⟨[gasWord, literalWethAccount.toB256, 0, inputOffset, inputSize,
      outputOffset, outputSize] , memory, 1000000⟩

theorem literal_wethAccount : literalWethAccount = wethAccount := by
  decide +kernel

theorem probe_h_stk :
    pre.stack = gasWord :: wethAccount.toB256 :: 0 :: inputOffset :: inputSize ::
      outputOffset :: outputSize :: rest := by
  rfl

theorem probe_h_window :
    (pre.memory.read inputOffset.toNat inputSize.toNat).1 = calldata := by
  decide +kernel

theorem probe_h_depth : sevm.depth ≠ 0 := by
  decide +kernel

theorem probe_h_dynamic : sevm.isStatic = false := by
  rfl

theorem probe_h_gas :
    let base := addAccessedAddress
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩) wethAccount
    let ext := (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).extCost
      [⟨inputOffset.toNat, inputSize.toNat⟩,
        ⟨outputOffset.toNat, outputSize.toNat⟩]
    let acc := accessCost wethAccount
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).accessedAddresses
    (calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext acc).1 + ext ≤
      base.gasLeft := by
  have hacc :
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).accessedAddresses =
        (Std.HashSet.emptyWithCapacity : AdrSet) := by
    rfl
  have hext :
      (pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩).extCost
        [⟨inputOffset.toNat, inputSize.toNat⟩,
          ⟨outputOffset.toNat, outputSize.toNat⟩] = 0 := by
    change calculateMemoryGasCost
        (memExtsSize 100 [(0, 100), (0, 0)]) -
      calculateMemoryGasCost 100 = 0
    decide +kernel
  dsimp
  rw [hext, hacc]
  unfold accessCost
  simp
  change (calculateMsgCallGas 0 1000000 1000000 0 2600).1 + 0 ≤ 1000000
  decide +kernel

theorem probe_config : DirectWethConfiguration vault sevm pre := by
  constructor
  · decide +kernel
  · decide +kernel
  · change ((state.get wethAccount).code).toList = Blanc.wethCode
    rw [show wethAccount = literalWethAccount from literal_wethAccount.symm]
    rw [state, State.get_set_self]
    simp [wethAcct, Bytes.toByteArray, ByteArray.toList_eq_toList_data]

theorem apply_literal_occurrence {post : Devm}
    (run : Ninst.RunCompiled sevm pre Ninst.call post) :
    ExactWethChildOccurrence sevm pre post Ninst.call calldata false := by
  apply exactWethCallOccurrence_of_runCompiled
    (sevm := sevm) (pre := pre) (post := post)
    (gasWord := gasWord) (inputOffset := inputOffset)
    (inputSize := inputSize) (outputOffset := outputOffset)
    (outputSize := outputSize) (rest := rest) (calldata := calldata)
  · exact probe_config
  · exact probe_h_stk
  · exact probe_h_window
  · exact probe_h_depth
  · exact probe_h_dynamic
  · exact probe_h_gas
  · exact run

theorem probe_literal_allowance_slot :
    ¬ ValidAdr ((owner.toB256.toBytes ++ vault.toB256.toBytes).keccak) := by
  rw [validAdr_iff]
  decide +kernel

theorem apply_literal_transferFrom_effect {post : Devm}
    (run : Ninst.RunCompiled sevm pre Ninst.call post)
    (successFlag : ∃ tail, post.stack = (1 : B256) :: tail)
    (returnData : post.returnData = (1 : B256).toBytes) :
    Transfer (Stor.rest (pre.state.getStor wethAccount)) owner wad vault
      (Stor.rest (post.state.getStor wethAccount)) := by
  have occurrence := apply_literal_occurrence run
  have success := ExactWethChildOccurrence.success_of_post occurrence
    successFlag returnData
  have programRun := ExactWethChildSuccess.programRun success
  have hcalldata : calldata = transferFromCalldata owner vault wad := by
    decide +kernel
  rw [hcalldata] at programRun
  exact (SuccessfulWethProgramRun.transferFrom_effect programRun).1

def popped : Devm :=
  pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩
def base : Devm := addAccessedAddress popped literalWethAccount
def ext : Nat := base.extCost
  [⟨inputOffset.toNat, inputSize.toNat⟩,
    ⟨outputOffset.toNat, outputSize.toNat⟩]
def access : Nat := accessCost literalWethAccount popped.accessedAddresses
def msgGas : Nat × Nat :=
  calculateMsgCallGas 0 gasWord.toNat base.gasLeft ext access
def childParent : Devm :=
  callSpawnParent base (msgGas.1 + ext)
    inputOffset.toNat inputSize.toNat outputOffset.toNat outputSize.toNat
def childMsg : Msg :=
  callMsg sevm childParent msgGas.2 0 vault literalWethAccount
    literalWethAccount true false calldata wethAcct.code false

end Blanc.ScratchPairProbe
