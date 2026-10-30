import Blanc.Lift.Weth9.Creation.Check
import Blanc.Lift.Weth9.Creation.Walk
import Blanc.Lift.Weth9.Spec
import Blanc.Lift.Deploy
import Blanc.BalanceAlgebra
import Blanc.ForkUniform

/-!
# Deploying WETH9 from its actual creation input

`weth9_create_framed` (and `weth9_create_framedH`, from rule facts alone): executing WETH9's
recorded creation input (3,504 bytes, `Creation/Cert.lean`, registered in
`scripts/lift/certificates.json` as `weth9-creation`) as a CREATE message
(`processCreateMessage`) succeeds, installs exactly the certified deployed runtime
`Blanc.Lift.Weth9.code` at the new address, and leaves exactly the constructor's storage
`deployedStor`: `name` (slot 0), `symbol` (slot 1) and `decimals = 18` (slot 2), nothing else.
`deployedStor_metadata`: every nonzero word of it is at a fixed slot `0`, `1` or `2`, the premise
of the footprint reading's `FootInv.deployed` (no hash fact).

`deployer`, `weth9Address` (the CREATE address of the deployer at nonce 446, `weth9Address_eq`)
and the creation message `deployMsg` name the recorded deployment. Gas: any message gas in
`[720000, 2^64)` suffices.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune Blanc.Lift Blanc.ForkUniform

/-- The storage the constructor leaves in a fresh account. -/
def deployedStor : Stor := ctorStor Stor.empty

/-- The constructor's storage holds nonzero words at the fixed slots only. -/
theorem deployedStor_metadata :
    ∀ x, deployedStor.get x ≠ 0 → x ∈ ([0, 1, 2] : List B256) := by
  intro x hx
  unfold deployedStor ctorStor at hx
  rw [Stor.get_set_ite, Stor.get_set_ite, Stor.get_set_ite] at hx
  by_cases h2 : (2 : B256) = x
  · rw [← h2]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
  · by_cases h1 : (1 : B256) = x
    · rw [← h1]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · by_cases h0 : (0 : B256) = x
      · rw [← h0]; exact List.mem_cons_self ..
      · rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right h0] at hx
        exact absurd (by simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
          Std.TreeMap.getD_emptyc]) hx

/-- **Deploying WETH9, from rule facts.**  The recorded creation input, executed as a zero-value
CREATE message with enough gas under rules without state gas and with a flat `SLOAD` price (if any)
of at most 2100, succeeds; the new account's code is the certified deployed
runtime and its storage is exactly the constructor's `name`/`symbol`/`decimals` words. -/
theorem weth9_create_framedH (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Blanc.Lift.Weth9.Creation.code)
    (hgas : 720000 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64)
    (hsg : msg.benv.stat.rules.stateGas = none)
    (hflat : ∀ g, msg.benv.stat.rules.access = .flat g → g.sload ≤ 2100)
    (hstatic : msg.isStatic = false)
    (hmax : 3124 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Weth9.code.toList ∧
      Devm.getStor post msg.currentTarget = deployedStor ∧
      (∀ a, post.state.get a = if a = msg.currentTarget then
        { msg.benv.state.get a with nonce := (msg.benv.state.get a).nonce + 1, stor := deployedStor, code := Blanc.Lift.Weth9.code }
        else msg.benv.state.get a) := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have fr : CtorFrameH sevm := ⟨by rw [hstat]; exact hsg, hstatic⟩
  have hinnerValue : (processCreateMessage.msg msg).value = 0 := hvalue
  have hempty : Devm.getStor b sevm.currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer _ (Or.inl hinnerValue),
      processCreateMessage_msg_getStor_currentTarget]
  have hstor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0 := fun x => by
    rw [hempty]; simp only [Stor.get, Stor.empty, Std.TreeMap.empty_eq_emptyc,
      Std.TreeMap.getD_emptyc]
  have hle := ctorCostH_le sevm b (by rw [hstat]; exact hflat)
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft, hworld⟩ :=
    ctor_run_framedH fr hcode hvalue hstor (G := msg.gas - ctorCostH sevm b) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - ctorCostH sevm b + ctorCostH sevm b) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun
  have hwin : raw.output = Blanc.Lift.Weth9.code.toList := by
    rw [hout, runtimeWindow, ByteArray.sliceD_eq]
    exact runtime_window
  have hlen : raw.output.length = 3124 := by rw [hout]; exact runtimeWindow_length
  have hpost := liftCreate_postH Blanc.Lift.Weth9.Creation.cert_check
    Blanc.Lift.Weth9.Creation.jumps_ok msg
    hcodeAddress hcode hsg htransfer hrun (by rw [herr]; rfl)
    (by rw [hwin]; exact runtime_head)
    (by rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega) (by rw [hlen]; exact hmax)
  let post := liftCreatePost msg.currentTarget
    (raw.recordTouch msg.benv.stat.rules true msg.currentTarget)
  have rfacts := liftCreatePost_facts msg.currentTarget
    (raw.recordTouch msg.benv.stat.rules true msg.currentTarget)
  simp only [Devm.recordTouch_state, Devm.recordTouch_output, Devm.recordTouch_error] at rfacts
  have hcodeEq : (⟨⟨raw.output⟩⟩ : ByteArray) = Blanc.Lift.Weth9.code := by
    rw [hwin]
    rw [ByteArray.toList_eq_toList_data]
  have hrawNe : raw.output ≠ [] := by
    intro hcon
    rw [hcon] at hlen
    exact absurd hlen (by decide)
  have hcodeSize : (({ raw.state.get msg.currentTarget with code :=
      (⟨⟨raw.output⟩⟩ : ByteArray) } : Acct).code.size ≠ 0) := by
    intro hz
    have hz' : (⟨⟨raw.output⟩⟩ : ByteArray) = ByteArray.empty :=
      ByteArray.size_eq_zero_iff.mp hz
    exact hrawNe (congrArg (fun b : ByteArray => b.data.toList) hz')
  have hnotEmpty : ¬ (({ raw.state.get msg.currentTarget with code :=
      (⟨⟨raw.output⟩⟩ : ByteArray) } : Acct).Empty) := by
    intro hem
    exact hcodeSize hem.1
  have hclear : (({ raw.state.get msg.currentTarget with code :=
      (⟨⟨raw.output⟩⟩ : ByteArray) } : Acct).clearIfEmpty =
      { raw.state.get msg.currentTarget with code := (⟨⟨raw.output⟩⟩ : ByteArray) }) := by
    unfold Acct.clearIfEmpty
    rw [ite_eq_right hnotEmpty]
  refine ⟨post, hpost, ?_, ?_, ?_⟩
  · show (post.state.get msg.currentTarget).code.toList = _
    rw [rfacts.2.2.1, hclear, hcodeEq]
  · show (post.state.get msg.currentTarget).stor = _
    rw [rfacts.2.2.1, hclear]
    change Devm.getStor raw sevm.currentTarget = _
    rw [hst, hempty]
    rfl
  · intro a
    by_cases ha : a = msg.currentTarget
    · subst ha
      rw [ite_eq_left rfl, rfacts.2.2.1, hclear, hcodeEq, hworld]
      change { ((((benv.state.setStorVal msg.currentTarget 0 nameSlotWord).setStorVal
        msg.currentTarget 1 symbolSlotWord).setStorVal msg.currentTarget 2 18).get
        msg.currentTarget) with code := Blanc.Lift.Weth9.code } = _
      simp only [State.setStorVal_get_self]
      rw [processCreateMessage_msg_afterTransfer_get hvalue htransfer, ite_eq_left rfl]
      rfl
    · rw [ite_eq_right ha, rfacts.2.2.2 a ha, hworld]
      change (((benv.state.setStorVal msg.currentTarget 0 nameSlotWord).setStorVal
        msg.currentTarget 1 symbolSlotWord).setStorVal msg.currentTarget 2 18).get a = _
      rw [State.get_setStorVal_ne _ _ _ (Ne.symm ha),
        State.get_setStorVal_ne _ _ _ (Ne.symm ha),
        State.get_setStorVal_ne _ _ _ (Ne.symm ha),
        processCreateMessage_msg_afterTransfer_get hvalue htransfer, ite_eq_right ha]

/-- **Deploying WETH9.**  The recorded creation input, executed as a zero-value CREATE message
with enough gas under a covered fork, succeeds; the new account's code is the certified deployed
runtime and its storage is exactly the constructor's `name`/`symbol`/`decimals` words. -/
theorem weth9_create_framed (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Blanc.Lift.Weth9.Creation.code)
    (hgas : 720000 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64)
    (hfork : CoveredFork msg.benv.stat.fork) (hstatic : msg.isStatic = false)
    (hmax : 3124 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Weth9.code.toList ∧
      Devm.getStor post msg.currentTarget = deployedStor ∧
      (∀ a, post.state.get a = if a = msg.currentTarget then
        { msg.benv.state.get a with nonce := (msg.benv.state.get a).nonce + 1, stor := deployedStor, code := Blanc.Lift.Weth9.code }
        else msg.benv.state.get a) :=
  weth9_create_framedH msg hvalue hcodeAddress hcode hgas hgasb hfork.rules_stateGas_none
    (fun _ h => by rw [hfork.rules_access] at h; cases h) hstatic hmax

/-! ## The recorded deployment, closed -/

/-- The recorded deployer of WETH9 (creation transaction `0xb9534341…c5b8442fa3`, block
4,719,568, sender nonce 446). -/
def deployer : Adr := 0x4f26ffbe5f04ed43630fdc30a87638d53d0b0876

/-- WETH9's address. -/
def weth9Address : Adr := 0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2

/-- WETH9's address is the CREATE address of the deployer at nonce 446. -/
theorem weth9Address_eq : weth9Address = computeContractAddress deployer 446 := by
  have hsender : deployer.toBytes = [0x4f, 0x26, 0xff, 0xbe, 0x5f, 0x04, 0xed, 0x43, 0x63, 0x0f,
      0xdc, 0x30, 0xa8, 0x76, 0x38, 0xd5, 0x3d, 0x0b, 0x08, 0x76] := by decide +kernel
  have hnonce : (UInt64.toBytes 446).sig = [0x01, 0xbe] := by decide +kernel
  have hrlp : BLT.toBytes (.list [.bytes [0x4f, 0x26, 0xff, 0xbe, 0x5f, 0x04, 0xed, 0x43, 0x63,
      0x0f, 0xdc, 0x30, 0xa8, 0x76, 0x38, 0xd5, 0x3d, 0x0b, 0x08, 0x76], .bytes [0x01, 0xbe]]) =
      [0xd8, 0x94, 0x4f, 0x26, 0xff, 0xbe, 0x5f, 0x04, 0xed, 0x43, 0x63, 0x0f, 0xdc, 0x30, 0xa8,
        0x76, 0x38, 0xd5, 0x3d, 0x0b, 0x08, 0x76, 0x82, 0x01, 0xbe] := by
    simp only [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin, List.length_cons, List.length_nil,
      zero_add, Nat.reduceAdd, Nat.reduceLT, ↓reduceIte, Nat.toUInt8_eq, UInt8.reduceOfNat,
      UInt8.reduceAdd, List.append_nil, List.cons_append, List.nil_append]
  unfold computeContractAddress
  simp only [hsender, hnonce, hrlp]
  decide +kernel

/-- The creation message: from the recorded deployer, the recorded creation input, to WETH9's
address, zero value, 1,000,000 gas, Jaune's default Prague environment (empty world).  A message,
not a validated transaction. -/
def deployMsg : Msg where
  benv := default
  tenv := default
  caller := deployer
  target := none
  currentTarget := weth9Address
  gas := 1000000
  value := 0
  data := []
  codeAddress := none
  code := Blanc.Lift.Weth9.Creation.code
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

end Blanc.Lift.Weth9.Creation
