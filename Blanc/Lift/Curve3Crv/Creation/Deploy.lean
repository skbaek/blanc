import Blanc.Lift.Curve3Crv.Creation.Check
import Blanc.Lift.Curve3Crv.Creation.Walk
import Blanc.Lift.Curve3Crv.Init
import Blanc.Lift.Deploy
import Blanc.BalanceAlgebra

/-!
# Deploying the 3Crv LP token from its actual creation input

`curve_create`: executing the 3Crv LP token's recorded creation input (3,151 bytes with its ABI
arguments: name `"Curve.fi DAI/USDC/USDT"`, symbol `"3Crv"`, decimals 18, supply 0;
`Creation/Cert.lean`, registered as `curve-3crv-creation`) as a CREATE message
(`processCreateMessage`) under a covered fork succeeds, installs exactly the certified deployed
runtime `Blanc.Lift.Curve3Crv.code`, and leaves the storage `deployedStor caller`: the two
strings, decimals 18, `balanceOf[caller] = 0`, `total_supply = 0`, `minter = caller`.

`curve_create_vyInv`: that storage satisfies the history theorem's checkpoint predicate
`VyInv … (fun _ => False)` (no live keys: the supply is 0, so no balance is minted) for the
deployed-shaped state with `minter = caller`, under the explicit hash premise that the
deployer's balance slot `keccak(3 ‖ caller)` is none of the fixed slots (the constructor writes
`0` there after the strings, so a colliding slot would erase one of them).

**Scope.**  Prague-era rules, although the historical deployment (block 10,809,467, 2020)
predates Prague; this is the modeled deployment of the recorded input, not historical inclusion.
Gas: any message gas in `[860000, 2^64)` suffices.
-/

namespace Blanc.Lift.Curve3Crv.Creation

open Jaune Blanc.Lift Blanc.Lift.Curve3Crv

/-! ## The stored words -/

theorem nameData_word : Bytes.toB256 ((code.sliceD 3023 96 (Linst.toUInt8 .stop)).sliceD 32 32 0) =
    curveStrWord curveShapedName := by
  rw [code_slice]; decide +kernel

theorem symbolData_word :
    Bytes.toB256 ((code.sliceD 3087 64 (Linst.toUInt8 .stop)).sliceD 32 32 0) =
      curveStrWord curveShapedSymbol := by
  rw [code_slice]; decide +kernel

theorem loopWord_name0 : loopWord mB4 0x00 0x1c0 0 = Nat.toB256 22 := by
  unfold loopWord
  rw [loopMem_read_other mB4_wf (by decide) 0]
  exact mB4_nameLen

theorem loopWord_name1 : loopWord mB4 0x00 0x1c0 1 = curveStrWord curveShapedName := by
  unfold loopWord
  rw [loopMem_read_other mB4_wf (by decide) 1, mB4,
    Mem.read_write_disjoint wfB3 _ _ (by rw [B256.length_toBytes]; omega), mB3,
    Mem.read_write_disjoint wfB2 _ _ (by rw [sliceD_len] <;> omega), mB2,
    Mem.read_write_disjoint wfB1 _ _ (by rw [sliceD_len] <;> omega), mB1,
    Mem.read_write_disjoint wfA9 _ _ (by rw [sliceD_len] <;> omega), mA9,
    Mem.read_write_disjoint wfA8 _ _ (by rw [sliceD_len] <;> omega), mA8,
    read_write_inside wfA7 (by omega) (by rw [sliceD_len] <;> omega)]
  exact nameData_word

theorem loopWord_symbol0 : loopWord memName 0x01 0x240 0 = Nat.toB256 4 := by
  unfold loopWord
  rw [loopMem_read_other memName_wf (by decide) 0, memName,
    loopMem_read_other mB4_wf (by decide) 2]
  exact mB4_symbolLen

theorem loopWord_symbol1 : loopWord memName 0x01 0x240 1 = curveStrWord curveShapedSymbol := by
  unfold loopWord
  rw [loopMem_read_other memName_wf (by decide) 1, memName,
    loopMem_read_other mB4_wf (by decide) 2, mB4,
    Mem.read_write_disjoint wfB3 _ _ (by rw [B256.length_toBytes]; omega), mB3,
    Mem.read_write_disjoint wfB2 _ _ (by rw [sliceD_len] <;> omega), mB2,
    read_write_inside wfB1 (by omega) (by rw [sliceD_len] <;> omega)]
  exact symbolData_word

theorem strBase0 (i : Nat) : strBase 0x00 + Nat.toB256 i = vyNameBase + Nat.toB256 i := by
  unfold strBase vyNameBase; rfl

theorem strBase1 (i : Nat) : strBase 0x01 + Nat.toB256 i = vySymbolBase + Nat.toB256 i := by
  unfold strBase vySymbolBase; rfl

/-! ## The deployed storage and the checkpoint predicate -/

/-- The strings, as the store loops leave them. -/
def stringsStor : Stor :=
  (((Stor.empty.set vyNameBase (Nat.toB256 22)).set (vyNameBase + Nat.toB256 1)
    (curveStrWord curveShapedName)).set vySymbolBase (Nat.toB256 4)).set
    (vySymbolBase + Nat.toB256 1) (curveStrWord curveShapedSymbol)

/-- The storage the constructor leaves for the deployer `c`. -/
def deployedStor (c : B256) : Stor :=
  (((stringsStor.set 2 18).set (balSlotOf c) 0).set 5 0).set 6 c

/-- The storage without the deployer-dependent writes (concrete). -/
def coreStor : Stor := (stringsStor.set 2 18).set 5 0

/-- The deployed-shaped token state with `minter = a`. -/
def curveDeployedState (a : Adr) : Curve3Crv.State where
  name := curveShapedName
  symbol := curveShapedSymbol
  decimals := 18
  balanceOf := fun _ => 0
  allowances := fun _ _ => 0
  totalSupply := 0
  minter := a

theorem deployedStor_get (c x : B256) :
    (deployedStor c).get x = if 6 = x then c else if balSlotOf c = x then 0 else coreStor.get x := by
  unfold deployedStor coreStor
  simp only [Stor.get_set_ite]
  by_cases h6 : (6 : B256) = x
  · rw [if_pos h6, if_pos h6]
  · rw [if_neg h6, if_neg h6]
    by_cases h5 : (5 : B256) = x
    · rw [if_pos h5, if_pos h5]
      split_ifs <;> rfl
    · rw [if_neg h5, if_neg h5]

theorem coreStor_support : ∀ x, coreStor.get x ≠ 0 → x ∈ vyFixedSlots := by
  intro x hx
  have h0 : ∀ x, Stor.empty.get x ≠ 0 → x ∈ ([] : List B256) := fun x hx =>
    absurd (by simp [Stor.get, Stor.empty]) hx
  have h := get_ne_zero_mem_set (get_ne_zero_mem_set (get_ne_zero_mem_set
    (get_ne_zero_mem_set (get_ne_zero_mem_set (get_ne_zero_mem_set h0 _ _) _ _) _ _) _ _) _ _)
    _ _ x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  unfold vyFixedSlots vyDecimalsSlot vySupplySlot vyMinterSlot
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem vyStr_congr {s t : Stor} {base : B256} {n : Nat} {bs : Bytes}
    (h0 : s.get base = t.get base)
    (h : ∀ j, j < n → s.get (base + Nat.toB256 (j + 1)) = t.get (base + Nat.toB256 (j + 1))) :
    VyStr s base n bs ↔ VyStr t base n bs := by
  have hw : vyStrWords s base n = vyStrWords t base n := by
    unfold vyStrWords
    exact List.flatMap_congr (fun j hj => by rw [h j (List.mem_range.mp hj)])
  unfold VyStr
  rw [h0, hw]

/-- **The checkpoint predicate at deployment.**  The deployed storage satisfies `VyInv` over no
live keys for the deployed-shaped state with `minter = a`, when `a`'s balance slot is not a
fixed slot. -/
theorem deployedStor_vyInv (a : Adr) (hbal : balSlotOf a.toB256 ∉ vyFixedSlots) :
    VyInv (deployedStor a.toB256) (curveDeployedState a) (fun _ => False) := by
  have hne : ∀ x ∈ vyFixedSlots, balSlotOf a.toB256 ≠ x := fun x hx h => hbal (h ▸ hx)
  have hfix : ∀ x ∈ vyFixedSlots, x ≠ 6 → (deployedStor a.toB256).get x = coreStor.get x :=
    fun x hx h6 => by
      rw [deployedStor_get, if_neg (Ne.symm h6), if_neg (hne x hx)]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun _ h => h.elim, fun k _ => by cases k <;> rfl, ?_,
    fun _ _ h => h.elim, fun _ h => h.elim, ?_⟩
  · rw [hfix _ (by simp [vyFixedSlots, vyDecimalsSlot, vySupplySlot, vyMinterSlot]) (by decide)]
    show coreStor.get 2 = 18
    decide +kernel
  · rw [hfix _ (by simp [vyFixedSlots, vyDecimalsSlot, vySupplySlot, vyMinterSlot]) (by decide)]
    show coreStor.get 5 = 0
    decide +kernel
  · show (deployedStor a.toB256).get 6 = a.toB256
    rw [deployedStor_get, if_pos rfl]
  · rw [vyStr_congr (t := coreStor) (hfix _ (by simp [vyFixedSlots, vyDecimalsSlot, vySupplySlot, vyMinterSlot]) (by decide +kernel)) ?_]
    · show VyStr coreStor vyNameBase 2 curveShapedName
      unfold VyStr; decide +kernel
    · intro j hj
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · exact hfix _ (by simp [vyFixedSlots, vyDecimalsSlot, vySupplySlot, vyMinterSlot]) (by decide +kernel)
      · exact hfix _ (by simp [vyFixedSlots, vyDecimalsSlot, vySupplySlot, vyMinterSlot]) (by decide +kernel)
  · rw [vyStr_congr (t := coreStor) (hfix _ (by simp [vyFixedSlots, vyDecimalsSlot, vySupplySlot, vyMinterSlot]) (by decide +kernel)) ?_]
    · show VyStr coreStor vySymbolBase 1 curveShapedSymbol
      unfold VyStr; decide +kernel
    · intro j hj
      rcases (show j = 0 by omega) with rfl
      exact hfix _ (by simp [vyFixedSlots, vyDecimalsSlot, vySupplySlot, vyMinterSlot]) (by decide +kernel)
  · intro x hx
    left
    rw [deployedStor_get] at hx
    by_cases h6 : (6 : B256) = x
    · subst h6; simp [vyFixedSlots, vyMinterSlot]
    · rw [if_neg h6] at hx
      by_cases hb : balSlotOf a.toB256 = x
      · rw [if_pos hb] at hx; exact absurd rfl hx
      · rw [if_neg hb] at hx; exact coreStor_support x hx
  · show (0 : B256).toNat = sum (fun _ : Adr => (0 : B256))
    rw [sum, sumBelow_zero, B256.toNat_zero]

/-! ## Deployment -/

theorem ctor_stor (sevm : Sevm) (b : Devm)
    (hempty : Devm.getStor b sevm.currentTarget = Stor.empty) :
    Devm.getStor (tw8 sevm (worldSymbol sevm b) memSymbol) sevm.currentTarget =
      deployedStor sevm.caller.toB256 := by
  have h0 : (Nat.toB256 0 : B256) = 0 := rfl
  simp only [tw8, Devm.addLog_getStor, tw7, tw6, tw5, tw4, afterSstore_getStor_self, worldSymbol,
    loopWorld_stor2, worldName, hempty, loopWord_name0, loopWord_name1, loopWord_symbol0,
    loopWord_symbol1, strBase0, strBase1, h0, B256.add_zero]
  rfl

/-- **Deploying the 3Crv LP token.**  The recorded creation input, executed as a zero-value CREATE
message with empty call data and enough gas under a covered fork, succeeds; the new account's
code is the certified deployed runtime and its storage is `deployedStor caller`. -/
theorem curve_create (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Blanc.Lift.Curve3Crv.Creation.code)
    (hdata : msg.data = []) (hgas : 860000 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64)
    (hfork : CoveredFork msg.benv.stat.fork) (hstatic : msg.isStatic = false)
    (hmax : 2276 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      Devm.getStor post msg.currentTarget = deployedStor msg.caller.toB256 := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have fr : CtorFrame sevm := ⟨by rw [hstat]; exact hfork, hstatic⟩
  have hempty : Devm.getStor b sevm.currentTarget = Stor.empty := by
    show benv.state.getStor msg.currentTarget = _
    rw [benvAfterTransfer_ok_getStor htransfer, processCreateMessage_msg_getStor_currentTarget]
  have hle := ctorCost_le sevm b
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft⟩ :=
    ctor_run_facts fr hcode hvalue hdata (b := b) (G := msg.gas - ctorCost sevm b) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - ctorCost sevm b + ctorCost sevm b) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun
  have hwin : raw.output = Blanc.Lift.Curve3Crv.code.toList := by
    rw [hout, runtimeWindow, ByteArray.sliceD_eq]
    exact runtime_window
  have hlen : raw.output.length = 2276 := by rw [hout]; exact runtimeWindow_length
  obtain ⟨post, hpost, hcodePost, hstorPost, -⟩ := liftCreate_ok
    Blanc.Lift.Curve3Crv.Creation.cert_check Blanc.Lift.Curve3Crv.Creation.jumps_ok msg
    hcodeAddress hcode hfork htransfer hrun (by rw [herr]; rfl)
    (by rw [hwin]; exact runtime_head)
    (by rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega)
    (by rw [hlen]; exact hmax)
  refine ⟨post, hpost, hcodePost.trans hwin, ?_⟩
  rw [hstorPost]
  show Devm.getStor raw sevm.currentTarget = _
  rw [hst]
  exact ctor_stor sevm b hempty

/-- **The checkpoint predicate after deployment.**  With the deployer's balance slot off the
fixed slots, the deployed storage satisfies `VyInv` over no live keys for the deployed-shaped
state whose minter is the deployer. -/
theorem curve_create_vyInv (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Blanc.Lift.Curve3Crv.Creation.code)
    (hdata : msg.data = []) (hgas : 860000 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64)
    (hfork : CoveredFork msg.benv.stat.fork) (hstatic : msg.isStatic = false)
    (hmax : 2276 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hbal : balSlotOf msg.caller.toB256 ∉ vyFixedSlots) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      VyInv (Devm.getStor post msg.currentTarget) (curveDeployedState msg.caller)
        (fun _ => False) := by
  obtain ⟨post, h1, h2, h3⟩ :=
    curve_create msg hvalue hcodeAddress hcode hdata hgas hgasb hfork hstatic hmax
  exact ⟨post, h1, h2, by rw [h3]; exact deployedStor_vyInv msg.caller hbal⟩

/-! ## The recorded deployment, closed -/

/-- The recorded deployer of the 3Crv LP token (creation transaction `0xa7d90e46…053694f8`, block
10,809,467, sender nonce 42). -/
def deployer : Adr := 0xbabe61887f1de2713c6f97e567623453d3c79f67

/-- The 3Crv LP token's address. -/
def tokenAddress : Adr := 0x6c3f90f043a72fa612cbac8115ee7e52bde6e490

/-- The token's address is the CREATE address of the deployer at nonce 42. -/
theorem tokenAddress_eq : tokenAddress = computeContractAddress deployer 42 := by
  have hsender : deployer.toBytes = [0xba, 0xbe, 0x61, 0x88, 0x7f, 0x1d, 0xe2, 0x71, 0x3c, 0x6f, 0x97, 0xe5, 0x67, 0x62, 0x34, 0x53, 0xd3, 0xc7, 0x9f, 0x67] := by decide +kernel
  have hnonce : (UInt64.toBytes 42).sig = [0x2a] := by decide +kernel
  have hrlp : BLT.toBytes (.list [.bytes [0xba, 0xbe, 0x61, 0x88, 0x7f, 0x1d, 0xe2, 0x71, 0x3c, 0x6f, 0x97, 0xe5, 0x67, 0x62, 0x34, 0x53, 0xd3, 0xc7, 0x9f, 0x67], .bytes [0x2a]]) =
      [0xd6, 0x94, 0xba, 0xbe, 0x61, 0x88, 0x7f, 0x1d, 0xe2, 0x71, 0x3c, 0x6f, 0x97, 0xe5, 0x67, 0x62, 0x34, 0x53, 0xd3, 0xc7, 0x9f, 0x67, 0x2a] := by
    simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin]
  unfold computeContractAddress
  simp only [hsender, hnonce, hrlp]
  decide +kernel

/-- The deployer's balance slot is none of the fixed slots (kernel-evaluated hashes). -/
theorem deployer_balSlot : balSlotOf deployer.toB256 ∉ vyFixedSlots := by decide +kernel

/-- The creation message: from the recorded deployer, the recorded creation input with its
arguments, to the token's address, zero value, 1,000,000 gas, empty call data, Jaune's default
Prague environment (empty world).  A message, not a validated transaction. -/
def deployMsg : Msg where
  benv := default
  tenv := default
  caller := deployer
  target := none
  currentTarget := tokenAddress
  gas := 1000000
  value := 0
  data := []
  codeAddress := none
  code := Blanc.Lift.Curve3Crv.Creation.code
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- **The recorded 3Crv deployment, closed.**  The token's address is the deployer's nonce-42
CREATE address, and executing the recorded creation input from the deployer as a Prague CREATE
message succeeds, installs exactly the certified deployed runtime there, and leaves storage
satisfying the history theorem's checkpoint predicate `VyInv … (fun _ => False)` for the
deployed-shaped state whose minter is the deployer. -/
theorem curve_deploy :
    tokenAddress = computeContractAddress deployer 42 ∧
    ∃ post, processCreateMessage deployMsg = .ok post ∧
      (post.getCode tokenAddress).toList = Blanc.Lift.Curve3Crv.code.toList ∧
      Devm.getStor post tokenAddress = deployedStor deployer.toB256 ∧
      VyInv (Devm.getStor post tokenAddress) (curveDeployedState deployer) (fun _ => False) := by
  refine ⟨tokenAddress_eq, ?_⟩
  obtain ⟨post, h1, h2, h3⟩ := curve_create deployMsg rfl rfl rfl rfl (by decide) (by decide)
    CoveredFork.prague rfl (by decide)
  have h3' : Devm.getStor post tokenAddress = deployedStor deployer.toB256 := h3
  exact ⟨post, h1, h2, h3', by rw [h3']; exact deployedStor_vyInv deployer deployer_balSlot⟩

end Blanc.Lift.Curve3Crv.Creation
