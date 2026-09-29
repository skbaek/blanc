import Blanc.Lift.Weth9.Creation.Check
import Blanc.Lift.Weth9.Creation.Walk
import Blanc.Lift.Weth9.Spec
import Blanc.Lift.Deploy
import Blanc.BalanceAlgebra

/-!
# Deploying WETH9 from its actual creation input

`weth9_create`: executing WETH9's recorded creation input (3,504 bytes, `Creation/Cert.lean`,
registered in `scripts/lift/certificates.json` as `weth9-creation`) as a CREATE message
(`processCreateMessage`) under a covered fork succeeds, installs exactly the certified deployed
runtime `Blanc.Lift.Weth9.code` at the new address, and leaves exactly the constructor's
storage: `name` (slot 0), `symbol` (slot 1) and `decimals = 18` (slot 2), nothing else.

Two readings of the history theorems' initial predicate follow:

* `weth9_create_metadata`: every nonzero word is at a fixed slot `0`, `1` or `2` — the premise of
  the footprint reading's `FootInv.deployed` (no hash fact);
* `weth9_create_solvent`: the original solvency invariant `Solvent … 0 _` holds under the explicit
  hash premise that no address's balance slot is one of the three fixed slots (the constructor
  writes nonzero words there, so without that premise a colliding address would book them).

**Scope.**  Prague-era rules, although the historical deployment (block 4,719,568, 2017)
predates Prague; this is the modeled deployment of the recorded input, not historical inclusion.
Gas: any message gas in `[720000, 2^64)` suffices.
-/

namespace Blanc.Lift.Weth9.Creation

open Jaune Blanc.Lift

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
      · rw [if_neg h2, if_neg h1, if_neg h0] at hx
        exact absurd (by simp [Stor.get, Stor.empty]) hx

/-- **Deploying WETH9.**  The recorded creation input, executed as a zero-value CREATE message
with enough gas under a covered fork, succeeds; the new account's code is the certified deployed
runtime and its storage is exactly the constructor's `name`/`symbol`/`decimals` words. -/
theorem weth9_create (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Blanc.Lift.Weth9.Creation.code)
    (hgas : 720000 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64)
    (hfork : CoveredFork msg.benv.stat.fork) (hstatic : msg.isStatic = false)
    (hmax : 3124 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Weth9.code.toList ∧
      Devm.getStor post msg.currentTarget = deployedStor := by
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
  have hstor : ∀ x, (Devm.getStor b sevm.currentTarget).get x = 0 := fun x => by
    rw [hempty]; simp [Stor.get, Stor.empty]
  have hle := ctorCost_le sevm b
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft⟩ :=
    ctor_run fr hcode hvalue hstor (G := msg.gas - ctorCost sevm b) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - ctorCost sevm b + ctorCost sevm b) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun
  have hwin : raw.output = Blanc.Lift.Weth9.code.toList := by
    rw [hout, runtimeWindow, ByteArray.sliceD_eq]
    exact runtime_window
  have hlen : raw.output.length = 3124 := by rw [hout]; exact runtimeWindow_length
  obtain ⟨post, hpost, hcodePost, hstorPost, -⟩ := liftCreate_ok Blanc.Lift.Weth9.Creation.cert_check
    Blanc.Lift.Weth9.Creation.jumps_ok msg
    hcodeAddress hcode hfork htransfer hrun (by rw [herr]; rfl)
    (by rw [hwin]; exact runtime_head)
    (by rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega) (by rw [hlen]; exact hmax)
  refine ⟨post, hpost, hcodePost.trans hwin, ?_⟩
  rw [hstorPost]
  show Devm.getStor raw sevm.currentTarget = _
  rw [hst, hempty]
  rfl

/-- **The footprint reading's initial premise.**  After the deployment every nonzero storage word
of the new account sits at a fixed slot (`name`, `symbol`, `decimals`). -/
theorem weth9_create_metadata (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = Blanc.Lift.Weth9.Creation.code)
    (hgas : 720000 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64)
    (hfork : CoveredFork msg.benv.stat.fork) (hstatic : msg.isStatic = false)
    (hmax : 3124 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.Weth9.code.toList ∧
      ∀ x, (Devm.getStor post msg.currentTarget).get x ≠ 0 → x ∈ ([0, 1, 2] : List B256) := by
  obtain ⟨post, h1, h2, h3⟩ :=
    weth9_create msg hvalue hcodeAddress hcode hgas hgasb hfork hstatic hmax
  exact ⟨post, h1, h2, by rw [h3]; exact deployedStor_metadata⟩

/-- **The solvency invariant at deployment**, under the explicit hash premise that no address's
balance slot is a fixed slot: nothing is booked, so any balance covers it. -/
theorem deployedStor_solvent (hslots : ∀ a : Adr, balSlot a ∉ ([0, 1, 2] : List B256))
    (bal : B256) : Solvent deployedStor 0 bal := by
  have hbooked : booked deployedStor = fun _ => 0 := by
    funext a
    unfold booked
    split_ifs
    · by_contra hne
      exact hslots a (deployedStor_metadata _ hne)
    · rfl
  have hsum : sum (fun _ : Adr => (0 : B256)) = 0 := sumBelow_zero _
  have hb : bookedSum deployedStor = 0 := by rw [bookedSum, hbooked, hsum]
  have h0 : (0 : B256).toNat = 0 := rfl
  rw [Solvent, hb, h0]
  exact Nat.zero_le _

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
    simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin]
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

/-- **The recorded WETH9 deployment, closed.**  WETH9's address is the deployer's nonce-446
CREATE address, and executing the recorded creation input from the deployer as a Prague CREATE
message succeeds, installs exactly the certified deployed runtime there, and leaves exactly the
constructor's `name`/`symbol`/`decimals` storage. -/
theorem weth9_deploy :
    weth9Address = computeContractAddress deployer 446 ∧
    ∃ post, processCreateMessage deployMsg = .ok post ∧
      (post.getCode weth9Address).toList = Blanc.Lift.Weth9.code.toList ∧
      Devm.getStor post weth9Address = deployedStor :=
  ⟨weth9Address_eq, weth9_create deployMsg rfl rfl rfl (by decide) (by decide)
    CoveredFork.prague rfl (by decide)⟩

end Blanc.Lift.Weth9.Creation
