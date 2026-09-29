import Blanc.Lift.BeaconDeposit.Creation.Check
import Blanc.Lift.BeaconDeposit.Creation.Walk
import Blanc.Lift.Deploy

/-!
# Deploying the Beacon deposit contract from its actual creation input

`beacon_create`: executing the deposit contract's recorded creation input (6,633 bytes,
`Creation/Cert.lean`, registered in `scripts/lift/certificates.json` as
`beacon-deposit-creation`) as a CREATE message (`processCreateMessage`) under a covered fork
succeeds, installs exactly the certified deployed runtime `Blanc.Lift.BeaconDeposit.code` at the
new address, and leaves storage satisfying the history theorem's checkpoint premise
`SolInv … []` (the O1 postcondition of `Blanc/Lift/BeaconDeposit/Init.lean`).

The constructor's 31 SHA-256 precompile calls stay symbolic: the stored table is
`zeroHash Bytes.sha256 h` by the definition of `zeroHash`.

**Scope.**  Jaune's covered forks are Prague-era rule sets, while the historical deployment
(block 11,052,984, 2020) predates Prague; this is the modeled deployment of the recorded
input, not a statement about historical inclusion.  Gas: any message gas in
`[need 0 + 45, 2^64 + 45)` (at least 2,210,045) suffices.
-/

namespace Blanc.Lift.BeaconDeposit.Creation

open Jaune Blanc.BeaconDeposit Blanc.Lift.BeaconDeposit

/-- The constructor's table is the checkpoint premise's zero-hash table over an empty
accumulator. -/
theorem solInv_of_ctorStor {s : Stor} (h : CtorStor 31 s) : SolInv s [] := by
  have hlow : ∀ x : B256, x.toNat < 33 → s.get x = 0 := fun x hx => by
    rw [h x, if_neg (by omega)]
  have hbranch : ∀ k, k < 32 → s.get (solBranchSlot k) = 0 := fun k hk =>
    hlow _ (by rw [solBranchSlot, toNat_toB256' (by omega)]; omega)
  have hcount : s.get solCountSlot = 0 := hlow _ (by decide)
  have hbr : (fun k => if k < 32 then s.get (solBranchSlot k) else 0) = fun _ => (0 : B256) := by
    funext k
    by_cases hk : k < 32
    · simp only [hk, ↓reduceIte, hbranch k hk]
    · simp only [hk, ↓reduceIte]
  have hacc : solAcc s = Acc.empty := congrArg₂ Acc.mk hbr (by rw [hcount]; rfl)
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [solZeroHashSlot]
    exact ctorStor_get h (by omega) (by omega)
  · rw [hacc]
    exact empty_inv _

/-- **Deploying the Beacon deposit contract.**  The recorded creation input, executed as a
zero-value CREATE message with enough gas, a warm and undelegated SHA-256 precompile, under a
covered fork, succeeds; the new account's code is the certified deployed runtime and its
storage satisfies the history theorem's checkpoint premise over the empty deposit history. -/
theorem beacon_create (msg : Msg) (hvalue : msg.value = 0) (hcodeAddress : msg.codeAddress = .none)
    (hcode : msg.code = code) (hgas : need 0 + 45 ≤ msg.gas) (hgasb : msg.gas < 2 ^ 64 + 45)
    (hshaCode : getDelegatedCodeAddress (msg.benv.state.getCode 2) = none)
    (hshaWarm : (2 : Adr) ∈ msg.accessedAddresses)
    (hpre : decide (msg.benv.stat.rules.isPrecomp 2) = true)
    (hfork : CoveredFork msg.benv.stat.fork) (hstatic : msg.isStatic = false)
    (hdepth : msg.depth ≠ 0) (hmax : 6358 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (Devm.getStor post msg.currentTarget) [] := by
  obtain ⟨benv, htransfer⟩ :=
    benvAfterTransfer_exists_zero (msg := processCreateMessage.msg msg) hvalue
  set sevm := initSevm (createSeed msg benv) with hsevm
  set b := initDevm (createSeed msg benv) with hb
  have hstat : sevm.benvStat = msg.benv.stat := by
    show benv.stat = (processCreateMessage.msg msg).benv.stat
    exact benvAfterTransfer_stat htransfer
  have fr : CtorFrame sevm :=
    ⟨by rw [hstat]; exact hpre, by rw [hstat]; exact hfork, hdepth, hstatic⟩
  have st : CtorStart sevm b := by
    refine ⟨hcode, hvalue, fun x => ?_, ?_, hshaWarm, rfl⟩
    · show (benv.state.getStor msg.currentTarget).get x = 0
      rw [benvAfterTransfer_ok_getStor htransfer, processCreateMessage_msg_getStor_currentTarget]
      rfl
    · show getDelegatedCodeAddress (benv.state.getCode 2) = none
      rw [benvAfterTransfer_ok_getCode htransfer, processCreateMessage.msg_getCode]
      exact hshaCode
  obtain ⟨raw, hrun, hout, herr, hstor, hgasLeft, -⟩ :=
    ctor_run fr st (G := msg.gas - 45) (by omega) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - 45 + 45) = b :=
    pre_eq_St rfl rfl (by show msg.gas - 45 + 45 = msg.gas; omega)
  rw [hpre0] at hrun
  have hwin : raw.output = Blanc.Lift.BeaconDeposit.code.toList := by
    rw [hout, runtimeWindow, ByteArray.sliceD_eq]
    exact runtime_window
  have hlen : raw.output.length = 6358 := by rw [hout]; exact runtimeWindow_length
  obtain ⟨post, hpost, hcodePost, hstorPost, -⟩ := liftCreate_ok cert_check jumps_ok msg
    hcodeAddress hcode hfork htransfer hrun herr
    (by rw [hwin, ByteArray.toList_eq_toList_data]; decide) (by rw [hlen]; exact le_trans (by decide) hgasLeft)
    (by rw [hlen]; exact hmax)
  refine ⟨post, hpost, hcodePost.trans hwin, ?_⟩
  rw [hstorPost]
  exact solInv_of_ctorStor hstor

/-! ## The recorded deployment, closed -/

/-- The recorded deployer of the deposit contract (creation transaction
`0xe75fb554…a7e1d0`, block 11,052,984, sender nonce 0). -/
def deployer : Adr := 0xb20a608c624ca5003905aa834de7156c68b2e1d0

/-- The deposit contract's address. -/
def depositAddress : Adr := 0x00000000219ab540356cbb839cbe05303d7705fa

/-- The deposit address is the CREATE address of the deployer at nonce 0. -/
theorem depositAddress_eq : depositAddress = computeContractAddress deployer 0 := by
  have hsender : deployer.toBytes = [0xb2, 0x0a, 0x60, 0x8c, 0x62, 0x4c, 0xa5, 0x00, 0x39, 0x05,
      0xaa, 0x83, 0x4d, 0xe7, 0x15, 0x6c, 0x68, 0xb2, 0xe1, 0xd0] := by decide +kernel
  have hnonce : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have hrlp : BLT.toBytes (.list [.bytes [0xb2, 0x0a, 0x60, 0x8c, 0x62, 0x4c, 0xa5, 0x00, 0x39,
      0x05, 0xaa, 0x83, 0x4d, 0xe7, 0x15, 0x6c, 0x68, 0xb2, 0xe1, 0xd0], .bytes []]) =
      [0xd6, 0x94, 0xb2, 0x0a, 0x60, 0x8c, 0x62, 0x4c, 0xa5, 0x00, 0x39, 0x05, 0xaa, 0x83, 0x4d,
        0xe7, 0x15, 0x6c, 0x68, 0xb2, 0xe1, 0xd0, 0x80] := by
    simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin]
  unfold computeContractAddress
  simp only [hsender, hnonce, hrlp]
  decide +kernel

/-- The creation message: from the recorded deployer, the recorded creation input, to the
deposit address, zero value, 3,000,000 gas, Jaune's default Prague environment (empty world),
the SHA-256 precompile warm.  A message, not a validated transaction. -/
def deployMsg : Msg where
  benv := default
  tenv := default
  caller := deployer
  target := none
  currentTarget := depositAddress
  gas := 3000000
  value := 0
  data := []
  codeAddress := none
  code := code
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := (Std.HashSet.emptyWithCapacity : AdrSet).insert 2
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- **The recorded deployment, closed.**  The deposit address is the deployer's nonce-0 CREATE
address, and executing the recorded creation input from the deployer as a Prague CREATE
message succeeds, installs exactly the certified deployed runtime there, and leaves storage
satisfying the history theorem's checkpoint premise over the empty deposit history. -/
theorem beacon_deploy :
    depositAddress = computeContractAddress deployer 0 ∧
    ∃ post, processCreateMessage deployMsg = .ok post ∧
      (post.getCode depositAddress).toList = Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv (Devm.getStor post depositAddress) [] :=
  ⟨depositAddress_eq, beacon_create deployMsg rfl rfl rfl (by decide) (by decide) rfl
    (Std.HashSet.mem_insert_self) (by decide) CoveredFork.prague rfl (by decide) (by decide)⟩

end Blanc.Lift.BeaconDeposit.Creation
