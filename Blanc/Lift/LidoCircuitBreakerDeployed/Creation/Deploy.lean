import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Check
import Blanc.Lift.LidoCircuitBreakerDeployed.Creation.Walk
import Blanc.Lift.LidoCircuitBreakerDeployed.Init
import Blanc.Lift.LidoCircuitBreakerDeployed.Foreign
import Blanc.Lift.Deploy

/-!
# Deploying the Lido CircuitBreaker from its actual creation input

`lido_create`: executing the Lido CircuitBreaker's recorded creation input (5,638 bytes: the solc
0.8.34 constructor, the 4,584-byte runtime template, and the 224 bytes of ABI-encoded mainnet
constructor arguments; `Creation/Cert.lean`, registered in `scripts/lift/certificates.json` as
`lido-circuit-breaker-creation`) as a CREATE message (`processCreateMessage`) under a covered
fork succeeds, installs exactly the certified deployed runtime
`Blanc.Lift.LidoCircuitBreakerDeployed.code` at the new address (the template with the five
immutables patched into its twelve reference spans, `runtime_window`), and leaves the storage
`deployedStor`: slot 0 (`pauseDuration`) the initial pause duration 1,814,400 and slot 1
(`heartbeatInterval`) the initial heartbeat interval 31,536,000, and nothing else.

`lido_create_registryZeroRaw` / `lido_create_stateInv`: that storage satisfies the Lido history
theorems' checkpoint premise `RegistryZeroRaw` (respectively `lidoSpec.StateInv`), under the two
explicit, bounded hash premises `ForeignApart 0 0` and `ForeignApart 0 1`: the constructor's two
writes (slots 0 and 1) are off the raw slot of every canonical Registry key family (assignment,
index and count words of canonical addresses, and the array length), the same per-written-slot
collision premise the history theorems use for foreign writes.  It is a statement about Keccak
outputs, not a fact the model can decide.

**Scope.**  Jaune's covered forks are Prague-era rule sets, while the historical deployment
(block 24,993,190, 2026-04-30) is a mainnet transaction; this is the modeled CREATE message of
the recorded input, not a statement about historical inclusion.  The closed instance is a message
over Jaune's default environment (empty world), not a validated transaction.  Gas: any message gas
of at least 1,000,000 suffices (the constructor costs at most 55,177 and the code deposit 916,800).
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed.Creation

open Jaune Blanc Blanc.Lift Blanc.LidoCircuitBreaker

/-! ## The deployed storage and the checkpoint premise -/

/-- The storage the constructor leaves: `pauseDuration := 1814400` (slot 0) and
`heartbeatInterval := 31536000` (slot 1). -/
def deployedStor : Stor := (Stor.empty.set 0 1814400).set 1 31536000

/-- A write to a slot off every Registry key family keeps the raw-slot zero premise. -/
theorem registryZeroRaw_set_foreign {s : Stor} (h : RegistryZeroRaw s) {w v : B256}
    (hfa : ForeignApart 0 w) : RegistryZeroRaw (s.set w v) := by
  refine ⟨?_, fun p hp => ?_⟩
  · have hk := hfa arrayLengthSlot (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    rw [solKey_arrayLengthSlot] at hk
    rw [Stor.get_set_ne s hk.symm v]
    exact h.1
  · obtain ⟨ha, hi, hc⟩ := h.2 p hp
    have hka := hfa (assignmentSlot p) (Or.inl ⟨p, hp, rfl⟩)
    have hki := hfa (indexSlot p) (Or.inr (Or.inl ⟨p, hp, rfl⟩))
    have hkc := hfa (countSlot p) (Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩)))
    rw [solKey_assignmentSlot hp] at hka
    rw [solKey_indexSlot hp] at hki
    rw [solKey_countSlot hp] at hkc
    rw [Stor.get_set_ne s hka.symm v, Stor.get_set_ne s hki.symm v, Stor.get_set_ne s hkc.symm v]
    exact ⟨ha, hi, hc⟩

/-- **The checkpoint premise at deployment.**  The constructor's storage satisfies
`RegistryZeroRaw` when its two written slots are off the Registry's raw slots. -/
theorem registryZeroRaw_deployedStor (hfa0 : ForeignApart 0 0) (hfa1 : ForeignApart 0 1) :
    RegistryZeroRaw deployedStor :=
  registryZeroRaw_set_foreign (registryZeroRaw_set_foreign registryZeroRaw_empty hfa0) hfa1

/-! ## Deployment -/

/-- **Deploying the Lido CircuitBreaker.**  The recorded creation input, executed as a zero-value
CREATE message with enough gas under a covered fork, succeeds; the new account's code is the
certified deployed runtime and its storage is `deployedStor`. -/
theorem lido_create (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hgas : 1000000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork)
    (hstatic : msg.isStatic = false) (hmax : 4584 ≤ msg.benv.stat.rules.code.maxCodeSize) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList =
        Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
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
  have hle := ctorCost_le sevm b
  obtain ⟨raw, hrun, hout, herr, hst, hgasLeft⟩ :=
    ctor_run_facts fr hcode hvalue hempty (b := b) (G := msg.gas - ctorCost sevm b) (by omega)
  have hpre0 : St b [] Mem.empty (msg.gas - ctorCost sevm b + ctorCost sevm b) = b :=
    pre_eq_St rfl rfl (by show _ = msg.gas; omega)
  rw [hpre0] at hrun
  have hlen : raw.output.length = 4584 := by
    rw [hout]; exact Blanc.Lift.LidoCircuitBreakerDeployed.code_toList_length
  obtain ⟨post, hpost, hcodePost, hstorPost, -⟩ := liftCreate_ok cert_check jumps_ok msg
    hcodeAddress hcode hfork htransfer hrun (by rw [herr]; rfl)
    (by rw [hout]; exact runtime_head)
    (by rw [hlen, hgasLeft]; unfold gasCodeDeposit; omega)
    (by rw [hlen]; exact hmax)
  refine ⟨post, hpost, hcodePost.trans hout, ?_⟩
  rw [hstorPost]
  show Devm.getStor raw sevm.currentTarget = _
  rw [hst]
  rfl

/-- **The checkpoint premise after deployment.**  With the constructor's two written slots off
the Registry's raw slots, deployment leaves the storage satisfying `RegistryZeroRaw`. -/
theorem lido_create_registryZeroRaw (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hgas : 1000000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork)
    (hstatic : msg.isStatic = false) (hmax : 4584 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hfa0 : ForeignApart 0 0) (hfa1 : ForeignApart 0 1) :
    ∃ post, processCreateMessage msg = .ok post ∧
      (post.getCode msg.currentTarget).toList =
        Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      RegistryZeroRaw (Devm.getStor post msg.currentTarget) := by
  obtain ⟨post, h1, h2, h3⟩ := lido_create msg hvalue hcodeAddress hcode hgas hfork hstatic hmax
  exact ⟨post, h1, h2, by rw [h3]; exact registryZeroRaw_deployedStor hfa0 hfa1⟩

/-- **The checkpoint state invariant after deployment.**  The same premises give
`lidoSpec.StateInv` of the deployed world. -/
theorem lido_create_stateInv (msg : Msg) (hvalue : msg.value = 0)
    (hcodeAddress : msg.codeAddress = .none) (hcode : msg.code = code)
    (hgas : 1000000 ≤ msg.gas) (hfork : CoveredFork msg.benv.stat.fork)
    (hstatic : msg.isStatic = false) (hmax : 4584 ≤ msg.benv.stat.rules.code.maxCodeSize)
    (hfa0 : ForeignApart 0 0) (hfa1 : ForeignApart 0 1) :
    ∃ post, processCreateMessage msg = .ok post ∧
      lidoSpec.StateInv msg.currentTarget post.state := by
  obtain ⟨post, h1, h2, h3⟩ :=
    lido_create_registryZeroRaw msg hvalue hcodeAddress hcode hgas hfork hstatic hmax hfa0 hfa1
  have h2' : (post.state.getCode msg.currentTarget).toList =
      Blanc.Lift.LidoCircuitBreakerDeployed.code.toList := h2
  exact ⟨post, h1, stateInv_of_registryZeroRaw (by rw [h2']; rfl) h3⟩

/-! ## The recorded deployment, closed -/

/-- The recorded deployer of the Lido CircuitBreaker (creation transaction `0x9a1328c1…5279f`,
block 24,993,190, sender nonce 0). -/
def deployer : Adr := 0xacf5f111399a7c613d2f5b96b70f2ea464d3cdf3

/-- The CircuitBreaker's address. -/
def breakerAddress : Adr := 0x6019cb557978296ba3c08a7b73225c0975dfb2f7

/-- The CircuitBreaker's address is the CREATE address of the deployer at nonce 0. -/
theorem breakerAddress_eq : breakerAddress = computeContractAddress deployer 0 := by
  have hsender : deployer.toBytes = [0xac, 0xf5, 0xf1, 0x11, 0x39, 0x9a, 0x7c, 0x61, 0x3d, 0x2f,
      0x5b, 0x96, 0xb7, 0x0f, 0x2e, 0xa4, 0x64, 0xd3, 0xcd, 0xf3] := by decide +kernel
  have hnonce : (UInt64.toBytes 0).sig = [] := by decide +kernel
  have hrlp : BLT.toBytes (.list [.bytes [0xac, 0xf5, 0xf1, 0x11, 0x39, 0x9a, 0x7c, 0x61, 0x3d,
      0x2f, 0x5b, 0x96, 0xb7, 0x0f, 0x2e, 0xa4, 0x64, 0xd3, 0xcd, 0xf3], .bytes []]) =
      [0xd6, 0x94, 0xac, 0xf5, 0xf1, 0x11, 0x39, 0x9a, 0x7c, 0x61, 0x3d, 0x2f, 0x5b, 0x96, 0xb7,
        0x0f, 0x2e, 0xa4, 0x64, 0xd3, 0xcd, 0xf3, 0x80] := by
    simp [BLT.toBytes, BLTs.toBytes, BLTs.toBytesJoin]
  unfold computeContractAddress
  simp only [hsender, hnonce, hrlp]
  decide +kernel

/-- The creation message: from the recorded deployer, the recorded creation input with the
mainnet constructor arguments, to the CircuitBreaker's address, zero value, 1,000,000 gas, empty
call data, Jaune's default Prague environment (empty world).  A message, not a validated
transaction. -/
def deployMsg : Msg where
  benv := default
  tenv := default
  caller := deployer
  target := none
  currentTarget := breakerAddress
  gas := 1000000
  value := 0
  data := []
  codeAddress := none
  code := code
  depth := 1024
  shouldTransferValue := true
  isStatic := false
  accessedAddresses := .emptyWithCapacity
  accessedStorageKeys := .emptyWithCapacity
  disablePrecompiles := false

/-- **The recorded Lido CircuitBreaker deployment, closed.**  The CircuitBreaker's address is the
deployer's nonce-0 CREATE address, and executing the recorded creation input from the deployer as
a Prague CREATE message succeeds, installs exactly the certified deployed runtime there, and
leaves storage `deployedStor`. -/
theorem lido_deploy :
    breakerAddress = computeContractAddress deployer 0 ∧
    ∃ post, processCreateMessage deployMsg = .ok post ∧
      (post.getCode breakerAddress).toList = Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      Devm.getStor post breakerAddress = deployedStor :=
  ⟨breakerAddress_eq, lido_create deployMsg rfl rfl rfl (by decide) CoveredFork.prague rfl
    (by decide)⟩

/-- **The recorded deployment establishes the history theorems' checkpoint premise.**  Under the
two bounded hash premises (the constructor's slots 0 and 1 are off the Registry's raw slots), the
closed deployment leaves storage satisfying `RegistryZeroRaw`, and the deployed world satisfies
`lidoSpec.StateInv`. -/
theorem lido_deploy_init (hfa0 : ForeignApart 0 0) (hfa1 : ForeignApart 0 1) :
    ∃ post, processCreateMessage deployMsg = .ok post ∧
      (post.getCode breakerAddress).toList = Blanc.Lift.LidoCircuitBreakerDeployed.code.toList ∧
      RegistryZeroRaw (Devm.getStor post breakerAddress) ∧
      lidoSpec.StateInv breakerAddress post.state := by
  obtain ⟨post, h1, h2, h3⟩ := lido_create deployMsg rfl rfl rfl (by decide)
    CoveredFork.prague rfl (by decide)
  have h3' : Devm.getStor post breakerAddress = deployedStor := h3
  have h2' : (post.state.getCode breakerAddress).toList =
      Blanc.Lift.LidoCircuitBreakerDeployed.code.toList := h2
  have hz : RegistryZeroRaw (Devm.getStor post breakerAddress) := by
    rw [h3']; exact registryZeroRaw_deployedStor hfa0 hfa1
  exact ⟨post, h1, h2, hz, stateInv_of_registryZeroRaw (by rw [h2']; rfl) hz⟩

end Blanc.Lift.LidoCircuitBreakerDeployed.Creation
