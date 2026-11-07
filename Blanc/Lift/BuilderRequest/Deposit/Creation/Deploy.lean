import Blanc.Lift.BuilderRequest.Deposit.Creation.Check
import Blanc.Lift.BuilderRequest.Deposit.Creation.Address
import Blanc.Lift.RuntimeInstall

/-!
# Deploying the builder deposit contract

`create_install`: the constructor run settles as a creation installing exactly the registered
runtime with empty storage. `factory_deploy`: the factory message with the recorded salt and init
code does so at the computed address, under each covered fork. This is message execution; the Safe
path that carried the mainnet message is not executed here.
-/

namespace Blanc.Lift.BuilderRequest.Deposit.Creation

open Jaune Blanc.Lift Blanc.Lift.Create2Factory

/-- The constructor's walk and its total charge: copy and return 628 bytes. -/
def constructorGas : Nat := 136

theorem runtime_length : Blanc.Lift.BuilderRequest.Deposit.code.toList.length = 628 := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  rfl

theorem runtime_prefix : Blanc.Lift.BuilderRequest.Deposit.code.toList.head? ≠ some 0xEF := by
  decide +kernel

/-- The runtime window of the recorded init code. -/
theorem runtime_window :
    creationCode.sliceD 10 628 0 = Blanc.Lift.BuilderRequest.Deposit.code.toList := by
  have h := creation_runtime_window constructorPrefix Blanc.Lift.BuilderRequest.Deposit.code
  rw [runtime_length] at h
  exact h

/-- **The creation.** A zero-value creation frame running the recorded init code under a covered
fork installs the runtime, with empty storage and nonce one above the entry nonce. -/
theorem create_install (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (hcodeAddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hvalue : msg.value = 0) (hgas : 125736 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.getCode msg.currentTarget = Blanc.Lift.BuilderRequest.Deposit.code ∧
      post.getStor msg.currentTarget = Stor.empty ∧
      (post.state.get msg.currentTarget).nonce =
        (msg.benv.state.get msg.currentTarget).nonce + 1 := by
  let sevm := initSevm (processCreateMessage.msg msg)
  let b := initDevm (processCreateMessage.msg msg)
  have hrules : sevm.benvStat = msg.benv.stat := rfl
  obtain ⟨G, hG⟩ : ∃ G, G = msg.gas - constructorGas := ⟨_, rfl⟩
  have hdep : 125600 ≤ G := by
    unfold constructorGas at hG
    omega
  have hwalk := push0RuntimeReturn_runExact (fs := cert.prog) (sevm := sevm) (b := b) (S := [])
    (G := G) (sizeHead := 0x02) (sizeTail := [0x74]) (offsetHead := 0x0a) (offsetTail := [])
    (sizeBound := by decide) (offsetBound := by decide) (le0 := by decide) (le1 := by decide)
    (size := 628) (offset := 10) (hfork.rules_push0) (by decide) (by decide) (by decide) (by decide)
  have htotal : G + 2 + (3 + gasCopy * ceilDiv (628 : B256).toNat 32 +
      calculateMemoryGasCost (memExtSize 0 0 (628 : B256).toNat)) + 2 + 3 + 3 + 3 = msg.gas := by
    have hk : gasCopy * ceilDiv (628 : B256).toNat 32 = 60 := by decide
    have hm : calculateMemoryGasCost (memExtSize 0 0 (628 : B256).toNat) = 60 := by decide
    rw [hk, hm]
    unfold constructorGas at hG
    omega
  rw [htotal, show St b [] Mem.empty msg.gas = b from (St.self rfl rfl).symm] at hwalk
  have hsevmCode : sevm.code = creationCode := hcode
  rw [hsevmCode] at hwalk
  have hslice : creationCode.sliceD (10 : B256).toNat (628 : B256).toNat (Linst.toUInt8 .stop) =
      Blanc.Lift.BuilderRequest.Deposit.code.toList := runtime_window
  rw [hslice] at hwalk
  obtain ⟨post, hcreate, herror, hinstalled, hstor, hnonce⟩ :=
    install_of_run cert_check jumps_ok (runtime := Blanc.Lift.BuilderRequest.Deposit.code) msg
      hcodeAddress hcode hfork.rules_stateGas_none hvalue ⟨t_0000_c0, rfl, hwalk⟩ rfl rfl
      (by rw [← List.length_pos_iff, runtime_length]; decide) runtime_prefix
      (by
        rw [runtime_length]
        have hk : 628 * gasCodeDeposit = 125600 := by decide
        rw [hk]
        exact hdep)
      (by
        rw [runtime_length, covered_maxCodeSize hfork]
        decide)
  refine ⟨post, hcreate, herror, hinstalled, ?_, ?_⟩
  · rw [hstor]
    exact processCreateMessage_msg_getStor_currentTarget msg
  · rw [hnonce]
    exact processCreateMessage_msg_nonce msg

/-- **The deployment.** The factory message with the recorded salt and init code, under a covered
fork, installs exactly the runtime at the computed address, with storage all zero, with nonce one.
The premises are the message's own identification, the target's nonce and code that the actual
collision check reads, and a gas floor. This is message execution: that a mainnet transaction delivered this message is not claimed. -/
theorem factory_deploy (msg : Msg) (h : FactoryMessage msg salt initBytes)
    (hfork : CoveredFork msg.benv.stat.fork)
    (hnonce0 : (msg.benv.state.get address).nonce = 0)
    (hcode0 : (msg.benv.state.get address).code.size = 0)
    (hgas : 170000 ≤ msg.gas) :
    ∃ post, processMessage msg = .ok post ∧ post.error = none ∧
      post.state.getCode address = Blanc.Lift.BuilderRequest.Deposit.code ∧
      post.state.getStor address = Stor.empty ∧
      post.state.getNonce address = 1 := by
  have hover : overhead initBytes.length = 32317 := by
    rw [initBytes_length]
    decide
  refine factory_install (n := 638) (need := 125736) h hfork (by rw [initBytes_length]; rfl)
    (by rw [initBytes_length]; decide) (by rw [initBytes_length]; decide) calldata_length_word
    address_eq address_ne_factory address_toB256_ne_zero hnonce0 hcode0 (by rw [hover]; omega)
    (by
      rw [hover]
      unfold except64th
      omega)
    (fun cm hcm hcmgas => create_install cm (hcm.stat ▸ hfork) hcm.codeAddress hcm.code
      hcm.value hcmgas)

end Blanc.Lift.BuilderRequest.Deposit.Creation
