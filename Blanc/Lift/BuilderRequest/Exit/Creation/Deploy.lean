import Blanc.Lift.BuilderRequest.Exit.Creation.Check
import Blanc.Lift.BuilderRequest.Exit.Creation.Address
import Blanc.Lift.RuntimeInstall

/-!
# Deploying the builder exit contract

`create_install`: the constructor run settles as a creation installing exactly the registered
runtime with storage slot 0 at the inhibitor and every other slot zero. `factory_deploy`: the factory
message with the recorded salt and init code does so at the computed address, under each covered
fork. This is message execution; the Safe path that carried the mainnet message is not executed here.
-/

namespace Blanc.Lift.BuilderRequest.Exit.Creation

open Jaune Blanc.Lift Blanc.Lift.Create2Factory

/-- The constructor's plain steps: PUSH32, PUSH0, then copy and return 458 bytes. -/
def constructorPlainGas : Nat := 111

theorem runtime_length : Blanc.Lift.BuilderRequest.Exit.code.toList.length = 458 := by
  decide +kernel

theorem jumps_ok : Cert.jumpsOk code cert = true := by
  rfl

theorem runtime_prefix : Blanc.Lift.BuilderRequest.Exit.code.toList.head? ≠ some 0xEF := by
  decide +kernel

/-- The runtime window of the recorded init code. -/
theorem runtime_window :
    creationCode.sliceD 45 458 0 = Blanc.Lift.BuilderRequest.Exit.code.toList := by
  have h := creation_runtime_window constructorPrefix Blanc.Lift.BuilderRequest.Exit.code
  rw [runtime_length] at h
  exact h

/-- **The creation.** A non-static zero-value creation frame running the recorded init code under a
covered fork installs the runtime, with the inhibitor in slot 0, every other slot zero, and nonce one
above the entry nonce. -/
theorem create_install (msg : Msg) (hfork : CoveredFork msg.benv.stat.fork)
    (hcodeAddress : msg.codeAddress = none) (hcode : msg.code = creationCode)
    (hstatic : msg.isStatic = false)
    (hvalue : msg.value = 0) (hgas : 113811 ≤ msg.gas) :
    ∃ post, processCreateMessage msg = .ok post ∧ post.error = none ∧
      post.getCode msg.currentTarget = Blanc.Lift.BuilderRequest.Exit.code ∧
      post.getStor msg.currentTarget = Stor.empty.set 0 B256.max ∧
      (post.state.get msg.currentTarget).nonce =
        (msg.benv.state.get msg.currentTarget).nonce + 1 := by
  let sevm := initSevm (processCreateMessage.msg msg)
  let b := initDevm (processCreateMessage.msg msg)
  have hsg : sevm.benvStat.rules.stateGas = none := hfork.rules_stateGas_none
  have hsstore : sstoreCostH sevm b 0 B256.max ≤ 22100 :=
    sstoreCostH_le (fun g hg => by
      have haccess : sevm.benvStat.rules.access = .eip2929 := hfork.rules_access
      rw [haccess] at hg
      cases hg)
  obtain ⟨G, hG⟩ : ∃ G, G = msg.gas - (constructorPlainGas + sstoreCostH sevm b 0 B256.max) :=
    ⟨_, rfl⟩
  have hdep : 91600 ≤ G := by
    unfold constructorPlainGas at hG
    omega
  have htail := push0RuntimeReturn_runExact (fs := cert.prog) (sevm := sevm)
    (b := afterSstoreH sevm b 0 B256.max) (S := [])
    (G := G) (sizeHead := 0x01) (sizeTail := [0xca]) (offsetHead := 0x2d) (offsetTail := [])
    (sizeBound := by decide) (offsetBound := by decide) (le0 := by decide) (le1 := by decide)
    (size := 458) (offset := 45) (hfork.rules_push0) (by decide) (by decide) (by decide) (by decide)
  have hsevmCode : sevm.code = creationCode := hcode
  rw [hsevmCode] at htail
  have hslice : creationCode.sliceD (45 : B256).toNat (458 : B256).toNat (Linst.toUInt8 .stop) =
      Blanc.Lift.BuilderRequest.Exit.code.toList := runtime_window
  rw [hslice] at htail
  have htotal : G + 2 + (3 + gasCopy * ceilDiv (458 : B256).toNat 32 +
      calculateMemoryGasCost (memExtSize 0 0 (458 : B256).toNat)) + 2 + 3 + 3 + 3 +
      sstoreCostH sevm b 0 B256.max + 2 + 3 = msg.gas := by
    have hk : gasCopy * ceilDiv (458 : B256).toNat 32 = 45 := by decide
    have hm : calculateMemoryGasCost (memExtSize 0 0 (458 : B256).toNat) = 45 := by decide
    rw [hk, hm]
    unfold constructorPlainGas at hG
    omega
  have hstart : St b [] Mem.empty (G + 2 + (3 + gasCopy * ceilDiv (458 : B256).toNat 32 +
      calculateMemoryGasCost (memExtSize 0 0 (458 : B256).toNat)) + 2 + 3 + 3 + 3 +
      sstoreCostH sevm b 0 B256.max + 2 + 3) = b := by
    rw [htotal]
    exact (St.self rfl rfl).symm
  have hwalk : SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 2 + (3 + gasCopy *
      ceilDiv (458 : B256).toNat 32 + calculateMemoryGasCost (memExtSize 0 0 (458 : B256).toNat)) +
      2 + 3 + 3 + 3 + sstoreCostH sevm b 0 B256.max + 2 + 3)) t_0000_c0 (.halted
      ((St (afterSstoreH sevm b 0 B256.max) []
        (Mem.empty.write 0 Blanc.Lift.BuilderRequest.Exit.code.toList) G).withOutput
        Blanc.Lift.BuilderRequest.Exit.code.toList)) := by
    unfold t_0000_c0
    refine rx_push (w := B256.max) rfl (by decide) ?_
    refine rx_push0 (h_push0 := hfork.rules_push0) (by change 1 < 1024; decide) ?_
    refine rx_sstoreH hsg (fun _ => ?_) hstatic ?_
    · have hstipend : gCallStipend = 2300 := rfl
      omega
    · exact htail
  rw [hstart] at hwalk
  have hrawError : (afterSstoreH sevm b 0 B256.max).error = none := by
    rw [afterSstoreH_error]
    rfl
  obtain ⟨post, hcreate, herror, hinstalled, hstor, hnonce⟩ :=
    install_of_run cert_check jumps_ok (runtime := Blanc.Lift.BuilderRequest.Exit.code) msg
      hcodeAddress hcode hfork.rules_stateGas_none hvalue ⟨t_0000_c0, rfl, hwalk⟩ hrawError rfl
      (by rw [← List.length_pos_iff, runtime_length]; decide) runtime_prefix
      (by
        rw [runtime_length]
        have hk : 458 * gasCodeDeposit = 91600 := by decide
        rw [hk]
        exact hdep)
      (by
        rw [runtime_length, covered_maxCodeSize hfork]
        decide)
  refine ⟨post, hcreate, herror, hinstalled, ?_, ?_⟩
  · rw [hstor]
    change Devm.getStor (afterSstoreH sevm b 0 B256.max) sevm.currentTarget = _
    rw [afterSstoreH_getStor_self]
    change ((processCreateMessage.msg msg).benv.state.getStor msg.currentTarget).set 0 B256.max = _
    rw [processCreateMessage_msg_getStor_currentTarget]
  · rw [hnonce]
    exact (afterSstoreH_nonce sevm b 0 B256.max).trans (processCreateMessage_msg_nonce msg)

/-- **The deployment.** The factory message with the recorded salt and init code, under a covered
fork, installs exactly the runtime at the computed address, with slot 0 at the inhibitor and every other slot zero, with nonce one.
The premises are the message's own identification, the target's nonce and code that the actual
collision check reads, and a gas floor. This is message execution: that a mainnet transaction delivered this message is not claimed. -/
theorem factory_deploy (msg : Msg) (h : FactoryMessage msg salt initBytes)
    (hfork : CoveredFork msg.benv.stat.fork)
    (hnonce0 : (msg.benv.state.get address).nonce = 0)
    (hcode0 : (msg.benv.state.get address).code.size = 0)
    (hgas : 150000 ≤ msg.gas) :
    ∃ post, processMessage msg = .ok post ∧ post.error = none ∧
      post.state.getCode address = Blanc.Lift.BuilderRequest.Exit.code ∧
      post.state.getStor address = Stor.empty.set 0 B256.max ∧
      post.state.getNonce address = 1 := by
  have hover : overhead initBytes.length = 32261 := by
    rw [initBytes_length]
    decide
  refine factory_install (n := 503) (need := 113811) h hfork (by rw [initBytes_length]; rfl)
    (by rw [initBytes_length]; decide) (by rw [initBytes_length]; decide) calldata_length_word
    address_eq address_ne_factory address_toB256_ne_zero hnonce0 hcode0 (by rw [hover]; omega)
    (by
      rw [hover]
      unfold except64th
      omega)
    (fun cm hcm hcmgas => create_install cm (hcm.stat ▸ hfork) hcm.codeAddress hcm.code hcm.isStatic
      hcm.value hcmgas)

end Blanc.Lift.BuilderRequest.Exit.Creation
