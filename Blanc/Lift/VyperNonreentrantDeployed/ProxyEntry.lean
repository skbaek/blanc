import Blanc.Lift.VyperNonreentrantDeployed.CodeFacts
import Blanc.DelegatecallEnvelope

/-! Exact native entry of the 45-byte deployed Vyper proxy. -/

namespace Blanc.Lift.VyperNonreentrantDeployed

open Jaune

def proxyAddress : Adr := 0x9848482da3ee3076165ce6497eda906e66bb85c5
def implementationAddress : Adr := 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e

private theorem proxy_at_calldatasize_0 :
    Ninst.At proxyCode 0 (.reg .calldatasize) := by rfl

private theorem proxy_at_returndatasize_1 :
    Ninst.At proxyCode 1 (.reg .returndatasize) := by rfl

private theorem proxy_at_returndatasize_2 :
    Ninst.At proxyCode 2 (.reg .returndatasize) := by rfl

private theorem proxy_at_calldatacopy_3 :
    Ninst.At proxyCode 3 (.reg .calldatacopy) := by rfl

private theorem proxy_at_returndatasize_4 :
    Ninst.At proxyCode 4 (.reg .returndatasize) := by rfl

private theorem proxy_at_returndatasize_5 :
    Ninst.At proxyCode 5 (.reg .returndatasize) := by rfl

private theorem proxy_at_returndatasize_6 :
    Ninst.At proxyCode 6 (.reg .returndatasize) := by rfl

private theorem proxy_at_calldatasize_7 :
    Ninst.At proxyCode 7 (.reg .calldatasize) := by rfl

private theorem proxy_at_returndatasize_8 :
    Ninst.At proxyCode 8 (.reg .returndatasize) := by rfl

private theorem proxy_at_push20_9 :
    Ninst.At proxyCode 9
      (.push [0x63, 0x26, 0xde, 0xbb, 0xaa, 0x15, 0xbc, 0xfe, 0x60, 0x3d,
        0x83, 0x1e, 0x7d, 0x75, 0xf4, 0xfc, 0x10, 0xd9, 0xb4, 0x3e]
        (by decide)) := by rfl

private theorem proxy_at_gas_30 :
    Ninst.At proxyCode 30 (.reg .gas) := by rfl

private theorem proxy_step_calldatasize (e : Sevm) (d : Devm) (pc : Nat)
    (hcode : e.code = proxyCode)
    (hat : Ninst.At proxyCode pc (.reg .calldatasize))
    (hgas : gBase ≤ d.gasLeft)
    (hroom : d.stack.length < 1024) :
    Evm.step ⟨pc, e, d⟩ = .cont (pc + 1)
      (d.setMach ⟨e.data.length.toB256 :: d.stack, d.memory,
        d.gasLeft - gBase, d.stateGas⟩) := by
  have hat' : Ninst.At e.code pc (.reg .calldatasize) := by
    rw [hcode]
    exact hat
  rw [Evm.step_next hat', Ninst.step_reg]
  change Step.ofExecution (pc + 1) (pushItem e.data.length.toB256 gBase d) = _
  rw [pushItem_eq_ok hgas hroom]
  rfl

private theorem proxy_step_returndatasize (e : Sevm) (d : Devm) (pc : Nat)
    (hcode : e.code = proxyCode)
    (hat : Ninst.At proxyCode pc (.reg .returndatasize))
    (hgas : gBase ≤ d.gasLeft)
    (hroom : d.stack.length < 1024) :
    Evm.step ⟨pc, e, d⟩ = .cont (pc + 1)
      (d.setMach ⟨d.returnData.length.toB256 :: d.stack, d.memory,
        d.gasLeft - gBase, d.stateGas⟩) := by
  have hat' : Ninst.At e.code pc (.reg .returndatasize) := by
    rw [hcode]
    exact hat
  rw [Evm.step_next hat', Ninst.step_reg]
  change Step.ofExecution (pc + 1) (pushItem d.returnData.length.toB256 gBase d) = _
  rw [pushItem_eq_ok hgas hroom]
  rfl

private theorem proxy_step_calldatacopy (e : Sevm) (d : Devm)
    (hcode : e.code = proxyCode)
    (hdata : e.data.length = 132)
    (hstack : d.stack = [0, 0, (132 : Nat).toB256])
    (hmemory : d.memory = Mem.empty)
    (hgas : 33 ≤ d.gasLeft) :
    Evm.step ⟨3, e, d⟩ = .cont 4
      (d.setMach ⟨[], Mem.empty.write 0 e.data,
        d.gasLeft - 33, d.stateGas⟩) := by
  have hat : Ninst.At e.code 3 (.reg .calldatacopy) := by
    rw [hcode]
    exact proxy_at_calldatacopy_3
  rw [Evm.step_next hat, Ninst.step_reg]
  change Step.ofExecution 4 (Rinst.runCore 3 d e .calldatacopy) = _
  simp only [Rinst.runCore]
  rw [Devm.popToNat_eq_ok hstack]
  simp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok (x := (0 : B256)) (s := [(132 : Nat).toB256]) (by rfl)]
  dsimp only [bind, Except.bind]
  rw [Devm.popToNat_eq_ok (x := (132 : Nat).toB256) (s := []) (by rfl)]
  have h132 : (Nat.toB256 132).toNat = 132 :=
    B256.toNat_toB256_of_lt (by decide)
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach, Devm.stateGas_setMach,
    B256.toNat_zero, h132]
  rw [hmemory]
  have hcost : gVerylow + gasCopy * ceilDiv 132 32 +
      (d.setMach ⟨[], Mem.empty, d.gasLeft, d.stateGas⟩).extCost [(0, 132)] = 33 := by
    simp only [Devm.extCost, Devm.memory_setMach]
    decide
  rw [hcost]
  have hgas' : 33 ≤ (d.setMach ⟨[], Mem.empty, d.gasLeft, d.stateGas⟩).gasLeft := by
    simpa only [Devm.setMach_gasLeft] using hgas
  rw [chargeGas_eq_ok hgas']
  rw [Bytes.sliceD_zero_length hdata]
  rfl

private theorem proxy_step_gas (e : Sevm) (d : Devm)
    (hcode : e.code = proxyCode)
    (hgas : gBase ≤ d.gasLeft)
    (hroom : d.stack.length < 1024) :
    Evm.step ⟨30, e, d⟩ = .cont 31
      (d.setMach ⟨(d.gasLeft - gBase).toB256 :: d.stack, d.memory,
        d.gasLeft - gBase, d.stateGas⟩) := by
  have hat : Ninst.At e.code 30 (.reg .gas) := by
    rw [hcode]
    exact proxy_at_gas_30
  rw [Evm.step_next hat, Ninst.step_reg]
  change Step.ofExecution 31
    (do let d' ← chargeGas gBase d; d'.push d'.gasLeft.toB256) = _
  rw [chargeGas_eq_ok hgas]
  simp only [bind, Except.bind, Devm.gasLeft_setMach]
  rw [Devm.push_eq_ok (devm := d.setMach
    ⟨d.stack, d.memory, d.gasLeft - gBase, d.stateGas⟩) hroom]
  rfl

private def proxyState (d : Devm) (stack : List B256) (memory : Mem)
    (cost : Nat) : Devm :=
  d.setMach ⟨stack, memory, d.gasLeft - cost, d.stateGas⟩

private def ProxyCont (e : Sevm) : (Nat × Devm) → (Nat × Devm) → Prop :=
  Relation.ReflTransGen
    (fun p q => Evm.step ⟨p.1, e, p.2⟩ = .cont q.1 q.2)

private theorem implementationCode_notDelegation :
    getDelegatedCodeAddress implementationCode = none := by
  have hnot : ¬ isValidDelegation implementationCode := by
    intro h
    have hs := h.1
    rw [implementationCode_size] at hs
    have hlen : eoaDelegatedCodeLength = 23 := rfl
    rw [hlen] at hs
    omega
  simp only [getDelegatedCodeAddress, hnot, ↓reduceIte]

private theorem proxy_copied_memory_size {data : Bytes}
    (hdata : data.length = 132) :
    (Mem.empty.write 0 data).size = 160 := by
  cases data with
  | nil => simp only [List.length_nil, OfNat.zero_ne_ofNat] at hdata
  | cons b bs =>
      simp only [Mem.write, hdata, zero_add, Mem.empty, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero,
        ↓reduceIte, ceil32, Nat.reduceMod, Nat.reduceAdd, Nat.succ_eq_add_one, Nat.reduceSub]

end Blanc.Lift.VyperNonreentrantDeployed
