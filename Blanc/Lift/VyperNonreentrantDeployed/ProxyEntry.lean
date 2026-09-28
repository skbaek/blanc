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

private theorem proxy_at_delegatecall_31 :
    Xinst.At proxyCode 31 .delegatecall := by rfl

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
    simpa using hgas
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

private theorem proxy_steps_0_3 (e : Sevm) (d : Devm)
    (hcode : e.code = proxyCode)
    (hdata : e.data.length = 132)
    (hstack : d.stack = [])
    (hmemory : d.memory = Mem.empty)
    (hreturn : d.returnData = [])
    (hgas : 2654 ≤ d.gasLeft) :
    ProxyCont e (0, d)
      (3, proxyState d [0, 0, (132 : Nat).toB256] Mem.empty 6) := by
  let s1 := proxyState d [(132 : Nat).toB256] Mem.empty 2
  let s2 := proxyState d [0, (132 : Nat).toB256] Mem.empty 4
  let s3 := proxyState d [0, 0, (132 : Nat).toB256] Mem.empty 6
  have h1 : Evm.step ⟨0, e, d⟩ = .cont 1 s1 := by
    have hg : gBase ≤ d.gasLeft := by change 2 ≤ d.gasLeft; omega
    simpa only [s1, proxyState, hdata, hstack, hmemory, gBase] using
      proxy_step_calldatasize e d 0 hcode proxy_at_calldatasize_0
        hg (by simp only [hstack, List.length_nil]; decide)
  have h2 : Evm.step ⟨1, e, s1⟩ = .cont 2 s2 := by
    have hg : gBase ≤ s1.gasLeft := by
      change 2 ≤ d.gasLeft - 2
      omega
    have hr : s1.stack.length < 1024 := by
      change ([(132 : Nat).toB256] : List B256).length < 1024
      decide
    simpa only [s1, s2, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.returnData_setMach, hreturn,
      List.length_nil, Nat.sub_sub, gBase, Nat.reduceAdd,
      show (Nat.toB256 0 : B256) = 0 from rfl] using
      proxy_step_returndatasize e s1 1 hcode proxy_at_returndatasize_1 hg hr
  have h3 : Evm.step ⟨2, e, s2⟩ = .cont 3 s3 := by
    have hg : gBase ≤ s2.gasLeft := by
      change 2 ≤ d.gasLeft - 4
      omega
    have hr : s2.stack.length < 1024 := by
      change ([0, (132 : Nat).toB256] : List B256).length < 1024
      decide
    simpa only [s2, s3, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.returnData_setMach, hreturn,
      List.length_nil, Nat.sub_sub, gBase, Nat.reduceAdd,
      show (Nat.toB256 0 : B256) = 0 from rfl] using
      proxy_step_returndatasize e s2 2 hcode proxy_at_returndatasize_2 hg hr
  have t1 : ProxyCont e (0, d) (1, s1) := Relation.ReflTransGen.single h1
  have t2 : ProxyCont e (1, s1) (2, s2) := Relation.ReflTransGen.single h2
  have t3 : ProxyCont e (2, s2) (3, s3) := Relation.ReflTransGen.single h3
  exact t1.trans (t2.trans t3)

private theorem proxy_steps_3_9 (e : Sevm) (d : Devm)
    (hcode : e.code = proxyCode)
    (hdata : e.data.length = 132)
    (hreturn : d.returnData = [])
    (hgas : 2654 ≤ d.gasLeft) :
    ProxyCont e
      (3, proxyState d [0, 0, (132 : Nat).toB256] Mem.empty 6)
      (9, proxyState d [0, (132 : Nat).toB256, 0, 0, 0]
        (Mem.empty.write 0 e.data) 49) := by
  let mem := Mem.empty.write 0 e.data
  let s3 := proxyState d [0, 0, (132 : Nat).toB256] Mem.empty 6
  let s4 := proxyState d [] mem 39
  let s5 := proxyState d [0] mem 41
  let s6 := proxyState d [0, 0] mem 43
  let s7 := proxyState d [0, 0, 0] mem 45
  let s8 := proxyState d [(132 : Nat).toB256, 0, 0, 0] mem 47
  let s9 := proxyState d [0, (132 : Nat).toB256, 0, 0, 0] mem 49
  have h4 : Evm.step ⟨3, e, s3⟩ = .cont 4 s4 := by
    have hs : s3.stack = [0, 0, (132 : Nat).toB256] := rfl
    have hm : s3.memory = Mem.empty := rfl
    have hg : 33 ≤ s3.gasLeft := by change 33 ≤ d.gasLeft - 6; omega
    simpa only [s3, s4, proxyState, mem, Devm.setMach_setMach,
      Devm.gasLeft_setMach, Devm.stateGas_setMach, Nat.sub_sub,
      Nat.reduceAdd] using
      proxy_step_calldatacopy e s3 hcode hdata hs hm hg
  have h5 : Evm.step ⟨4, e, s4⟩ = .cont 5 s5 := by
    have hg : gBase ≤ s4.gasLeft := by change 2 ≤ d.gasLeft - 39; omega
    have hr : s4.stack.length < 1024 := by change (0 : Nat) < 1024; decide
    simpa only [s4, s5, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.returnData_setMach, hreturn,
      List.length_nil, Nat.sub_sub, gBase, Nat.reduceAdd,
      show (Nat.toB256 0 : B256) = 0 from rfl] using
      proxy_step_returndatasize e s4 4 hcode proxy_at_returndatasize_4 hg hr
  have h6 : Evm.step ⟨5, e, s5⟩ = .cont 6 s6 := by
    have hg : gBase ≤ s5.gasLeft := by change 2 ≤ d.gasLeft - 41; omega
    have hr : s5.stack.length < 1024 := by
      change ([0] : List B256).length < 1024
      decide
    simpa only [s5, s6, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.returnData_setMach, hreturn,
      List.length_nil, Nat.sub_sub, gBase, Nat.reduceAdd,
      show (Nat.toB256 0 : B256) = 0 from rfl] using
      proxy_step_returndatasize e s5 5 hcode proxy_at_returndatasize_5 hg hr
  have h7 : Evm.step ⟨6, e, s6⟩ = .cont 7 s7 := by
    have hg : gBase ≤ s6.gasLeft := by change 2 ≤ d.gasLeft - 43; omega
    have hr : s6.stack.length < 1024 := by
      change ([0, 0] : List B256).length < 1024
      decide
    simpa only [s6, s7, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.returnData_setMach, hreturn,
      List.length_nil, Nat.sub_sub, gBase, Nat.reduceAdd,
      show (Nat.toB256 0 : B256) = 0 from rfl] using
      proxy_step_returndatasize e s6 6 hcode proxy_at_returndatasize_6 hg hr
  have h8 : Evm.step ⟨7, e, s7⟩ = .cont 8 s8 := by
    have hg : gBase ≤ s7.gasLeft := by change 2 ≤ d.gasLeft - 45; omega
    have hr : s7.stack.length < 1024 := by
      change ([0, 0, 0] : List B256).length < 1024
      decide
    simpa only [s7, s8, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, hdata, Nat.sub_sub, gBase, Nat.reduceAdd] using
      proxy_step_calldatasize e s7 7 hcode proxy_at_calldatasize_7 hg hr
  have h9 : Evm.step ⟨8, e, s8⟩ = .cont 9 s9 := by
    have hg : gBase ≤ s8.gasLeft := by change 2 ≤ d.gasLeft - 47; omega
    have hr : s8.stack.length < 1024 := by
      change ([(132 : Nat).toB256, 0, 0, 0] : List B256).length < 1024
      decide
    simpa only [s8, s9, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Devm.returnData_setMach, hreturn,
      List.length_nil, Nat.sub_sub, gBase, Nat.reduceAdd,
      show (Nat.toB256 0 : B256) = 0 from rfl] using
      proxy_step_returndatasize e s8 8 hcode proxy_at_returndatasize_8 hg hr
  have t4 : ProxyCont e (3, s3) (4, s4) := Relation.ReflTransGen.single h4
  have t5 : ProxyCont e (4, s4) (5, s5) := Relation.ReflTransGen.single h5
  have t6 : ProxyCont e (5, s5) (6, s6) := Relation.ReflTransGen.single h6
  have t7 : ProxyCont e (6, s6) (7, s7) := Relation.ReflTransGen.single h7
  have t8 : ProxyCont e (7, s7) (8, s8) := Relation.ReflTransGen.single h8
  have t9 : ProxyCont e (8, s8) (9, s9) := Relation.ReflTransGen.single h9
  exact t4.trans (t5.trans (t6.trans (t7.trans (t8.trans t9))))

private theorem proxy_steps_9_31 (e : Sevm) (d : Devm)
    (hcode : e.code = proxyCode)
    (hgas : 2654 ≤ d.gasLeft) :
    ProxyCont e
      (9, proxyState d [0, (132 : Nat).toB256, 0, 0, 0]
        (Mem.empty.write 0 e.data) 49)
      (31, proxyState d
        [(d.gasLeft - 54).toB256, implementationAddress.toB256,
          0, (132 : Nat).toB256, 0, 0, 0]
        (Mem.empty.write 0 e.data) 54) := by
  let mem := Mem.empty.write 0 e.data
  let s9 := proxyState d [0, (132 : Nat).toB256, 0, 0, 0] mem 49
  let s30 := proxyState d
    [implementationAddress.toB256, 0, (132 : Nat).toB256, 0, 0, 0] mem 52
  let s31 := proxyState d
    [(d.gasLeft - 54).toB256, implementationAddress.toB256,
      0, (132 : Nat).toB256, 0, 0, 0] mem 54
  have h30 : Evm.step ⟨9, e, s9⟩ = .cont 30 s30 := by
    have hat : Ninst.At e.code 9
        (.push [0x63, 0x26, 0xde, 0xbb, 0xaa, 0x15, 0xbc, 0xfe, 0x60, 0x3d,
          0x83, 0x1e, 0x7d, 0x75, 0xf4, 0xfc, 0x10, 0xd9, 0xb4, 0x3e]
          (by decide)) := by rw [hcode]; exact proxy_at_push20_9
    have hg : gVerylow ≤ s9.gasLeft := by change 3 ≤ d.gasLeft - 49; omega
    have hr : s9.stack.length < 1024 := by
      change ([0, (132 : Nat).toB256, 0, 0, 0] : List B256).length < 1024
      decide
    have hv : Bytes.toB256
        [0x63, 0x26, 0xde, 0xbb, 0xaa, 0x15, 0xbc, 0xfe, 0x60, 0x3d,
          0x83, 0x1e, 0x7d, 0x75, 0xf4, 0xfc, 0x10, 0xd9, 0xb4, 0x3e] =
        implementationAddress.toB256 := by decide
    simpa only [s9, s30, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Nat.sub_sub, Nat.reduceAdd,
      List.length_cons, List.length_nil, gVerylow, hv] using
      Evm.push_cont (by decide) hat hg hr
  have h31 : Evm.step ⟨30, e, s30⟩ = .cont 31 s31 := by
    have hg : gBase ≤ s30.gasLeft := by change 2 ≤ d.gasLeft - 52; omega
    have hr : s30.stack.length < 1024 := by
      change ([implementationAddress.toB256, 0, (132 : Nat).toB256,
        0, 0, 0] : List B256).length < 1024
      decide
    simpa only [s30, s31, proxyState, Devm.setMach_setMach,
      Devm.stack_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
      Devm.stateGas_setMach, Nat.sub_sub, gBase, Nat.reduceAdd] using
      proxy_step_gas e s30 hcode hg hr
  have t30 : ProxyCont e (9, s9) (30, s30) := Relation.ReflTransGen.single h30
  have t31 : ProxyCont e (30, s30) (31, s31) := Relation.ReflTransGen.single h31
  exact t30.trans t31

/-- Eleven childless steps from the exact proxy entry to its real call opcode. -/
private theorem proxy_prefix (e : Sevm) (d : Devm)
    (hcode : e.code = proxyCode)
    (hdata : e.data.length = 132)
    (hstack : d.stack = [])
    (hmemory : d.memory = Mem.empty)
    (hreturn : d.returnData = [])
    (hgas : 2654 ≤ d.gasLeft) :
    ProxyCont e (0, d)
      (31, proxyState d
        [(d.gasLeft - 54).toB256, implementationAddress.toB256,
          0, (132 : Nat).toB256, 0, 0, 0]
        (Mem.empty.write 0 e.data) 54) := by
  exact (proxy_steps_0_3 e d hcode hdata hstack hmemory hreturn hgas).trans
    ((proxy_steps_3_9 e d hcode hdata hreturn hgas).trans
      (proxy_steps_9_31 e d hcode hgas))

private theorem implementationCode_notDelegation :
    getDelegatedCodeAddress implementationCode = none := by
  have hnot : ¬ isValidDelegation implementationCode := by
    intro h
    have hs := h.1
    rw [implementationCode_size] at hs
    have hlen : eoaDelegatedCodeLength = 23 := rfl
    rw [hlen] at hs
    omega
  simp [getDelegatedCodeAddress, hnot]

private theorem proxy_copied_memory_size {data : Bytes}
    (hdata : data.length = 132) :
    (Mem.empty.write 0 data).size = 160 := by
  cases data with
  | nil => simp at hdata
  | cons b bs =>
      simp [Mem.write, Mem.empty, hdata, ceil32]

private theorem proxy_call_extension_zero (pre : Devm) (data : Bytes)
    (hdata : data.length = 132)
    (hmemory : pre.memory = Mem.empty.write 0 data) :
    (pre.setMach ⟨[0], pre.memory, pre.gasLeft, pre.stateGas⟩).extCost
      [(0, 132), (0, 0)] = 0 := by
  simp only [Devm.extCost, Devm.memory_setMach, hmemory,
    proxy_copied_memory_size hdata]
  decide

private theorem proxy_call_code (pre : Devm)
    (himpl : pre.state.getCode implementationAddress = implementationCode) :
    accessDelegation
      (addAccessedAddress
        (pre.setMach ⟨[0], pre.memory, pre.gasLeft, pre.stateGas⟩)
        implementationAddress)
      implementationAddress =
      ⟨false, implementationAddress, implementationCode, 0,
        addAccessedAddress
          (pre.setMach ⟨[0], pre.memory, pre.gasLeft, pre.stateGas⟩)
          implementationAddress⟩ := by
  have hc :
      (addAccessedAddress
        (pre.setMach ⟨[0], pre.memory, pre.gasLeft, pre.stateGas⟩)
        implementationAddress).state.getCode implementationAddress =
        implementationCode := by
    rw [← (addAccessedAddress_worldEq
      (pre.setMach ⟨[0], pre.memory, pre.gasLeft, pre.stateGas⟩)
      implementationAddress).1]
    exact himpl
  simp only [accessDelegation, hc, implementationCode_notDelegation]

private theorem proxy_implementation_not_precompile (e : Sevm)
    (hfork : e.benvStat.fork = .prague) :
    e.benvStat.rules.isPrecomp implementationAddress = false := by
  change (Fork.ruleSet e.benvStat.fork).isPrecomp implementationAddress = false
  rw [hfork]
  decide

/-- The exact `DELEGATECALL` spawn from the proxy's seven-word call stack. -/
theorem proxy_spawn_at_call (e : Sevm) (pre : Devm) (gw : B256)
    (hcode : e.code = proxyCode)
    (hfork : e.benvStat.fork = .prague)
    (hstack : pre.stack = gw :: implementationAddress.toB256 :: 0 ::
      (132 : Nat).toB256 :: 0 :: 0 :: [0])
    (hdata : e.data.length = 132)
    (hmemory : pre.memory = Mem.empty.write 0 e.data)
    (himpl : pre.state.getCode implementationAddress = implementationCode)
    (hgas : 2600 ≤ pre.gasLeft)
    (hdepth : e.depth ≠ 0) :
    ∃ desc : DelegatecallSpawnDescriptor e pre,
      desc.resolvedCodeAddress = implementationAddress ∧
      desc.code = implementationCode ∧
      desc.child.currentTarget = e.currentTarget ∧
      desc.child.caller = e.caller ∧
      desc.child.value = e.value ∧
      desc.child.data = e.data ∧
      desc.child.codeAddress = some implementationAddress ∧
      desc.child.shouldTransferValue = false ∧
      desc.child.depth = e.depth - 1 ∧
      (Frame.ofCall desc.child).enter = .run (initEvm desc.child) ∧
      Evm.step ⟨31, e, pre⟩ =
        .spawn (Frame.ofCall desc.child) desc.resume 32 := by
  let acc := accessCost implementationAddress pre.accessedAddresses
  let after := addAccessedAddress
    (pre.setMach ⟨[0], pre.memory, pre.gasLeft, pre.stateGas⟩)
    implementationAddress
  let costs := calculateMsgCallGas 0 gw.toNat after.gasLeft 0 acc
  have hext :
      (pre.setMach ⟨[0], pre.memory, pre.gasLeft, pre.stateGas⟩).extCost
        [(0, (Nat.toB256 132).toNat), (0, 0)] = 0 := by
    have h132 : (Nat.toB256 132).toNat = 132 :=
      B256.toNat_toB256_of_lt (by decide)
    rw [h132]
    exact proxy_call_extension_zero pre e.data hdata hmemory
  have hdel : accessDelegation after implementationAddress =
      ⟨false, implementationAddress, implementationCode, 0, after⟩ :=
    proxy_call_code pre himpl
  have hacc : acc ≤ gasColdAccountAccess := accessCost_le
  have ha : acc + 0 ≤ after.gasLeft := by
    change acc + 0 ≤ pre.gasLeft
    change acc ≤ 2600 at hacc
    omega
  let desc : DelegatecallSpawnDescriptor e pre := {
    gasWord := gw
    codeWord := implementationAddress.toB256
    inputOffsetWord := 0
    inputSizeWord := (132 : Nat).toB256
    outputOffsetWord := 0
    outputSizeWord := 0
    stackTail := [0]
    delegated := false
    resolvedCodeAddress := implementationAddress
    code := implementationCode
    delegationGas := 0
    afterAccess := after
    extensionCost := 0
    accessCharge := acc
    callCost := costs.1
    childGas := costs.2
    stackEq := hstack
    extensionEq := hext
    delegationEq := by
      simpa only [toAdr_toB256] using hdel
    accessEq := by
      rfl
    splitEq := by
      rfl
    affordable := by
      exact calculateMsgCallGas_cost_le ha
    depthHeadroom := hdepth
    resolvedNotPrecompile := proxy_implementation_not_precompile e hfork
    covered := by
      rw [hfork]
      exact CoveredFork.prague
  }
  have hii : desc.inputOffsetWord.toNat = 0 := by
    simp only [desc, B256.toNat_zero]
  have his : desc.inputSizeWord.toNat = 132 := by
    change (Nat.toB256 132).toNat = 132
    exact B256.toNat_toB256_of_lt (by decide)
  have hparentMemory : desc.parent.memory = pre.memory := by
    rw [DelegatecallSpawnDescriptor.parent, callSpawnParent_memory,
      desc.afterAccess_memory]
    apply Mem.extends_covered
    rw [hmemory, proxy_copied_memory_size hdata]
    rw [hii, his]
    decide
  have hchildData : desc.child.data = e.data := by
    rw [DelegatecallSpawnDescriptor.child_data, hparentMemory, hmemory]
    rw [hii, his]
    have hn : e.data ≠ [] := by
      intro hempty
      simp [hempty] at hdata
    simpa [hdata] using (Mem.read_write_zero Mem.empty hn)
  refine ⟨desc, rfl, rfl, rfl, rfl, rfl, hchildData, rfl, rfl, rfl, ?_, ?_⟩
  · exact desc.crossing.1
  have hat : Ninst.At e.code 31 (.exec .delegatecall) := by
    rw [hcode]
    exact proxy_at_delegatecall_31
  rw [Evm.step_next hat, Ninst.step_exec, desc.step]
  rfl

end Blanc.Lift.VyperNonreentrantDeployed
