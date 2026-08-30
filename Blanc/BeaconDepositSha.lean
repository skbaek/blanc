import Blanc.BeaconDeposit
import Blanc.ForwardSha256

/-!
# Beacon deposit SHA-256 wrapper carrier

The executable contract's `sha64` helper performs one warm call to the SHA-256
precompile and then checks both the status word and the returned byte count.
This module exposes the successful path with exact gas and the digest, storage,
log, output, and error facts needed by its continuations.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Exact successful cost of the contract's `sha64` wrapper.

The fixed suffix costs 223 gas: `GAS` costs 2, the warm SHA-256 crossing 184,
`ISZERO` 3, the two untaken-branch frames 13 each, and the returndata-length
guard 8.  The remaining cost is the five argument pushes.
-/
def sha64SuccessCost (inputWord outputWord : B256) : Nat :=
  pushCost ((32 : B256).toBytes.sig) +
  pushCost ((outputWord * 32).toBytes.sig) +
  pushCost ((64 : B256).toBytes.sig) +
  pushCost ((inputWord * 32).toBytes.sig) +
  pushCost ((2 : B256).toBytes.sig) + 223

private theorem sha64_success_suffix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {K : Nat}
    {stack : List B256} {success : Func} {ex : Execution}
    (h_ge : (Nat.toB256 base.returnData.length <? (32 : B256)) = 0)
    (h_tail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, base.memory, K⟩) success ex)
    (h_room : stack.length < 1019) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨1 :: stack, base.memory, K + 37⟩)
      (iszero :::
        (.call bubbleRevertSlot) <?>
        (retdataShorterThan 32 +++
          ((.call emptyRevertSlot) <?> success))) ex := by
  func_run (6) [0, 0]
  all_goals try {
    simp only [Devm.stack_setMach, List.length_cons] at *
    omega }
  all_goals try omega
  simpa only [Devm.memory_setMach, Nat.add_sub_cancel] using h_tail

/-- Run the argument prefix, warm SHA-256 call, and successful decoder guards
with an exact selected memory-expansion charge.

The returned `callPost` is the state immediately after `STATICCALL`; the last
field turns any exact-gas continuation from the post-guard state into a run of
the complete `sha64` wrapper.  Keeping the call state visible lets downstream
fold proofs consume the digest and preservation facts without re-opening the
precompile semantics.
-/
theorem sha64_success_prefix_runCompiledTo_ext
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {inputWord outputWord : B256} {stack : List B256}
    {success : Func} {K ext : Nat}
    (hext : base.extCost
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = ext)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 + ext < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      (∃ stmid,
        base.state.subBal sevm.currentTarget 0 = some stmid ∧
        callPost.state = stmid.addBal 2 0) ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + sha64SuccessCost inputWord outputWord + ext⟩)
          (sha64 inputWord outputWord success) ex := by
  let callPre := base.setMach
    ⟨Nat.toB256 (K + 221 + ext) :: (2 : B256) ::
      (inputWord * 32) :: (64 : B256) ::
      (outputWord * 32) :: (32 : B256) :: stack,
      base.memory, K + 221 + ext⟩
  obtain ⟨callPost, hstat, hstack, hmemory, hgas, hreturn,
      hstorage, hcode, haddresses, hkeys,
      hlogs, houtput, herror, stmid, hsub, hstate⟩ :=
    Ninst.runCompiled_statcall_sha256_64_warm_ext
      (sevm := sevm) (devm := callPre)
      (iiw := inputWord * 32) (oiw := outputWord * 32)
      (s := stack) (G := K + 221 + ext) (ext := ext)
      (by simp only [callPre, Devm.stack_setMach])
      (by simp only [callPre, Devm.gasLeft_setMach])
      (by
        simpa only [callPre, Devm.extCost, Devm.memory_setMach] using hext)
      (by simpa only [callPre, Devm.getCode_setMach] using hnodeleg)
      (by
        change (2 : Adr) ∈ base.accessedAddresses
        exact hwarm)
      hpre hdepth (by omega) hbound (by omega)
  have hgas' : callPost.gasLeft = K + 37 := by omega
  have hmemory' :
      callPost.memory = (base.memory.extends
        [⟨(inputWord * 32).toNat, 64⟩,
          ⟨(outputWord * 32).toNat, 32⟩]).write
        (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hmemory
  have hreturn' :
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes := by
    simpa only [callPre, Devm.memory_setMach] using hreturn
  have hstorage' : ∀ a,
      Devm.getStor callPost a = Devm.getStor base a := by
    intro a
    calc
      Devm.getStor callPost a = Devm.getStor callPre a := hstorage a
      _ = Devm.getStor base a := by rfl
  have hcode' : ∀ a, callPost.getCode a = base.getCode a := by
    intro a
    calc
      callPost.getCode a = callPre.getCode a := hcode a
      _ = base.getCode a := by rfl
  have haddresses' :
      callPost.accessedAddresses = base.accessedAddresses := by
    calc
      callPost.accessedAddresses = callPre.accessedAddresses := haddresses
      _ = base.accessedAddresses := by rfl
  have hkeys' :
      callPost.accessedStorageKeys = base.accessedStorageKeys := by
    calc
      callPost.accessedStorageKeys = callPre.accessedStorageKeys := hkeys
      _ = base.accessedStorageKeys := by rfl
  have hlogs' : callPost.logs = base.logs := by
    calc
      callPost.logs = callPre.logs := hlogs
      _ = base.logs := by rfl
  have houtput' : callPost.output = base.output := by
    calc
      callPost.output = callPre.output := houtput
      _ = base.output := by rfl
  have herror' : callPost.error = base.error := by
    calc
      callPost.error = callPre.error := herror
      _ = base.error := by rfl
  have hsub' : base.state.subBal sevm.currentTarget 0 = some stmid := by
    change base.state.subBal sevm.currentTarget 0 = some stmid at hsub
    exact hsub
  refine ⟨callPost, hstack, hmemory', hgas', hreturn',
    hstorage', hcode', haddresses', hkeys',
    hlogs', houtput', herror', ⟨stmid, hsub', hstate⟩, ?_⟩
  intro ex htail
  have hge :
      (Nat.toB256 callPost.returnData.length <? (32 : B256)) = 0 := by
    rw [hreturn', B256.length_toBytes]
    decide +kernel
  have hsuffix : Func.RunCompiledTo fs sevm
      (callPost.setMach ⟨1 :: stack, callPost.memory, K + 37⟩)
      (iszero :::
        (.call bubbleRevertSlot) <?>
        (retdataShorterThan 32 +++
          ((.call emptyRevertSlot) <?> success))) ex :=
    sha64_success_suffix_runCompiledTo hge htail hroom
  let c32 := pushCost ((32 : B256).toBytes.sig)
  let cout := pushCost ((outputWord * 32).toBytes.sig)
  let c64 := pushCost ((64 : B256).toBytes.sig)
  let cin := pushCost ((inputWord * 32).toBytes.sig)
  let c2 := pushCost ((2 : B256).toBytes.sig)
  simp only [sha64, pushList, List.map, prepend]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (sevm := sevm)
      (devm := base.setMach
        ⟨stack, base.memory,
          K + sha64SuccessCost inputWord outputWord + ext⟩)
      (w := (32 : B256)) (c := c32)
      (G := K + (cout + c64 + cin + c2 + 223) + ext)
      (by rfl)
      (by
        simp only [Devm.gasLeft_setMach, sha64SuccessCost,
          c32, cout, c64, cin, c2]
        omega)
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := outputWord * 32) (c := cout)
      (G := K + (c64 + cin + c2 + 223) + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (64 : B256)) (c := c64)
      (G := K + (cin + c2 + 223) + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := inputWord * 32) (c := cin)
      (G := K + (c2 + 223) + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := (2 : B256)) (c := c2)
      (G := K + 223 + ext)
      (by rfl)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_gas
      (G := K + 221 + ext)
      (by simp only [Devm.gasLeft_setMach, gBase]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next ?_ hsuffix
  have hpost :
      callPost.setMach
        ⟨1 :: stack, callPost.memory, K + 37⟩ = callPost := by
    apply Devm.ext
    · apply Mach.ext
      · exact hstack.symm
      · rfl
      · exact hgas'.symm
    · rfl
    · rfl
  rw [hpost]
  simpa only [callPre, Devm.stack_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach] using hstat

/-- Covered-memory compatibility form of
`sha64_success_prefix_runCompiledTo_ext`. -/
theorem sha64_success_prefix_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {inputWord outputWord : B256} {stack : List B256}
    {success : Func} {K : Nat}
    (hcovered : memExtsSize base.memory.size
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = base.memory.size)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hbound : K + 221 < 2 ^ 256)
    (hroom : stack.length < 1019) :
    ∃ callPost,
      callPost.stack = 1 :: stack ∧
      callPost.memory = base.memory.write (outputWord * 32).toNat
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      callPost.gasLeft = K + 37 ∧
      callPost.returnData =
        (Bytes.sha256
          (base.memory.data.sliceD (inputWord * 32).toNat 64 0)).toBytes ∧
      (∀ a, Devm.getStor callPost a = Devm.getStor base a) ∧
      (∀ a, callPost.getCode a = base.getCode a) ∧
      callPost.accessedAddresses = base.accessedAddresses ∧
      callPost.accessedStorageKeys = base.accessedStorageKeys ∧
      callPost.logs = base.logs ∧
      callPost.output = base.output ∧
      callPost.error = base.error ∧
      (∃ stmid,
        base.state.subBal sevm.currentTarget 0 = some stmid ∧
        callPost.state = stmid.addBal 2 0) ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (callPost.setMach ⟨stack, callPost.memory, K⟩) success ex →
        Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨stack, base.memory,
              K + sha64SuccessCost inputWord outputWord⟩)
          (sha64 inputWord outputWord success) ex := by
  have hext : base.extCost
      [⟨(inputWord * 32).toNat, 64⟩,
        ⟨(outputWord * 32).toNat, 32⟩] = 0 := by
    simp only [Devm.extCost, hcovered]
    omega
  simpa only [Nat.add_zero, Mem.extends_covered hcovered] using
    (sha64_success_prefix_runCompiledTo_ext
      (ext := 0) hext hnodeleg hwarm hpre hdepth (by simpa using hbound) hroom)

/-! ## Contract-site cost specializations -/

@[simp] theorem sha64SuccessCost_zero_node :
    sha64SuccessCost 0 nodeWord = 237 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_zero_intermediate :
    sha64SuccessCost 0 intermediateWord = 237 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_zero_secondIntermediate :
    sha64SuccessCost 0 secondIntermediateWord = 237 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_six_node :
    sha64SuccessCost 6 nodeWord = 238 := by
  decide +kernel

@[simp] theorem sha64SuccessCost_thirteen_intermediate :
    sha64SuccessCost 13 intermediateWord = 238 := by
  decide +kernel

end Blanc.BeaconDeposit
