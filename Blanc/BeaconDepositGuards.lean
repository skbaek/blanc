import Blanc.BeaconDepositGuardMemory

/-!
# Beacon deposit guard traversal

The six source-level guards between ABI decoding and event staging are proved
as small continuation-polymorphic certificates and composed backward.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

/-- Gas consumed by the six successful deposit guards. -/
def depositGuardsGas : Nat := 214

theorem depositLengthWord_of_payload
    {data payload : Bytes} {head len : Nat}
    (heq : dynamicPayload data head = payload) (hlen : payload.length = len) :
    depositLengthWord data head = Nat.toB256 len := by
  have h := congrArg List.length heq
  simp only [dynamicPayload, List.length_sliceD, hlen] at h
  simp only [depositLengthWord, h]

/-- One successful decoded-length guard. -/
theorem depositLengthGuard_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {data : Bytes} {word expected : B256}
    {index slot G : Nat} {rest : Func} {ex : Execution}
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hindex : (word * 32).toNat = index)
    (hcovered : index + 32 ≤ memory.size)
    (hread : Bytes.toB256 (memory.read index 32).1 = expected)
    (hwordPush : pushCost (word * 32).toBytes.sig = 3)
    (hexpectedPush : pushCost expected.toBytes.sig = 3)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 28⟩)
      (loadWord word +++ pushB256 expected ::: eq ::: iszero :::
        ((.call slot) <?> rest)) ex := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hmemory : (memory.read index 32).2 = memory :=
    Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)
  unfold loadWord
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 25) hwordPush
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := word * 32) (v := expected) (s := [])
      (c := 3) (G := G + 22) (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by rw [hindex]; exact hcovered)]
        decide)
      (by rw [Devm.memory_setMach, hindex, hread])
      (by rw [Devm.memory_setMach, hindex, hmemory])
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 19) hexpectedPush
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  func_run (3) [1, 0]
  case h_val => simp [B256.eqCheck]
  case h_arm =>
    simpa only [Devm.setMach_setMach, Nat.add_sub_cancel] using htail

/-- The three successful decoded-length guards, with an arbitrary
continuation after the signature check. -/
theorem depositLengthGuards_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {data : Bytes} {G : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {rest : Func} {ex : Execution}
    (hcarrier : DepositDecodedMemoryCarrier memory data)
    (hdec : DepositAbiDecodable data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hpubkey : pubkey.length = 48)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hsignature : signature.length = 96)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 84⟩)
      (loadWord 3 +++ pushB256 48 ::: eq ::: iszero :::
        ((.call pubkeyLengthErrorSlot) <?>
          (loadWord 4 +++ pushB256 32 ::: eq ::: iszero :::
            ((.call withdrawalLengthErrorSlot) <?>
              (loadWord 5 +++ pushB256 96 ::: eq ::: iszero :::
                ((.call signatureLengthErrorSlot) <?> rest)))))) ex := by
  have hlen0 : depositLengthWord data 0 = 48 :=
    depositLengthWord_of_payload hdec.pubkey_eq hpubkey
  have hlen1 : depositLengthWord data 1 = 32 :=
    depositLengthWord_of_payload hdec.withdrawalCredentials_eq hwithdrawal
  have hlen2 : depositLengthWord data 2 = 96 :=
    depositLengthWord_of_payload hdec.signature_eq hsignature
  have hread0 : Bytes.toB256 (memory.read 96 32).1 = 48 := by
    rw [hcarrier.read_length0, B256.toB256_toBytes, hlen0]
  have hread1 : Bytes.toB256 (memory.read 128 32).1 = 32 := by
    rw [hcarrier.read_length1, B256.toB256_toBytes, hlen1]
  have hread2 : Bytes.toB256 (memory.read 160 32).1 = 96 := by
    rw [hcarrier.read_length2, B256.toB256_toBytes, hlen2]
  have hsignatureRun := depositLengthGuard_runCompiledTo
    (word := 5) (expected := 96) (index := 160)
    (slot := signatureLengthErrorSlot) hcarrier (by decide +kernel)
    (by rw [hcarrier.size_eq]) hread2
    (by decide +kernel) (by decide +kernel) htail
  have hwithdrawalRun := depositLengthGuard_runCompiledTo
    (word := 4) (expected := 32) (index := 128)
    (slot := withdrawalLengthErrorSlot) hcarrier (by decide +kernel)
    (by rw [hcarrier.size_eq]; omega) hread1
    (by decide +kernel) (by decide +kernel) hsignatureRun
  have hpubkeyRun := depositLengthGuard_runCompiledTo
    (word := 3) (expected := 48) (index := 96)
    (slot := pubkeyLengthErrorSlot) hcarrier (by decide +kernel)
    (by rw [hcarrier.size_eq]; omega) hread0
    (by decide +kernel) (by decide +kernel) hwithdrawalRun
  have hgas : ((G + 28) + 28) + 28 = G + 84 := by omega
  simpa only [hgas] using hpubkeyRun

/-- The lower-value guard passes in exactly 21 gas. -/
theorem depositValueLowerGuard_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {G slot : Nat} {rest : Func} {ex : Execution}
    (hlower : Nat.toB256 oneEther ≤ sevm.value)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 21⟩)
      (pushB256 (Nat.toB256 oneEther) ::: callvalue ::: lt :::
        ((.call slot) <?> rest)) ex := by
  func_run (4) [0]
  case h_val => simp [B256.ltCheck, not_lt_of_ge hlower]
  case h_arm =>
    simpa only [Devm.setMach_setMach, Nat.add_sub_cancel] using htail

/-- The exact-gwei-multiple guard passes in exactly 23 gas. -/
theorem depositGweiMultipleGuard_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {G slot : Nat} {rest : Func} {ex : Execution}
    (hgwei : sevm.value % Nat.toB256 oneGwei = 0)
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 23⟩)
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: mod :::
        ((.call slot) <?> rest)) ex := by
  func_run (4) [0]
  case h_gas => simp only [Devm.gasLeft_setMach, gLow]; omega
  case h_arm =>
    simpa only [Devm.setMach_setMach, Nat.add_sub_cancel] using htail

/-- The upper-value guard retains the amount and passes in exactly 86 gas. -/
theorem depositAmountUpperGuard_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {data : Bytes} {amount : B256}
    {G slot : Nat} {rest : Func} {ex : Execution}
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hamount : sevm.value / Nat.toB256 oneGwei = amount)
    (hupper : amount ≤ Nat.toB256 (2 ^ 64 - 1))
    (htail : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], memory.write 672 amount.toBytes, G⟩) rest ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory, G + 86⟩)
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: div ::: dup 0 :::
        mstoreAt amountWord +++
        pushB256 (Nat.toB256 (2 ^ 64 - 1)) ::: lt :::
        ((.call slot) <?> rest)) ex := by
  func_run (9) [amount, 48, 0]
  case h_gas => simp only [Devm.gasLeft_setMach, gLow]; omega
  case h_ext =>
    rw [show (amountWord * 32 : B256).toNat = 672 by decide +kernel]
    exact Devm.extCost_of_size hmem.size_eq (by decide +kernel)
  case h_val =>
    rw [B256.ltCheck, if_neg (B256.not_lt.mpr hupper)]
  case h_arm =>
    rw [show (amountWord * 32 : B256).toNat = 672 by decide +kernel]
    simpa only [Devm.setMach_setMach, Nat.add_sub_cancel] using htail

/-- The complete successful traversal of the three decoded-length guards and
the three value guards. -/
theorem depositGuards_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {pubkey withdrawalCredentials signature : Bytes} {depositDataRoot : B256}
    {amount : B256} {ex : Execution}
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hpubkey : pubkey.length = 48)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hsignature : signature.length = 96)
    (hamount : sevm.value / Nat.toB256 oneGwei = amount)
    (hlower : Nat.toB256 oneEther ≤ sevm.value)
    (hgwei : sevm.value % Nat.toB256 oneGwei = 0)
    (hupper : amount ≤ Nat.toB256 (2 ^ 64 - 1))
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositEventInputMemory sevm.data amount, G⟩)
      (stageDepositEvent +++ depositAfterEvent) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], depositDecodedMemory sevm.data, G + depositGuardsGas⟩)
      depositBody ex := by
  let memory := depositDecodedMemory sevm.data
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data := by
    exact depositDecodedMemory_carrier sevm.data
  have hbody' : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], memory.write 672 amount.toBytes, G⟩)
      (stageDepositEvent +++ depositAfterEvent) ex := by
    simpa only [memory, depositEventInputMemory] using hbody
  have hupperRun := depositAmountUpperGuard_runCompiledTo
    (slot := valueTooHighErrorSlot) hcarrier hamount hupper hbody'
  have hgweiRun := depositGweiMultipleGuard_runCompiledTo
    (slot := valueNotGweiErrorSlot) hgwei hupperRun
  have hlowerRun := depositValueLowerGuard_runCompiledTo
    (slot := valueTooLowErrorSlot) hlower hgweiRun
  have hlengthRun := depositLengthGuards_runCompiledTo
    (base := base) (memory := memory) hcarrier hdec hpubkey hwithdrawal
    hsignature hlowerRun
  simpa only [memory, depositGuardsGas, depositBody] using hlengthRun

end Blanc.BeaconDeposit
