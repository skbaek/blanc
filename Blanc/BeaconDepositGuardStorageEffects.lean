import Blanc.BeaconDepositGuards
import Blanc.ForwardStorageEffects

/-! # Exact storage effects through successful Beacon deposit source guards -/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- One successful decoded-length guard preserves exact chronology. -/
theorem depositLengthGuard_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {data : Bytes} {word expected : B256}
    {index slot G : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hindex : (word * 32).toNat = index)
    (hcovered : index + 32 ≤ memory.size)
    (hread : Bytes.toB256 (memory.read index 32).1 = expected)
    (hwordPush : pushCost (word * 32).toBytes.sig = 3)
    (hexpectedPush : pushCost expected.toBytes.sig = 3)
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 28⟩)
      (loadWord word +++ pushB256 expected ::: eq ::: iszero :::
        ((.call slot) <?> rest)) ex effects := by
  have hmod : memory.size % 32 = 0 := by
    rw [hmem.size_eq]
  have hmemory : (memory.read index 32).2 = memory :=
    Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)
  unfold loadWord
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 25) hwordPush
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mload_of
      (i := word * 32) (v := expected) (s := [])
      (c := 3) (G := G + 22) (M := memory) rfl
      (by
        rw [Devm.extCost_zero_of_le hmod (by rw [hindex]; exact hcovered)]
        decide)
      (by rw [Devm.memory_setMach, hindex, hread])
      (by rw [Devm.memory_setMach, hindex, hmemory])
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 19) hexpectedPush
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .eq) (f := B256.eqCheck) (cost := gVerylow)
      (x := expected) (y := expected) (v := 1) (s := [])
      (G := G + 16) (by rintro ⟨⟩) rfl rfl
      (by simp [B256.eqCheck])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_unary
      (r := .iszero) (f := (B256.eqCheck · 0))
      (cost := gVerylow) (x := 1) (v := 0) (s := [])
      (G := G + 13) (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (Devm.popBurnBy_setMach (s := []) (G := G)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using htail

/-- The three successful decoded-length guards preserve exact chronology. -/
theorem depositLengthGuards_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {data : Bytes} {G : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hcarrier : DepositDecodedMemoryCarrier memory data)
    (hdec : DepositAbiDecodable data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hpubkey : pubkey.length = 48)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hsignature : signature.length = 96)
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 84⟩)
      (loadWord 3 +++ pushB256 48 ::: eq ::: iszero :::
        ((.call pubkeyLengthErrorSlot) <?>
          (loadWord 4 +++ pushB256 32 ::: eq ::: iszero :::
            ((.call withdrawalLengthErrorSlot) <?>
              (loadWord 5 +++ pushB256 96 ::: eq ::: iszero :::
                ((.call signatureLengthErrorSlot) <?> rest)))))) ex effects := by
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
  have hsignatureRun := depositLengthGuard_storageEffectRun
    (word := 5) (expected := 96) (index := 160)
    (slot := signatureLengthErrorSlot) hcarrier (by decide +kernel)
    (by rw [hcarrier.size_eq]) hread2
    (by decide +kernel) (by decide +kernel) htail
  have hwithdrawalRun := depositLengthGuard_storageEffectRun
    (word := 4) (expected := 32) (index := 128)
    (slot := withdrawalLengthErrorSlot) hcarrier (by decide +kernel)
    (by rw [hcarrier.size_eq]; omega) hread1
    (by decide +kernel) (by decide +kernel) hsignatureRun
  have hpubkeyRun := depositLengthGuard_storageEffectRun
    (word := 3) (expected := 48) (index := 96)
    (slot := pubkeyLengthErrorSlot) hcarrier (by decide +kernel)
    (by rw [hcarrier.size_eq]; omega) hread0
    (by decide +kernel) (by decide +kernel) hwithdrawalRun
  have hgas : ((G + 28) + 28) + 28 = G + 84 := by omega
  simpa only [hgas] using hpubkeyRun

/-- The successful lower-value guard preserves exact chronology. -/
theorem depositValueLowerGuard_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {G slot : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hlower : Nat.toB256 oneEther ≤ sevm.value)
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 21⟩)
      (pushB256 (Nat.toB256 oneEther) ::: callvalue ::: lt :::
        ((.call slot) <?> rest)) ex effects := by
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := Nat.toB256 oneEther)
      (c := gVerylow) (G := G + 18)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushItem
      (r := .callvalue) (x := sevm.value) (cost := gBase)
      (G := G + 16) (by rintro ⟨⟩) rfl
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .lt) (f := B256.ltCheck) (cost := gVerylow)
      (x := sevm.value) (y := Nat.toB256 oneEther)
      (v := 0) (s := []) (G := G + 13)
      (by rintro ⟨⟩) rfl rfl
      (by simp [B256.ltCheck, not_lt_of_ge hlower])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (Devm.popBurnBy_setMach (s := []) (G := G)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using htail

/-- The successful gwei-multiple guard preserves exact chronology. -/
theorem depositGweiMultipleGuard_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {memory : Mem}
    {G slot : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hgwei : sevm.value % Nat.toB256 oneGwei = 0)
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G⟩) rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 23⟩)
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: mod :::
        ((.call slot) <?> rest)) ex effects := by
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := Nat.toB256 oneGwei)
      (c := gVerylow) (G := G + 20)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushItem
      (r := .callvalue) (x := sevm.value) (cost := gBase)
      (G := G + 18) (by rintro ⟨⟩) rfl
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .mod) (f := (· % ·)) (cost := gLow)
      (x := sevm.value) (y := Nat.toB256 oneGwei)
      (v := 0) (s := []) (G := G + 13)
      (by rintro ⟨⟩) rfl rfl
      (by simpa using hgwei)
      (by simp only [Devm.gasLeft_setMach, gLow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (Devm.popBurnBy_setMach (s := []) (G := G)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach] using htail

/-- The successful upper-value guard preserves exact chronology and carries
the expanded decoded-memory image into event staging. -/
theorem depositAmountUpperGuard_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {data : Bytes} {amount : B256}
    {G slot : Nat} {rest : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hmem : DepositDecodedMemoryCarrier memory data)
    (hamount : sevm.value / Nat.toB256 oneGwei = amount)
    (hupper : amount ≤ Nat.toB256 (2 ^ 64 - 1))
    (htail : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[], memory.write 672 amount.toBytes, G⟩) rest ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory, G + 86⟩)
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: div ::: dup 0 :::
        mstoreAt amountWord +++
        pushB256 (Nat.toB256 (2 ^ 64 - 1)) ::: lt :::
        ((.call slot) <?> rest)) ex effects := by
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := Nat.toB256 oneGwei)
      (c := gVerylow) (G := G + 83)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushItem
      (r := .callvalue) (x := sevm.value) (cost := gBase)
      (G := G + 81) (by rintro ⟨⟩) rfl
      (by simp only [Devm.gasLeft_setMach, gBase])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .div) (f := (· / ·)) (cost := gLow)
      (x := sevm.value) (y := Nat.toB256 oneGwei)
      (v := amount) (s := []) (G := G + 76)
      (by rintro ⟨⟩) rfl rfl hamount
      (by simp only [Devm.gasLeft_setMach, gLow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_dup (n := 0) (w := amount) (G := G + 73) rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach, mstoreAt, prepend]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := amountWord * 32)
      (c := gVerylow) (G := G + 70)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mstore_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨amountWord * 32 :: amount :: amount :: [], memory, G + 70⟩)
      (i := amountWord * 32) (v := amount) (s := amount :: [])
      (G := G + 19) (e := 48) rfl
      (by
        rw [show (amountWord * 32 : B256).toNat = 672 by decide +kernel]
        exact Devm.extCost_of_size hmem.size_eq (by decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256
      (w := Nat.toB256 (2 ^ 64 - 1)) (c := gVerylow) (G := G + 16)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_binary
      (r := .lt) (f := B256.ltCheck) (cost := gVerylow)
      (x := Nat.toB256 (2 ^ 64 - 1)) (y := amount)
      (v := 0) (s := []) (G := G + 13)
      (by rintro ⟨⟩) rfl rfl
      (by rw [B256.ltCheck, if_neg (B256.not_lt.mpr hupper)])
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [List.length_nil]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  apply Func.StorageEffectRun.zero
    (by
      simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
      omega)
    (Devm.popBurnBy_setMach (s := []) (G := G)
      (by simp only [Devm.stack_setMach])
      (by simp only [Devm.gasLeft_setMach, gVerylow, gHigh]))
  simpa only [Devm.setMach_setMach, Devm.memory_setMach,
    show (amountWord * 32 : B256).toNat = 672 by decide +kernel] using htail

/-- The complete six-guard success traversal preserves exact chronology. -/
theorem depositGuards_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {pubkey withdrawalCredentials signature : Bytes} {depositDataRoot : B256}
    {amount : B256} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hpubkey : pubkey.length = 48)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hsignature : signature.length = 96)
    (hamount : sevm.value / Nat.toB256 oneGwei = amount)
    (hlower : Nat.toB256 oneEther ≤ sevm.value)
    (hgwei : sevm.value % Nat.toB256 oneGwei = 0)
    (hupper : amount ≤ Nat.toB256 (2 ^ 64 - 1))
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositEventInputMemory sevm.data amount, G⟩)
      (stageDepositEvent +++ depositAfterEvent) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[], depositDecodedMemory sevm.data, G + depositGuardsGas⟩)
      depositBody ex effects := by
  let memory := depositDecodedMemory sevm.data
  have hcarrier : DepositDecodedMemoryCarrier memory sevm.data :=
    depositDecodedMemory_carrier sevm.data
  have hbody' : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], memory.write 672 amount.toBytes, G⟩)
      (stageDepositEvent +++ depositAfterEvent) ex effects := by
    simpa only [memory, depositEventInputMemory] using hbody
  have hupperRun := depositAmountUpperGuard_storageEffectRun
    (slot := valueTooHighErrorSlot) hcarrier hamount hupper hbody'
  have hgweiRun := depositGweiMultipleGuard_storageEffectRun
    (slot := valueNotGweiErrorSlot) hgwei hupperRun
  have hlowerRun := depositValueLowerGuard_storageEffectRun
    (slot := valueTooLowErrorSlot) hlower hgweiRun
  have hlengthRun := depositLengthGuards_storageEffectRun
    (base := base) (memory := memory) hcarrier hdec hpubkey hwithdrawal
    hsignature hlowerRun
  simpa only [memory, depositGuardsGas, depositBody] using hlengthRun

end Blanc.BeaconDeposit
