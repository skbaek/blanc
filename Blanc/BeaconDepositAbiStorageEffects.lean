import Blanc.BeaconDepositAbi
import Blanc.ForwardStorageEffects

/-! # Exact storage effects through successful Beacon deposit ABI decoding -/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

private theorem validateDynamicTailAfterArg_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256} {G head offsetWord lengthWord : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DynamicTailDecodable sevm.data head)
    (hroom : stack.length < 1018)
    (haccept : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨depositLengthWord sevm.data head ::
          depositOffsetWord sevm.data head :: stack, memory, G⟩)
      (mstoreAt (Nat.toB256 lengthWord) +++
        mstoreAt (Nat.toB256 offsetWord) +++ body) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨depositOffsetWord sevm.data head :: stack, memory, G + 143⟩)
      (validateDynamicTailAfterArg
        (Nat.toB256 offsetWord) (Nat.toB256 lengthWord) body) ex effects := by
  let offsetNat := dynamicOffset sevm.data head
  let lengthNat := dynamicLength sevm.data head
  let offset := depositOffsetWord sevm.data head
  let length := depositLengthWord sevm.data head
  let rounded : B256 := (~~~ (31 : B256)) &&& (31 + length)
  let paddedEnd : B256 := 36 + (offset + rounded)
  change offsetNat < 2 ^ 32 ∧
      36 + offsetNat ≤ sevm.data.length ∧
      lengthNat < 2 ^ 32 ∧
      36 + offsetNat + ceil32 lengthNat ≤ sevm.data.length at hdec
  rcases hdec with ⟨hoffset, hlengthWord, hlength, hpadded⟩
  have hoffsetNat : offset.toNat = offsetNat :=
    depositOffsetWord_toNat (by omega)
  have hlengthNat : length.toNat = lengthNat :=
    depositLengthWord_toNat (by omega)
  have hlimitNat : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 :=
    B256.toNat_toB256_of_lt (by omega)
  have hoffsetLt :
      B256.ltCheck offset (Nat.toB256 (2 ^ 32)) = 1 := by
    simp only [B256.ltCheck]
    rw [if_pos]
    rw [B256.lt_iff_toNat_lt_toNat, hoffsetNat, hlimitNat]
    exact hoffset
  have hlengthLt :
      B256.ltCheck length (Nat.toB256 (2 ^ 32)) = 1 := by
    simp only [B256.ltCheck]
    rw [if_pos]
    rw [B256.lt_iff_toNat_lt_toNat, hlengthNat, hlimitNat]
    exact hlength
  have hoffsetPlusFour :
      4 + offset = Nat.toB256 (4 + offsetNat) := by
    rw [B256.add_comm]
    exact depositOffsetWord_add_four hoffset
  have hlengthLoad : Sevm.dataWord sevm (4 + offset) = length := by
    rw [hoffsetPlusFour]
    exact dataWord_depositLengthWord head (by omega)
  have hoffsetPlusThirtySixNat : (36 + offset).toNat = 36 + offsetNat := by
    rw [B256.toNat_add_eq_of_nof]
    · rw [hoffsetNat, show (36 : B256).toNat = 36 by decide +kernel]
    · unfold B256.Nof
      rw [hoffsetNat, show (36 : B256).toNat = 36 by decide +kernel]
      omega
  have hlengthWordInBounds :
      B256.ltCheck sevm.data.length.toB256 (36 + offset) = 0 := by
    simp only [B256.ltCheck]
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hdataBound, hoffsetPlusThirtySixNat]
    omega
  have hroundedNat : rounded.toNat = ceil32 lengthNat := by
    dsimp only [rounded, length]
    simpa only [depositLengthWord] using
      (B256.toNat_ceil32 (len := lengthNat) (by omega))
  have hoffsetRoundedNat :
      (offset + rounded).toNat = offsetNat + ceil32 lengthNat := by
    rw [B256.toNat_add_eq_of_nof]
    · rw [hoffsetNat, hroundedNat]
    · unfold B256.Nof
      rw [hoffsetNat, hroundedNat]
      omega
  have hpaddedEndNat :
      paddedEnd.toNat = 36 + offsetNat + ceil32 lengthNat := by
    dsimp only [paddedEnd]
    rw [B256.toNat_add_eq_of_nof]
    · rw [hoffsetRoundedNat,
        show (36 : B256).toNat = 36 by decide +kernel]
      omega
    · unfold B256.Nof
      rw [hoffsetRoundedNat,
        show (36 : B256).toNat = 36 by decide +kernel]
      omega
  have hpaddedInBounds :
      B256.ltCheck sevm.data.length.toB256 paddedEnd = 0 := by
    simp only [B256.ltCheck]
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hdataBound, hpaddedEndNat]
    omega
  let accept : Func :=
    mstoreAt (Nat.toB256 lengthWord) +++
      mstoreAt (Nat.toB256 offsetWord) +++ body
  let checkPaddedEnd : Func :=
    dup 0 ::: pushB256 31 ::: add :::
    pushB256 31 ::: Ninst.not ::: Ninst.and :::
    dup 2 ::: add ::: pushB256 36 ::: add :::
    calldatasize ::: lt :::
    ((.call emptyRevertSlot) <?> accept)
  let checkLength : Func :=
    dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
    swap 0 ::: lt ::: iszero :::
    ((.call emptyRevertSlot) <?> checkPaddedEnd)
  let loadLength : Func :=
    dup 0 ::: pushB256 4 ::: add ::: calldataload ::: checkLength
  let checkLengthWord : Func :=
    dup 0 ::: pushB256 36 ::: add ::: calldatasize ::: lt :::
    ((.call emptyRevertSlot) <?> loadLength)
  have hpaddedRun : Func.StorageEffectRun fs sevm
      (base.setMach ⟨length :: offset :: stack, memory, G + 48⟩)
      checkPaddedEnd ex effects := by
    dsimp only [checkPaddedEnd]
    storage_effect_run (13)
      [31 + length, ~~~ (31 : B256), rounded, offset + rounded,
        paddedEnd, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [accept, show G + 48 - 48 = G by omega] using haccept
  have hlengthRun : Func.StorageEffectRun fs sevm
      (base.setMach ⟨length :: offset :: stack, memory, G + 76⟩)
      checkLength ex effects := by
    dsimp only [checkLength]
    storage_effect_run (6) [1, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [show G + 76 - 28 = G + 48 by omega] using hpaddedRun
  have hloadRun : Func.StorageEffectRun fs sevm
      (base.setMach ⟨offset :: stack, memory, G + 88⟩)
      loadLength ex effects := by
    dsimp only [loadLength]
    storage_effect_run (4) [4 + offset]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    rw [hlengthLoad]
    simpa only [show G + 88 - 12 = G + 76 by omega] using hlengthRun
  have hlengthWordRun : Func.StorageEffectRun fs sevm
      (base.setMach ⟨offset :: stack, memory, G + 115⟩)
      checkLengthWord ex effects := by
    dsimp only [checkLengthWord]
    storage_effect_run (6) [36 + offset, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [show G + 115 - 27 = G + 88 by omega] using hloadRun
  have hoffsetRun : Func.StorageEffectRun fs sevm
      (base.setMach ⟨offset :: stack, memory, G + 143⟩)
      (dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
        swap 0 ::: lt ::: iszero :::
        ((.call emptyRevertSlot) <?> checkLengthWord)) ex effects := by
    storage_effect_run (6) [1, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [show G + 143 - 28 = G + 115 by omega] using hlengthWordRun
  simpa only [validateDynamicTailAfterArg] using hoffsetRun

private theorem depositTail0Stores_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedTail0Memory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[depositLengthWord sevm.data 0,
          depositOffsetWord sevm.data 0], Mem.empty, G + 23⟩)
      (mstoreAt 3 +++ mstoreAt 0 +++ body) ex effects := by
  storage_effect_run (2) [12]
  case h_ext =>
    exact Devm.extCost_of_size
      (show Mem.empty.size = 0 by rfl) (by decide +kernel)
  case tail =>
    storage_effect_run (2) [0]
    case h_ext =>
      exact Devm.extCost_zero_of_le
        (by rw [Mem.size_write_word_at]; decide +kernel)
        (by rw [Mem.size_write_word_at]; decide +kernel)
    case tail =>
      simpa only [depositDecodedTail0Memory, prepend,
        show ((3 : B256) * 32).toNat = 96 by decide +kernel,
        show ((0 : B256) * 32).toNat = 0 by decide +kernel,
        show G + 23 - 23 = G by omega] using hbody

private theorem depositTail1Stores_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedTail1Memory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[depositLengthWord sevm.data 1,
          depositOffsetWord sevm.data 1],
          depositDecodedTail0Memory sevm.data, G + 15⟩)
      (mstoreAt 4 +++ mstoreAt 1 +++ body) ex effects := by
  storage_effect_run (2) [3]
  case h_ext =>
    exact Devm.extCost_of_size
      (depositDecodedTail0Memory_size sevm.data) (by decide +kernel)
  case tail =>
    storage_effect_run (2) [0]
    case h_ext =>
      exact Devm.extCost_zero_of_le
        (by
          rw [Mem.size_write_word_at,
            depositDecodedTail0Memory_size]
          decide +kernel)
        (by
          rw [Mem.size_write_word_at,
            depositDecodedTail0Memory_size]
          decide +kernel)
    case tail =>
      simpa only [depositDecodedTail1Memory, prepend,
        show ((4 : B256) * 32).toNat = 128 by decide +kernel,
        show ((1 : B256) * 32).toNat = 32 by decide +kernel,
        show G + 15 - 15 = G by omega] using hbody

private def depositDecodedTail2LengthMemoryEffects (data : Bytes) : Mem :=
  (depositDecodedTail1Memory data).write 160
    (depositLengthWord data 2).toBytes

private theorem depositDecodedTail2LengthMemory_size_effects (data : Bytes) :
    (depositDecodedTail2LengthMemoryEffects data).size = 192 := by
  unfold depositDecodedTail2LengthMemoryEffects
  rw [Mem.size_write_word_at, depositDecodedTail1Memory_size]
  decide +kernel

private theorem depositDecodedTail2Memory_eq_effects (data : Bytes) :
    (depositDecodedTail2LengthMemoryEffects data).write 64
        (depositOffsetWord data 2).toBytes =
      depositDecodedMemory data := by
  rfl

private theorem depositTail2OffsetStore_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[depositOffsetWord sevm.data 2],
          depositDecodedTail2LengthMemoryEffects sevm.data, G + 6⟩)
      (mstoreAt 2 +++ body) ex effects := by
  simp only [mstoreAt, prepend]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (w := 64) (c := gVerylow) (G := G + 3)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by
        simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
        omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_mstore_of
      (sevm := sevm)
      (devm := base.setMach
        ⟨64 :: depositOffsetWord sevm.data 2 :: [],
          depositDecodedTail2LengthMemoryEffects sevm.data, G + 3⟩)
      (i := 64) (v := depositOffsetWord sevm.data 2) (s := [])
      (G := G) (e := 0) rfl
      (Devm.extCost_zero_of_le
        (by rw [depositDecodedTail2LengthMemory_size_effects])
        (by
          rw [depositDecodedTail2LengthMemory_size_effects]
          decide +kernel))
      (by simp only [Devm.gasLeft_setMach, gVerylow]) rfl)
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simpa only [Devm.setMach_setMach, Devm.memory_setMach,
    show (64 : B256).toNat = 64 by decide +kernel,
    depositDecodedTail2Memory_eq_effects] using hbody

private theorem depositTail2Stores_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[depositLengthWord sevm.data 2,
          depositOffsetWord sevm.data 2],
          depositDecodedTail1Memory sevm.data, G + 15⟩)
      (mstoreAt 5 +++ mstoreAt 2 +++ body) ex effects := by
  storage_effect_run (2) [3]
  case h_ext =>
    exact Devm.extCost_of_size
      (depositDecodedTail1Memory_size sevm.data) (by decide +kernel)
  case tail =>
    change Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[depositOffsetWord sevm.data 2],
          depositDecodedTail2LengthMemoryEffects sevm.data, G + 6⟩)
      (mstoreAt 2 +++ body) ex effects
    exact depositTail2OffsetStore_success_storageEffectRun hbody

private theorem validateDynamicTail_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256}
    {G head headNat offsetWord lengthWord : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (haddress : (32 * Nat.toB256 head) + 4 =
      Nat.toB256 (4 + 32 * headNat))
    (hpushCost :
      pushCost ((32 * Nat.toB256 head) + 4).toBytes.sig = 3)
    (hheadBound : 4 + 32 * headNat < 2 ^ 256)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DynamicTailDecodable sevm.data headNat)
    (hroom : stack.length < 1018)
    (haccept : Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨depositLengthWord sevm.data headNat ::
          depositOffsetWord sevm.data headNat :: stack, memory, G⟩)
      (mstoreAt (Nat.toB256 lengthWord) +++
        mstoreAt (Nat.toB256 offsetWord) +++ body) ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨stack, memory, G + 149⟩)
      (validateDynamicTail (Nat.toB256 head)
        (Nat.toB256 offsetWord) (Nat.toB256 lengthWord) body) ex effects := by
  have hafter := validateDynamicTailAfterArg_success_storageEffectRun
    (base := base) (memory := memory) (stack := stack)
    (head := headNat) (offsetWord := offsetWord)
    (lengthWord := lengthWord) hdataBound hdec hroom haccept
  have hload :
      Sevm.dataWord sevm ((32 * Nat.toB256 head) + 4) =
        depositOffsetWord sevm.data headNat := by
    rw [haddress]
    exact dataWord_depositOffsetWord headNat hheadBound
  rw [validateDynamicTail_eq]
  unfold arg cdl
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_pushB256 (G := G + 146) hpushCost
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach]; omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.StorageEffectRun.next_effectNeutral
    (Ninst.runCompiled_calldataload
      (v := depositOffsetWord sevm.data headNat) (G := G + 143)
      rfl hload
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by omega))
    (by rintro ⟨⟩) (by rintro operation ⟨⟩)
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, prepend] using hafter

private theorem depositTail2_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DynamicTailDecodable sevm.data 2)
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[], depositDecodedTail1Memory sevm.data, G + 164⟩)
      (validateDynamicTail 2 2 5 body) ex effects := by
  have hstores := depositTail2Stores_success_storageEffectRun
    (base := base) hbody
  have hrun := validateDynamicTail_success_storageEffectRun
    (base := base) (memory := depositDecodedTail1Memory sevm.data)
    (stack := []) (G := G + 15)
    (head := 2) (headNat := 2) (offsetWord := 2) (lengthWord := 5)
    (body := body)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hdataBound hdec (by decide) hstores
  simpa only [
    show Nat.toB256 2 = (2 : B256) by decide +kernel,
    show Nat.toB256 5 = (5 : B256) by decide +kernel,
    show G + 15 + 149 = G + 164 by omega] using hrun

private theorem depositTail1_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach
        ⟨[], depositDecodedTail0Memory sevm.data, G + 328⟩)
      (validateDynamicTail 1 1 4
        (validateDynamicTail 2 2 5 body)) ex effects := by
  have htail2 := depositTail2_success_storageEffectRun
    (base := base) hdataBound hdec2 hbody
  have hstores := depositTail1Stores_success_storageEffectRun
    (base := base) htail2
  have hrun := validateDynamicTail_success_storageEffectRun
    (base := base) (memory := depositDecodedTail0Memory sevm.data)
    (stack := []) (G := G + 164 + 15)
    (head := 1) (headNat := 1) (offsetWord := 1) (lengthWord := 4)
    (body := validateDynamicTail 2 2 5 body)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hdataBound hdec1 (by decide) hstores
  simpa only [
    show Nat.toB256 1 = (1 : B256) by decide +kernel,
    show Nat.toB256 4 = (4 : B256) by decide +kernel,
    show G + 164 + 15 + 149 = G + 328 by omega] using hrun

private theorem depositDynamicTails_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec0 : DynamicTailDecodable sevm.data 0)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, G + 500⟩)
      (validateDynamicTail 0 0 3
        (validateDynamicTail 1 1 4
          (validateDynamicTail 2 2 5 body))) ex effects := by
  have htail1 := depositTail1_success_storageEffectRun
    (base := base) hdataBound hdec1 hdec2 hbody
  have hstores := depositTail0Stores_success_storageEffectRun
    (base := base) htail1
  have hrun := validateDynamicTail_success_storageEffectRun
    (base := base) (memory := Mem.empty) (stack := [])
    (G := G + 328 + 23)
    (head := 0) (headNat := 0) (offsetWord := 0) (lengthWord := 3)
    (body := validateDynamicTail 1 1 4
      (validateDynamicTail 2 2 5 body))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    hdataBound hdec0 (by decide) hstores
  simpa only [
    show Nat.toB256 0 = (0 : B256) by decide +kernel,
    show Nat.toB256 3 = (3 : B256) by decide +kernel,
    show G + 328 + 23 + 149 = G + 500 by omega] using hrun

/-- Successful ABI decoding preserves the continuation's exact retained
storage chronology. -/
theorem validateDepositAbi_success_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {body : Func} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey
      withdrawalCredentials signature depositDataRoot)
    (hbody : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex effects) :
    Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, G + 521⟩)
      (validateDepositAbi body) ex effects := by
  have hlengthNat : sevm.data.length.toB256.toNat =
      sevm.data.length :=
    B256.toNat_toB256_of_lt hdataBound
  have hheadInBounds :
      B256.ltCheck sevm.data.length.toB256 132 = 0 := by
    simp only [B256.ltCheck]
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat, hlengthNat,
      show (132 : B256).toNat = 132 by decide +kernel]
    exact not_lt_of_ge hdec.head
  have hdecoded := depositDynamicTails_success_storageEffectRun
    (base := base) hdataBound hdec.pubkeyTail
      hdec.withdrawalCredentialsTail hdec.signatureTail hbody
  unfold validateDepositAbi
  storage_effect_run (4) [0]
  case h_arm =>
    simpa only [show G + 521 - 21 = G + 500 by omega] using hdecoded

end Blanc.BeaconDeposit
