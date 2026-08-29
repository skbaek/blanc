import Blanc.BeaconDepositAbiMemory
import Blanc.ForwardCall

/-!
# Beacon deposit compiled ABI decoder

The successful dynamic-tail boundary is factored into its six source-shaped
pieces.  Each piece is a short forward certificate over an abstract memory and
stack; the concrete six-word image is introduced only by the three store
suffixes below.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Ninst

private def validateDynamicTailAfterArg
    (offsetWord lengthWord : B256) (body : Func) : Func :=
  let accept : Func :=
    mstoreAt lengthWord +++ mstoreAt offsetWord +++ body
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
  dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
  swap 0 ::: lt ::: iszero :::
  ((.call emptyRevertSlot) <?> checkLengthWord)

private theorem validateDynamicTailAfterArg_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256} {G head offsetWord lengthWord : Nat}
    {body : Func} {ex : Execution}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DynamicTailDecodable sevm.data head)
    (hroom : stack.length < 1018)
    (haccept : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨depositLengthWord sevm.data head ::
          depositOffsetWord sevm.data head :: stack, memory, G⟩)
      (mstoreAt (Nat.toB256 lengthWord) +++
        mstoreAt (Nat.toB256 offsetWord) +++ body) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨depositOffsetWord sevm.data head :: stack, memory, G + 143⟩)
      (validateDynamicTailAfterArg
        (Nat.toB256 offsetWord) (Nat.toB256 lengthWord) body) ex := by
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
  have hoffsetNat : offset.toNat = offsetNat := by
    exact depositOffsetWord_toNat (by omega)
  have hlengthNat : length.toNat = lengthNat := by
    exact depositLengthWord_toNat (by omega)
  have hlimitNat : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by
    exact B256.toNat_toB256_of_lt (by omega)
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
    exact dataWord_depositLengthWord head (by
      omega)
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
  have hpaddedRun : Func.RunCompiledTo fs sevm
      (base.setMach ⟨length :: offset :: stack, memory, G + 48⟩)
      checkPaddedEnd ex := by
    dsimp only [checkPaddedEnd]
    func_run (13)
      [31 + length, ~~~ (31 : B256), rounded, offset + rounded,
        paddedEnd, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [accept, show G + 48 - 48 = G by omega] using haccept
  have hlengthRun : Func.RunCompiledTo fs sevm
      (base.setMach ⟨length :: offset :: stack, memory, G + 76⟩)
      checkLength ex := by
    dsimp only [checkLength]
    func_run (6) [1, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [show G + 76 - 28 = G + 48 by omega] using hpaddedRun
  have hloadRun : Func.RunCompiledTo fs sevm
      (base.setMach ⟨offset :: stack, memory, G + 88⟩)
      loadLength ex := by
    dsimp only [loadLength]
    func_run (4) [4 + offset]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    rw [hlengthLoad]
    simpa only [show G + 88 - 12 = G + 76 by omega] using hlengthRun
  have hlengthWordRun : Func.RunCompiledTo fs sevm
      (base.setMach ⟨offset :: stack, memory, G + 115⟩)
      checkLengthWord ex := by
    dsimp only [checkLengthWord]
    func_run (6) [36 + offset, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [show G + 115 - 27 = G + 88 by omega] using hloadRun
  have hoffsetRun : Func.RunCompiledTo fs sevm
      (base.setMach ⟨offset :: stack, memory, G + 143⟩)
      (dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
        swap 0 ::: lt ::: iszero :::
        ((.call emptyRevertSlot) <?> checkLengthWord)) ex := by
    func_run (6) [1, 0]
    all_goals try {
      simp only [Devm.stack_setMach, List.length_cons] at *
      omega }
    simpa only [show G + 143 - 28 = G + 115 by omega] using hlengthWordRun
  simpa only [validateDynamicTailAfterArg] using hoffsetRun

private def depositDecodedTail0Memory (data : Bytes) : Mem :=
  (Mem.empty.write 96 (depositLengthWord data 0).toBytes)
    |>.write 0 (depositOffsetWord data 0).toBytes

private def depositDecodedTail1Memory (data : Bytes) : Mem :=
  (depositDecodedTail0Memory data).write 128
      (depositLengthWord data 1).toBytes
    |>.write 32 (depositOffsetWord data 1).toBytes

private theorem depositDecodedTail0Memory_size (data : Bytes) :
    (depositDecodedTail0Memory data).size = 128 := by
  unfold depositDecodedTail0Memory
  rw [Mem.size_write_word_at, Mem.size_write_word_at]
  decide +kernel

private theorem depositDecodedTail1Memory_size (data : Bytes) :
    (depositDecodedTail1Memory data).size = 160 := by
  unfold depositDecodedTail1Memory
  rw [Mem.size_write_word_at, Mem.size_write_word_at,
    depositDecodedTail0Memory_size]
  decide +kernel

private theorem depositTail0Stores_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedTail0Memory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[depositLengthWord sevm.data 0,
          depositOffsetWord sevm.data 0], Mem.empty, G + 23⟩)
      (mstoreAt 3 +++ mstoreAt 0 +++ body) ex := by
  func_run (2) [12]
  case h_ext =>
    exact Devm.extCost_of_size
      (show Mem.empty.size = 0 by rfl) (by decide +kernel)
  case a =>
    func_run (2) [0]
    case h_ext =>
      exact Devm.extCost_zero_of_le
        (by rw [Mem.size_write_word_at]; decide +kernel)
        (by rw [Mem.size_write_word_at]; decide +kernel)
    case a =>
      simpa only [depositDecodedTail0Memory, prepend,
        show ((3 : B256) * 32).toNat = 96 by decide +kernel,
        show ((0 : B256) * 32).toNat = 0 by decide +kernel,
        show G + 23 - 23 = G by omega] using hbody

private theorem depositTail1Stores_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedTail1Memory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[depositLengthWord sevm.data 1,
          depositOffsetWord sevm.data 1],
          depositDecodedTail0Memory sevm.data, G + 15⟩)
      (mstoreAt 4 +++ mstoreAt 1 +++ body) ex := by
  func_run (2) [3]
  case h_ext =>
    exact Devm.extCost_of_size
      (depositDecodedTail0Memory_size sevm.data) (by decide +kernel)
  case a =>
    func_run (2) [0]
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
    case a =>
      simpa only [depositDecodedTail1Memory, prepend,
        show ((4 : B256) * 32).toNat = 128 by decide +kernel,
        show ((1 : B256) * 32).toNat = 32 by decide +kernel,
        show G + 15 - 15 = G by omega] using hbody

end Blanc.BeaconDeposit
