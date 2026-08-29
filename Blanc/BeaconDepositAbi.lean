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

/-- One `mstoreAt` step over an abstract memory.  Keeping the threaded memory
abstract prevents the compiled-walk term from carrying a concrete write tower. -/
private theorem mstoreAt_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256} {value word : B256}
    {G pushGas extGas : Nat} {body : Func} {ex : Execution}
    (hpushCost : pushCost (word * 32).toBytes.sig = pushGas)
    (hroom : stack.length < 1023)
    (hext : ∀ (S : List B256) (G' : Nat),
      (base.setMach ⟨S, memory, G'⟩).extCost
        [⟨(word * 32).toNat, 32⟩] = extGas)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory.write (word * 32).toNat value.toBytes, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨value :: stack, memory, G + pushGas + gVerylow + extGas⟩)
      (mstoreAt word +++ body) ex := by
  unfold mstoreAt
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + gVerylow + extGas) hpushCost
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by
        simp only [Devm.stack_setMach, List.length_cons]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.runCompiledTo_mstore_step
    (M := memory) (c := gVerylow + extGas) rfl rfl ?_ ?_ ?_
  · rw [hext]
  · simp only [Devm.gasLeft_setMach]
    omega
  · intro memory' G' hmemory hgas
    simp only [Devm.gasLeft_setMach] at hgas
    subst memory'
    have hG' : G' = G := by omega
    subst G'
    simpa only [Devm.setMach_setMach, prepend] using hbody

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

private def depositDecodedTail2LengthMemory (data : Bytes) : Mem :=
  (depositDecodedTail1Memory data).write 160
    (depositLengthWord data 2).toBytes

private theorem depositDecodedTail2LengthMemory_size (data : Bytes) :
    (depositDecodedTail2LengthMemory data).size = 192 := by
  unfold depositDecodedTail2LengthMemory
  rw [Mem.size_write_word_at, depositDecodedTail1Memory_size]
  decide +kernel

private theorem depositDecodedTail2Memory_eq (data : Bytes) :
    (depositDecodedTail2LengthMemory data).write 64
        (depositOffsetWord data 2).toBytes =
      depositDecodedMemory data := by
  rfl

private theorem depositTail2OffsetStore_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[depositOffsetWord sevm.data 2],
          depositDecodedTail2LengthMemory sevm.data, G + 6⟩)
      (mstoreAt 2 +++ body) ex := by
  have hbody' : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], (depositDecodedTail2LengthMemory sevm.data).write
          ((2 : B256) * 32).toNat
          (depositOffsetWord sevm.data 2).toBytes, G⟩)
      body ex := by
    rw [show ((2 : B256) * 32).toNat = 64 by decide +kernel,
      depositDecodedTail2Memory_eq]
    exact hbody
  have hstore := mstoreAt_success_runCompiledTo
    (base := base) (memory := depositDecodedTail2LengthMemory sevm.data)
    (stack := []) (value := depositOffsetWord sevm.data 2)
    (word := 2) (G := G) (pushGas := 3) (extGas := 0)
    (body := body)
    (by decide +kernel) (by decide)
    (by
      intro S G'
      exact Devm.extCost_zero_of_le
        (N := depositDecodedTail2LengthMemory sevm.data)
        (i := ((2 : B256) * 32).toNat) (sz := 32)
        (by rw [depositDecodedTail2LengthMemory_size])
        (by rw [depositDecodedTail2LengthMemory_size]; decide +kernel))
    hbody'
  simpa only [
    show G + 3 + gVerylow + 0 = G + 6 by
      simp only [gVerylow]] using hstore

private theorem depositTail2Stores_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[depositLengthWord sevm.data 2,
          depositOffsetWord sevm.data 2],
          depositDecodedTail1Memory sevm.data, G + 15⟩)
      (mstoreAt 5 +++ mstoreAt 2 +++ body) ex := by
  have hoffsetRun :=
    depositTail2OffsetStore_success_runCompiledTo (base := base) hbody
  have hrest : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[depositOffsetWord sevm.data 2],
          (depositDecodedTail1Memory sevm.data).write
            ((5 : B256) * 32).toNat
            (depositLengthWord sevm.data 2).toBytes,
          G + 6⟩)
      (mstoreAt 2 +++ body) ex := by
    rw [show ((5 : B256) * 32).toNat = 160 by decide +kernel]
    simpa only [depositDecodedTail2LengthMemory] using hoffsetRun
  have hstore := mstoreAt_success_runCompiledTo
    (base := base) (memory := depositDecodedTail1Memory sevm.data)
    (stack := [depositOffsetWord sevm.data 2])
    (value := depositLengthWord sevm.data 2)
    (word := 5) (G := G + 6) (pushGas := 3) (extGas := 3)
    (body := mstoreAt 2 +++ body)
    (by decide +kernel)
    (by
      simp only [List.length_cons, List.length_nil]
      omega)
    (by
      intro S G'
      exact Devm.extCost_of_size
        (N := depositDecodedTail1Memory sevm.data)
        (i := ((5 : B256) * 32).toNat) (sz := 32)
        (depositDecodedTail1Memory_size sevm.data) (by decide +kernel))
    hrest
  simpa only [
    show G + 6 + 3 + gVerylow + 3 = G + 15 by
      simp only [gVerylow]] using hstore

private theorem validateDynamicTail_eq
    (head offsetWord lengthWord : B256) (body : Func) :
    validateDynamicTail head offsetWord lengthWord body =
      arg head +++
        validateDynamicTailAfterArg offsetWord lengthWord body := by
  rfl

/-- Add the two-instruction ABI-head load to an already certified tail. -/
private theorem validateDynamicTail_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256}
    {G head headNat offsetWord lengthWord : Nat}
    {body : Func} {ex : Execution}
    (haddress : (32 * Nat.toB256 head) + 4 =
      Nat.toB256 (4 + 32 * headNat))
    (hpushCost :
      pushCost ((32 * Nat.toB256 head) + 4).toBytes.sig = 3)
    (hheadBound : 4 + 32 * headNat < 2 ^ 256)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DynamicTailDecodable sevm.data headNat)
    (hroom : stack.length < 1018)
    (haccept : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨depositLengthWord sevm.data headNat ::
          depositOffsetWord sevm.data headNat :: stack, memory, G⟩)
      (mstoreAt (Nat.toB256 lengthWord) +++
        mstoreAt (Nat.toB256 offsetWord) +++ body) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, memory, G + 149⟩)
      (validateDynamicTail (Nat.toB256 head)
        (Nat.toB256 offsetWord) (Nat.toB256 lengthWord) body) ex := by
  have hafter := validateDynamicTailAfterArg_success_runCompiledTo
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
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256 (G := G + 146) hpushCost
      (by simp only [Devm.gasLeft_setMach])
      (by
        simp only [Devm.stack_setMach]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldataload
      (v := depositOffsetWord sevm.data headNat) (G := G + 143)
      rfl hload
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by omega)) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, prepend]
    using hafter

private theorem depositTail2_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DynamicTailDecodable sevm.data 2)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], depositDecodedTail1Memory sevm.data, G + 164⟩)
      (validateDynamicTail 2 2 5 body) ex := by
  have hstores := depositTail2Stores_success_runCompiledTo
    (base := base) hbody
  have hrun := validateDynamicTail_success_runCompiledTo
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

private theorem depositTail1_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], depositDecodedTail0Memory sevm.data, G + 328⟩)
      (validateDynamicTail 1 1 4
        (validateDynamicTail 2 2 5 body)) ex := by
  have htail2 := depositTail2_success_runCompiledTo
    (base := base) hdataBound hdec2 hbody
  have hstores := depositTail1Stores_success_runCompiledTo
    (base := base) htail2
  have hrun := validateDynamicTail_success_runCompiledTo
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

private theorem depositDynamicTails_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec0 : DynamicTailDecodable sevm.data 0)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 500⟩)
      (validateDynamicTail 0 0 3
        (validateDynamicTail 1 1 4
          (validateDynamicTail 2 2 5 body))) ex := by
  have htail1 := depositTail1_success_runCompiledTo
    (base := base) hdataBound hdec1 hdec2 hbody
  have hstores := depositTail0Stores_success_runCompiledTo
    (base := base) htail1
  have hrun := validateDynamicTail_success_runCompiledTo
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

/-- A well-formed deposit ABI reaches the source body with the exact six-word
decoder memory and 521 gas consumed. -/
theorem validateDepositAbi_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {pubkey withdrawalCredentials signature : Bytes}
    {depositDataRoot : B256} {body : Func} {ex : Execution}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey
      withdrawalCredentials signature depositDataRoot)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], depositDecodedMemory sevm.data, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 521⟩)
      (validateDepositAbi body) ex := by
  have hlengthNat : sevm.data.length.toB256.toNat =
      sevm.data.length := by
    exact B256.toNat_toB256_of_lt hdataBound
  have hheadInBounds :
      B256.ltCheck sevm.data.length.toB256 132 = 0 := by
    simp only [B256.ltCheck]
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat, hlengthNat,
      show (132 : B256).toNat = 132 by decide +kernel]
    exact not_lt_of_ge hdec.head
  have hdecoded := depositDynamicTails_success_runCompiledTo
    (base := base) hdataBound hdec.pubkeyTail
      hdec.withdrawalCredentialsTail hdec.signatureTail hbody
  unfold validateDepositAbi
  func_run (4) [0]
  simpa only [show G + 521 - 21 = G + 500 by omega] using hdecoded

end Blanc.BeaconDeposit
