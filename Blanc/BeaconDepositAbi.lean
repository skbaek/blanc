import Blanc.BeaconDepositAbiMemory
import Blanc.ForwardCall
import Blanc.ForwardNoRawSstore

/-!
# Beacon deposit compiled ABI decoder

The successful dynamic-tail boundary is factored into its six source-shaped
pieces.  Each piece is a short forward certificate over an abstract memory and
stack; the concrete six-word image is introduced only by the three store
suffixes below.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-! ## Structure-only malformed-input partition -/

/-- The first failing guard within one dynamic ABI tail. -/
inductive DynamicTailFailureStage
  | offset
  | lengthWord
  | length
  | paddedEnd
deriving DecidableEq

/-- Exact source-order premises selecting one dynamic-tail failure stage. -/
def DynamicTailFailsAt
    (data : Bytes) (head : Nat) : DynamicTailFailureStage → Prop
  | .offset =>
      ¬ dynamicOffset data head < 2 ^ 32
  | .lengthWord =>
      dynamicOffset data head < 2 ^ 32 ∧
        ¬ 36 + dynamicOffset data head ≤ data.length
  | .length =>
      dynamicOffset data head < 2 ^ 32 ∧
        36 + dynamicOffset data head ≤ data.length ∧
        ¬ dynamicLength data head < 2 ^ 32
  | .paddedEnd =>
      dynamicOffset data head < 2 ^ 32 ∧
        36 + dynamicOffset data head ≤ data.length ∧
        dynamicLength data head < 2 ^ 32 ∧
        ¬ 36 + dynamicOffset data head + ceil32 (dynamicLength data head) ≤
          data.length

/-- Exact gas consumed by one selected dynamic-tail failure, including its
two-instruction ABI-head load and empty-revert auxiliary. -/
def DynamicTailFailureStage.gas : DynamicTailFailureStage → Nat
  | .offset => 51
  | .lengthWord => 78
  | .length => 118
  | .paddedEnd => 166

/-- Gas consumed after the two-instruction ABI-head load. -/
private def DynamicTailFailureStage.afterArgGas :
    DynamicTailFailureStage → Nat
  | .offset => 45
  | .lengthWord => 72
  | .length => 112
  | .paddedEnd => 160

private theorem DynamicTailFailureStage.gas_eq_afterArgGas
    (failure : DynamicTailFailureStage) :
    failure.gas = failure.afterArgGas + 6 := by
  cases failure <;> rfl

/-- Stack left by the selected validator guard before the empty revert. -/
def DynamicTailFailureStage.finalStack
    (failure : DynamicTailFailureStage) (data : Bytes) (head : Nat) :
    List B256 :=
  match failure with
  | .offset | .lengthWord => [depositOffsetWord data head]
  | .length | .paddedEnd =>
      [depositLengthWord data head, depositOffsetWord data head]

/-- Every structurally invalid tail has a unique first-failure-shaped row. -/
theorem exists_dynamicTailFailureStage
    {data : Bytes} {head : Nat}
    (hbad : ¬ DynamicTailDecodable data head) :
    ∃ failure, DynamicTailFailsAt data head failure := by
  by_cases hoffset : dynamicOffset data head < 2 ^ 32
  · by_cases hword : 36 + dynamicOffset data head ≤ data.length
    · by_cases hlength : dynamicLength data head < 2 ^ 32
      · exact ⟨.paddedEnd, hoffset, hword, hlength,
          fun hpadded => hbad ⟨hoffset, hword, hlength, hpadded⟩⟩
      · exact ⟨.length, hoffset, hword, hlength⟩
    · exact ⟨.lengthWord, hoffset, hword⟩
  · exact ⟨.offset, hoffset⟩

/-- The thirteen first-failure rows of the complete deposit ABI validator. -/
inductive DepositAbiFailure
  | head
  | tail0 (stage : DynamicTailFailureStage)
  | tail1 (stage : DynamicTailFailureStage)
  | tail2 (stage : DynamicTailFailureStage)
deriving DecidableEq

/-- Exact endpoint gas consumed by one malformed-input row. -/
def DepositAbiFailure.endpointGas : DepositAbiFailure → Nat
  | .head => 38
  | .tail0 stage => 21 + stage.gas
  | .tail1 stage => 21 + 172 + stage.gas
  | .tail2 stage => 21 + 172 + 164 + stage.gas

/-- Stack retained by the first failing complete-validator guard. -/
def DepositAbiFailure.finalStack
    (failure : DepositAbiFailure) (data : Bytes) : List B256 :=
  match failure with
  | .head => []
  | .tail0 stage => stage.finalStack data 0
  | .tail1 stage => stage.finalStack data 1
  | .tail2 stage => stage.finalStack data 2

/-- Exact source-order premises selecting one complete-validator failure. -/
def DepositAbiFailure.Holds (data : Bytes) : DepositAbiFailure → Prop
  | .head => ¬ 132 ≤ data.length
  | .tail0 stage =>
      132 ≤ data.length ∧ DynamicTailFailsAt data 0 stage
  | .tail1 stage =>
      132 ≤ data.length ∧ DynamicTailDecodable data 0 ∧
        DynamicTailFailsAt data 1 stage
  | .tail2 stage =>
      132 ≤ data.length ∧ DynamicTailDecodable data 0 ∧
        DynamicTailDecodable data 1 ∧ DynamicTailFailsAt data 2 stage

/-- Negating structure-only decodability selects one of the thirteen exact
validator failure rows. -/
theorem exists_depositAbiFailure
    {data : Bytes} (hbad : ¬ DepositAbiStructureDecodable data) :
    ∃ failure, DepositAbiFailure.Holds data failure := by
  by_cases hhead : 132 ≤ data.length
  · by_cases htail0 : DynamicTailDecodable data 0
    · by_cases htail1 : DynamicTailDecodable data 1
      · have htail2 : ¬ DynamicTailDecodable data 2 :=
          fun accepted => hbad ⟨hhead, htail0, htail1, accepted⟩
        obtain ⟨stage, hstage⟩ := exists_dynamicTailFailureStage htail2
        exact ⟨DepositAbiFailure.tail2 stage, hhead, htail0, htail1, hstage⟩
      · obtain ⟨stage, hstage⟩ := exists_dynamicTailFailureStage htail1
        exact ⟨DepositAbiFailure.tail1 stage, hhead, htail0, hstage⟩
    · obtain ⟨stage, hstage⟩ := exists_dynamicTailFailureStage htail0
      exact ⟨DepositAbiFailure.tail0 stage, hhead, hstage⟩
  · exact ⟨DepositAbiFailure.head, hhead⟩

/-- ABI dynamic-tail validation after the head offset word has been loaded.
Exposed as the contract-local proof boundary shared by successful and failing
compiled walks. -/
def validateDynamicTailAfterArg
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

/-- A selected dynamic-tail guard reaches the empty-revert auxiliary with the
exact source-prefix cost and the exact stack retained by that guard. -/
private theorem validateDynamicTailAfterArg_failure_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256} {G head : Nat}
    {offsetWord lengthWord : B256} {body : Func}
    (failure : DynamicTailFailureStage)
    (hrev : fs[emptyRevertSlot]? = some Func.rev)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hfailure : DynamicTailFailsAt sevm.data head failure)
    (hroom : stack.length < 1018) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨depositOffsetWord sevm.data head :: stack, memory,
          G + failure.afterArgGas⟩)
      (validateDynamicTailAfterArg offsetWord lengthWord body)
      (.error (.revert,
        (base.setMach
          ⟨failure.finalStack sevm.data head ++ stack, memory, G⟩).withOutput
            [])) := by
  let offsetNat := dynamicOffset sevm.data head
  let lengthNat := dynamicLength sevm.data head
  let offset := depositOffsetWord sevm.data head
  let length := depositLengthWord sevm.data head
  have hoffsetBound : offsetNat < 2 ^ 256 := by
    dsimp only [offsetNat, dynamicOffset]
    exact B256.toNat_lt _
  have hlengthBound : lengthNat < 2 ^ 256 := by
    dsimp only [lengthNat, dynamicLength]
    exact B256.toNat_lt _
  have hoffsetNat : offset.toNat = offsetNat := by
    simpa only [offset, offsetNat] using
      (depositOffsetWord_toNat (data := sevm.data) (head := head) hoffsetBound)
  have hlengthNat : length.toNat = lengthNat := by
    simpa only [length, lengthNat] using
      (depositLengthWord_toNat (data := sevm.data) (head := head) hlengthBound)
  have hlimitNat : (Nat.toB256 (2 ^ 32)).toNat = 2 ^ 32 := by
    exact B256.toNat_toB256_of_lt (by omega)
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
  cases failure with
  | offset =>
      change ¬ offsetNat < 2 ^ 32 at hfailure
      have hoffsetLt :
          B256.ltCheck offset (Nat.toB256 (2 ^ 32)) = 0 := by
        simp only [B256.ltCheck]
        rw [if_neg]
        rw [B256.lt_iff_toNat_lt_toNat, hoffsetNat, hlimitNat]
        exact hfailure
      have hoffsetRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 45⟩)
          (dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
            swap 0 ::: lt ::: iszero :::
            ((.call emptyRevertSlot) <?> checkLengthWord))
          (.error (.revert,
            (base.setMach ⟨offset :: stack, memory, G⟩).withOutput [])) := by
        func_run (5) [0, 1]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        all_goals try omega
        have hguard := Func.runCompiledTo_emptyRevertGuard
            (sevm := sevm)
            (devm := base.setMach
              ⟨(1 : B256) :: offset :: stack, memory, G + 45 - 15⟩)
            (G := G) (w := (1 : B256)) (stack := offset :: stack)
            (otherwise := checkLengthWord)
            hrev (by decide) rfl (by
              simp only [Devm.gasLeft_setMach, emptyRevertGuardCost,
                gVerylow, gHigh, gJumpdest, gMid, gBase]
              omega) (by
              simp only [Devm.stack_setMach, List.length_cons]
              omega)
        rw [Devm.setMach_setMach, Devm.memory_setMach] at hguard
        exact hguard
      simpa only [validateDynamicTailAfterArg, checkLengthWord, loadLength,
          checkLength, checkPaddedEnd, accept,
          DynamicTailFailureStage.afterArgGas,
          DynamicTailFailureStage.finalStack, List.singleton_append,
          List.cons_append, List.nil_append,
          offset] using hoffsetRun
  | lengthWord =>
      change offsetNat < 2 ^ 32 ∧
        ¬ 36 + offsetNat ≤ sevm.data.length at hfailure
      rcases hfailure with ⟨hoffset, hword⟩
      have hoffsetLt :
          B256.ltCheck offset (Nat.toB256 (2 ^ 32)) = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos]
        rw [B256.lt_iff_toNat_lt_toNat, hoffsetNat, hlimitNat]
        exact hoffset
      have hoffsetPlusThirtySixNat :
          (36 + offset).toNat = 36 + offsetNat := by
        rw [B256.toNat_add_eq_of_nof]
        · rw [hoffsetNat,
            show (36 : B256).toNat = 36 by decide +kernel]
        · unfold B256.Nof
          rw [hoffsetNat,
            show (36 : B256).toNat = 36 by decide +kernel]
          omega
      have hlengthWordOut :
          B256.ltCheck sevm.data.length.toB256 (36 + offset) = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos]
        rw [B256.lt_iff_toNat_lt_toNat,
          B256.toNat_toB256_of_lt hdataBound, hoffsetPlusThirtySixNat]
        omega
      have hlengthWordRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 44⟩)
          checkLengthWord
          (.error (.revert,
            (base.setMach ⟨offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [checkLengthWord]
        func_run (5) [36 + offset, 1]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        all_goals try omega
        simpa only [Devm.setMach_setMach, Devm.memory_setMach] using
          (Func.runCompiledTo_emptyRevertGuard
            (devm := base.setMach
              ⟨(1 : B256) :: offset :: stack, memory, G + 44 - 14⟩)
            (G := G) (w := (1 : B256)) (stack := offset :: stack)
            (otherwise := loadLength)
            hrev (by decide) rfl (by
              simp only [Devm.gasLeft_setMach, emptyRevertGuardCost,
                gVerylow, gHigh, gJumpdest, gMid, gBase]
              omega) (by
              simp only [Devm.stack_setMach, List.length_cons]
              omega))
      have hoffsetRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 72⟩)
          (dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
            swap 0 ::: lt ::: iszero :::
            ((.call emptyRevertSlot) <?> checkLengthWord))
          (.error (.revert,
            (base.setMach ⟨offset :: stack, memory, G⟩).withOutput [])) := by
        func_run (6) [1, 0]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        simpa only [show G + 72 - 28 = G + 44 by omega] using
          hlengthWordRun
      simpa only [validateDynamicTailAfterArg, checkLengthWord, loadLength,
          checkLength, checkPaddedEnd, accept,
          DynamicTailFailureStage.afterArgGas,
          DynamicTailFailureStage.finalStack, List.singleton_append,
          List.cons_append, List.nil_append,
          offset] using hoffsetRun
  | length =>
      change offsetNat < 2 ^ 32 ∧
        36 + offsetNat ≤ sevm.data.length ∧
        ¬ lengthNat < 2 ^ 32 at hfailure
      rcases hfailure with ⟨hoffset, hword, hlength⟩
      have hoffsetLt :
          B256.ltCheck offset (Nat.toB256 (2 ^ 32)) = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos]
        rw [B256.lt_iff_toNat_lt_toNat, hoffsetNat, hlimitNat]
        exact hoffset
      have hoffsetPlusFour :
          4 + offset = Nat.toB256 (4 + offsetNat) := by
        rw [B256.add_comm]
        simpa only [offset, offsetNat] using
          (depositOffsetWord_add_four
            (data := sevm.data) (head := head) hoffset)
      have hlengthLoad : Sevm.dataWord sevm (4 + offset) = length := by
        rw [hoffsetPlusFour]
        simpa only [length, offsetNat] using
          (dataWord_depositLengthWord (sevm := sevm) head (by omega))
      have hoffsetPlusThirtySixNat :
          (36 + offset).toNat = 36 + offsetNat := by
        rw [B256.toNat_add_eq_of_nof]
        · rw [hoffsetNat,
            show (36 : B256).toNat = 36 by decide +kernel]
        · unfold B256.Nof
          rw [hoffsetNat,
            show (36 : B256).toNat = 36 by decide +kernel]
          omega
      have hlengthWordInBounds :
          B256.ltCheck sevm.data.length.toB256 (36 + offset) = 0 := by
        simp only [B256.ltCheck]
        rw [if_neg]
        rw [B256.lt_iff_toNat_lt_toNat,
          B256.toNat_toB256_of_lt hdataBound, hoffsetPlusThirtySixNat]
        omega
      have hlengthLt :
          B256.ltCheck length (Nat.toB256 (2 ^ 32)) = 0 := by
        simp only [B256.ltCheck]
        rw [if_neg]
        rw [B256.lt_iff_toNat_lt_toNat, hlengthNat, hlimitNat]
        exact hlength
      have hlengthRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨length :: offset :: stack, memory, G + 45⟩)
          checkLength
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [checkLength]
        func_run (5) [0, 1]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        all_goals try omega
        simpa only [Devm.setMach_setMach, Devm.memory_setMach] using
          (Func.runCompiledTo_emptyRevertGuard
            (devm := base.setMach
              ⟨(1 : B256) :: length :: offset :: stack, memory,
                G + 45 - 15⟩)
            (G := G) (w := (1 : B256))
            (stack := length :: offset :: stack)
            (otherwise := checkPaddedEnd)
            hrev (by decide) rfl (by
              simp only [Devm.gasLeft_setMach, emptyRevertGuardCost,
                gVerylow, gHigh, gJumpdest, gMid, gBase]
              omega) (by
              simp only [Devm.stack_setMach, List.length_cons]
              omega))
      have hloadRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 57⟩)
          loadLength
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [loadLength]
        func_run (4) [4 + offset]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        rw [hlengthLoad]
        simpa only [show G + 57 - 12 = G + 45 by omega] using hlengthRun
      have hlengthWordRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 84⟩)
          checkLengthWord
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [checkLengthWord]
        func_run (6) [36 + offset, 0]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        simpa only [show G + 84 - 27 = G + 57 by omega] using hloadRun
      have hoffsetRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 112⟩)
          (dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
            swap 0 ::: lt ::: iszero :::
            ((.call emptyRevertSlot) <?> checkLengthWord))
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        func_run (6) [1, 0]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        simpa only [show G + 112 - 28 = G + 84 by omega] using
          hlengthWordRun
      simpa only [validateDynamicTailAfterArg, checkLengthWord, loadLength,
          checkLength, checkPaddedEnd, accept,
          DynamicTailFailureStage.afterArgGas,
          DynamicTailFailureStage.finalStack, List.singleton_append,
          List.cons_append, List.nil_append,
          offset, length] using hoffsetRun
  | paddedEnd =>
      change offsetNat < 2 ^ 32 ∧
        36 + offsetNat ≤ sevm.data.length ∧
        lengthNat < 2 ^ 32 ∧
        ¬ 36 + offsetNat + ceil32 lengthNat ≤ sevm.data.length at hfailure
      rcases hfailure with ⟨hoffset, hword, hlength, hpadded⟩
      let rounded : B256 := (~~~ (31 : B256)) &&& (31 + length)
      let paddedEnd : B256 := 36 + (offset + rounded)
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
        simpa only [offset, offsetNat] using
          (depositOffsetWord_add_four
            (data := sevm.data) (head := head) hoffset)
      have hlengthLoad : Sevm.dataWord sevm (4 + offset) = length := by
        rw [hoffsetPlusFour]
        simpa only [length, offsetNat] using
          (dataWord_depositLengthWord (sevm := sevm) head (by omega))
      have hoffsetPlusThirtySixNat :
          (36 + offset).toNat = 36 + offsetNat := by
        rw [B256.toNat_add_eq_of_nof]
        · rw [hoffsetNat,
            show (36 : B256).toNat = 36 by decide +kernel]
        · unfold B256.Nof
          rw [hoffsetNat,
            show (36 : B256).toNat = 36 by decide +kernel]
          omega
      have hlengthWordInBounds :
          B256.ltCheck sevm.data.length.toB256 (36 + offset) = 0 := by
        simp only [B256.ltCheck]
        rw [if_neg]
        rw [B256.lt_iff_toNat_lt_toNat,
          B256.toNat_toB256_of_lt hdataBound, hoffsetPlusThirtySixNat]
        omega
      have hceilUpper : ceil32 lengthNat ≤ 31 + lengthNat := by
        rw [ceil32_eq_mul, Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
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
      have hpaddedOut :
          B256.ltCheck sevm.data.length.toB256 paddedEnd = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos]
        rw [B256.lt_iff_toNat_lt_toNat,
          B256.toNat_toB256_of_lt hdataBound, hpaddedEndNat]
        omega
      have hpaddedRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨length :: offset :: stack, memory, G + 65⟩)
          checkPaddedEnd
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [checkPaddedEnd]
        func_run (12)
          [31 + length, ~~~ (31 : B256), rounded, offset + rounded,
            paddedEnd, 1]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        all_goals try omega
        simpa only [Devm.setMach_setMach, Devm.memory_setMach] using
          (Func.runCompiledTo_emptyRevertGuard
            (devm := base.setMach
              ⟨(1 : B256) :: length :: offset :: stack, memory,
                G + 65 - 35⟩)
            (G := G) (w := (1 : B256))
            (stack := length :: offset :: stack) (otherwise := accept)
            hrev (by decide) rfl (by
              simp only [Devm.gasLeft_setMach, emptyRevertGuardCost,
                gVerylow, gHigh, gJumpdest, gMid, gBase]
              omega) (by
              simp only [Devm.stack_setMach, List.length_cons]
              omega))
      have hlengthRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨length :: offset :: stack, memory, G + 93⟩)
          checkLength
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [checkLength]
        func_run (6) [1, 0]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        simpa only [show G + 93 - 28 = G + 65 by omega] using hpaddedRun
      have hloadRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 105⟩)
          loadLength
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [loadLength]
        func_run (4) [4 + offset]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        rw [hlengthLoad]
        simpa only [show G + 105 - 12 = G + 93 by omega] using hlengthRun
      have hlengthWordRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 132⟩)
          checkLengthWord
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        dsimp only [checkLengthWord]
        func_run (6) [36 + offset, 0]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        simpa only [show G + 132 - 27 = G + 105 by omega] using hloadRun
      have hoffsetRun : Func.RunCompiledTo fs sevm
          (base.setMach ⟨offset :: stack, memory, G + 160⟩)
          (dup 0 ::: pushB256 (Nat.toB256 (2 ^ 32)) :::
            swap 0 ::: lt ::: iszero :::
            ((.call emptyRevertSlot) <?> checkLengthWord))
          (.error (.revert,
            (base.setMach
              ⟨length :: offset :: stack, memory, G⟩).withOutput [])) := by
        func_run (6) [1, 0]
        all_goals try {
          simp only [Devm.stack_setMach, List.length_cons] at *
          omega }
        simpa only [show G + 160 - 28 = G + 132 by omega] using
          hlengthWordRun
      simpa only [validateDynamicTailAfterArg, checkLengthWord, loadLength,
          checkLength, checkPaddedEnd, accept,
          DynamicTailFailureStage.afterArgGas,
          DynamicTailFailureStage.finalStack, List.singleton_append,
          List.cons_append, List.nil_append,
          offset, length] using hoffsetRun

def depositDecodedTail0Memory (data : Bytes) : Mem :=
  (Mem.empty.write 96 (depositLengthWord data 0).toBytes)
    |>.write 0 (depositOffsetWord data 0).toBytes

def depositDecodedTail1Memory (data : Bytes) : Mem :=
  (depositDecodedTail0Memory data).write 128
      (depositLengthWord data 1).toBytes
    |>.write 32 (depositOffsetWord data 1).toBytes

/-- Decoder memory retained when the selected malformed row reverts. -/
def DepositAbiFailure.finalMemory
    (failure : DepositAbiFailure) (data : Bytes) : Mem :=
  match failure with
  | .head | .tail0 _ => Mem.empty
  | .tail1 _ => depositDecodedTail0Memory data
  | .tail2 _ => depositDecodedTail1Memory data

/-- Exact scratch-memory size after staging the first decoded dynamic tail. -/
theorem depositDecodedTail0Memory_size (data : Bytes) :
    (depositDecodedTail0Memory data).size = 128 := by
  unfold depositDecodedTail0Memory
  rw [Mem.size_write_word_at, Mem.size_write_word_at]
  decide +kernel

/-- Exact scratch-memory size after staging the first two decoded dynamic tails. -/
theorem depositDecodedTail1Memory_size (data : Bytes) :
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
  have hstore := Func.runCompiledTo_mstoreAt
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
  have hstore := Func.runCompiledTo_mstoreAt
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

/-- Split dynamic-tail validation into its two-instruction argument load and
the proof-facing post-load validator. -/
theorem validateDynamicTail_eq
    (head offsetWord lengthWord : B256) (body : Func) :
    validateDynamicTail head offsetWord lengthWord body =
      arg head +++
        validateDynamicTailAfterArg offsetWord lengthWord body := by
  rfl

/-- Add the two-instruction ABI-head load to a selected failing tail. -/
private theorem validateDynamicTail_failure_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256}
    {G head headNat offsetWord lengthWord : Nat} {body : Func}
    (failure : DynamicTailFailureStage)
    (hrev : fs[emptyRevertSlot]? = some Func.rev)
    (haddress : (32 * Nat.toB256 head) + 4 =
      Nat.toB256 (4 + 32 * headNat))
    (hpushCost :
      pushCost ((32 * Nat.toB256 head) + 4).toBytes.sig = 3)
    (hheadBound : 4 + 32 * headNat < 2 ^ 256)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hfailure : DynamicTailFailsAt sevm.data headNat failure)
    (hroom : stack.length < 1018) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, memory, G + failure.gas⟩)
      (validateDynamicTail (Nat.toB256 head)
        (Nat.toB256 offsetWord) (Nat.toB256 lengthWord) body)
      (.error (.revert,
        (base.setMach
          ⟨failure.finalStack sevm.data headNat ++ stack, memory, G⟩).withOutput
            [])) := by
  have hafter := validateDynamicTailAfterArg_failure_runCompiledTo
    (base := base) (memory := memory) (stack := stack) (G := G)
    (head := headNat) (offsetWord := Nat.toB256 offsetWord)
    (lengthWord := Nat.toB256 lengthWord) (body := body)
    failure hrev hdataBound hfailure hroom
  have hload :
      Sevm.dataWord sevm ((32 * Nat.toB256 head) + 4) =
        depositOffsetWord sevm.data headNat := by
    rw [haddress]
    exact dataWord_depositOffsetWord headNat hheadBound
  rw [validateDynamicTail_eq]
  unfold arg cdl
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + failure.afterArgGas + 3) hpushCost
      (by
        simp only [Devm.gasLeft_setMach]
        rw [DynamicTailFailureStage.gas_eq_afterArgGas failure]
        omega)
      (by
        simp only [Devm.stack_setMach]
        omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_calldataload
      (v := depositOffsetWord sevm.data headNat)
      (G := G + failure.afterArgGas) rfl hload
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by omega)) ?_
  simpa only [Devm.setMach_setMach, Devm.memory_setMach, prepend]
    using hafter

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

/-- A complete head falls through to the three dynamic validators in exactly
21 gas. -/
private theorem validateDepositAbi_head_success_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} {ex : Execution}
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hhead : 132 ≤ sevm.data.length)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (validateDynamicTail 0 0 3
        (validateDynamicTail 1 1 4
          (validateDynamicTail 2 2 5 body))) ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + 21⟩)
      (validateDepositAbi body) ex := by
  have hheadInBounds :
      B256.ltCheck sevm.data.length.toB256 132 = 0 := by
    simp only [B256.ltCheck]
    rw [if_neg]
    rw [B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hdataBound,
      show (132 : B256).toNat = 132 by decide +kernel]
    omega
  unfold validateDepositAbi
  func_run (4) [0]
  simpa only [Nat.add_sub_cancel] using hbody

/-- Every selected malformed-input row follows its exact compiled validator
prefix to an empty revert, with no source guard or source body entered. -/
theorem validateDepositAbi_failure_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm} {G : Nat}
    {body : Func} (failure : DepositAbiFailure)
    (hrev : fs[emptyRevertSlot]? = some Func.rev)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hfailure : failure.Holds sevm.data) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], Mem.empty, G + failure.endpointGas⟩)
      (validateDepositAbi body)
      (.error (.revert,
        (base.setMach
          ⟨failure.finalStack sevm.data,
            failure.finalMemory sevm.data, G⟩).withOutput [])) := by
  cases failure with
  | head =>
      change ¬ 132 ≤ sevm.data.length at hfailure
      have hheadOut :
          B256.ltCheck sevm.data.length.toB256 132 = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos]
        rw [B256.lt_iff_toNat_lt_toNat,
          B256.toNat_toB256_of_lt hdataBound,
          show (132 : B256).toNat = 132 by decide +kernel]
        omega
      unfold validateDepositAbi DepositAbiFailure.endpointGas
      func_run (3) [1]
      all_goals try {
        simp only [Devm.stack_setMach, List.length_cons] at *
        omega }
      all_goals try omega
      simpa only [Devm.setMach_setMach, Devm.memory_setMach,
          DepositAbiFailure.finalStack, DepositAbiFailure.finalMemory] using
        (Func.runCompiledTo_emptyRevertGuard
          (sevm := sevm)
          (devm := base.setMach ⟨[(1 : B256)], Mem.empty, G + 38 - 8⟩)
          (G := G) (w := (1 : B256)) (stack := [])
          (otherwise := validateDynamicTail 0 0 3
            (validateDynamicTail 1 1 4
              (validateDynamicTail 2 2 5 body)))
          hrev (by decide) rfl (by
            simp only [Devm.gasLeft_setMach, emptyRevertGuardCost,
              gVerylow, gHigh, gJumpdest, gMid, gBase]
            omega) (by
            simp only [Devm.stack_setMach, List.length_cons, List.length_nil]
            decide))
  | tail0 stage =>
      change 132 ≤ sevm.data.length ∧
        DynamicTailFailsAt sevm.data 0 stage at hfailure
      rcases hfailure with ⟨hhead, hstage⟩
      have htail := validateDynamicTail_failure_runCompiledTo
        (fs := fs) (sevm := sevm) (base := base)
        (memory := Mem.empty) (stack := []) (G := G)
        (head := 0) (headNat := 0) (offsetWord := 0) (lengthWord := 3)
        (body := validateDynamicTail 1 1 4
          (validateDynamicTail 2 2 5 body))
        stage hrev (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hdataBound hstage (by decide)
      have hrun := validateDepositAbi_head_success_runCompiledTo
        (base := base) hdataBound hhead htail
      have hgas : G + stage.gas + 21 =
          G + (21 + stage.gas) := by omega
      simpa only [DepositAbiFailure.endpointGas,
        DepositAbiFailure.finalStack, DepositAbiFailure.finalMemory,
        List.append_nil, hgas] using hrun
  | tail1 stage =>
      change 132 ≤ sevm.data.length ∧
        DynamicTailDecodable sevm.data 0 ∧
        DynamicTailFailsAt sevm.data 1 stage at hfailure
      rcases hfailure with ⟨hhead, hdec0, hstage⟩
      have htail1 := validateDynamicTail_failure_runCompiledTo
        (fs := fs) (sevm := sevm) (base := base)
        (memory := depositDecodedTail0Memory sevm.data) (stack := [])
        (G := G) (head := 1) (headNat := 1)
        (offsetWord := 1) (lengthWord := 4)
        (body := validateDynamicTail 2 2 5 body)
        stage hrev (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hdataBound hstage (by decide)
      have hstores := depositTail0Stores_success_runCompiledTo
        (base := base) htail1
      have htail0 := validateDynamicTail_success_runCompiledTo
        (base := base) (memory := Mem.empty) (stack := [])
        (G := G + stage.gas + 23)
        (head := 0) (headNat := 0) (offsetWord := 0) (lengthWord := 3)
        (body := validateDynamicTail 1 1 4
          (validateDynamicTail 2 2 5 body))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        hdataBound hdec0 (by decide) hstores
      have hrun := validateDepositAbi_head_success_runCompiledTo
        (base := base) hdataBound hhead htail0
      have hgas : G + stage.gas + 23 + 149 + 21 =
          G + (21 + 172 + stage.gas) := by omega
      simpa only [DepositAbiFailure.endpointGas,
        DepositAbiFailure.finalStack, DepositAbiFailure.finalMemory,
        List.append_nil, hgas] using hrun
  | tail2 stage =>
      change 132 ≤ sevm.data.length ∧
        DynamicTailDecodable sevm.data 0 ∧
        DynamicTailDecodable sevm.data 1 ∧
        DynamicTailFailsAt sevm.data 2 stage at hfailure
      rcases hfailure with ⟨hhead, hdec0, hdec1, hstage⟩
      have htail2 := validateDynamicTail_failure_runCompiledTo
        (fs := fs) (sevm := sevm) (base := base)
        (memory := depositDecodedTail1Memory sevm.data) (stack := [])
        (G := G) (head := 2) (headNat := 2)
        (offsetWord := 2) (lengthWord := 5) (body := body)
        stage hrev (by decide +kernel) (by decide +kernel)
        (by decide +kernel) hdataBound hstage (by decide)
      have htail1Stores := depositTail1Stores_success_runCompiledTo
        (base := base) htail2
      have htail1 := validateDynamicTail_success_runCompiledTo
        (base := base) (memory := depositDecodedTail0Memory sevm.data)
        (stack := []) (G := G + stage.gas + 15)
        (head := 1) (headNat := 1) (offsetWord := 1) (lengthWord := 4)
        (body := validateDynamicTail 2 2 5 body)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        hdataBound hdec1 (by decide) htail1Stores
      have htail0Stores := depositTail0Stores_success_runCompiledTo
        (base := base) htail1
      have htail0 := validateDynamicTail_success_runCompiledTo
        (base := base) (memory := Mem.empty) (stack := [])
        (G := G + stage.gas + 15 + 149 + 23)
        (head := 0) (headNat := 0) (offsetWord := 0) (lengthWord := 3)
        (body := validateDynamicTail 1 1 4
          (validateDynamicTail 2 2 5 body))
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
        hdataBound hdec0 (by decide) htail0Stores
      have hrun := validateDepositAbi_head_success_runCompiledTo
        (base := base) hdataBound hhead htail0
      have hgas : G + stage.gas + 15 + 149 + 23 + 149 + 21 =
          G + (21 + 172 + 164 + stage.gas) := by omega
      simpa only [DepositAbiFailure.endpointGas,
        DepositAbiFailure.finalStack, DepositAbiFailure.finalMemory,
        List.append_nil, hgas] using hrun

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
