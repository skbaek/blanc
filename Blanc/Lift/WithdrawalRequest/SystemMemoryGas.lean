import Blanc.Lift.WithdrawalRequest.SystemLoop
import Blanc.MemoryStageGas

/-! Actual padded allocation and expansion charges of the system queue loop. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- All eleven certified store windows, evaluated only for the bounded loop index. -/
theorem systemRecordStage_footprint_nat (i : Nat) (bound : i < 16)
    (caller pubkey packed : B256) :
    (systemRecordStage i.toB256 caller pubkey packed).footprint =
      [(76*i,32), (20+76*i,32), (52+76*i,32),
       (75+76*i,1), (74+76*i,1), (73+76*i,1), (72+76*i,1),
       (71+76*i,1), (70+76*i,1), (69+76*i,1), (68+76*i,1)] := by
  rw [systemRecordStage_footprint]
  simp only [systemRecordOffset, systemRecordPubkeyOffset, systemRecordSuffixOffset,
    systemRecordAmountOffset, B256.toNat_add, B256.toNat_mul,
    B256.toNat_toB256, Nat.lo_eq]
  change [((76*(i % 2^256)) % 2^256,32),
    ((20+(76*(i % 2^256)) % 2^256) % 2^256,32),
    ((32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256,32),
    ((7+(16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256) % 2^256,1),
    ((6+(16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256) % 2^256,1),
    ((5+(16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256) % 2^256,1),
    ((4+(16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256) % 2^256,1),
    ((3+(16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256) % 2^256,1),
    ((2+(16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256) % 2^256,1),
    ((1+(16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256) % 2^256,1),
    ((16+(32+(20+(76*(i % 2^256)) % 2^256) % 2^256) % 2^256) % 2^256,1)] = _
  rw [Nat.mod_eq_of_lt (by omega : i < 2^256)]
  rw [Nat.mod_eq_of_lt (by omega : 76*i < 2^256)]
  rw [Nat.mod_eq_of_lt (by omega : 20+76*i < 2^256)]
  rw [Nat.mod_eq_of_lt (by omega : 32+(20+76*i) < 2^256)]
  rw [Nat.mod_eq_of_lt (by omega : 16+(32+(20+76*i)) < 2^256)]
  simp only [Nat.mod_eq_of_lt (by omega : 7+(16+(32+(20+76*i))) < 2^256),
    Nat.mod_eq_of_lt (by omega : 6+(16+(32+(20+76*i))) < 2^256),
    Nat.mod_eq_of_lt (by omega : 5+(16+(32+(20+76*i))) < 2^256),
    Nat.mod_eq_of_lt (by omega : 4+(16+(32+(20+76*i))) < 2^256),
    Nat.mod_eq_of_lt (by omega : 3+(16+(32+(20+76*i))) < 2^256),
    Nat.mod_eq_of_lt (by omega : 2+(16+(32+(20+76*i))) < 2^256),
    Nat.mod_eq_of_lt (by omega : 1+(16+(32+(20+76*i))) < 2^256)]
  simp only [← Nat.add_assoc]

/-- One record reaches byte 76*i+84, even though its visible width is 76. -/
theorem systemRecordMemory_size_exact (i : Nat) (bound : i < 16)
    (caller pubkey packed : B256) (memory : Mem)
    (aligned : memory.size % 32 = 0)
    (start : memory.size ≤ ceil32 (76*i+84)) :
    (systemRecordMemory i.toB256 caller pubkey packed memory).size = ceil32 (76*i+84) := by
  rw [systemRecordMemory_size _ _ _ _ _ aligned,
    systemRecordStage_footprint_nat i bound]
  have rounded : (ceil32 (76*i+84)) % 32 = 0 := by
    rw [ceil32_eq_mul]
    omega
  have covers : 76*i+84 ≤ ceil32 (76*i+84) := by
    rw [ceil32_eq_mul]
    omega
  apply Nat.le_antisymm
  · apply MemoryStage.memExtsSize_le rounded start
    intro w member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only <;> omega
  · have member : (52+76*i,32) ∈
        [(76*i,32), (20+76*i,32), (52+76*i,32),
         (75+76*i,1), (74+76*i,1), (73+76*i,1), (72+76*i,1),
         (71+76*i,1), (70+76*i,1), (69+76*i,1), (68+76*i,1)] :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have lower := MemoryStage.memExtsSize_ge_window member (by change 0 < 32; decide) memory.size
    change ceil32 (52+76*i+32) ≤ _ at lower
    rw [show 52+76*i+32 = 76*i+84 by omega] at lower
    exact lower

private theorem word_charges (index caller pubkey packed : B256) (memory : Mem) :
    systemRecordWordCharge index caller pubkey packed memory 0 +
    systemRecordWordCharge index caller pubkey packed memory 1 +
    systemRecordWordCharge index caller pubkey packed memory 2 =
      (systemRecordWordStage index caller pubkey packed).selectedGas memory := by
  simp only [systemRecordWordCharge, systemRecordWordStage, MemoryStage.selectedGas,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, MemoryStage.applyMemory,
    List.foldl, Nat.add_zero]
  omega

private theorem amount_charges (index packed : B256) (memory : Mem) :
    systemRecordAmountCharge index packed memory 0 +
    systemRecordAmountCharge index packed memory 1 +
    systemRecordAmountCharge index packed memory 2 +
    systemRecordAmountCharge index packed memory 3 +
    systemRecordAmountCharge index packed memory 4 +
    systemRecordAmountCharge index packed memory 5 +
    systemRecordAmountCharge index packed memory 6 +
    systemRecordAmountCharge index packed memory 7 =
      (systemRecordAmountStage index packed).selectedGas memory := by
  simp only [systemRecordAmountCharge, systemRecordAmountStage, MemoryStage.selectedGas,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.take, MemoryStage.applyMemory,
    List.foldl, Nat.add_zero]
  omega

/-- The record's selected storage reads, with each actual incoming warm set. -/
def systemRecordReadGas (sevm : Sevm) (base : Devm) (head index : B256) : Nat :=
  sloadCost sevm base (systemBodyKey head index) +
  sloadCost sevm (systemBodyBase1 sevm base head index) (1+systemBodyKey head index) +
  sloadCost sevm (systemBodyBase2 sevm base head index) (2+systemBodyKey head index)

/-- All eleven actual base charges are extracted; only the net expansion remains. -/
theorem systemLoopBodyCharges_closed (sevm : Sevm) (base : Devm) (head index : B256)
    (memory : Mem) (aligned : memory.size % 32 = 0) :
    systemLoopBodyCharges sevm base head index memory =
      systemRecordReadGas sevm base head index + 33 +
      (calculateMemoryGasCost (systemBodyMemory sevm base head index memory).size -
        calculateMemoryGasCost memory.size) := by
  let words := systemRecordWordStage index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index)
  let amounts := systemRecordAmountStage index (systemBodyPacked sevm base head index)
  have wordsAligned := MemoryStage.applyMemory_aligned words memory aligned
  have wordsGas := MemoryStage.selectedGas_eq words memory aligned
  have amountsGas := MemoryStage.selectedGas_eq amounts (words.applyMemory memory) wordsAligned
  have first := calculateMemoryGasCost_mono
    (memExtsSize_ge memory.size words.footprint)
  rw [← MemoryStage.applyMemory_size words memory aligned] at first
  have second := calculateMemoryGasCost_mono
    (memExtsSize_ge (words.applyMemory memory).size amounts.footprint)
  rw [← MemoryStage.applyMemory_size amounts _ wordsAligned] at second
  have wordLength : words.length = 3 := rfl
  have amountLength : amounts.length = 8 := rfl
  rw [wordLength] at wordsGas
  rw [amountLength] at amountsGas
  simp only [systemLoopBodyCharges, systemRecordReadGas, systemBodyMemory]
  rw [show systemRecordMemory index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory =
    amounts.applyMemory (words.applyMemory memory) from MemoryStage.applyMemory_append _ _ _]
  have wordSum := word_charges index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory
  have amountSum := amount_charges index (systemBodyPacked sevm base head index)
    (words.applyMemory memory)
  change _ = words.selectedGas memory at wordSum
  change _ = amounts.selectedGas (words.applyMemory memory) at amountSum
  change _ = _ + 33 +
    (calculateMemoryGasCost (amounts.applyMemory (words.applyMemory memory)).size -
      calculateMemoryGasCost memory.size)
  change systemRecordWordCharge index _ _ _ memory 0 +
    systemRecordWordCharge index _ _ _ memory 1 +
    systemRecordWordCharge index _ _ _ memory 2 = _ at wordSum
  simp only [gVerylow] at wordsGas amountsGas
  unfold systemBodyWordMemory
  simp only [words, amounts] at *
  omega

/-- The fresh allocation after n records includes the suffix word's padding. -/
def systemAllocatedSize (n : Nat) : Nat := if n = 0 then 0 else ceil32 (76*n+8)

theorem systemAllocatedSize_aligned (n : Nat) : systemAllocatedSize n % 32 = 0 := by
  unfold systemAllocatedSize
  split
  · rfl
  · rw [ceil32_eq_mul]
    omega

theorem systemAllocatedSize_covers (n : Nat) : 76*n ≤ systemAllocatedSize n := by
  unfold systemAllocatedSize
  split
  · subst n; rfl
  · rw [ceil32_eq_mul]
    omega

theorem systemAllocatedSize_le (n : Nat) (cap : n ≤ 16) : systemAllocatedSize n ≤ 1248 := by
  unfold systemAllocatedSize
  split
  · decide
  · rw [ceil32_eq_mul]
    omega

/-- Allocation is derived from each actual record stage, without truncating its image. -/
theorem systemLoopFold_size (sevm : Sevm) (head : B256) (n index : Nat)
    (cap : index+n ≤ 16) (base : Devm) (memory : Mem)
    (size : memory.size = systemAllocatedSize index) :
    (systemLoopFold sevm head index n base memory).memory.size =
      systemAllocatedSize (index+n) := by
  induction n generalizing index base memory with
  | zero => simpa only [systemLoopFold, Nat.add_zero] using size
  | succ n ih =>
    have aligned : memory.size % 32 = 0 := by
      rw [size]; exact systemAllocatedSize_aligned index
    have start : memory.size ≤ ceil32 (76*index+84) := by
      rw [size]
      unfold systemAllocatedSize
      split
      · omega
      · rw [ceil32_eq_mul, ceil32_eq_mul]
        omega
    have step := systemRecordMemory_size_exact index (by omega)
      (systemBodyCaller sevm base head index.toB256)
      (systemBodyPubkey sevm base head index.toB256)
      (systemBodyPacked sevm base head index.toB256) memory aligned start
    have next : (systemBodyMemory sevm base head index.toB256 memory).size =
        systemAllocatedSize (index+1) := by
      change _ = systemAllocatedSize (index+1) at step
      exact step
    have suffix := ih (index+1) (by omega)
      (systemBodyBase sevm base head index.toB256)
      (systemBodyMemory sevm base head index.toB256 memory) next
    simpa only [systemLoopFold, Nat.add_assoc, Nat.add_comm 1 n] using suffix

/-- The finite ordered SLOAD schedule retains each actual incoming base. -/
def systemLoopReadSchedule (sevm : Sevm) (head : B256) (index : Nat) :
    Nat → Devm → List (Devm × B256)
  | 0, _ => []
  | n+1, base =>
    (base, systemBodyKey head index.toB256) ::
    (systemBodyBase1 sevm base head index.toB256, 1+systemBodyKey head index.toB256) ::
    (systemBodyBase2 sevm base head index.toB256, 2+systemBodyKey head index.toB256) ::
    systemLoopReadSchedule sevm head (index+1) n (systemBodyBase sevm base head index.toB256)

/-- Exact selected costs for this explicitly listed read schedule. -/
def systemLoopReadCharges (sevm : Sevm) (head : B256) (index n : Nat) (base : Devm) : List Nat :=
  (systemLoopReadSchedule sevm head index n base).map fun read => sloadCost sevm read.1 read.2

theorem systemLoopReadSchedule_length (sevm : Sevm) (head : B256) (index n : Nat) (base : Devm) :
    (systemLoopReadSchedule sevm head index n base).length = 3*n := by
  induction n generalizing index base with
  | zero => rfl
  | succ n ih =>
    simp only [systemLoopReadSchedule, List.length_cons, ih]
    omega

theorem systemLoopFold_memory_ge (sevm : Sevm) (head : B256) (index n : Nat)
    (base : Devm) (memory : Mem) (aligned : memory.size % 32 = 0) :
    memory.size ≤ (systemLoopFold sevm head index n base memory).memory.size := by
  induction n generalizing index base memory with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have nextAligned := MemoryStage.applyMemory_aligned
      (systemRecordStage index.toB256 (systemBodyCaller sevm base head index.toB256)
        (systemBodyPubkey sevm base head index.toB256) (systemBodyPacked sevm base head index.toB256))
      memory aligned
    have grows := memExtsSize_ge memory.size
      (systemRecordStage index.toB256 (systemBodyCaller sevm base head index.toB256)
        (systemBodyPubkey sevm base head index.toB256) (systemBodyPacked sevm base head index.toB256)).footprint
    rw [← systemRecordMemory_size _ _ _ _ _ aligned] at grows
    exact Nat.le_trans grows (ih (index+1) _ _ nextAligned)

/-- The whole ordered write expansion telescopes while preserving all selected reads. -/
theorem systemLoopFold_charges_closed (sevm : Sevm) (head : B256) (index n : Nat)
    (base : Devm) (memory : Mem) (aligned : memory.size % 32 = 0) :
    (systemLoopFold sevm head index n base memory).charges =
      33*n + (systemLoopReadCharges sevm head index n base).sum +
      (calculateMemoryGasCost (systemLoopFold sevm head index n base memory).memory.size -
        calculateMemoryGasCost memory.size) := by
  induction n generalizing index base memory with
  | zero => simp only [systemLoopFold, systemLoopReadCharges, systemLoopReadSchedule, List.map_nil, List.sum_nil,
      Nat.mul_zero, Nat.add_zero, Nat.sub_self]
  | succ n ih =>
    have nextAligned := MemoryStage.applyMemory_aligned
      (systemRecordStage index.toB256 (systemBodyCaller sevm base head index.toB256)
        (systemBodyPubkey sevm base head index.toB256) (systemBodyPacked sevm base head index.toB256))
      memory aligned
    have first := calculateMemoryGasCost_mono
      (systemLoopFold_memory_ge sevm head index 1 base memory aligned)
    change calculateMemoryGasCost memory.size ≤
      calculateMemoryGasCost (systemBodyMemory sevm base head index.toB256 memory).size at first
    have later := calculateMemoryGasCost_mono
      (systemLoopFold_memory_ge sevm head (index+1) n
        (systemBodyBase sevm base head index.toB256)
        (systemBodyMemory sevm base head index.toB256 memory) nextAligned)
    simp only [systemLoopFold, systemLoopReadCharges, systemLoopReadSchedule, List.map_cons, List.sum_cons]
    rw [systemLoopBodyCharges_closed _ _ _ _ _ aligned,
      ih (index+1) (systemBodyBase sevm base head index.toB256)
        (systemBodyMemory sevm base head index.toB256 memory) nextAligned]
    simp only [systemLoopReadCharges] at *
    unfold systemRecordReadGas
    omega


/-- The canonical queue loop's allocation from any zero-size memory. -/
theorem systemQueuePost_size (sevm : Sevm) (base : Devm) (memory : Mem)
    (fresh : memory.size = 0) :
    (systemQueuePost sevm base memory).memory.size =
      systemAllocatedSize (systemCount sevm base).toNat := by
  simpa only [systemQueuePost, Nat.zero_add] using
    systemLoopFold_size sevm (systemHead sevm base) (systemCount sevm base).toNat
    0 (by simpa only [Nat.zero_add] using systemCount_le sevm base)
    (systemSetupBase sevm base) memory fresh

/-- Exactly33*n base store gas, the finite selected read schedule and fresh Cmem. -/
theorem systemQueuePost_charges (sevm : Sevm) (base : Devm) (memory : Mem)
    (fresh : memory.size = 0) :
    (systemQueuePost sevm base memory).charges =
      33*(systemCount sevm base).toNat +
      (systemLoopReadCharges sevm (systemHead sevm base) 0 (systemCount sevm base).toNat
        (systemSetupBase sevm base)).sum +
      calculateMemoryGasCost (systemAllocatedSize (systemCount sevm base).toNat) := by
  have charges := systemLoopFold_charges_closed sevm (systemHead sevm base) 0
    (systemCount sevm base).toNat (systemSetupBase sevm base) memory (by rw [fresh])
  change (systemQueuePost sevm base memory).charges = _ at charges
  change _ = _ + _ + (calculateMemoryGasCost (systemQueuePost sevm base memory).memory.size -
    calculateMemoryGasCost memory.size) at charges
  rw [systemQueuePost_size sevm base memory fresh, fresh] at charges
  simpa only [show calculateMemoryGasCost 0 = 0 by rfl, Nat.sub_zero] using charges

end Blanc.Lift.WithdrawalRequest
