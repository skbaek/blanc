import Blanc.Lift.WithdrawalRequest.SystemLoop
import Blanc.Lift.WithdrawalRequest.SystemImage

/-! Conditional FIFO output correspondence of the actual system queue loop. -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune
open Blanc.WithdrawalRequest

theorem systemHead_represented (sevm : Sevm) (base : Devm) (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    systemHead sevm base = state.head.toB256 := rep.head

theorem systemTail_represented (sevm : Sevm) (base : Devm) (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    systemTail sevm base = state.tail.toB256 := rep.tail

theorem systemDifference_represented (sevm : Sevm) (base : Devm)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    (systemDifference sevm base).toNat = state.queue.length := by
  have headNat := B256.toNat_toB256_of_lt rep.bounds.head_lt
  have tailNat := B256.toNat_toB256_of_lt rep.bounds.tail_lt
  have coherent := rep.coherent
  change state.head + state.queue.length = state.tail at coherent
  rw [systemDifference, systemTail_represented sevm base state rep,
    systemHead_represented sevm base state rep,
    B256.toNat_sub_eq_of_le _ _ (by
      rw [B256.le_iff_toNat_le_toNat, headNat, tailNat]
      omega), tailNat, headNat]
  omega

theorem systemCount_represented (sevm : Sevm) (base : Devm)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state) :
    (systemCount sevm base).toNat = min 16 state.queue.length := by
  rw [systemCount_toNat, systemDifference_represented sevm base state rep]

/-- All setup and body loads preserve storage at every address. -/
theorem systemSetupBase_storage (sevm : Sevm) (base : Devm) (address : Adr) :
    (systemSetupBase sevm base).getStor address = base.getStor address := by
  simp only [systemSetupBase, afterSload_getStor]

theorem systemBodyBase_storage (sevm : Sevm) (base : Devm) (head index : B256)
    (address : Adr) :
    (systemBodyBase sevm base head index).getStor address = base.getStor address := by
  simp only [systemBodyBase, systemBodyBase2, systemBodyBase1, afterSload_getStor]

/-- Queue reads use the same modulo-word key as Layout; no slot bound is needed. -/
theorem systemBodyKey_queueSlot (head index offset : Nat) :
    offset.toB256 + systemBodyKey head.toB256 index.toB256 =
      queueSlot (head + index) offset := by
  apply B256.toNat_inj
  simp only [systemBodyKey, queueSlot, queueBase, B256.toNat_add,
    B256.toNat_mul, B256.toNat_toB256, Nat.lo_eq]
  change (offset % 2 ^ 256 + (4 + (3 * ((index % 2 ^ 256 + head % 2 ^ 256) %
    2 ^ 256)) % 2 ^ 256) % 2 ^ 256) % 2 ^ 256 =
    (4 + 3 * (head + index) + offset) % 2 ^ 256
  omega

theorem systemBody_words_represented (sevm : Sevm) (base : Devm)
    (state : WithdrawalRequest.State)
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (i : Nat) (hi : i < state.queue.length) :
    systemBodyCaller sevm base state.head.toB256 i.toB256 = callerWord state.queue[i] ∧
    systemBodyPubkey sevm base state.head.toB256 i.toB256 = pubkeyWord state.queue[i] ∧
    systemBodyPacked sevm base state.head.toB256 i.toB256 = pubkeyAmountWord state.queue[i] := by
  have key0 := systemBodyKey_queueSlot state.head i 0
  rw [show (0 : Nat).toB256 = 0 by rfl, B256.add_comm, B256.add_zero] at key0
  have key1 := systemBodyKey_queueSlot state.head i 1
  have key2 := systemBodyKey_queueSlot state.head i 2
  change (1 : B256) + _ = _ at key1
  change (2 : B256) + _ = _ at key2
  simp only [systemBodyCaller, systemBodyPubkey, systemBodyPacked,
    systemBodyBase1, systemBodyBase2, getStorVal_afterSload]
  rw [key1, key2, key0]
  exact rep.live i hi

theorem systemLoopFold_storage (sevm : Sevm) (head : B256) (index remaining : Nat)
    (base : Devm) (memory : Mem) (address : Adr) :
    (systemLoopFold sevm head index remaining base memory).base.getStor address =
      base.getStor address := by
  induction remaining generalizing index base memory with
  | zero => rfl
  | succ remaining ih =>
    simp only [systemLoopFold]
    rw [ih, systemBodyBase_storage]

/-- The actual fold preserves the full padded image while extending its visible FIFO prefix. -/
theorem systemLoopFold_image (sevm : Sevm) (state : WithdrawalRequest.State)
    (remaining : Nat) {index : Nat} {base : Devm} {memory : Mem} {image : Bytes}
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (wf : Mem.Wf memory) (reads : Mem.Reads memory image)
    (bound : index + remaining ≤ min 16 state.queue.length)
    (hPrefix : image.sliceD 0 (76 * index) 0 = outputRecords (state.queue.take index)) :
    ∃ finalImage : Bytes,
      Mem.Wf (systemLoopFold sevm state.head.toB256 index remaining base memory).memory ∧
      Mem.Reads (systemLoopFold sevm state.head.toB256 index remaining base memory).memory
        finalImage ∧
      finalImage.sliceD 0 (76 * (index + remaining)) 0 =
        outputRecords (state.queue.take (index + remaining)) := by
  induction remaining generalizing index base memory image with
  | zero =>
    exact ⟨image, wf, reads, hPrefix⟩
  | succ remaining ih =>
    have cap := Nat.min_le_left 16 state.queue.length
    have queueBound := Nat.min_le_right 16 state.queue.length
    have hi : index < state.queue.length := by omega
    have indexCap : index < 16 := by omega
    obtain ⟨caller, pubkey, packed⟩ := systemBody_words_represented sevm base state rep index hi
    let nextImage := systemRecordImage index.toB256 (callerWord state.queue[index])
      (pubkeyWord state.queue[index]) (pubkeyAmountWord state.queue[index]) image
    have nextMemory : Mem.Wf (systemBodyMemory sevm base state.head.toB256 index.toB256 memory) ∧
        Mem.Reads (systemBodyMemory sevm base state.head.toB256 index.toB256 memory) nextImage := by
      simpa only [systemBodyMemory, caller, pubkey, packed, nextImage] using
        systemRecordMemory_image index.toB256 (callerWord state.queue[index])
          (pubkeyWord state.queue[index]) (pubkeyAmountWord state.queue[index]) wf reads
    have nextPrefix : nextImage.sliceD 0 (76 * (index + 1)) 0 =
        outputRecords (state.queue.take (index + 1)) := by
      dsimp only [nextImage]
      rw [systemRecordImage_prefix_extend index indexCap, hPrefix,
        List.take_succ_eq_append_getElem hi, outputRecords_append,
        outputRecords, outputRecords, List.append_nil]
    have nextRep : RepresentsStorage
        ((systemBodyBase sevm base state.head.toB256 index.toB256).getStorVal sevm.currentTarget)
        state := by
      have storage : (systemBodyBase sevm base state.head.toB256 index.toB256).getStorVal
          sevm.currentTarget = base.getStorVal sevm.currentTarget := by
        funext key
        change ((systemBodyBase sevm base state.head.toB256 index.toB256).getStor
          sevm.currentTarget).get key = (base.getStor sevm.currentTarget).get key
        rw [systemBodyBase_storage]
      rw [storage]
      exact rep
    obtain ⟨finalImage, finalWf, finalReads, finalPrefix⟩ :=
      ih nextRep nextMemory.1 nextMemory.2 (by omega) nextPrefix
    refine ⟨finalImage, finalWf, finalReads, ?_⟩
    rw [show index + (remaining + 1) = index + 1 + remaining by omega]
    exact finalPrefix

theorem systemQueuePost_storage (sevm : Sevm) (base : Devm) (memory : Mem) (address : Adr) :
    (systemQueuePost sevm base memory).base.getStor address = base.getStor address := by
  rw [systemQueuePost, systemLoopFold_storage, systemSetupBase_storage]

/-- Conditional representation-to-image correspondence, with arbitrary incoming image. -/
theorem systemQueuePost_image (sevm : Sevm) (base : Devm) (state : WithdrawalRequest.State)
    {memory : Mem} {image : Bytes}
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (wf : Mem.Wf memory) (reads : Mem.Reads memory image) :
    ∃ finalImage : Bytes,
      Mem.Wf (systemQueuePost sevm base memory).memory ∧
      Mem.Reads (systemQueuePost sevm base memory).memory finalImage ∧
      finalImage.sliceD 0 (76 * min 16 state.queue.length) 0 = systemOutput state := by
  have setupRep : RepresentsStorage
      ((systemSetupBase sevm base).getStorVal sevm.currentTarget) state := by
    have storage : (systemSetupBase sevm base).getStorVal sevm.currentTarget =
        base.getStorVal sevm.currentTarget := by
      funext key
      change ((systemSetupBase sevm base).getStor sevm.currentTarget).get key =
        (base.getStor sevm.currentTarget).get key
      rw [systemSetupBase_storage]
    rw [storage]
    exact rep
  obtain ⟨finalImage, finalWf, finalReads, finalPrefix⟩ :=
    systemLoopFold_image sevm state (min 16 state.queue.length) (index := 0)
      setupRep wf reads (by omega) (by rfl)
  have takeEq : state.queue.take (min 16 state.queue.length) = state.queue.take 16 := by
    rw [← List.take_take, List.take_length]
  refine ⟨finalImage, ?_, ?_, ?_⟩
  · simpa only [systemQueuePost, systemHead_represented sevm base state rep,
      systemCount_represented sevm base state rep] using finalWf
  · simpa only [systemQueuePost, systemHead_represented sevm base state rep,
      systemCount_represented sevm base state rep] using finalReads
  · simpa only [Nat.zero_add, takeEq, systemOutput, emitted, maxPerBlock] using finalPrefix

/-- The actual queue-loop memory read returns Layout's ordered emitted records. -/
theorem systemQueuePost_read (sevm : Sevm) (base : Devm) (state : WithdrawalRequest.State)
    {memory : Mem} {image : Bytes}
    (rep : RepresentsStorage (base.getStorVal sevm.currentTarget) state)
    (wf : Mem.Wf memory) (reads : Mem.Reads memory image) :
    ((systemQueuePost sevm base memory).memory.read 0 (76 * min 16 state.queue.length)).1 =
      systemOutput state := by
  obtain ⟨_, _, finalReads, finalPrefix⟩ := systemQueuePost_image sevm base state rep wf reads
  rw [finalReads.read]
  exact finalPrefix

end Blanc.Lift.WithdrawalRequest
