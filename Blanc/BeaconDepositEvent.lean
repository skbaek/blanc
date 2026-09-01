import Blanc.BeaconDepositEventMemory
import Blanc.BytesWrite
import Blanc.ForwardLog

/-!
# Beacon deposit event compiled carrier

The successful deposit path copies its three validated calldata payloads before
overwriting the decoder words, writes the five-tail ABI event image, reads the
old deposit count, and emits the exact `DepositEvent` log.  This module keeps
the state-dependent storage charge explicit and leaves the following deposit
walk outcome-polymorphic.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Event staging after the three validated dynamic payload copies and before
the fixed ABI headers are written. -/
def eventPayloadMemory (data : Bytes) (amount : B256) : Mem :=
  let M0 := depositEventInputMemory data amount
  let M1 := M0.write 224 (0 : B256).toBytes
  let M2 := M1.write 192 (depositEventPubkeySlice data)
  let M3 := M2.write 288 (depositEventWithdrawalSlice data)
  M3.write 416 (depositEventSignatureSlice data)

/-- Event staging after the fixed ABI headers and amount encoding, immediately
before the old deposit count is loaded. -/
def eventBeforeCountMemory (data : Bytes) (amount : B256) : Mem :=
  let M4 := eventPayloadMemory data amount
  let M5 := M4.write 0 (160 : B256).toBytes
  let M6 := M5.write 32 (256 : B256).toBytes
  let M7 := M6.write 64 (320 : B256).toBytes
  let M8 := M7.write 96 (384 : B256).toBytes
  let M9 := M8.write 128 (512 : B256).toBytes
  let M10 := M9.write 160 (48 : B256).toBytes
  let M11 := M10.write 256 (32 : B256).toBytes
  let M12 := M11.write 320 (8 : B256).toBytes
  let M13 := M12.write 352 (0 : B256).toBytes
  let M14 := storeLe64Memory M13 352 amount
  let M15 := M14.write 384 (96 : B256).toBytes
  let M16 := M15.write 512 (8 : B256).toBytes
  M16.write 544 (0 : B256).toBytes

/-- Normalize the public event image as the pre-count image followed by the
old-count word and its little-endian encoding. -/
theorem eventMemory_eq
    (data : Bytes) (amount oldCount : B256) :
    depositEventMemory data amount oldCount =
      storeLe64Memory
        ((eventBeforeCountMemory data amount).write
          576 oldCount.toBytes)
        544 oldCount := by
  rfl

structure EventOffsetMemoryCarrier
    (memory : Mem) (data : Bytes) (amount : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 704
  image_length : image.length = 704
  offset0_read : image.sliceD 0 32 0 =
    (depositOffsetWord data 0).toBytes
  offset1_read : image.sliceD 32 32 0 =
    (depositOffsetWord data 1).toBytes
  offset2_read : image.sliceD 64 32 0 =
    (depositOffsetWord data 2).toBytes
  amount_read : image.sliceD 672 32 0 = amount.toBytes

def EventOffsetMemoryCarrier.input
    (data : Bytes) (amount : B256) :
    EventOffsetMemoryCarrier
      (depositEventInputMemory data amount) data amount := by
  let h := depositEventInputMemory_carrier data amount
  exact ⟨h.image, h.wf, h.reads, h.size_eq, h.image_length,
    h.offset0_read, h.offset1_read, h.offset2_read, h.amount_read⟩

def EventOffsetMemoryCarrier.writeAfter
    {memory : Mem} {data : Bytes} {amount : B256}
    (h : EventOffsetMemoryCarrier memory data amount)
    (n : Nat) (xs : Bytes) (hstart : 96 ≤ n)
    (hbeforeAmount : n + xs.length ≤ 672)
    (hfit : n + xs.length ≤ 704) :
    EventOffsetMemoryCarrier (memory.write n xs) data amount := by
  have hsize : (memory.write n xs).size = 704 := by
    rw [Mem.size_write_of_le (by rw [h.size_eq]; exact hfit), h.size_eq]
  have hlen : (Bytes.writeAt h.image n xs).length = 704 := by
    simp only [Bytes.writeAt, List.length_append, List.takeD_length,
      List.length_drop, h.image_length]
    omega
  refine ⟨Bytes.writeAt h.image n xs, h.wf.write _ _,
    Mem.Reads.write h.wf h.reads _ _, hsize, hlen, ?_, ?_, ?_, ?_⟩
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.offset0_read
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.offset1_read
  · rw [Bytes.sliceD_writeAt_before _ _ _ _ _ (by omega)]
    exact h.offset2_read
  · rw [Bytes.sliceD_writeAt_after _ _ _ _ _
      hbeforeAmount]
    exact h.amount_read

structure EventAmountMemoryCarrier
    (memory : Mem) (amount : B256) : Type where
  image : Bytes
  wf : Mem.Wf memory
  reads : Mem.Reads memory image
  size_eq : memory.size = 704
  image_length : image.length = 704
  amount_read : image.sliceD 672 32 0 = amount.toBytes

def EventAmountMemoryCarrier.ofOffsets
    {memory : Mem} {data : Bytes} {amount : B256}
    (h : EventOffsetMemoryCarrier memory data amount) :
    EventAmountMemoryCarrier memory amount :=
  ⟨h.image, h.wf, h.reads, h.size_eq, h.image_length, h.amount_read⟩

def EventAmountMemoryCarrier.writeBefore
    {memory : Mem} {amount : B256}
    (h : EventAmountMemoryCarrier memory amount)
    (n : Nat) (xs : Bytes) (hbeforeAmount : n + xs.length ≤ 672)
    (hfit : n + xs.length ≤ 704) :
    EventAmountMemoryCarrier (memory.write n xs) amount := by
  have hsize : (memory.write n xs).size = 704 := by
    rw [Mem.size_write_of_le (by rw [h.size_eq]; exact hfit), h.size_eq]
  have hlen : (Bytes.writeAt h.image n xs).length = 704 := by
    simp only [Bytes.writeAt, List.length_append, List.takeD_length,
      List.length_drop, h.image_length]
    omega
  refine ⟨Bytes.writeAt h.image n xs, h.wf.write _ _,
    Mem.Reads.write h.wf h.reads _ _, hsize, hlen, ?_⟩
  rw [Bytes.sliceD_writeAt_after _ _ _ _ _ hbeforeAmount]
  exact h.amount_read

def EventAmountMemoryCarrier.writeWordBefore
    {memory : Mem} {amount : B256}
    (h : EventAmountMemoryCarrier memory amount)
    (n : Nat) (word : B256) (hbeforeAmount : n + 32 ≤ 672)
    (hfit : n + 32 ≤ 704) :
    EventAmountMemoryCarrier (memory.write n word.toBytes) amount :=
  h.writeBefore n word.toBytes
    (by simpa only [B256.length_toBytes] using hbeforeAmount)
    (by simpa only [B256.length_toBytes] using hfit)

def EventAmountMemoryCarrier.storeLe64Before
    {memory : Mem} {amount word : B256}
    (h : EventAmountMemoryCarrier memory amount)
    (base : Nat) (hbeforeAmount : base + 8 ≤ 672)
    (hfit : base + 8 ≤ 704) :
    EventAmountMemoryCarrier (storeLe64Memory memory base word) amount := by
  have hinv := storeLe64Memory_inv
    (base := base) (word := word) h.wf h.reads
  have hsize : (storeLe64Memory memory base word).size = 704 := by
    rw [storeLe64Memory_size_of_le (by rw [h.size_eq]; exact hfit),
      h.size_eq]
  have hlen : (storeLe64Image h.image base word).length = 704 := by
    rw [storeLe64Image_eq_le64]
    have hle : (le64 word.toNat).length = 8 := rfl
    simp only [Bytes.writeAt, List.length_append, List.takeD_length,
      List.length_drop, h.image_length, hle]
    omega
  refine ⟨storeLe64Image h.image base word, hinv.1, hinv.2,
    hsize, hlen, ?_⟩
  rw [storeLe64Image_eq_le64,
    Bytes.sliceD_writeAt_after _ _ _ _ _ (by
      simp only [le64, List.length_cons, List.length_nil]
      exact hbeforeAmount)]
  exact h.amount_read

def eventPayloadMemory_carrier
    (data : Bytes) (amount : B256) :
    EventAmountMemoryCarrier (eventPayloadMemory data amount) amount := by
  let M0 := depositEventInputMemory data amount
  let M1 := M0.write 224 (0 : B256).toBytes
  let M2 := M1.write 192 (depositEventPubkeySlice data)
  let M3 := M2.write 288 (depositEventWithdrawalSlice data)
  let M4 := M3.write 416 (depositEventSignatureSlice data)
  let c0 := EventOffsetMemoryCarrier.input data amount
  have c1 : EventOffsetMemoryCarrier M1 data amount := by
    dsimp only [M1, M0]
    exact c0.writeAfter 224 (0 : B256).toBytes (by omega) (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c2 : EventOffsetMemoryCarrier M2 data amount := by
    dsimp only [M2]
    exact c1.writeAfter 192 (depositEventPubkeySlice data) (by omega) (by
      simp only [depositEventPubkeySlice, List.length_sliceD]
      omega) (by
      simp only [depositEventPubkeySlice, List.length_sliceD]
      omega)
  have c3 : EventOffsetMemoryCarrier M3 data amount := by
    dsimp only [M3]
    exact c2.writeAfter 288 (depositEventWithdrawalSlice data) (by omega) (by
      simp only [depositEventWithdrawalSlice, List.length_sliceD]
      omega) (by
      simp only [depositEventWithdrawalSlice, List.length_sliceD]
      omega)
  have c4 : EventOffsetMemoryCarrier M4 data amount := by
    dsimp only [M4]
    exact c3.writeAfter 416 (depositEventSignatureSlice data) (by omega) (by
      simp only [depositEventSignatureSlice, List.length_sliceD]
      omega) (by
      simp only [depositEventSignatureSlice, List.length_sliceD]
      omega)
  simpa only [eventPayloadMemory, M4, M3, M2, M1, M0] using
    EventAmountMemoryCarrier.ofOffsets c4

def eventBeforeCountMemory_carrier
    (data : Bytes) (amount : B256) :
    EventAmountMemoryCarrier (eventBeforeCountMemory data amount) amount := by
  let c4 := eventPayloadMemory_carrier data amount
  let c5 := c4.writeWordBefore 0 160 (by omega) (by omega)
  let c6 := c5.writeWordBefore 32 256 (by omega) (by omega)
  let c7 := c6.writeWordBefore 64 320 (by omega) (by omega)
  let c8 := c7.writeWordBefore 96 384 (by omega) (by omega)
  let c9 := c8.writeWordBefore 128 512 (by omega) (by omega)
  let c10 := c9.writeWordBefore 160 48 (by omega) (by omega)
  let c11 := c10.writeWordBefore 256 32 (by omega) (by omega)
  let c12 := c11.writeWordBefore 320 8 (by omega) (by omega)
  let c13 := c12.writeWordBefore 352 0 (by omega) (by omega)
  let c14 := c13.storeLe64Before (word := amount) 352 (by omega) (by omega)
  let c15 := c14.writeWordBefore 384 96 (by omega) (by omega)
  let c16 := c15.writeWordBefore 512 8 (by omega) (by omega)
  let c17 := c16.writeWordBefore 544 0 (by omega) (by omega)
  simpa only [eventBeforeCountMemory, c17, c16, c15, c14, c13, c12,
    c11, c10, c9, c8, c7, c6, c5, c4,
    EventAmountMemoryCarrier.writeWordBefore,
    EventAmountMemoryCarrier.writeBefore] using c17

private theorem pushMstoreAt_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256} {value word : B256}
    {offset G valueGas wordGas : Nat} {body : Func} {ex : Execution}
    (hvalueCost : pushCost value.toBytes.sig = valueGas)
    (hwordCost : pushCost (word * 32).toBytes.sig = wordGas)
    (hoffset : (word * 32).toNat = offset)
    (hsize32 : memory.size % 32 = 0)
    (hfit : offset + 32 ≤ memory.size)
    (hroom : stack.length < 1023)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory.write offset value.toBytes, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory, G + valueGas + wordGas + gVerylow⟩)
      (([pushB256 value] ++ mstoreAt word) +++ body) ex := by
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + wordGas + gVerylow) hvalueCost
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.runCompiledTo_mstoreAt
      (pushGas := wordGas) (extGas := 0) hwordCost hroom
  · intro S G'
    apply Devm.extCost_zero_of_le hsize32
    simpa only [hoffset] using hfit
  · simpa only [hoffset, prepend] using hbody

private theorem loadAmountStoreLe64_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256} {amount : B256}
    {G : Nat} {body : Func} {ex : Execution}
    (hsize32 : memory.size % 32 = 0)
    (hreadFit : 672 + 32 ≤ memory.size)
    (hread : Bytes.toB256 (memory.read 672 32).1 = amount)
    (hreadMemory : (memory.read 672 32).2 = memory)
    (hroom : stack.length < 1022)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, storeLe64Memory memory 352 amount, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach ⟨stack, memory, G + 117⟩)
      (loadWord amountWord +++ storeLe64At 352 +++ body) ex := by
  have hamountAddress : (amountWord * 32 : B256).toNat = 672 := by
    decide +kernel
  unfold loadWord
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := amountWord * 32) (c := 3) (G := G + 114)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := amountWord * 32) (v := amount) (s := stack)
      (c := gVerylow) (G := G + 111) (M := memory)
      rfl ?_
      (by simpa only [Devm.memory_setMach, hamountAddress] using hread)
      (by simpa only [Devm.memory_setMach, hamountAddress] using hreadMemory)
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by omega)) ?_
  · have hext :
        (base.setMach
          ⟨amountWord * 32 :: stack, memory, G + 114⟩).extCost
            [⟨(amountWord * 32).toNat, 32⟩] = 0 := by
      apply Devm.extCost_zero_of_le hsize32
      simpa only [hamountAddress] using hreadFit
    rw [hext]
    decide
  simp only [Devm.setMach_setMach]
  apply storeLe64At_runCompiledTo
      (memory := memory) (word := amount) (address := 352)
      (offset := 352) (G := G) (stack := stack)
  · exact hsize32
  · omega
  · omega
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · simpa only [prepend] using hbody

private theorem copyDynamicPayload_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {stack : List B256}
    {offset offsetWord delta destination size : B256}
    {payload : Bytes} {G sizeGas offsetGas deltaGas destinationGas copyGas : Nat}
    {body : Func} {ex : Execution}
    (hsizeCost : pushCost size.toBytes.sig = sizeGas)
    (hoffsetCost : pushCost (offsetWord * 32).toBytes.sig = offsetGas)
    (hdeltaCost : pushCost (36 + delta).toBytes.sig = deltaGas)
    (hdestinationCost : pushCost destination.toBytes.sig = destinationGas)
    (hcopyCost : gVerylow + gasCopy * ceilDiv size.toNat 32 = copyGas)
    (hsize32 : memory.size % 32 = 0)
    (hreadFit : (offsetWord * 32).toNat + 32 ≤ memory.size)
    (hcopyFit : destination.toNat + size.toNat ≤ memory.size)
    (hread : Bytes.toB256
      (memory.read (offsetWord * 32).toNat 32).1 = offset)
    (hreadMemory : (memory.read (offsetWord * 32).toNat 32).2 = memory)
    (hpayload : sevm.data.sliceD
      ((36 + delta) + offset).toNat size.toNat 0 = payload)
    (hroom : stack.length < 1022)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory.write destination.toNat payload, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨stack, memory,
          G + sizeGas + offsetGas + gVerylow + deltaGas + gVerylow +
            destinationGas + copyGas⟩)
      (copyDynamicPayload offsetWord delta destination size +++ body) ex := by
  unfold copyDynamicPayload loadWord
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + offsetGas + gVerylow + deltaGas + gVerylow +
        destinationGas + copyGas)
      hsizeCost
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + gVerylow + deltaGas + gVerylow + destinationGas + copyGas)
      hoffsetCost
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_mload_of
      (i := offsetWord * 32) (v := offset)
      (s := size :: stack) (c := gVerylow)
      (G := G + deltaGas + gVerylow + destinationGas + copyGas)
      (M := memory) rfl ?_ hread hreadMemory
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [List.length_cons]; omega)) ?_
  · have hext :
        (base.setMach
          ⟨offsetWord * 32 :: size :: stack, memory,
            G + gVerylow + deltaGas + gVerylow + destinationGas +
              copyGas⟩).extCost
            [⟨(offsetWord * 32).toNat, 32⟩] = 0 := by
      exact Devm.extCost_zero_of_le hsize32 hreadFit
    rw [hext]
    decide
  simp only [Devm.setMach_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + gVerylow + destinationGas + copyGas)
      hdeltaCost
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_binary
      (r := .add) (f := (· + ·)) (cost := gVerylow)
      (x := 36 + delta) (y := offset)
      (v := (36 + delta) + offset) (s := size :: stack)
      (G := G + destinationGas + copyGas)
      (by rintro ⟨⟩) rfl rfl rfl
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (G := G + copyGas) hdestinationCost
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach, List.length_cons]; omega)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.runCompiledTo_calldatacopy_step
      (M := memory) (c := copyGas) rfl rfl ?_ ?_ ?_
  · have hext :
        (base.setMach
          ⟨destination :: ((36 + delta) + offset) :: size :: stack,
            memory, G + copyGas⟩).extCost
            [⟨destination.toNat, size.toNat⟩] = 0 := by
      exact Devm.extCost_zero_of_le hsize32 hcopyFit
    rw [hext, hcopyCost]
    omega
  · simp only [Devm.gasLeft_setMach]
    omega
  · intro memory' G' hmemory hgas
    simp only [Devm.gasLeft_setMach, hpayload] at hmemory hgas
    subst memory'
    have hG' : G' = G := by omega
    subst G'
    simpa only [Devm.setMach_setMach, prepend] using hbody

private theorem stageEventPayloads_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {amount : B256} {G : Nat} {body : Func} {ex : Execution}
    (hdec0 : DynamicTailDecodable sevm.data 0)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], eventPayloadMemory sevm.data amount, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], depositEventInputMemory sevm.data amount, G + 88⟩)
      (([pushB256 0] ++ mstoreAt 7 ++
        copyDynamicPayload 0 0 192 48 ++
        copyDynamicPayload 1 0 288 32 ++
        copyDynamicPayload 2 0 416 96) +++ body) ex := by
  simp only [DynamicTailDecodable] at hdec0 hdec1 hdec2
  let M0 := depositEventInputMemory sevm.data amount
  let M1 := M0.write 224 (0 : B256).toBytes
  let M2 := M1.write 192 (depositEventPubkeySlice sevm.data)
  let M3 := M2.write 288 (depositEventWithdrawalSlice sevm.data)
  let M4 := M3.write 416 (depositEventSignatureSlice sevm.data)
  let c0 := EventOffsetMemoryCarrier.input sevm.data amount
  have c1 : EventOffsetMemoryCarrier M1 sevm.data amount := by
    dsimp only [M1, M0]
    exact c0.writeAfter 224 (0 : B256).toBytes (by omega) (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c2 : EventOffsetMemoryCarrier M2 sevm.data amount := by
    dsimp only [M2]
    exact c1.writeAfter 192 (depositEventPubkeySlice sevm.data)
      (by omega) (by
        simp only [depositEventPubkeySlice, List.length_sliceD]
        omega) (by
        simp only [depositEventPubkeySlice, List.length_sliceD]
        omega)
  have c3 : EventOffsetMemoryCarrier M3 sevm.data amount := by
    dsimp only [M3]
    exact c2.writeAfter 288 (depositEventWithdrawalSlice sevm.data)
      (by omega) (by
        simp only [depositEventWithdrawalSlice, List.length_sliceD]
        omega) (by
        simp only [depositEventWithdrawalSlice, List.length_sliceD]
        omega)
  have c4 : EventOffsetMemoryCarrier M4 sevm.data amount := by
    dsimp only [M4]
    exact c3.writeAfter 416 (depositEventSignatureSlice sevm.data)
      (by omega) (by
        simp only [depositEventSignatureSlice, List.length_sliceD]
        omega) (by
        simp only [depositEventSignatureSlice, List.length_sliceD]
        omega)
  have hread0 : Bytes.toB256 (M1.read 0 32).1 =
      depositOffsetWord sevm.data 0 := by
    rw [Mem.Reads.read c1.reads, c1.offset0_read,
      B256.toB256_toBytes]
  have hread1 : Bytes.toB256 (M2.read 32 32).1 =
      depositOffsetWord sevm.data 1 := by
    rw [Mem.Reads.read c2.reads, c2.offset1_read,
      B256.toB256_toBytes]
  have hread2 : Bytes.toB256 (M3.read 64 32).1 =
      depositOffsetWord sevm.data 2 := by
    rw [Mem.Reads.read c3.reads, c3.offset2_read,
      B256.toB256_toBytes]
  have hreadMemory0 : (M1.read 0 32).2 = M1 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [c1.size_eq]
    · rw [c1.size_eq]
      omega
  have hreadMemory1 : (M2.read 32 32).2 = M2 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [c2.size_eq]
    · rw [c2.size_eq]
      omega
  have hreadMemory2 : (M3.read 64 32).2 = M3 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [c3.size_eq]
    · rw [c3.size_eq]
      omega
  have hsource0 :
      ((36 : B256) + depositOffsetWord sevm.data 0).toNat =
        36 + dynamicOffset sevm.data 0 := by
    rw [B256.toNat_add_eq_of_nof]
    · rw [depositOffsetWord_toNat (by omega),
        show (36 : B256).toNat = 36 by decide +kernel]
    · unfold B256.Nof
      rw [depositOffsetWord_toNat (by omega),
        show (36 : B256).toNat = 36 by decide +kernel]
      omega
  have hsource1 :
      ((36 : B256) + depositOffsetWord sevm.data 1).toNat =
        36 + dynamicOffset sevm.data 1 := by
    rw [B256.toNat_add_eq_of_nof]
    · rw [depositOffsetWord_toNat (by omega),
        show (36 : B256).toNat = 36 by decide +kernel]
    · unfold B256.Nof
      rw [depositOffsetWord_toNat (by omega),
        show (36 : B256).toNat = 36 by decide +kernel]
      omega
  have hsource2 :
      ((36 : B256) + depositOffsetWord sevm.data 2).toNat =
        36 + dynamicOffset sevm.data 2 := by
    rw [B256.toNat_add_eq_of_nof]
    · rw [depositOffsetWord_toNat (by omega),
        show (36 : B256).toNat = 36 by decide +kernel]
    · unfold B256.Nof
      rw [depositOffsetWord_toNat (by omega),
        show (36 : B256).toNat = 36 by decide +kernel]
      omega
  have htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], M4, G⟩) body ex := by
    simpa only [eventPayloadMemory, M4, M3, M2, M1, M0] using hbody
  apply pushMstoreAt_runCompiledTo
      (valueGas := 2) (wordGas := 3)
      (memory := M0) (value := 0) (word := 7) (offset := 224)
      (G := G + 80)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c0.size_eq]
  · rw [c0.size_eq]
    decide +kernel
  · decide
  apply copyDynamicPayload_runCompiledTo
      (memory := M1) (offset := depositOffsetWord sevm.data 0)
      (offsetWord := 0) (delta := 0) (destination := 192) (size := 48)
      (payload := depositEventPubkeySlice sevm.data)
      (sizeGas := 3) (offsetGas := 2) (deltaGas := 3)
      (destinationGas := 3) (copyGas := 9) (G := G + 54)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c1.size_eq]
  · rw [c1.size_eq]
    decide +kernel
  · rw [c1.size_eq]
    decide +kernel
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide +kernel] using
      hread0
  · simpa only [show ((0 : B256) * 32).toNat = 0 by decide +kernel] using
      hreadMemory0
  · rw [show (36 + (0 : B256)) = 36 by decide +kernel,
      hsource0, show (48 : B256).toNat = 48 by decide +kernel]
    rfl
  · decide
  apply copyDynamicPayload_runCompiledTo
      (memory := M2) (offset := depositOffsetWord sevm.data 1)
      (offsetWord := 1) (delta := 0) (destination := 288) (size := 32)
      (payload := depositEventWithdrawalSlice sevm.data)
      (sizeGas := 3) (offsetGas := 3) (deltaGas := 3)
      (destinationGas := 3) (copyGas := 6) (G := G + 30)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c2.size_eq]
  · rw [c2.size_eq]
    decide +kernel
  · rw [c2.size_eq]
    decide +kernel
  · simpa only [show ((1 : B256) * 32).toNat = 32 by decide +kernel] using
      hread1
  · simpa only [show ((1 : B256) * 32).toNat = 32 by decide +kernel] using
      hreadMemory1
  · rw [show (36 + (0 : B256)) = 36 by decide +kernel,
      hsource1, show (32 : B256).toNat = 32 by decide +kernel]
    rfl
  · decide
  apply copyDynamicPayload_runCompiledTo
      (memory := M3) (offset := depositOffsetWord sevm.data 2)
      (offsetWord := 2) (delta := 0) (destination := 416) (size := 96)
      (payload := depositEventSignatureSlice sevm.data)
      (sizeGas := 3) (offsetGas := 3) (deltaGas := 3)
      (destinationGas := 3) (copyGas := 12) (G := G)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c3.size_eq]
  · rw [c3.size_eq]
    decide +kernel
  · rw [c3.size_eq]
    decide +kernel
  · simpa only [show ((2 : B256) * 32).toNat = 64 by decide +kernel] using
      hread2
  · simpa only [show ((2 : B256) * 32).toNat = 64 by decide +kernel] using
      hreadMemory2
  · rw [show (36 + (0 : B256)) = 36 by decide +kernel,
      hsource2, show (96 : B256).toNat = 96 by decide +kernel]
    rfl
  · decide
  simpa only [M4, show (416 : B256).toNat = 416 by decide +kernel] using
    htail

private theorem stageEventHeaders_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {amount : B256} {G : Nat} {body : Func} {ex : Execution}
    (hbody : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], eventBeforeCountMemory sevm.data amount, G⟩)
      body ex) :
    Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], eventPayloadMemory sevm.data amount, G + 222⟩)
      (([pushB256 160] ++ mstoreAt 0 ++
        [pushB256 256] ++ mstoreAt 1 ++
        [pushB256 320] ++ mstoreAt 2 ++
        [pushB256 384] ++ mstoreAt 3 ++
        [pushB256 512] ++ mstoreAt 4 ++
        [pushB256 48] ++ mstoreAt 5 ++
        [pushB256 32] ++ mstoreAt 8 ++
        [pushB256 8] ++ mstoreAt 10 ++
        [pushB256 0] ++ mstoreAt 11 ++
        loadWord amountWord ++ storeLe64At 352 ++
        [pushB256 96] ++ mstoreAt 12 ++
        [pushB256 8] ++ mstoreAt 16 ++
        [pushB256 0] ++ mstoreAt 17) +++ body) ex := by
  let M4 := eventPayloadMemory sevm.data amount
  let M5 := M4.write 0 (160 : B256).toBytes
  let M6 := M5.write 32 (256 : B256).toBytes
  let M7 := M6.write 64 (320 : B256).toBytes
  let M8 := M7.write 96 (384 : B256).toBytes
  let M9 := M8.write 128 (512 : B256).toBytes
  let M10 := M9.write 160 (48 : B256).toBytes
  let M11 := M10.write 256 (32 : B256).toBytes
  let M12 := M11.write 320 (8 : B256).toBytes
  let M13 := M12.write 352 (0 : B256).toBytes
  let M14 := storeLe64Memory M13 352 amount
  let M15 := M14.write 384 (96 : B256).toBytes
  let M16 := M15.write 512 (8 : B256).toBytes
  let M17 := M16.write 544 (0 : B256).toBytes
  let c4 := eventPayloadMemory_carrier sevm.data amount
  have c5 : EventAmountMemoryCarrier M5 amount := by
    dsimp only [M5, M4]
    exact c4.writeBefore 0 (160 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c6 : EventAmountMemoryCarrier M6 amount := by
    dsimp only [M6]
    exact c5.writeBefore 32 (256 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c7 : EventAmountMemoryCarrier M7 amount := by
    dsimp only [M7]
    exact c6.writeBefore 64 (320 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c8 : EventAmountMemoryCarrier M8 amount := by
    dsimp only [M8]
    exact c7.writeBefore 96 (384 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c9 : EventAmountMemoryCarrier M9 amount := by
    dsimp only [M9]
    exact c8.writeBefore 128 (512 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c10 : EventAmountMemoryCarrier M10 amount := by
    dsimp only [M10]
    exact c9.writeBefore 160 (48 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c11 : EventAmountMemoryCarrier M11 amount := by
    dsimp only [M11]
    exact c10.writeBefore 256 (32 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c12 : EventAmountMemoryCarrier M12 amount := by
    dsimp only [M12]
    exact c11.writeBefore 320 (8 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c13 : EventAmountMemoryCarrier M13 amount := by
    dsimp only [M13]
    exact c12.writeBefore 352 (0 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c14 : EventAmountMemoryCarrier M14 amount := by
    dsimp only [M14]
    exact c13.storeLe64Before 352 (by omega) (by omega)
  have c15 : EventAmountMemoryCarrier M15 amount := by
    dsimp only [M15]
    exact c14.writeBefore 384 (96 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c16 : EventAmountMemoryCarrier M16 amount := by
    dsimp only [M16]
    exact c15.writeBefore 512 (8 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have c17 : EventAmountMemoryCarrier M17 amount := by
    dsimp only [M17]
    exact c16.writeBefore 544 (0 : B256).toBytes (by
      simp only [B256.length_toBytes]
      omega) (by
      simp only [B256.length_toBytes]
      omega)
  have hamount : Bytes.toB256 (M13.read 672 32).1 = amount := by
    rw [Mem.Reads.read c13.reads, c13.amount_read,
      B256.toB256_toBytes]
  have hamountMemory : (M13.read 672 32).2 = M13 := by
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [c13.size_eq]
    · rw [c13.size_eq]
  have htail : Func.RunCompiledTo fs sevm
      (base.setMach ⟨[], M17, G⟩) body ex := by
    simpa only [eventBeforeCountMemory, M17, M16, M15, M14, M13, M12,
      M11, M10, M9, M8, M7, M6, M5, M4] using hbody
  apply pushMstoreAt_runCompiledTo
      (memory := M4) (value := 160) (word := 0) (offset := 0)
      (valueGas := 3) (wordGas := 2) (G := G + 214)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c4.size_eq]
  · rw [c4.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M5) (value := 256) (word := 1) (offset := 32)
      (valueGas := 3) (wordGas := 3) (G := G + 205)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c5.size_eq]
  · rw [c5.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M6) (value := 320) (word := 2) (offset := 64)
      (valueGas := 3) (wordGas := 3) (G := G + 196)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c6.size_eq]
  · rw [c6.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M7) (value := 384) (word := 3) (offset := 96)
      (valueGas := 3) (wordGas := 3) (G := G + 187)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c7.size_eq]
  · rw [c7.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M8) (value := 512) (word := 4) (offset := 128)
      (valueGas := 3) (wordGas := 3) (G := G + 178)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c8.size_eq]
  · rw [c8.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M9) (value := 48) (word := 5) (offset := 160)
      (valueGas := 3) (wordGas := 3) (G := G + 169)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c9.size_eq]
  · rw [c9.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M10) (value := 32) (word := 8) (offset := 256)
      (valueGas := 3) (wordGas := 3) (G := G + 160)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c10.size_eq]
  · rw [c10.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M11) (value := 8) (word := 10) (offset := 320)
      (valueGas := 3) (wordGas := 3) (G := G + 151)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c11.size_eq]
  · rw [c11.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M12) (value := 0) (word := 11) (offset := 352)
      (valueGas := 2) (wordGas := 3) (G := G + 143)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c12.size_eq]
  · rw [c12.size_eq]
    omega
  · decide
  apply loadAmountStoreLe64_runCompiledTo
      (memory := M13) (amount := amount) (G := G + 26)
  · rw [c13.size_eq]
  · rw [c13.size_eq]
  · exact hamount
  · exact hamountMemory
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M14) (value := 96) (word := 12) (offset := 384)
      (valueGas := 3) (wordGas := 3) (G := G + 17)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c14.size_eq]
  · rw [c14.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M15) (value := 8) (word := 16) (offset := 512)
      (valueGas := 3) (wordGas := 3) (G := G + 8)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c15.size_eq]
  · rw [c15.size_eq]
    omega
  · decide
  apply pushMstoreAt_runCompiledTo
      (memory := M16) (value := 0) (word := 17) (offset := 544)
      (valueGas := 2) (wordGas := 3) (G := G)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · rw [c16.size_eq]
  · rw [c16.size_eq]
    omega
  · decide
  exact htail

private theorem emitDepositEvent_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {event : DepositEvent} {amount oldCount : B256}
    {G : Nat} {body : Func}
    (hstatic : sevm.isStatic = false)
    (hmem : DepositEventMemoryCarrier memory event amount oldCount) :
    ∃ logged : Devm,
      logged.logs = base.logs ++ [depositEventLog sevm.currentTarget event] ∧
      (∀ (a : Adr) (k : B256),
        logged.getStorVal a k = base.getStorVal a k) ∧
      (∀ a : Adr, Devm.getStor logged a = Devm.getStor base a) ∧
      (∀ a : Adr, logged.getBal a = base.getBal a) ∧
      (∀ a : Adr, logged.getCode a = base.getCode a) ∧
      logged.accessedStorageKeys = base.accessedStorageKeys ∧
      logged.accessedAddresses = base.accessedAddresses ∧
      logged.output = base.output ∧
      logged.error = base.error ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (logged.setMach ⟨[], memory, G⟩) body ex →
        Func.RunCompiledTo fs sevm
          (base.setMach ⟨[], memory, G + 5366⟩)
          (([pushB256 depositEventTopic] ++ logWith 0 0 18) +++ body) ex := by
  obtain ⟨logged, hlogs, hstor, hstorMap, hbal, hcode, haccess, haddresses,
      houtput, herror, hlift⟩ :=
    Func.runCompiledTo_log_step_exists (fs := fs) (sevm := sevm)
      (devm := base.setMach
        ⟨[0 * 32, 18 * 32, depositEventTopic], memory, G + 5358⟩)
      (n := (0 : Fin 4).succ) (topics := [depositEventTopic]) (s := [])
      (c := 5358) (G := G) (M := memory) (M' := memory)
      (payload := abiDepositEvent event) (rest := body)
      rfl rfl hstatic rfl
      (by
        have hext :
            (base.setMach
              ⟨[0 * 32, 18 * 32, depositEventTopic], memory,
                G + 5358⟩).extCost
              [⟨(0 * 32 : B256).toNat, (18 * 32 : B256).toNat⟩] = 0 := by
          apply Devm.extCost_zero_of_le
          · rw [hmem.size_eq]
          · rw [hmem.size_eq]
            decide +kernel
        rw [hext]
        decide)
      (by
        rw [Mem.Reads.read hmem.reads]
        simpa only [show (0 * 32 : B256).toNat = 0 by decide +kernel,
          show (18 * 32 : B256).toNat = 576 by decide +kernel] using
          hmem.event_read)
      (by
        apply Mem.read_snd_eq_self
        apply memExtSize_of_le
        · rw [hmem.size_eq]
        · rw [hmem.size_eq]
          decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
  change logged.logs = base.logs ++
    [⟨sevm.currentTarget, [depositEventTopic], abiDepositEvent event⟩]
    at hlogs
  simp only [Devm.getStorVal_setMach] at hstor
  change (∀ a : Adr, Devm.getStor logged a = Devm.getStor base a) at hstorMap
  change (∀ a : Adr, logged.getBal a = base.getBal a) at hbal
  change (∀ a : Adr, logged.getCode a = base.getCode a) at hcode
  change logged.accessedStorageKeys = base.accessedStorageKeys at haccess
  change logged.accessedAddresses = base.accessedAddresses at haddresses
  change logged.output = base.output at houtput
  change logged.error = base.error at herror
  refine ⟨logged, ?_, hstor, hstorMap, hbal, hcode, haccess, haddresses,
    houtput, herror, ?_⟩
  · simpa only [depositEventLog] using hlogs
  intro ex htail
  unfold logWith
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := depositEventTopic) (c := 3) (G := G + 5363)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach]; decide)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := 18 * 32) (c := 3) (G := G + 5360)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; decide)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := 0 * 32) (c := 2) (G := G + 5358)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach])
      (by simp only [Devm.stack_setMach, List.length_cons]; decide)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  exact hlift htail

private theorem stageEventCountLog_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {amount oldCount : B256} {G : Nat} {body : Func}
    (hvalue : base.getStorVal sevm.currentTarget depositCountSlot = oldCount)
    (hstatic : sevm.isStatic = false) :
    ∃ logged : Devm,
      logged.logs =
        (afterSload sevm base depositCountSlot).logs ++
          [depositEventLog sevm.currentTarget
            (stagedDepositEvent sevm.data amount oldCount)] ∧
      (∀ (a : Adr) (k : B256),
        logged.getStorVal a k =
          (afterSload sevm base depositCountSlot).getStorVal a k) ∧
      (∀ a : Adr, Devm.getStor logged a =
        Devm.getStor (afterSload sevm base depositCountSlot) a) ∧
      (∀ a : Adr, logged.getBal a =
        (afterSload sevm base depositCountSlot).getBal a) ∧
      (∀ a : Adr, logged.getCode a =
        (afterSload sevm base depositCountSlot).getCode a) ∧
      logged.accessedStorageKeys =
        (afterSload sevm base depositCountSlot).accessedStorageKeys ∧
      logged.accessedAddresses =
        (afterSload sevm base depositCountSlot).accessedAddresses ∧
      logged.output =
        (afterSload sevm base depositCountSlot).output ∧
      logged.error =
        (afterSload sevm base depositCountSlot).error ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (logged.setMach
            ⟨[], depositEventMemory sevm.data amount oldCount, G⟩)
          body ex →
        Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨[], eventBeforeCountMemory sevm.data amount,
              G + 5489 + sloadCost sevm base depositCountSlot⟩)
          (([pushB256 depositCountSlot, sload, dup 0] ++
            mstoreAt oldCountWord ++ storeLe64At 544 ++
            [pushB256 depositEventTopic] ++ logWith 0 0 18) +++ body) ex := by
  let M17 := eventBeforeCountMemory sevm.data amount
  let M18 := M17.write 576 oldCount.toBytes
  let M19 := storeLe64Memory M18 544 oldCount
  let c17 := eventBeforeCountMemory_carrier sevm.data amount
  have hsize18 : M18.size = 704 := by
    dsimp only [M18, M17]
    rw [Mem.size_write_of_le (by
      rw [B256.length_toBytes, c17.size_eq]
      omega), c17.size_eq]
  have hfinal : DepositEventMemoryCarrier M19
      (stagedDepositEvent sevm.data amount oldCount) amount oldCount := by
    simpa only [M19, M18, M17, eventMemory_eq] using
      depositEventMemory_carrier sevm.data amount oldCount
  obtain ⟨logged, hlogs, hstor, hstorMap, hbal, hcode, haccess, haddresses,
      houtput, herror, hlift⟩ :=
    emitDepositEvent_runCompiledTo
      (base := afterSload sevm base depositCountSlot) (G := G) hstatic hfinal
  refine ⟨logged, hlogs, hstor, hstorMap, hbal, hcode, haccess, haddresses,
    houtput, herror, ?_⟩
  intro ex htail
  have hlog := hlift (by
    simpa only [M19, M18, M17, ← eventMemory_eq] using htail)
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_pushB256
      (w := depositCountSlot) (c := 3)
      (G := G + 5486 + sloadCost sevm base depositCountSlot)
      (by decide +kernel)
      (by simp only [Devm.gasLeft_setMach]; omega)
      (by simp only [Devm.stack_setMach]; decide)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_sload_selected
      (stack := []) (memory := M17) (G := G + 5486)
      hvalue (by decide)) ?_
  refine Func.RunCompiledTo.next
    (Ninst.runCompiled_dup
      (n := 0) (w := oldCount) (G := G + 5483)
      rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow])
      (by simp only [Devm.stack_setMach, List.length_cons,
        List.length_nil]; decide)) ?_
  simp only [Devm.setMach_setMach, Devm.stack_setMach,
    Devm.memory_setMach]
  apply Func.runCompiledTo_mstoreAt
      (base := afterSload sevm base depositCountSlot)
      (memory := M17) (stack := [oldCount])
      (value := oldCount) (word := oldCountWord)
      (G := G + 5477) (pushGas := 3) (extGas := 0)
  · decide +kernel
  · simp only [List.length_cons, List.length_nil]
    decide
  · intro S G'
    apply Devm.extCost_zero_of_le
    · rw [c17.size_eq]
    · rw [c17.size_eq]
      decide +kernel
  apply storeLe64At_runCompiledTo
      (base := afterSload sevm base depositCountSlot)
      (memory := M18) (word := oldCount) (address := 544)
      (offset := 544) (G := G + 5366) (stack := [])
  · rw [hsize18]
  · rw [hsize18]
    omega
  · decide
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · change Func.RunCompiledTo fs sevm
      ((afterSload sevm base depositCountSlot).setMach
        ⟨[], M19, G + 5366⟩)
      (([pushB256 depositEventTopic] ++ logWith 0 0 18) +++ body) ex
    exact hlog

/-- Execute the complete event-staging line before an arbitrary continuation.
The fixed work costs exactly 5,799 gas; the old-count read adds the actually
selected warm/cold `SLOAD` charge. -/
theorem stageDepositEvent_runCompiledTo
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {amount oldCount : B256} {G : Nat} {body : Func}
    (hdec0 : DynamicTailDecodable sevm.data 0)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hvalue : base.getStorVal sevm.currentTarget depositCountSlot = oldCount)
    (hstatic : sevm.isStatic = false) :
    ∃ logged : Devm,
      logged.logs =
        (afterSload sevm base depositCountSlot).logs ++
          [depositEventLog sevm.currentTarget
            (stagedDepositEvent sevm.data amount oldCount)] ∧
      (∀ (a : Adr) (k : B256),
        logged.getStorVal a k =
          (afterSload sevm base depositCountSlot).getStorVal a k) ∧
      (∀ a : Adr, Devm.getStor logged a =
        Devm.getStor (afterSload sevm base depositCountSlot) a) ∧
      (∀ a : Adr, logged.getBal a =
        (afterSload sevm base depositCountSlot).getBal a) ∧
      (∀ a : Adr, logged.getCode a =
        (afterSload sevm base depositCountSlot).getCode a) ∧
      logged.accessedStorageKeys =
        (afterSload sevm base depositCountSlot).accessedStorageKeys ∧
      logged.accessedAddresses =
        (afterSload sevm base depositCountSlot).accessedAddresses ∧
      logged.output =
        (afterSload sevm base depositCountSlot).output ∧
      logged.error =
        (afterSload sevm base depositCountSlot).error ∧
      ∀ {ex : Execution},
        Func.RunCompiledTo fs sevm
          (logged.setMach
            ⟨[], depositEventMemory sevm.data amount oldCount, G⟩)
          body ex →
        Func.RunCompiledTo fs sevm
          (base.setMach
            ⟨[], depositEventInputMemory sevm.data amount,
              G + 5799 + sloadCost sevm base depositCountSlot⟩)
          (stageDepositEvent +++ body) ex := by
  obtain ⟨logged, hlogs, hstor, hstorMap, hbal, hcode, haccess, haddresses,
      houtput, herror, hlift⟩ :=
    stageEventCountLog_runCompiledTo
      (fs := fs) (amount := amount) (body := body) (G := G) hvalue hstatic
  refine ⟨logged, hlogs, hstor, hstorMap, hbal, hcode, haccess, haddresses,
    houtput, herror, ?_⟩
  intro ex htail
  have hsuffix := hlift htail
  have hheaders := stageEventHeaders_runCompiledTo
    (G := G + 5489 + sloadCost sevm base depositCountSlot) hsuffix
  have hpayloads := stageEventPayloads_runCompiledTo
    (G := G + 5489 + sloadCost sevm base depositCountSlot + 222)
    hdec0 hdec1 hdec2 hheaders
  simpa only [stageDepositEvent, prepend_append, List.append_assoc,
    show G + 5489 + sloadCost sevm base depositCountSlot + 222 + 88 =
      G + 5799 + sloadCost sevm base depositCountSlot by omega] using
    hpayloads

end Blanc.BeaconDeposit
