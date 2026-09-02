import Blanc.BeaconDepositAbiSource
import Blanc.BeaconDepositHistory
import Blanc.BeaconDepositSha
import Blanc.CommonProofs

/-!
# Source-level Beacon deposit success inversion

The open-history proof starts with an existing successful execution of the
actual runtime.  This module walks that execution backwards.  It first
recovers the six source guard facts while retaining the decoder memory image;
later sections cross event staging, the seven native SHA-256 calls, and the
two committing stores.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- One little-endian byte store followed by the source word shift. -/
private theorem storeByteShift_success_of_run
    {sevm : Sevm} {pre post : Devm} {word address : B256}
    {tail : Stack}
    (hp : word :: tail <<+ pre.stack)
    (run : Line.Run sevm pre
      [dup 0, pushB256 address, mstore8, pushB256 8, shr] post) :
    (word >>> 8) :: tail <<+ post.stack ∧
      post.memory =
        pre.memory.write address.toNat [word.2.2.toUInt8] ∧
      pre.state = post.state := by
  rcases Line.of_run_cons run with ⟨afterDup, dupRun, run⟩
  rcases Line.of_run_cons run with ⟨afterAddress, addressRun, run⟩
  rcases Line.of_run_cons run with ⟨afterStore, storeRun, run⟩
  rcases Line.of_run_cons run with ⟨afterEight, eightRun, run⟩
  rcases Line.of_run_cons run with ⟨_, shiftRun, nilRun⟩
  cases nilRun
  have hpDup : word :: word :: tail <<+ afterDup.stack :=
    prefix_of_dup_val dupRun (Stack.Nth.head _ _) hp
  have addressPush := of_run_pushB256 addressRun
  have hpAddress : address :: word :: word :: tail <<+
      afterAddress.stack :=
    prefix_of_push addressPush hpDup
  obtain ⟨hpStore, memoryStore⟩ :=
    prefix_of_mstore8_val storeRun hpAddress
  have eightPush := of_run_pushB256 eightRun
  have hpEight : (8 : B256) :: word :: tail <<+ afterEight.stack :=
    prefix_of_push eightPush hpStore
  have hpShift : (word >>> 8) :: tail <<+ post.stack :=
    prefix_of_shr shiftRun hpEight
  refine ⟨hpShift, ?_,
    (Ninst.Hinv.inv (f := Devm.state) dupRun).trans
      ((Ninst.Hinv.inv (f := Devm.state) addressRun).trans
        ((of_run_mstore8_state storeRun).trans
          ((Ninst.Hinv.inv (f := Devm.state) eightRun).trans
            (Ninst.Hinv.inv (f := Devm.state) shiftRun))))⟩
  rw [← Ninst.Hinv.inv (f := Devm.memory) shiftRun,
    ← eightPush.memory, memoryStore,
    ← addressPush.memory,
    ← Ninst.Hinv.inv (f := Devm.memory) dupRun]

/-- The final little-endian byte store consumes the remaining shifted word. -/
private theorem storeLastByte_success_of_run
    {sevm : Sevm} {pre post : Devm} {word address : B256}
    {tail : Stack}
    (hp : word :: tail <<+ pre.stack)
    (run : Line.Run sevm pre [pushB256 address, mstore8] post) :
    tail <<+ post.stack ∧
      post.memory =
        pre.memory.write address.toNat [word.2.2.toUInt8] ∧
      pre.state = post.state := by
  rcases Line.of_run_cons run with ⟨afterAddress, addressRun, run⟩
  rcases Line.of_run_cons run with ⟨_, storeRun, nilRun⟩
  cases nilRun
  have addressPush := of_run_pushB256 addressRun
  have hpAddress : address :: word :: tail <<+ afterAddress.stack :=
    prefix_of_push addressPush hp
  obtain ⟨hpStore, memoryStore⟩ :=
    prefix_of_mstore8_val storeRun hpAddress
  refine ⟨hpStore, ?_,
    (Ninst.Hinv.inv (f := Devm.state) addressRun).trans
      (of_run_mstore8_state storeRun)⟩
  rw [memoryStore, ← addressPush.memory]

/-- Invert the source `storeLe64At` fragment, retaining its exact eight-byte
little-endian memory image. -/
theorem storeLe64At_success_of_run
    {sevm : Sevm} {pre post : Devm} {word address : B256}
    {offset : Nat} {tail : Stack}
    (hnat0 : address.toNat = offset)
    (hnat1 : (address + 1).toNat = offset + 1)
    (hnat2 : (address + 2).toNat = offset + 2)
    (hnat3 : (address + 3).toNat = offset + 3)
    (hnat4 : (address + 4).toNat = offset + 4)
    (hnat5 : (address + 5).toNat = offset + 5)
    (hnat6 : (address + 6).toNat = offset + 6)
    (hnat7 : (address + 7).toNat = offset + 7)
    (hp : word :: tail <<+ pre.stack)
    (run : Line.Run sevm pre (storeLe64At address) post) :
    tail <<+ post.stack ∧
      post.memory = storeLe64Memory pre.memory offset word ∧
      pre.state = post.state := by
  unfold storeLe64At at run
  rcases of_run_append
      [dup 0, pushB256 address, mstore8, pushB256 8, shr] run with
    ⟨s1, r1, run⟩
  rcases of_run_append
      [dup 0, pushB256 (address + 1), mstore8, pushB256 8, shr] run with
    ⟨s2, r2, run⟩
  rcases of_run_append
      [dup 0, pushB256 (address + 2), mstore8, pushB256 8, shr] run with
    ⟨s3, r3, run⟩
  rcases of_run_append
      [dup 0, pushB256 (address + 3), mstore8, pushB256 8, shr] run with
    ⟨s4, r4, run⟩
  rcases of_run_append
      [dup 0, pushB256 (address + 4), mstore8, pushB256 8, shr] run with
    ⟨s5, r5, run⟩
  rcases of_run_append
      [dup 0, pushB256 (address + 5), mstore8, pushB256 8, shr] run with
    ⟨s6, r6, run⟩
  rcases of_run_append
      [dup 0, pushB256 (address + 6), mstore8, pushB256 8, shr] run with
    ⟨s7, r7, run⟩
  have h1 := storeByteShift_success_of_run hp r1
  have h2 := storeByteShift_success_of_run h1.1 r2
  have h3 := storeByteShift_success_of_run h2.1 r3
  have h4 := storeByteShift_success_of_run h3.1 r4
  have h5 := storeByteShift_success_of_run h4.1 r5
  have h6 := storeByteShift_success_of_run h5.1 r6
  have h7 := storeByteShift_success_of_run h6.1 r7
  have h8 := storeLastByte_success_of_run h7.1 run
  refine ⟨h8.1, ?_, h1.2.2.trans (h2.2.2.trans
    (h3.2.2.trans (h4.2.2.trans (h5.2.2.trans
      (h6.2.2.trans (h7.2.2.trans h8.2.2))))))⟩
  rw [h8.2.1, h7.2.1, h6.2.1, h5.2.1, h4.2.1, h3.2.1,
    h2.2.1, h1.2.1, hnat0, hnat1, hnat2, hnat3, hnat4, hnat5,
    hnat6, hnat7]
  rfl

/-- Invert one source `copyDynamicPayload` fragment against a proof-carrying
decoder image.  The covered `MLOAD` window collapses back to the input memory,
so the only surviving memory effect is the exact calldata slice write. -/
private theorem copyDynamicPayload_success_of_run
    {sevm : Sevm} {pre post : Devm}
    {offsetWord delta destination size offset : B256}
    {source : Nat} {payload : Bytes} {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hreads : Mem.Reads pre.memory image)
    (hread : Bytes.toB256
      (image.sliceD (offsetWord * 32).toNat 32 0) = offset)
    (hmod : pre.memory.size % 32 = 0)
    (hcovered : (offsetWord * 32).toNat + 32 ≤ pre.memory.size)
    (hsource : ((36 + delta) + offset).toNat = source)
    (hpayload : sevm.data.sliceD source size.toNat 0 = payload)
    (run : Line.Run sevm pre
      (copyDynamicPayload offsetWord delta destination size) post) :
    tail <<+ post.stack ∧
      post.memory = pre.memory.write destination.toNat payload ∧
      pre.state = post.state := by
  have state : pre.state = post.state :=
    Line.of_inv Devm.state
      (by unfold copyDynamicPayload loadWord; line_inv) run
  unfold copyDynamicPayload loadWord at run
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  rcases Line.of_run_cons run with ⟨_, q7, hnil⟩
  cases hnil
  have push1 := of_run_pushB256 q1
  have push2 := of_run_pushB256 q2
  have hp1 : size :: tail <<+ s1.stack :=
    prefix_of_push push1 hp
  have hp2 : (offsetWord * 32) :: size :: tail <<+ s2.stack :=
    prefix_of_push push2 hp1
  have reads2 : Mem.Reads s2.memory image := by
    rw [← push2.memory, ← push1.memory]
    exact hreads
  obtain ⟨hp3, memory3, _returnData3⟩ :=
    prefix_of_mload_val q3 hp2 reads2
  have hp3' : offset :: size :: tail <<+ s3.stack := by
    simpa only [hread] using hp3
  have push4 := of_run_pushB256 q4
  have hp4 : (36 + delta) :: offset :: size :: tail <<+ s4.stack :=
    prefix_of_push push4 hp3'
  have hp5 : ((36 + delta) + offset) :: size :: tail <<+ s5.stack :=
    prefix_of_add q5 hp4
  have push6 := of_run_pushB256 q6
  have hp6 : destination :: ((36 + delta) + offset) :: size :: tail <<+
      s6.stack := prefix_of_push push6 hp5
  obtain ⟨stack7, memory7⟩ :=
    prefix_of_calldatacopy_val q7 hp6
  have covered2 :
      s2.memory.extend (offsetWord * 32).toNat 32 = s2.memory := by
    change (s2.memory.read (offsetWord * 32).toNat 32).2 = s2.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [← push2.memory, ← push1.memory]
      exact hmod
    · rw [← push2.memory, ← push1.memory]
      exact hcovered
  refine ⟨stack7, ?_, state⟩
  rw [memory7, ← push6.memory,
    ← Ninst.Hinv.inv (f := Devm.memory) q5,
    ← push4.memory, memory3, covered2,
    ← push2.memory, ← push1.memory, hsource, hpayload]

/-- The successful event payload prefix copies the three validated dynamic
tails into their exact staging windows without changing persistent state. -/
theorem stageEventPayloads_success_of_run
    {sevm : Sevm} {pre post : Devm} {amount : B256}
    {tail : Stack}
    (hdec0 : DynamicTailDecodable sevm.data 0)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hp : tail <<+ pre.stack)
    (hmemory : pre.memory = depositEventInputMemory sevm.data amount)
    (run : Line.Run sevm pre
      ([pushB256 0] ++ mstoreAt 7 ++
        copyDynamicPayload 0 0 192 48 ++
        copyDynamicPayload 1 0 288 32 ++
        copyDynamicPayload 2 0 416 96) post) :
    tail <<+ post.stack ∧
      post.memory = eventPayloadMemory sevm.data amount ∧
      pre.state = post.state := by
  have state : pre.state = post.state :=
    Line.of_inv Devm.state
      (by unfold copyDynamicPayload loadWord mstoreAt; line_inv) run
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
  rcases of_run_append ([pushB256 0] ++ mstoreAt 7) run with
    ⟨s1, firstRun, run⟩
  rcases of_run_append [pushB256 0] firstRun with
    ⟨afterZero, zeroLine, storeRun⟩
  rcases Line.of_run_cons zeroLine with
    ⟨_, zeroRun, zeroNil⟩
  cases zeroNil
  have zeroPush := of_run_pushB256 zeroRun
  have hpZero : (0 : B256) :: tail <<+ afterZero.stack :=
    prefix_of_push zeroPush hp
  obtain ⟨hp1, memory1'⟩ :=
    of_run_mstoreAt_val storeRun hpZero
  have memory1 : s1.memory = M1 := by
    rw [memory1', ← zeroPush.memory,
      show ((7 : B256) * 32).toNat = 224 by decide +kernel,
      hmemory]
  rcases of_run_append (copyDynamicPayload 0 0 192 48) run with
    ⟨s2, copy0Run, run⟩
  have read0 : Bytes.toB256
      (c1.image.sliceD ((0 : B256) * 32).toNat 32 0) =
        depositOffsetWord sevm.data 0 := by
    rw [show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      c1.offset0_read, B256.toB256_toBytes]
  obtain ⟨hp2, memory2', _state2⟩ :=
    copyDynamicPayload_success_of_run hp1
      (by rw [memory1]; exact c1.reads) read0
      (by rw [memory1, c1.size_eq])
      (by rw [memory1, c1.size_eq]; decide +kernel)
      (by simpa only [show (36 + (0 : B256)) = 36 by decide +kernel]
        using hsource0)
      (by
        rw [show (48 : B256).toNat = 48 by decide +kernel]
      )
      copy0Run
  have memory2 : s2.memory = M2 := by
    rw [memory2', memory1,
      show (192 : B256).toNat = 192 by decide +kernel]
    rfl
  rcases of_run_append (copyDynamicPayload 1 0 288 32) run with
    ⟨s3, copy1Run, run⟩
  have read1 : Bytes.toB256
      (c2.image.sliceD ((1 : B256) * 32).toNat 32 0) =
        depositOffsetWord sevm.data 1 := by
    rw [show ((1 : B256) * 32).toNat = 32 by decide +kernel,
      c2.offset1_read, B256.toB256_toBytes]
  obtain ⟨hp3, memory3', _state3⟩ :=
    copyDynamicPayload_success_of_run hp2
      (by rw [memory2]; exact c2.reads) read1
      (by rw [memory2, c2.size_eq])
      (by rw [memory2, c2.size_eq]; decide +kernel)
      (by simpa only [show (36 + (0 : B256)) = 36 by decide +kernel]
        using hsource1)
      (by
        rw [show (32 : B256).toNat = 32 by decide +kernel]
      )
      copy1Run
  have memory3 : s3.memory = M3 := by
    rw [memory3', memory2,
      show (288 : B256).toNat = 288 by decide +kernel]
    rfl
  have read2 : Bytes.toB256
      (c3.image.sliceD ((2 : B256) * 32).toNat 32 0) =
        depositOffsetWord sevm.data 2 := by
    rw [show ((2 : B256) * 32).toNat = 64 by decide +kernel,
      c3.offset2_read, B256.toB256_toBytes]
  obtain ⟨hp4, memory4', _state4⟩ :=
    copyDynamicPayload_success_of_run hp3
      (by rw [memory3]; exact c3.reads) read2
      (by rw [memory3, c3.size_eq])
      (by rw [memory3, c3.size_eq]; decide +kernel)
      (by simpa only [show (36 + (0 : B256)) = 36 by decide +kernel]
        using hsource2)
      (by
        rw [show (96 : B256).toNat = 96 by decide +kernel]
      )
      run
  refine ⟨hp4, ?_, state⟩
  rw [memory4', memory3,
    show (416 : B256).toNat = 416 by decide +kernel]
  rfl

/-- Invert one fixed event-word write.  The setup push and `mstoreAt`
fragment preserve the world state and leave the caller's stack tail intact. -/
theorem pushMstoreAt_success_of_run
    {sevm : Sevm} {pre post : Devm} {value word : B256}
    {offset : Nat} {tail : Stack}
    (hoffset : (word * 32).toNat = offset)
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre ([pushB256 value] ++ mstoreAt word) post) :
    tail <<+ post.stack ∧
      post.memory = pre.memory.write offset value.toBytes ∧
      pre.state = post.state := by
  have state : pre.state = post.state :=
    Line.of_inv Devm.state (by unfold mstoreAt; line_inv) run
  rcases of_run_append [pushB256 value] run with
    ⟨afterPush, pushLine, storeRun⟩
  rcases Line.of_run_cons pushLine with
    ⟨_, pushRun, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 pushRun
  have hpPush : value :: tail <<+ afterPush.stack :=
    prefix_of_push pushed hp
  obtain ⟨hpPost, memoryPost⟩ :=
    of_run_mstoreAt_val storeRun hpPush
  refine ⟨hpPost, ?_, state⟩
  rw [memoryPost, ← pushed.memory, hoffset]

/-- Invert a covered scratch-word load followed by one exact word store. -/
theorem loadMstore_success_of_run
    {sevm : Sevm} {pre post : Devm}
    {sourceWord targetWord value : B256}
    {targetOffset : Nat} {tail : Stack} {image : Bytes}
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hvalue : Bytes.toB256
      (image.sliceD (sourceWord * 32).toNat 32 0) = value)
    (hcovered :
      pre.memory.extend (sourceWord * 32).toNat 32 = pre.memory)
    (htarget : (targetWord * 32).toNat = targetOffset)
    (run : Line.Run sevm pre
      (loadWord sourceWord ++ mstoreAt targetWord) post) :
    tail <<+ post.stack ∧
      post.memory = pre.memory.write targetOffset value.toBytes ∧
      pre.state = post.state := by
  rcases of_run_append (loadWord sourceWord) run with
    ⟨afterLoad, loadRun, storeRun⟩
  obtain ⟨hpLoad, _wfLoad, _readsLoad, stateLoad, memoryLoad⟩ :=
    of_run_loadWordAt_image_memory hp hwf hreads hvalue loadRun
  obtain ⟨hpPost, memoryPost⟩ :=
    of_run_mstoreAt_val storeRun hpLoad
  have stateStore : afterLoad.state = post.state :=
    Line.of_inv Devm.state (by unfold mstoreAt; line_inv) storeRun
  refine ⟨hpPost, ?_, stateLoad.trans stateStore⟩
  rw [memoryPost, memoryLoad, hcovered, htarget]

/-- Invert a covered two-word staging prefix and its source sha64 call.
The continuation state contains the exact pair digest and preserves the
entry storage and code maps. -/
theorem reconstructPairSha_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate second : B256}
    {leftWord rightWord outputWord left right : B256}
    {outputOffset : Nat} {tail : Stack} {success : Func}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 2) = none)
    (hregisters : ReconstructRegistersMemoryCarrier pre.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768)
    (hleftFit : (leftWord * 32).toNat + 32 ≤ 768)
    (hrightFit : (rightWord * 32).toNat + 32 ≤ 768)
    (houtput : (outputWord * 32).toNat = outputOffset)
    (hshaCovered :
      memExtsSize 768 (reconstructionShaWindows 0 outputWord) = 768)
    (hleftRead : Bytes.toB256
      (pre.memory.read (leftWord * 32).toNat 32).1 = left)
    (hrightRead : Bytes.toB256
      ((pre.memory.write 0 left.toBytes).read
        (rightWord * 32).toNat 32).1 = right)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (loadWord leftWord +++ mstoreAt 0 +++
        loadWord rightWord +++ mstoreAt 1 +++
        sha64 0 outputWord success) post) :
    ∃ q,
      tail <<+ q.stack ∧
      Func.Run fs sevm q success post ∧
      q.memory =
        ((pre.memory.write 0 left.toBytes).write 32 right.toBytes).write
          outputOffset (hashPair Bytes.sha256 left right).toBytes ∧
      Devm.getStor q = Devm.getStor pre ∧
      Devm.getCode q = Devm.getCode pre := by
  rcases of_run_prepend (loadWord leftWord ++ mstoreAt 0) _ run with
    ⟨afterLeft, leftRun, run⟩
  have leftImage : Bytes.toB256
      (hregisters.intermediate.node.source.image.sliceD
        (leftWord * 32).toNat 32 0) = left := by
    rw [← Mem.Reads.read hregisters.intermediate.node.source.reads]
    exact hleftRead
  have leftCovered :
      pre.memory.extend (leftWord * 32).toNat 32 = pre.memory := by
    change (pre.memory.read (leftWord * 32).toNat 32).2 = pre.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hregisters.intermediate.node.source.size_eq]
    · rw [hregisters.intermediate.node.source.size_eq]
      exact hleftFit
  obtain ⟨hpLeft, leftMemory, leftState⟩ :=
    loadMstore_success_of_run hp
      hregisters.intermediate.node.source.wf
      hregisters.intermediate.node.source.reads leftImage leftCovered
      (targetOffset := 0) (by decide +kernel) leftRun
  have firstCarrier : ReconstructRegistersMemoryCarrier afterLeft.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second 768 := by
    rw [leftMemory]
    exact hregisters.writeBeforeSources 0 left.toBytes
      (by rw [B256.length_toBytes]; omega)
      (by rw [B256.length_toBytes]; omega)
  rcases of_run_prepend (loadWord rightWord ++ mstoreAt 1) _ run with
    ⟨afterRight, rightRun, shaRun⟩
  have rightImage : Bytes.toB256
      (firstCarrier.intermediate.node.source.image.sliceD
        (rightWord * 32).toNat 32 0) = right := by
    rw [← Mem.Reads.read firstCarrier.intermediate.node.source.reads]
    rw [leftMemory]
    exact hrightRead
  have rightCovered :
      afterLeft.memory.extend (rightWord * 32).toNat 32 =
        afterLeft.memory := by
    change (afterLeft.memory.read (rightWord * 32).toNat 32).2 =
      afterLeft.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [firstCarrier.intermediate.node.source.size_eq]
    · rw [firstCarrier.intermediate.node.source.size_eq]
      exact hrightFit
  obtain ⟨hpRight, rightMemory, rightState⟩ :=
    loadMstore_success_of_run hpLeft
      firstCarrier.intermediate.node.source.wf
      firstCarrier.intermediate.node.source.reads rightImage rightCovered
      (targetOffset := 32) (by decide +kernel) rightRun
  have pairCarrier : ReconstructPairMemoryCarrier afterRight.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate second left right 768 := by
    rw [rightMemory, leftMemory]
    exact hregisters.stagePair left right (by omega)
  have stageState : pre.state = afterRight.state :=
    leftState.trans rightState
  have hnodelegRight :
      getDelegatedCodeAddress (afterRight.getCode 2) = none := by
    rw [← getCode_eq_of_state_eq stageState 2]
    exact hnodeleg
  obtain ⟨q, hpQ, runQ, memoryQ, _returnQ, storageQ, codeQ⟩ :=
    sha64_success_of_run hbubble hrev hpre hnodelegRight hpRight shaRun
  have shaCovered :
      afterRight.memory.extends
        (reconstructionShaWindows 0 outputWord) = afterRight.memory := by
    apply Mem.extends_covered
    rw [pairCarrier.registers.intermediate.node.source.size_eq]
    exact hshaCovered
  have shaInput : (afterRight.memory.read 0 64).1 =
      left.toBytes ++ right.toBytes := by
    change afterRight.memory.data.sliceD 0 64 0 =
      left.toBytes ++ right.toBytes
    exact pairCarrier.shaInput
  have shaCovered' : afterRight.memory.extends
      [⟨0, 64⟩, ⟨outputOffset, 32⟩] = afterRight.memory := by
    simpa only [reconstructionShaWindows,
      show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      houtput] using shaCovered
  refine ⟨q, hpQ, runQ, ?_, ?_, ?_⟩
  · rw [show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      houtput, shaInput, shaCovered'] at memoryQ
    rw [rightMemory, leftMemory] at memoryQ
    simpa only [hashPair] using memoryQ
  · calc
      Devm.getStor q = Devm.getStor afterRight := storageQ
      _ = Devm.getStor pre := by
        funext address
        exact (getStor_eq_of_state_eq stageState address).symm
  · calc
      Devm.getCode q = Devm.getCode afterRight := codeQ
      _ = Devm.getCode pre := by
        funext address
        exact (getCode_eq_of_state_eq stageState address).symm

/-- Invert the signature-tail staging fragment and its expanding SHA call,
establishing all three reconstruction digest registers. -/
theorem reconstructSignatureSecondSha_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node intermediate : B256}
    {tail : Stack} {success : Func}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 2) = none)
    (hintermediate : ReconstructIntermediateMemoryCarrier pre.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate 736)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (loadWord 15 +++ mstoreAt 0 +++
        pushB256 0 ::: mstoreAt 1 +++
        sha64 0 secondIntermediateWord success) post) :
    ∃ q,
      tail <<+ q.stack ∧
      Func.Run fs sevm q success post ∧
      Nonempty (ReconstructRegistersMemoryCarrier q.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount node intermediate
        (reconstructSignatureSecondDigest signatureTail) 768) ∧
      Devm.getStor q = Devm.getStor pre ∧
      Devm.getCode q = Devm.getCode pre := by
  let tailWord := Bytes.toB256 signatureTail
  rcases of_run_prepend (loadWord 15 ++ mstoreAt 0) _ run with
    ⟨afterTail, tailRun, run⟩
  have tailImage : Bytes.toB256
      (hintermediate.node.source.image.sliceD
        ((15 : B256) * 32).toNat 32 0) = tailWord := by
    rw [← Mem.Reads.read hintermediate.node.source.reads]
    exact hintermediate.node.source.readSignatureTail
  have tailCovered :
      pre.memory.extend ((15 : B256) * 32).toNat 32 = pre.memory := by
    change (pre.memory.read ((15 : B256) * 32).toNat 32).2 =
      pre.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hintermediate.node.source.size_eq]
    · rw [hintermediate.node.source.size_eq]
      decide +kernel
  obtain ⟨hpTail, tailMemory, tailState⟩ :=
    loadMstore_success_of_run hp
      hintermediate.node.source.wf hintermediate.node.source.reads
      tailImage tailCovered (targetOffset := 0) (by decide +kernel) tailRun
  rcases of_run_prepend ([pushB256 0] ++ mstoreAt 1) _ run with
    ⟨afterZero, zeroRun, shaRun⟩
  obtain ⟨hpZero, zeroMemory, zeroState⟩ :=
    pushMstoreAt_success_of_run (offset := 32)
      (by decide +kernel) hpTail zeroRun
  have pairCarrier :
      ReconstructIntermediatePairMemoryCarrier afterZero.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount node intermediate tailWord 0 736 := by
    rw [zeroMemory, tailMemory]
    exact hintermediate.stagePair tailWord 0 (by omega)
  have stageState : pre.state = afterZero.state :=
    tailState.trans zeroState
  have hnodelegZero :
      getDelegatedCodeAddress (afterZero.getCode 2) = none := by
    rw [← getCode_eq_of_state_eq stageState 2]
    exact hnodeleg
  obtain ⟨q, hpQ, runQ, memoryQ, _returnQ, storageQ, codeQ⟩ :=
    sha64_success_of_run hbubble hrev hpre hnodelegZero hpZero shaRun
  have shaInput : (afterZero.memory.read 0 64).1 =
      tailWord.toBytes ++ (0 : B256).toBytes := by
    change afterZero.memory.data.sliceD 0 64 0 =
      tailWord.toBytes ++ (0 : B256).toBytes
    exact pairCarrier.shaInput
  have memoryQ' : q.memory =
      (afterZero.memory.extends
        (reconstructionShaWindows 0 secondIntermediateWord)).write
        736 (reconstructSignatureSecondDigest signatureTail).toBytes := by
    rw [show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      show (secondIntermediateWord * 32).toNat = 736 by decide +kernel,
      shaInput] at memoryQ
    rw [show reconstructionShaWindows 0 secondIntermediateWord =
      [⟨0, 64⟩, ⟨736, 32⟩] by decide +kernel]
    simpa only [reconstructSignatureSecondDigest, tailWord] using memoryQ
  have extended : ReconstructIntermediateMemoryCarrier
      (afterZero.memory.extends
        (reconstructionShaWindows 0 secondIntermediateWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate 768 := by
    have h := pairCarrier.intermediate.extendForHash
      0 secondIntermediateWord
    have hsize : memExtsSize 736
        (reconstructionShaWindows 0 secondIntermediateWord) = 768 := by
      decide +kernel
    rw [hsize] at h
    exact h
  have registers : ReconstructRegistersMemoryCarrier q.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node intermediate
      (reconstructSignatureSecondDigest signatureTail) 768 := by
    rw [memoryQ']
    exact extended.writeSecond
      (reconstructSignatureSecondDigest signatureTail) (by omega)
  refine ⟨q, hpQ, runQ, ⟨registers⟩, ?_, ?_⟩
  · calc
      Devm.getStor q = Devm.getStor afterZero := storageQ
      _ = Devm.getStor pre := by
        funext address
        exact (getStor_eq_of_state_eq stageState address).symm
  · calc
      Devm.getCode q = Devm.getCode afterZero := codeQ
      _ = Devm.getCode pre := by
        funext address
        exact (getCode_eq_of_state_eq stageState address).symm

/-- Invert the direct pubkey SHA site and establish the node register. -/
theorem reconstructPubkeySha_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount : B256} {tail : Stack} {success : Func}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 2) = none)
    (source : ReconstructSourceMemoryCarrier pre.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount 704)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre (sha64 6 nodeWord success) post) :
    ∃ q,
      tail <<+ q.stack ∧
      Func.Run fs sevm q success post ∧
      Nonempty (ReconstructNodeMemoryCarrier q.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount (Bytes.sha256 pubkeyInput) 704) ∧
      Devm.getStor q = Devm.getStor pre ∧
      Devm.getCode q = Devm.getCode pre := by
  obtain ⟨q, hpQ, runQ, memoryQ, _returnQ, storageQ, codeQ⟩ :=
    sha64_success_of_run hbubble hrev hpre hnodeleg hp run
  have shaInput : (pre.memory.read 192 64).1 = pubkeyInput := by
    change pre.memory.data.sliceD 192 64 0 = pubkeyInput
    exact source.shaPubkeyInput
  have shaCovered : pre.memory.extends
      (reconstructionShaWindows 6 nodeWord) = pre.memory := by
    apply Mem.extends_covered
    rw [source.size_eq]
    decide +kernel
  have memoryQ' : q.memory =
      pre.memory.write 640 (Bytes.sha256 pubkeyInput).toBytes := by
    rw [show ((6 : B256) * 32).toNat = 192 by decide +kernel,
      show (nodeWord * 32).toNat = 640 by decide +kernel,
      shaInput] at memoryQ
    have hcovered : pre.memory.extends
        [⟨192, 64⟩, ⟨640, 32⟩] = pre.memory := by
      simpa only [reconstructionShaWindows,
        show ((6 : B256) * 32).toNat = 192 by decide +kernel,
        show (nodeWord * 32).toNat = 640 by decide +kernel] using shaCovered
    rw [hcovered] at memoryQ
    exact memoryQ
  have nodeCarrier : ReconstructNodeMemoryCarrier q.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount (Bytes.sha256 pubkeyInput) 704 := by
    rw [memoryQ']
    exact source.writeNode (Bytes.sha256 pubkeyInput) (by omega)
  exact ⟨q, hpQ, runQ, ⟨nodeCarrier⟩, storageQ, codeQ⟩

/-- Invert the direct first-signature SHA site and establish the intermediate
digest register after the exact 704-to-736-byte expansion. -/
theorem reconstructSignatureFirstSha_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {pubkeyInput signatureFirst signatureTail withdrawal amountPadded : Bytes}
    {oldCount amount node : B256} {tail : Stack} {success : Func}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 2) = none)
    (hnode : ReconstructNodeMemoryCarrier pre.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node 704)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (sha64 13 intermediateWord success) post) :
    ∃ q,
      tail <<+ q.stack ∧
      Func.Run fs sevm q success post ∧
      Nonempty (ReconstructIntermediateMemoryCarrier q.memory
        pubkeyInput signatureFirst signatureTail withdrawal amountPadded
        oldCount amount node (Bytes.sha256 signatureFirst) 736) ∧
      Devm.getStor q = Devm.getStor pre ∧
      Devm.getCode q = Devm.getCode pre := by
  obtain ⟨q, hpQ, runQ, memoryQ, _returnQ, storageQ, codeQ⟩ :=
    sha64_success_of_run hbubble hrev hpre hnodeleg hp run
  have shaInput : (pre.memory.read 416 64).1 = signatureFirst := by
    change pre.memory.data.sliceD 416 64 0 = signatureFirst
    exact hnode.source.shaSignatureFirstInput
  have memoryQ' : q.memory =
      (pre.memory.extends
        (reconstructionShaWindows 13 intermediateWord)).write
        704 (Bytes.sha256 signatureFirst).toBytes := by
    rw [show ((13 : B256) * 32).toNat = 416 by decide +kernel,
      show (intermediateWord * 32).toNat = 704 by decide +kernel,
      shaInput] at memoryQ
    rw [show reconstructionShaWindows 13 intermediateWord =
      [⟨416, 64⟩, ⟨704, 32⟩] by decide +kernel]
    exact memoryQ
  have extended : ReconstructNodeMemoryCarrier
      (pre.memory.extends
        (reconstructionShaWindows 13 intermediateWord))
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node 736 := by
    have h := hnode.extendForHash 13 intermediateWord
    have hsize : memExtsSize 704
        (reconstructionShaWindows 13 intermediateWord) = 736 := by
      decide +kernel
    rw [hsize] at h
    exact h
  have intermediateCarrier : ReconstructIntermediateMemoryCarrier q.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount node (Bytes.sha256 signatureFirst) 736 := by
    rw [memoryQ']
    exact extended.writeIntermediate
      (Bytes.sha256 signatureFirst) (by omega)
  exact ⟨q, hpQ, runQ, ⟨intermediateCarrier⟩, storageQ, codeQ⟩

/-- Invert all seven reconstruction SHA sites.  The final node register is
identified with the model deposit-data node, while the caller receives the
actual continuation state and the exact storage/code frame equalities. -/
theorem reconstructDepositDataNode_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {pubkey withdrawal signature : Bytes}
    {oldCount amount : B256} {tail : Stack} {success : Func}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hnodeleg : getDelegatedCodeAddress (pre.getCode 2) = none)
    (hwithdrawal : withdrawal.length = 32)
    (hsignature : signature.length = 96)
    (source : ReconstructSourceMemoryCarrier pre.memory
      (pubkey ++ zeros 16) (signature.take 64) (signature.drop 64)
      withdrawal (le64 amount.toNat ++ zeros 24) oldCount amount 704)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (reconstructDepositDataNode success) post) :
    ∃ q depositNode amountSignatureNode signatureSecondNode,
      tail <<+ q.stack ∧
      Func.Run fs sevm q success post ∧
      Nonempty (ReconstructRegistersMemoryCarrier q.memory
        (pubkey ++ zeros 16) (signature.take 64) (signature.drop 64)
        withdrawal (le64 amount.toNat ++ zeros 24) oldCount amount
        depositNode amountSignatureNode signatureSecondNode 768) ∧
      depositNode =
        depositDataNode Bytes.sha256 pubkey withdrawal signature
          (le64 amount.toNat) ∧
      Devm.getStor q = Devm.getStor pre ∧
      Devm.getCode q = Devm.getCode pre := by
  let pubkeyInput := pubkey ++ zeros 16
  let signatureFirst := signature.take 64
  let signatureTail := signature.drop 64
  let amountPadded := le64 amount.toNat ++ zeros 24
  let pubkeyNode := Bytes.sha256 pubkeyInput
  let signatureFirstNode := Bytes.sha256 signatureFirst
  let signatureSecondNode :=
    reconstructSignatureSecondDigest signatureTail
  let signatureNode :=
    hashPair Bytes.sha256 signatureFirstNode signatureSecondNode
  let pubkeyWithdrawalNode :=
    hashPair Bytes.sha256 pubkeyNode (Bytes.toB256 withdrawal)
  let amountSignatureNode :=
    hashPair Bytes.sha256 (Bytes.toB256 amountPadded) signatureNode
  let depositNode :=
    hashPair Bytes.sha256 pubkeyWithdrawalNode amountSignatureNode
  let finish :=
    loadWord nodeWord +++ mstoreAt 0 +++
    loadWord intermediateWord +++ mstoreAt 1 +++
    sha64 0 nodeWord success
  let amountAndSignature :=
    loadWord 11 +++ mstoreAt 0 +++
    loadWord intermediateWord +++ mstoreAt 1 +++
    sha64 0 intermediateWord finish
  let pubkeyAndWithdrawal :=
    loadWord nodeWord +++ mstoreAt 0 +++
    loadWord 9 +++ mstoreAt 1 +++
    sha64 0 nodeWord amountAndSignature
  let signatureRoot :=
    loadWord intermediateWord +++ mstoreAt 0 +++
    loadWord secondIntermediateWord +++ mstoreAt 1 +++
    sha64 0 intermediateWord pubkeyAndWithdrawal
  let signatureSecondHalf :=
    loadWord 15 +++ mstoreAt 0 +++
    pushB256 0 ::: mstoreAt 1 +++
    sha64 0 secondIntermediateWord signatureRoot
  have run0 : Func.Run fs sevm pre
      (sha64 6 nodeWord
        (sha64 13 intermediateWord signatureSecondHalf)) post := by
    simpa only [reconstructDepositDataNode, finish, amountAndSignature,
      pubkeyAndWithdrawal, signatureRoot, signatureSecondHalf] using run
  obtain ⟨q1, hp1, run1, hnode1, storage1, code1⟩ :=
    reconstructPubkeySha_success_of_run
      hbubble hrev hpre hnodeleg source hp run0
  obtain ⟨hnode1⟩ := hnode1
  have hnodeleg1 : getDelegatedCodeAddress (q1.getCode 2) = none := by
    rw [code1]
    exact hnodeleg
  obtain ⟨q2, hp2, run2, hintermediate2, storage2, code2⟩ :=
    reconstructSignatureFirstSha_success_of_run
      hbubble hrev hpre hnodeleg1 hnode1 hp1 run1
  obtain ⟨hintermediate2⟩ := hintermediate2
  have hnodeleg2 : getDelegatedCodeAddress (q2.getCode 2) = none := by
    rw [code2]
    exact hnodeleg1
  obtain ⟨q3, hp3, run3, hregisters3, storage3, code3⟩ :=
    reconstructSignatureSecondSha_success_of_run
      hbubble hrev hpre hnodeleg2 hintermediate2 hp2
      (by simpa only [signatureSecondHalf] using run2)
  obtain ⟨hregisters3⟩ := hregisters3
  have hnodeleg3 : getDelegatedCodeAddress (q3.getCode 2) = none := by
    rw [code3]
    exact hnodeleg2
  let first4 := q3.memory.write 0 signatureFirstNode.toBytes
  have firstCarrier4 : ReconstructRegistersMemoryCarrier first4
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount pubkeyNode signatureFirstNode signatureSecondNode 768 := by
    simpa only [first4] using
      hregisters3.writeBeforeSources 0 signatureFirstNode.toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  obtain ⟨q4, hp4, run4, memory4, storage4, code4⟩ :=
    reconstructPairSha_success_of_run
      (leftWord := intermediateWord)
      (rightWord := secondIntermediateWord)
      (outputWord := intermediateWord)
      (left := signatureFirstNode) (right := signatureSecondNode)
      (outputOffset := 704)
      hbubble hrev hpre hnodeleg3 hregisters3
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      hregisters3.intermediate.readIntermediate
      (by
        simpa only [first4,
          show (secondIntermediateWord * 32).toNat = 736 by
            decide +kernel] using firstCarrier4.readSecond)
      hp3 (by simpa only [signatureRoot] using run3)
  have pair4 :=
    hregisters3.stagePair signatureFirstNode signatureSecondNode (by omega)
  have hregisters4 : ReconstructRegistersMemoryCarrier q4.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount pubkeyNode signatureNode signatureSecondNode 768 := by
    rw [memory4]
    exact pair4.registers.writeIntermediate signatureNode (by omega)
  have hnodeleg4 : getDelegatedCodeAddress (q4.getCode 2) = none := by
    rw [code4]
    exact hnodeleg3
  let first5 := q4.memory.write 0 pubkeyNode.toBytes
  have firstCarrier5 : ReconstructRegistersMemoryCarrier first5
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount pubkeyNode signatureNode signatureSecondNode 768 := by
    simpa only [first5] using
      hregisters4.writeBeforeSources 0 pubkeyNode.toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  obtain ⟨q5, hp5, run5, memory5, storage5, code5⟩ :=
    reconstructPairSha_success_of_run
      (leftWord := nodeWord) (rightWord := 9)
      (outputWord := nodeWord)
      (left := pubkeyNode) (right := Bytes.toB256 withdrawal)
      (outputOffset := 640)
      hbubble hrev hpre hnodeleg4 hregisters4
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      hregisters4.intermediate.node.readNode
      (by
        simpa only [first5,
          show ((9 : B256) * 32).toNat = 288 by decide +kernel] using
          firstCarrier5.intermediate.node.source.readWithdrawal)
      hp4 (by simpa only [pubkeyAndWithdrawal] using run4)
  have pair5 :=
    hregisters4.stagePair pubkeyNode (Bytes.toB256 withdrawal) (by omega)
  have hregisters5 : ReconstructRegistersMemoryCarrier q5.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount pubkeyWithdrawalNode signatureNode
      signatureSecondNode 768 := by
    rw [memory5]
    exact pair5.registers.writeNode pubkeyWithdrawalNode (by omega)
  have hnodeleg5 : getDelegatedCodeAddress (q5.getCode 2) = none := by
    rw [code5]
    exact hnodeleg4
  let amountWord := Bytes.toB256 amountPadded
  let first6 := q5.memory.write 0 amountWord.toBytes
  have firstCarrier6 : ReconstructRegistersMemoryCarrier first6
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount pubkeyWithdrawalNode signatureNode
      signatureSecondNode 768 := by
    simpa only [first6] using
      hregisters5.writeBeforeSources 0 amountWord.toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  obtain ⟨q6, hp6, run6, memory6, storage6, code6⟩ :=
    reconstructPairSha_success_of_run
      (leftWord := 11) (rightWord := intermediateWord)
      (outputWord := intermediateWord)
      (left := amountWord) (right := signatureNode)
      (outputOffset := 704)
      hbubble hrev hpre hnodeleg5 hregisters5
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      (by
        simpa only [amountWord,
          show ((11 : B256) * 32).toNat = 352 by decide +kernel] using
          hregisters5.intermediate.node.source.readAmountPadded)
      (by
        simpa only [first6,
          show (intermediateWord * 32).toNat = 704 by
            decide +kernel] using firstCarrier6.intermediate.readIntermediate)
      hp5 (by simpa only [amountAndSignature] using run5)
  have pair6 := hregisters5.stagePair amountWord signatureNode (by omega)
  have hregisters6 : ReconstructRegistersMemoryCarrier q6.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount pubkeyWithdrawalNode amountSignatureNode
      signatureSecondNode 768 := by
    rw [memory6]
    exact pair6.registers.writeIntermediate amountSignatureNode (by omega)
  have hnodeleg6 : getDelegatedCodeAddress (q6.getCode 2) = none := by
    rw [code6]
    exact hnodeleg5
  let first7 := q6.memory.write 0 pubkeyWithdrawalNode.toBytes
  have firstCarrier7 : ReconstructRegistersMemoryCarrier first7
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount pubkeyWithdrawalNode amountSignatureNode
      signatureSecondNode 768 := by
    simpa only [first7] using
      hregisters6.writeBeforeSources 0 pubkeyWithdrawalNode.toBytes
        (by rw [B256.length_toBytes]; omega)
        (by rw [B256.length_toBytes]; omega)
  obtain ⟨q7, hp7, run7, memory7, storage7, code7⟩ :=
    reconstructPairSha_success_of_run
      (leftWord := nodeWord) (rightWord := intermediateWord)
      (outputWord := nodeWord)
      (left := pubkeyWithdrawalNode) (right := amountSignatureNode)
      (outputOffset := 640)
      hbubble hrev hpre hnodeleg6 hregisters6
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
      hregisters6.intermediate.node.readNode
      (by
        simpa only [first7,
          show (intermediateWord * 32).toNat = 704 by
            decide +kernel] using firstCarrier7.intermediate.readIntermediate)
      hp6 (by simpa only [finish] using run6)
  have pair7 :=
    hregisters6.stagePair pubkeyWithdrawalNode amountSignatureNode (by omega)
  have hregisters7 : ReconstructRegistersMemoryCarrier q7.memory
      pubkeyInput signatureFirst signatureTail withdrawal amountPadded
      oldCount amount depositNode amountSignatureNode signatureSecondNode
      768 := by
    rw [memory7]
    exact pair7.registers.writeNode depositNode (by omega)
  have modelEq : depositNode =
      depositDataNode Bytes.sha256 pubkey withdrawal signature
        (le64 amount.toNat) := by
    simpa only [pubkeyInput, signatureFirst, signatureTail, amountPadded,
      pubkeyNode, signatureFirstNode, signatureSecondNode, signatureNode,
      pubkeyWithdrawalNode, amountSignatureNode, depositNode] using
      reconstructedDepositNode_eq_model pubkey withdrawal signature
        (le64 amount.toNat) hwithdrawal (le64_length amount.toNat) hsignature
  refine ⟨q7, depositNode, amountSignatureNode, signatureSecondNode,
    hp7, run7, ?_, modelEq, ?_, ?_⟩
  · simpa only [pubkeyInput, signatureFirst, signatureTail, amountPadded]
      using (⟨hregisters7⟩ : Nonempty _)
  · calc
      Devm.getStor q7 = Devm.getStor q6 := storage7
      _ = Devm.getStor q5 := storage6
      _ = Devm.getStor q4 := storage5
      _ = Devm.getStor q3 := storage4
      _ = Devm.getStor q2 := storage3
      _ = Devm.getStor q1 := storage2
      _ = Devm.getStor pre := storage1
  · calc
      Devm.getCode q7 = Devm.getCode q6 := code7
      _ = Devm.getCode q5 := code6
      _ = Devm.getCode q4 := code5
      _ = Devm.getCode q3 := code4
      _ = Devm.getCode q2 := code3
      _ = Devm.getCode q1 := code2
      _ = Devm.getCode pre := code1

/-- Invert the fixed ABI-header portion of event staging.  Its one source-word
load is already covered by the 704-byte carrier, and the amount is retained as
the exact little-endian eight-byte payload written by `storeLe64At`. -/
theorem stageEventHeaders_success_of_run
    {sevm : Sevm} {pre post : Devm} {amount : B256}
    {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hmemory : pre.memory = eventPayloadMemory sevm.data amount)
    (run : Line.Run sevm pre
      ([pushB256 160] ++ mstoreAt 0 ++
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
        [pushB256 0] ++ mstoreAt 17) post) :
    tail <<+ post.stack ∧
      post.memory = eventBeforeCountMemory sevm.data amount ∧
      pre.state = post.state := by
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
  let c5 := c4.writeWordBefore 0 160 (by omega) (by omega)
  let c6 := c5.writeWordBefore 32 256 (by omega) (by omega)
  let c7 := c6.writeWordBefore 64 320 (by omega) (by omega)
  let c8 := c7.writeWordBefore 96 384 (by omega) (by omega)
  let c9 := c8.writeWordBefore 128 512 (by omega) (by omega)
  let c10 := c9.writeWordBefore 160 48 (by omega) (by omega)
  let c11 := c10.writeWordBefore 256 32 (by omega) (by omega)
  let c12 := c11.writeWordBefore 320 8 (by omega) (by omega)
  let c13 := c12.writeWordBefore 352 0 (by omega) (by omega)
  rcases of_run_append ([pushB256 160] ++ mstoreAt 0) run with
    ⟨s5, r5, run⟩
  obtain ⟨hp5, memory5', state5⟩ :=
    pushMstoreAt_success_of_run (offset := 0)
      (by decide +kernel) hp r5
  have memory5 : s5.memory = M5 := by
    rw [memory5', hmemory]
  rcases of_run_append ([pushB256 256] ++ mstoreAt 1) run with
    ⟨s6, r6, run⟩
  obtain ⟨hp6, memory6', state6⟩ :=
    pushMstoreAt_success_of_run (offset := 32)
      (by decide +kernel) hp5 r6
  have memory6 : s6.memory = M6 := by
    rw [memory6', memory5]
  rcases of_run_append ([pushB256 320] ++ mstoreAt 2) run with
    ⟨s7, r7, run⟩
  obtain ⟨hp7, memory7', state7⟩ :=
    pushMstoreAt_success_of_run (offset := 64)
      (by decide +kernel) hp6 r7
  have memory7 : s7.memory = M7 := by
    rw [memory7', memory6]
  rcases of_run_append ([pushB256 384] ++ mstoreAt 3) run with
    ⟨s8, r8, run⟩
  obtain ⟨hp8, memory8', state8⟩ :=
    pushMstoreAt_success_of_run (offset := 96)
      (by decide +kernel) hp7 r8
  have memory8 : s8.memory = M8 := by
    rw [memory8', memory7]
  rcases of_run_append ([pushB256 512] ++ mstoreAt 4) run with
    ⟨s9, r9, run⟩
  obtain ⟨hp9, memory9', state9⟩ :=
    pushMstoreAt_success_of_run (offset := 128)
      (by decide +kernel) hp8 r9
  have memory9 : s9.memory = M9 := by
    rw [memory9', memory8]
  rcases of_run_append ([pushB256 48] ++ mstoreAt 5) run with
    ⟨s10, r10, run⟩
  obtain ⟨hp10, memory10', state10⟩ :=
    pushMstoreAt_success_of_run (offset := 160)
      (by decide +kernel) hp9 r10
  have memory10 : s10.memory = M10 := by
    rw [memory10', memory9]
  rcases of_run_append ([pushB256 32] ++ mstoreAt 8) run with
    ⟨s11, r11, run⟩
  obtain ⟨hp11, memory11', state11⟩ :=
    pushMstoreAt_success_of_run (offset := 256)
      (by decide +kernel) hp10 r11
  have memory11 : s11.memory = M11 := by
    rw [memory11', memory10]
  rcases of_run_append ([pushB256 8] ++ mstoreAt 10) run with
    ⟨s12, r12, run⟩
  obtain ⟨hp12, memory12', state12⟩ :=
    pushMstoreAt_success_of_run (offset := 320)
      (by decide +kernel) hp11 r12
  have memory12 : s12.memory = M12 := by
    rw [memory12', memory11]
  rcases of_run_append ([pushB256 0] ++ mstoreAt 11) run with
    ⟨s13, r13, run⟩
  obtain ⟨hp13, memory13', state13⟩ :=
    pushMstoreAt_success_of_run (offset := 352)
      (by decide +kernel) hp12 r13
  have memory13 : s13.memory = M13 := by
    rw [memory13', memory12]
  rcases of_run_append
      (loadWord amountWord ++ storeLe64At 352) run with
    ⟨s14, amountLine, run⟩
  rcases of_run_append (loadWord amountWord) amountLine with
    ⟨afterLoad, loadRun, storeRun⟩
  obtain ⟨hpAmount, _wfAmount, _readsAmount, stateAmountLoad,
      memoryAmount⟩ :=
    of_run_loadWordAt_image_memory hp13
      (by rw [memory13]; exact c13.wf)
      (by rw [memory13]; exact c13.reads)
      (by
        rw [show (amountWord * 32 : B256).toNat = 672 by decide +kernel,
          c13.amount_read, B256.toB256_toBytes])
      loadRun
  have coveredAmount :
      s13.memory.extend (amountWord * 32).toNat 32 = s13.memory := by
    change (s13.memory.read (amountWord * 32).toNat 32).2 = s13.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [memory13, c13.size_eq]
    · rw [memory13, c13.size_eq]
      decide +kernel
  have memoryAfterLoad : afterLoad.memory = M13 := by
    rw [memoryAmount, coveredAmount, memory13]
  obtain ⟨hp14, memory14', stateAmountStore⟩ :=
    storeLe64At_success_of_run
      (address := (352 : B256)) (offset := 352)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      hpAmount storeRun
  have memory14 : s14.memory = M14 := by
    rw [memory14', memoryAfterLoad]
  rcases of_run_append ([pushB256 96] ++ mstoreAt 12) run with
    ⟨s15, r15, run⟩
  obtain ⟨hp15, memory15', state15⟩ :=
    pushMstoreAt_success_of_run (offset := 384)
      (by decide +kernel) hp14 r15
  have memory15 : s15.memory = M15 := by
    rw [memory15', memory14]
  rcases of_run_append ([pushB256 8] ++ mstoreAt 16) run with
    ⟨s16, r16, run⟩
  obtain ⟨hp16, memory16', state16⟩ :=
    pushMstoreAt_success_of_run (offset := 512)
      (by decide +kernel) hp15 r16
  have memory16 : s16.memory = M16 := by
    rw [memory16', memory15]
  obtain ⟨hp17, memory17, state17⟩ :=
    pushMstoreAt_success_of_run (offset := 544)
      (by decide +kernel) hp16 run
  have state : pre.state = post.state := by
    calc
      pre.state = s5.state := state5
      _ = s6.state := state6
      _ = s7.state := state7
      _ = s8.state := state8
      _ = s9.state := state9
      _ = s10.state := state10
      _ = s11.state := state11
      _ = s12.state := state12
      _ = s13.state := state13
      _ = afterLoad.state := stateAmountLoad
      _ = s14.state := stateAmountStore
      _ = s15.state := state15
      _ = s16.state := state16
      _ = post.state := state17
  refine ⟨hp17, ?_, state⟩
  rw [memory17, memory16]
  rfl

/-- A covered one-topic `logWith 0 0 18` consumes its known topic and leaves
the 576-byte read window's already-large memory unchanged. -/
theorem logWith0_success_of_run
    {sevm : Sevm} {pre post : Devm} {topic : B256}
    {tail : Stack}
    (hp : topic :: tail <<+ pre.stack)
    (hmod : pre.memory.size % 32 = 0)
    (hcovered : 576 ≤ pre.memory.size)
    (run : Line.Run sevm pre (logWith 0 0 18) post) :
    tail <<+ post.stack ∧ post.memory = pre.memory := by
  unfold logWith at run
  rcases Line.of_run_cons run with ⟨s1, sizeRun, run⟩
  rcases Line.of_run_cons run with ⟨s2, offsetRun, run⟩
  rcases Line.of_run_cons run with ⟨_, logRun, hnil⟩
  cases hnil
  have sizePush := of_run_pushB256 sizeRun
  have offsetPush := of_run_pushB256 offsetRun
  have hp1 : (18 * 32 : B256) :: topic :: tail <<+ s1.stack :=
    prefix_of_push sizePush hp
  have hp2 : (0 * 32 : B256) :: (18 * 32 : B256) ::
      topic :: tail <<+ s2.stack :=
    prefix_of_push offsetPush hp1
  obtain ⟨mi, sz, topics, hlen, hpop, memory⟩ :=
    of_run_log_mem_val logRun
  have known : ([0 * 32, 18 * 32, topic] : List B256) <<+
      s2.stack := by
    exact @pref_trans _ [0 * 32, 18 * 32, topic]
      ([0 * 32, 18 * 32, topic] ++ tail) _
      ⟨tail, rfl⟩ (by simpa using hp2)
  have words : ([0 * 32, 18 * 32, topic] : List B256) =
      mi :: sz :: topics :=
    List.pref_unique (by simp [hlen]) known (pref_of_split hpop)
  simp only [List.cons.injEq] at words
  rcases words with ⟨rfl, rfl, rfl⟩
  refine ⟨of_append_pref hpop (by simpa using hp2), ?_⟩
  rw [memory, ← offsetPush.memory, ← sizePush.memory,
    show (0 * 32 : B256).toNat = 0 by decide +kernel,
    show (18 * 32 : B256).toNat = 576 by decide +kernel]
  change (pre.memory.read 0 576).2 = pre.memory
  exact Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)

/-- Invert the old-count read and event emission.  The log payload itself is
not needed by the storage frame theorem; what matters here is that the count
comes from the target storage and that the complete event image survives the
covered `LOG1` read unchanged. -/
theorem stageEventCountLog_success_of_run
    {sevm : Sevm} {pre post : Devm} {amount : B256}
    {tail : Stack}
    (hp : tail <<+ pre.stack)
    (hmemory : pre.memory = eventBeforeCountMemory sevm.data amount)
    (run : Line.Run sevm pre
      ([pushB256 depositCountSlot, sload, dup 0] ++
        mstoreAt oldCountWord ++ storeLe64At 544 ++
        [pushB256 depositEventTopic] ++ logWith 0 0 18) post) :
    ∃ oldCount,
      oldCount =
        pre.getStorVal sevm.currentTarget depositCountSlot ∧
      tail <<+ post.stack ∧
      post.memory = depositEventMemory sevm.data amount oldCount ∧
      Devm.getStor post = Devm.getStor pre ∧
      Devm.getCode post = Devm.getCode pre := by
  have runAll := run
  have storage : Devm.getStor post = Devm.getStor pre :=
    (Line.of_inv Devm.getStor
      (by unfold mstoreAt storeLe64At logWith; line_inv) runAll).symm
  have code : Devm.getCode post = Devm.getCode pre :=
    (Line.of_inv Devm.getCode
      (by unfold mstoreAt storeLe64At logWith; line_inv) runAll).symm
  rcases of_run_append [pushB256 depositCountSlot, sload, dup 0] run with
    ⟨afterLoad, loadLine, run⟩
  have loadMemory : pre.memory = afterLoad.memory :=
    Line.of_inv Devm.memory (by line_inv) loadLine
  rcases Line.of_run_cons loadLine with
    ⟨afterSlot, slotRun, loadLine⟩
  rcases Line.of_run_cons loadLine with
    ⟨afterSload, sloadRun, loadLine⟩
  rcases Line.of_run_cons loadLine with
    ⟨_, dupRun, hnil⟩
  cases hnil
  have slotPush := of_run_pushB256 slotRun
  have hpSlot : depositCountSlot :: tail <<+ afterSlot.stack :=
    prefix_of_push slotPush hp
  obtain ⟨oldCount, hpLoad, oldCountEq'⟩ :=
    prefix_of_sload sloadRun hpSlot
  have hpDup : oldCount :: oldCount :: tail <<+ afterLoad.stack :=
    prefix_of_dup_val dupRun (Stack.Nth.head _ _) hpLoad
  have oldCountEq :
      oldCount = pre.getStorVal sevm.currentTarget depositCountSlot := by
    calc
      oldCount =
          afterSlot.getStorVal sevm.currentTarget depositCountSlot :=
        oldCountEq'
      _ = pre.getStorVal sevm.currentTarget depositCountSlot := by
        show (afterSlot.state.get sevm.currentTarget).stor.get
            depositCountSlot =
          (pre.state.get sevm.currentTarget).stor.get depositCountSlot
        rw [← slotPush.state]
  let M17 := eventBeforeCountMemory sevm.data amount
  let M18 := M17.write 576 oldCount.toBytes
  let M19 := storeLe64Memory M18 544 oldCount
  rcases of_run_append (mstoreAt oldCountWord) run with
    ⟨afterWord, wordRun, run⟩
  obtain ⟨hpWord, memoryWord⟩ :=
    of_run_mstoreAt_val wordRun hpDup
  have memory18 : afterWord.memory = M18 := by
    rw [memoryWord, ← loadMemory, hmemory,
      show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel]
  rcases of_run_append (storeLe64At 544) run with
    ⟨afterLe, leRun, run⟩
  obtain ⟨hpLe, memoryLe, _stateLe⟩ :=
    storeLe64At_success_of_run
      (address := (544 : B256)) (offset := 544)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      hpWord leRun
  have memory19 : afterLe.memory = M19 := by
    rw [memoryLe, memory18]
  have finalMemory :
      afterLe.memory = depositEventMemory sevm.data amount oldCount := by
    rw [memory19]
    exact (eventMemory_eq sevm.data amount oldCount).symm
  rcases of_run_append [pushB256 depositEventTopic] run with
    ⟨afterTopic, topicLine, logRun⟩
  rcases Line.of_run_cons topicLine with
    ⟨_, topicRun, topicNil⟩
  cases topicNil
  have topicPush := of_run_pushB256 topicRun
  have hpTopic : depositEventTopic :: tail <<+ afterTopic.stack :=
    prefix_of_push topicPush hpLe
  let c19 := depositEventMemory_carrier sevm.data amount oldCount
  obtain ⟨hpPost, logMemory⟩ :=
    logWith0_success_of_run hpTopic
      (by
        rw [← topicPush.memory, finalMemory, c19.size_eq])
      (by
        rw [← topicPush.memory, finalMemory, c19.size_eq]
        decide +kernel)
      logRun
  refine ⟨oldCount, oldCountEq, hpPost, ?_, storage, code⟩
  rw [logMemory, ← topicPush.memory, finalMemory]

/-- Invert the complete source event stage.  The returned old count is the
value read from the target contract before any persistent deposit update, and
the exact staged event image is carried into root reconstruction. -/
theorem stageDepositEvent_success_of_run
    {sevm : Sevm} {pre post : Devm} {amount : B256}
    {tail : Stack}
    (hdec0 : DynamicTailDecodable sevm.data 0)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hp : tail <<+ pre.stack)
    (hmemory : pre.memory = depositEventInputMemory sevm.data amount)
    (run : Line.Run sevm pre stageDepositEvent post) :
    ∃ oldCount,
      oldCount = pre.getStorVal sevm.currentTarget depositCountSlot ∧
      tail <<+ post.stack ∧
      post.memory = depositEventMemory sevm.data amount oldCount ∧
      Devm.getStor post = Devm.getStor pre ∧
      Devm.getCode post = Devm.getCode pre := by
  unfold stageDepositEvent at run
  rcases of_run_append
      ([pushB256 0] ++ mstoreAt 7 ++
        copyDynamicPayload 0 0 192 48 ++
        copyDynamicPayload 1 0 288 32 ++
        copyDynamicPayload 2 0 416 96) run with
    ⟨afterPayloads, payloadRun, run⟩
  obtain ⟨hpPayloads, payloadMemory, payloadState⟩ :=
    stageEventPayloads_success_of_run hdec0 hdec1 hdec2 hp hmemory
      payloadRun
  rcases of_run_append
      ([pushB256 160] ++ mstoreAt 0 ++
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
        [pushB256 0] ++ mstoreAt 17) run with
    ⟨afterHeaders, headerRun, countRun⟩
  obtain ⟨hpHeaders, headerMemory, headerState⟩ :=
    stageEventHeaders_success_of_run hpPayloads payloadMemory headerRun
  obtain ⟨oldCount, oldCountEq, hpPost, postMemory, postStorage,
      postCode⟩ :=
    stageEventCountLog_success_of_run hpHeaders headerMemory countRun
  refine ⟨oldCount, ?_, hpPost, postMemory, ?_, ?_⟩
  · calc
      oldCount =
          afterHeaders.getStorVal sevm.currentTarget depositCountSlot :=
        oldCountEq
      _ = pre.getStorVal sevm.currentTarget depositCountSlot := by
        show (afterHeaders.state.get sevm.currentTarget).stor.get
            depositCountSlot =
          (pre.state.get sevm.currentTarget).stor.get depositCountSlot
        rw [← headerState, ← payloadState]
  · calc
      Devm.getStor post = Devm.getStor afterHeaders := postStorage
      _ = Devm.getStor afterPayloads := by
        funext address
        exact (getStor_eq_of_state_eq headerState address).symm
      _ = Devm.getStor pre := by
        funext address
        exact (getStor_eq_of_state_eq payloadState address).symm
  · calc
      Devm.getCode post = Devm.getCode afterHeaders := postCode
      _ = Devm.getCode afterPayloads := by
        funext address
        exact (getCode_eq_of_state_eq headerState address).symm
      _ = Devm.getCode pre := by
        funext address
        exact (getCode_eq_of_state_eq payloadState address).symm

/-- A successful fall-through past a constant-error branch consumes the zero
selector and otherwise preserves the machine-local memory and world state. -/
theorem branchRevWith_success_of_prefix
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {flag : B256} {slot : Nat} {reason : String}
    {tail : Stack} {rest : Func}
    (hget : fs[slot]? = some (Func.revertWith reason))
    (hp : flag :: tail <<+ pre.stack)
    (run : Func.Run fs sevm pre ((.call slot) <?> rest) post) :
    flag = 0 ∧
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next rest post ∧
      next.memory = pre.memory ∧
      pre.state = next.state := by
  rcases of_run_branch_call_revertWith hget run with
    ⟨next, pop, restRun⟩
  exact ⟨(popBurn_pref pop hp).1.symm, next,
    (popBurn_pref pop hp).2, restRun, pop.memory.symm, pop.state⟩

/-- A successful reconstructed-root guard identifies the supplied argument
with the node register and reaches its continuation without changing state or
the insertion-start memory image. -/
theorem depositRootGuard_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount node : B256} {tail : Stack} {rest : Func}
    (hget : fs[rootMismatchErrorSlot]? =
      some (Func.revertWith rootMismatchReason))
    (hmem : InsertionStartMemoryCarrier pre.memory oldCount node)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (loadWord nodeWord +++ arg 3 +++ eq ::: iszero :::
        ((.call rootMismatchErrorSlot) <?> rest)) post) :
    Sevm.argWord sevm 3 = node ∧
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next rest post ∧
      Nonempty (InsertionStartMemoryCarrier next.memory oldCount node) ∧
      pre.state = next.state := by
  rcases of_run_prepend (loadWord nodeWord) _ run with
    ⟨afterLoad, loadRun, run⟩
  obtain ⟨hpLoad, _wfLoad, _readsLoad, stateLoad, memoryLoad⟩ :=
    of_run_loadWordAt_image_memory hp hmem.wf hmem.reads
      (by
        rw [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
          hmem.node_read, B256.toB256_toBytes])
      loadRun
  rcases of_run_prepend (arg 3 ++ [eq, iszero]) _ run with
    ⟨afterTest, testRun, branchRun⟩
  have testRunInv := testRun
  rcases of_run_append (arg 3) testRun with
    ⟨afterArg, argRun, testRun⟩
  have hpArg : Sevm.argWord sevm 3 :: node :: tail <<+
      afterArg.stack := prefix_of_arg hpLoad argRun
  rcases Line.of_run_cons testRun with ⟨afterEq, eqRun, testRun⟩
  have hpEq : (Sevm.argWord sevm 3 =? node) :: tail <<+
      afterEq.stack := prefix_of_eq eqRun hpArg
  rcases Line.of_run_cons testRun with ⟨_, zeroRun, nilRun⟩
  cases nilRun
  have hpTest : ((Sevm.argWord sevm 3 =? node) =? 0) :: tail <<+
      afterTest.stack := prefix_of_iszero zeroRun hpEq
  obtain ⟨hflag, next, hpNext, restRun, memoryNext, stateNext⟩ :=
    branchRevWith_success_of_prefix hget hpTest branchRun
  have hroot : Sevm.argWord sevm 3 = node := by
    by_contra hne
    simp [B256.eqCheck, hne] at hflag
    exact (by decide +kernel : (1 : B256) ≠ 0) hflag
  have covered :
      pre.memory.extend (nodeWord * 32).toNat 32 = pre.memory := by
    change (pre.memory.read (nodeWord * 32).toNat 32).2 = pre.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hmem.size_eq]
    · rw [hmem.size_eq]
      decide +kernel
  have memoryEq : next.memory = pre.memory := by
    rw [memoryNext,
      ← Line.of_inv Devm.memory (by unfold arg; line_inv) testRunInv,
      memoryLoad, covered]
  have nextCarrier :
      InsertionStartMemoryCarrier next.memory oldCount node := by
    rw [memoryEq]
    exact hmem
  refine ⟨hroot, next, hpNext, restRun, ⟨nextCarrier⟩, ?_⟩
  exact stateLoad.trans
    ((Line.of_inv Devm.state (by unfold arg; line_inv) testRunInv).trans
      stateNext)

/-- A successful capacity guard proves that the old count is below the final
admissible tree index and reaches the commit continuation unchanged. -/
theorem depositCapGuard_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount node : B256} {tail : Stack} {rest : Func}
    {reason : String}
    (hget : fs[treeFullErrorSlot]? = some (Func.revertWith reason))
    (hmem : InsertionStartMemoryCarrier pre.memory oldCount node)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (pushB256 (Nat.toB256 (2 ^ 32 - 1)) :::
        loadWord oldCountWord +++ lt ::: iszero :::
        ((.call treeFullErrorSlot) <?> rest)) post) :
    oldCount < Nat.toB256 (2 ^ 32 - 1) ∧
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next rest post ∧
      Nonempty (InsertionStartMemoryCarrier next.memory oldCount node) ∧
      pre.state = next.state := by
  rcases of_run_prepend [pushB256 (Nat.toB256 (2 ^ 32 - 1))] _ run with
    ⟨afterMax, maxLine, run⟩
  rcases Line.of_run_cons maxLine with ⟨_, maxRun, maxNil⟩
  cases maxNil
  have maxPush := of_run_pushB256 maxRun
  have hpMax : Nat.toB256 (2 ^ 32 - 1) :: tail <<+
      afterMax.stack := prefix_of_push maxPush hp
  rcases of_run_prepend (loadWord oldCountWord) _ run with
    ⟨afterLoad, loadRun, run⟩
  obtain ⟨hpLoad, _wfLoad, _readsLoad, stateLoad, memoryLoad⟩ :=
    of_run_loadWordAt_image_memory hpMax
      (by rw [← maxPush.memory]; exact hmem.wf)
      (by rw [← maxPush.memory]; exact hmem.reads)
      (by
        rw [show (oldCountWord * 32 : B256).toNat = 576 by decide +kernel,
          hmem.oldCount_read, B256.toB256_toBytes])
      loadRun
  rcases of_run_prepend [lt, iszero] _ run with
    ⟨afterTest, testRun, branchRun⟩
  have testRunInv := testRun
  rcases Line.of_run_cons testRun with ⟨afterLt, ltRun, testRun⟩
  have hpLt : (oldCount <? Nat.toB256 (2 ^ 32 - 1)) :: tail <<+
      afterLt.stack := prefix_of_lt ltRun hpLoad
  rcases Line.of_run_cons testRun with ⟨_, zeroRun, nilRun⟩
  cases nilRun
  have hpTest : ((oldCount <? Nat.toB256 (2 ^ 32 - 1)) =? 0) ::
      tail <<+ afterTest.stack := prefix_of_iszero zeroRun hpLt
  obtain ⟨hflag, next, hpNext, restRun, memoryNext, stateNext⟩ :=
    branchRevWith_success_of_prefix hget hpTest branchRun
  have hcap : oldCount < Nat.toB256 (2 ^ 32 - 1) := by
    by_contra hnot
    have hzero : (oldCount <? Nat.toB256 (2 ^ 32 - 1)) = 0 := by
      simp only [B256.ltCheck]
      rw [if_neg hnot]
    have hone :
        ((oldCount <? Nat.toB256 (2 ^ 32 - 1)) =? 0) = 1 := by
      rw [hzero]
      decide +kernel
    exact (by decide +kernel : (1 : B256) ≠ 0)
      (hone.symm.trans hflag)
  have covered :
      afterMax.memory.extend (oldCountWord * 32).toNat 32 =
        afterMax.memory := by
    change (afterMax.memory.read (oldCountWord * 32).toNat 32).2 =
      afterMax.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [← maxPush.memory, hmem.size_eq]
    · rw [← maxPush.memory, hmem.size_eq]
      decide +kernel
  have memoryEq : next.memory = pre.memory := by
    rw [memoryNext,
      ← Line.of_inv Devm.memory (by line_inv) testRunInv,
      memoryLoad, covered, ← maxPush.memory]
  have nextCarrier :
      InsertionStartMemoryCarrier next.memory oldCount node := by
    rw [memoryEq]
    exact hmem
  refine ⟨hcap, next, hpNext, restRun, ⟨nextCarrier⟩, ?_⟩
  exact maxPush.state.trans
    (stateLoad.trans
      ((Line.of_inv Devm.state (by line_inv) testRunInv).trans stateNext))

/-- Invert both successful post-reconstruction guards and expose the exact
commit entry state. -/
theorem depositSuccessGuards_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount node : B256} {tail : Stack} {treeReason : String}
    (hrootGet : fs[rootMismatchErrorSlot]? =
      some (Func.revertWith rootMismatchReason))
    (htreeGet : fs[treeFullErrorSlot]? =
      some (Func.revertWith treeReason))
    (hmem : InsertionStartMemoryCarrier pre.memory oldCount node)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre depositSuccessGuards post) :
    ∃ next,
      Sevm.argWord sevm 3 = node ∧
      oldCount < Nat.toB256 (2 ^ 32 - 1) ∧
      tail <<+ next.stack ∧
      Func.Run fs sevm next commitDeposit post ∧
      Nonempty (InsertionStartMemoryCarrier next.memory oldCount node) ∧
      pre.state = next.state := by
  unfold depositSuccessGuards at run
  obtain ⟨hroot, afterRoot, hpRoot, capRun, hmemRoot, stateRoot⟩ :=
    depositRootGuard_success_of_run hrootGet hmem hp run
  obtain ⟨hmemRoot⟩ := hmemRoot
  obtain ⟨hcap, next, hpNext, commitRun, hmemNext, stateCap⟩ :=
    depositCapGuard_success_of_run htreeGet hmemRoot hpRoot capRun
  exact ⟨next, hroot, hcap, hpNext, commitRun, hmemNext,
    stateRoot.trans stateCap⟩

/-- Invert the terminal insertion arm: the unique persistent effect is the
branch-slot write of the current accumulated node. -/
theorem insertionLive_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount : B256} {s : InsertionLoopState} {tail : Stack}
    (hmem : InsertionMemoryCarrier pre.memory oldCount s.size s.node)
    (hp : s.height :: tail <<+ pre.stack)
    (run : Func.Run fs sevm pre insertionLive post) :
    Devm.getStor post sevm.currentTarget =
      (Devm.getStor pre sevm.currentTarget).set s.key s.node := by
  unfold insertionLive at run
  rcases of_run_prepend [dup 0, pushB256 branchBase, add] _ run with
    ⟨afterKey, keyRun, run⟩
  have keyRunInv := keyRun
  rcases Line.of_run_cons keyRun with ⟨afterDup, dupRun, keyRun⟩
  have hpDup : s.height :: s.height :: tail <<+ afterDup.stack :=
    prefix_of_dup_val dupRun (Stack.Nth.head _ _) hp
  rcases Line.of_run_cons keyRun with ⟨afterBase, baseRun, keyRun⟩
  have hpBase : branchBase :: s.height :: s.height :: tail <<+
      afterBase.stack :=
    prefix_of_push (of_run_pushB256 baseRun) hpDup
  rcases Line.of_run_cons keyRun with ⟨_, addRun, keyNil⟩
  cases keyNil
  have hpKey : s.key :: s.height :: tail <<+ afterKey.stack := by
    simpa only [InsertionLoopState.key] using prefix_of_add addRun hpBase
  rcases of_run_prepend (loadWord nodeWord) _ run with
    ⟨afterLoad, loadRun, run⟩
  have hmemKey :
      InsertionMemoryCarrier afterKey.memory oldCount s.size s.node := by
    rw [← Line.of_inv Devm.memory (by line_inv) keyRunInv]
    exact hmem
  obtain ⟨hpLoad, _wfLoad, _readsLoad, _stateLoad, _memoryLoad⟩ :=
    of_run_loadWordAt_image_memory hpKey hmemKey.wf hmemKey.reads
      (by
        rw [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
          hmemKey.node_read, B256.toB256_toBytes])
      loadRun
  rcases of_run_next run with ⟨afterSwap, swapRun, run⟩
  have hswap : Stack.Swap (0 : Fin 16).val
      (s.node :: s.key :: s.height :: tail)
      (s.key :: s.node :: s.height :: tail) :=
    Stack.swapCore_zero
  have hpSwap : s.key :: s.node :: s.height :: tail <<+
      afterSwap.stack :=
    Stack.prefix_of_swap hswap (of_run_swap swapRun) hpLoad
  rcases of_run_next run with ⟨afterStore, storeRun, suffixRun⟩
  have stored : Devm.getStor afterStore sevm.currentTarget =
      (Devm.getStor afterSwap sevm.currentTarget).set s.key s.node :=
    sstore_getStor_set storeRun hpSwap
  have prefixStorage : Devm.getStor pre = Devm.getStor afterSwap :=
    (Line.of_inv Devm.getStor (by line_inv) keyRunInv).trans
      ((Line.of_inv Devm.getStor (by unfold loadWord; line_inv) loadRun).trans
        (Ninst.Hinv.inv (f := Devm.getStor) swapRun))
  have suffixStorage : Devm.getStor afterStore = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by func_inv) suffixRun
  calc
    Devm.getStor post sevm.currentTarget =
        Devm.getStor afterStore sevm.currentTarget := by
      rw [congrFun suffixStorage sevm.currentTarget]
    _ = (Devm.getStor afterSwap sevm.currentTarget).set s.key s.node :=
      stored
    _ = (Devm.getStor pre sevm.currentTarget).set s.key s.node := by
      rw [← congrFun prefixStorage sevm.currentTarget]

/-- Invert one dead insertion arm through its native SHA-256 call.  The
returned state is the exact continuation-call entry with the next node in
word 20; persistent storage is unchanged. -/
theorem insertionDeadStage_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount : B256} {s : InsertionLoopState} {tail : Stack}
    {stor : Stor}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (native : NativeShaEntry sevm pre)
    (hmem : InsertionMemoryCarrier pre.memory oldCount s.size s.node)
    (hstor : Devm.getStor pre sevm.currentTarget = stor)
    (hp : s.height :: tail <<+ pre.stack)
    (run : Func.Run fs sevm pre insertionDead post) :
    ∃ q,
      s.height :: tail <<+ q.stack ∧
      Func.Run fs sevm q (.call insertionContinuationSlot) post ∧
      Nonempty (InsertionMemoryCarrier q.memory oldCount s.size
        (hashPair Bytes.sha256 (stor.get s.key) s.node)) ∧
      NativeShaEntry sevm q ∧
      Devm.getStor q sevm.currentTarget = stor := by
  unfold insertionDead at run
  rcases of_run_prepend [dup 0, pushB256 branchBase, add, sload] _ run with
    ⟨afterLoad, loadLine, run⟩
  have loadLineInv := loadLine
  rcases Line.of_run_cons loadLine with ⟨afterDup, dupRun, loadLine⟩
  have hpDup : s.height :: s.height :: tail <<+ afterDup.stack :=
    prefix_of_dup_val dupRun (Stack.Nth.head _ _) hp
  rcases Line.of_run_cons loadLine with ⟨afterBase, baseRun, loadLine⟩
  have hpBase : branchBase :: s.height :: s.height :: tail <<+
      afterBase.stack :=
    prefix_of_push (of_run_pushB256 baseRun) hpDup
  rcases Line.of_run_cons loadLine with ⟨beforeLoad, addRun, loadLine⟩
  have hpKey : s.key :: s.height :: tail <<+ beforeLoad.stack := by
    simpa only [InsertionLoopState.key] using prefix_of_add addRun hpBase
  rcases Line.of_run_cons loadLine with ⟨_, sloadRun, loadNil⟩
  cases loadNil
  obtain ⟨left, hpLoad, leftEq⟩ := prefix_of_sload sloadRun hpKey
  have prefixStorage : Devm.getStor pre = Devm.getStor beforeLoad :=
    (Ninst.Hinv.inv (f := Devm.getStor) dupRun).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) baseRun).trans
        (Ninst.Hinv.inv (f := Devm.getStor) addRun))
  have leftEq' : left = stor.get s.key := by
    calc
      left = beforeLoad.getStorVal sevm.currentTarget s.key := leftEq
      _ = (Devm.getStor beforeLoad sevm.currentTarget).get s.key := rfl
      _ = (Devm.getStor pre sevm.currentTarget).get s.key := by
        rw [congrFun prefixStorage sevm.currentTarget]
      _ = stor.get s.key := by rw [hstor]
  have hpLoad' : stor.get s.key :: s.height :: tail <<+
      afterLoad.stack := by
    rw [← leftEq']
    exact hpLoad
  have loadMemory : pre.memory = afterLoad.memory :=
    Line.of_inv Devm.memory (by line_inv) loadLineInv
  rcases of_run_prepend (mstoreAt 0) _ run with
    ⟨afterLeft, leftRun, run⟩
  obtain ⟨hpLeft, leftMemory⟩ :=
    of_run_mstoreAt_val leftRun hpLoad'
  have leftCarrier : InsertionMemoryCarrier afterLeft.memory
      oldCount s.size s.node := by
    rw [leftMemory, ← loadMemory]
    exact hmem.writeBeforeRegisters 0 (stor.get s.key).toBytes
      (by rw [B256.length_toBytes]; omega)
      (by rw [B256.length_toBytes]; omega)
  rcases of_run_prepend (loadWord nodeWord ++ mstoreAt 1) _ run with
    ⟨afterPair, pairRun, shaRun⟩
  have nodeCovered :
      afterLeft.memory.extend (nodeWord * 32).toNat 32 =
        afterLeft.memory := by
    change (afterLeft.memory.read (nodeWord * 32).toNat 32).2 =
      afterLeft.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [leftCarrier.size_eq]
    · rw [leftCarrier.size_eq]
      decide +kernel
  obtain ⟨hpPair, pairMemory, _pairState⟩ :=
    loadMstore_success_of_run hpLeft leftCarrier.wf leftCarrier.reads
      (by
        rw [show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
          leftCarrier.node_read, B256.toB256_toBytes])
      nodeCovered (targetOffset := 32) (by decide +kernel) pairRun
  have pairCarrier : InsertionPairMemoryCarrier afterPair.memory oldCount
      s.size (stor.get s.key) s.node := by
    rw [pairMemory, leftMemory, ← loadMemory]
    exact hmem.stagePair
  have stageStorage : Devm.getStor pre = Devm.getStor afterPair :=
    (Line.of_inv Devm.getStor (by line_inv) loadLineInv).trans
      ((Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) leftRun).trans
        (Line.of_inv Devm.getStor
          (by unfold loadWord mstoreAt; line_inv) pairRun))
  have stageCode : Devm.getCode pre = Devm.getCode afterPair :=
    (Line.of_inv Devm.getCode (by line_inv) loadLineInv).trans
      ((Line.of_inv Devm.getCode (by unfold mstoreAt; line_inv) leftRun).trans
        (Line.of_inv Devm.getCode
          (by unfold loadWord mstoreAt; line_inv) pairRun))
  have nodelegPair :
      getDelegatedCodeAddress (afterPair.getCode 2) = none := by
    rw [← congrFun stageCode 2]
    exact native.nondelegated
  obtain ⟨q, hpQ, callRun, memoryQ, _returnQ, storageQ, codeQ⟩ :=
    sha64_success_of_run hbubble hrev native.precompile nodelegPair hpPair
      shaRun
  have shaCovered : afterPair.memory.extends
      [⟨0, 64⟩, ⟨640, 32⟩] = afterPair.memory := by
    apply Mem.extends_covered
    rw [pairCarrier.size_eq]
    decide +kernel
  have shaInput : (afterPair.memory.read 0 64).1 =
      (stor.get s.key).toBytes ++ s.node.toBytes := by
    change afterPair.memory.data.sliceD 0 64 0 =
      (stor.get s.key).toBytes ++ s.node.toBytes
    exact pairCarrier.shaInput
  have qMemory : q.memory = afterPair.memory.write 640
      (hashPair Bytes.sha256 (stor.get s.key) s.node).toBytes := by
    rw [show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      show (nodeWord * 32 : B256).toNat = 640 by decide +kernel,
      shaInput, shaCovered] at memoryQ
    simpa only [hashPair] using memoryQ
  have qCarrier : InsertionMemoryCarrier q.memory oldCount s.size
      (hashPair Bytes.sha256 (stor.get s.key) s.node) := by
    rw [qMemory]
    exact pairCarrier.finishHash
  have nativeQ : NativeShaEntry sevm q := by
    refine ⟨?_, native.precompile⟩
    rw [congrFun codeQ 2, ← congrFun stageCode 2]
    exact native.nondelegated
  have storageQ' : Devm.getStor q sevm.currentTarget = stor := by
    calc
      Devm.getStor q sevm.currentTarget =
          Devm.getStor afterPair sevm.currentTarget :=
        congrFun storageQ sevm.currentTarget
      _ = Devm.getStor pre sevm.currentTarget := by
        rw [congrFun stageStorage sevm.currentTarget]
      _ = stor := hstor
  exact ⟨q, hpQ, callRun, ⟨qCarrier⟩, nativeQ, storageQ'⟩

/-- Invert the dead-arm continuation: shift the size register, increment the
height, and expose the recursive loop call without changing storage. -/
theorem insertionContinuation_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount : B256} {s : InsertionLoopState} {tail : Stack}
    {stor : Stor}
    (hloop : fs[insertionLoopSlot]? = some insertionLoop)
    (native : NativeShaEntry sevm pre)
    (hmem : InsertionMemoryCarrier pre.memory oldCount s.size
      (s.step sevm.currentTarget stor).node)
    (hstor : Devm.getStor pre sevm.currentTarget = stor)
    (hp : s.height :: tail <<+ pre.stack)
    (run : Func.Run fs sevm pre insertionContinuation post) :
    ∃ q,
      (s.step sevm.currentTarget stor).height :: tail <<+ q.stack ∧
      Func.Run fs sevm q insertionLoop post ∧
      Nonempty (InsertionMemoryCarrier q.memory oldCount
        (s.step sevm.currentTarget stor).size
        (s.step sevm.currentTarget stor).node) ∧
      NativeShaEntry sevm q ∧
      Devm.getStor q sevm.currentTarget = stor := by
  unfold insertionContinuation at run
  rcases of_run_prepend (loadWord shiftedSizeWord) _ run with
    ⟨afterLoad, loadRun, run⟩
  obtain ⟨hpLoad, _wfLoad, _readsLoad, _stateLoad, loadMemory⟩ :=
    of_run_loadWordAt_image_memory hp hmem.wf hmem.reads
      (by
        rw [show (shiftedSizeWord * 32 : B256).toNat = 608 by
            decide +kernel,
          hmem.shiftedSize_read, B256.toB256_toBytes])
      loadRun
  have loadCovered : pre.memory.extend
      (shiftedSizeWord * 32).toNat 32 = pre.memory := by
    change (pre.memory.read (shiftedSizeWord * 32).toNat 32).2 = pre.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hmem.size_eq]
    · rw [hmem.size_eq]
      decide +kernel
  have loadMemoryEq : afterLoad.memory = pre.memory := by
    rw [loadMemory, loadCovered]
  rcases of_run_prepend [pushB256 1, shr] _ run with
    ⟨afterShift, shiftRun, run⟩
  have shiftRunInv := shiftRun
  rcases Line.of_run_cons shiftRun with
    ⟨afterOne, oneRun, shiftRun⟩
  have hpOne : (1 : B256) :: s.size :: s.height :: tail <<+
      afterOne.stack :=
    prefix_of_push (of_run_pushB256 oneRun) hpLoad
  rcases Line.of_run_cons shiftRun with
    ⟨_, shrRun, shiftNil⟩
  cases shiftNil
  have hpShift : (s.size >>> 1) :: s.height :: tail <<+
      afterShift.stack := prefix_of_shr shrRun hpOne
  have shiftMemory : afterLoad.memory = afterShift.memory :=
    Line.of_inv Devm.memory (by line_inv) shiftRunInv
  rcases of_run_prepend (mstoreAt shiftedSizeWord) _ run with
    ⟨afterStore, storeRun, run⟩
  obtain ⟨hpStore, storeMemory⟩ :=
    of_run_mstoreAt_val storeRun hpShift
  have storeCarrier : InsertionMemoryCarrier afterStore.memory oldCount
      (s.step sevm.currentTarget stor).size
      (s.step sevm.currentTarget stor).node := by
    rw [storeMemory, ← shiftMemory, loadMemoryEq,
      show (shiftedSizeWord * 32 : B256).toNat = 608 by decide +kernel]
    simpa only [InsertionLoopState.step] using
      hmem.writeShiftedSize (s.size >>> 1)
  rcases of_run_prepend [pushB256 1, add] _ run with
    ⟨afterAdd, addLine, callRun⟩
  have addLineInv := addLine
  rcases Line.of_run_cons addLine with ⟨afterOne, oneRun, addLine⟩
  have hpOne : (1 : B256) :: s.height :: tail <<+ afterOne.stack :=
    prefix_of_push (of_run_pushB256 oneRun) hpStore
  rcases Line.of_run_cons addLine with ⟨_, addRun, addNil⟩
  cases addNil
  have hpAdd : (1 + s.height) :: tail <<+ afterAdd.stack :=
    prefix_of_add addRun hpOne
  rcases of_run_call callRun with
    ⟨found, q, foundGet, burn, bodyRun⟩
  have foundEq : insertionLoop = found :=
    Option.some.inj (hloop.symm.trans foundGet)
  subst found
  have hpQ : (s.step sevm.currentTarget stor).height :: tail <<+
      q.stack := by
    have hpRaw : (1 + s.height) :: tail <<+ q.stack := by
      rw [← burn.stack]
      exact hpAdd
    simpa only [InsertionLoopState.step, B256.add_comm] using hpRaw
  have addMemory : afterStore.memory = afterAdd.memory :=
    Line.of_inv Devm.memory (by line_inv) addLineInv
  have qCarrier : InsertionMemoryCarrier q.memory oldCount
      (s.step sevm.currentTarget stor).size
      (s.step sevm.currentTarget stor).node := by
    rw [← burn.memory, ← addMemory]
    exact storeCarrier
  have prefixStorage : Devm.getStor pre = Devm.getStor q :=
    (Line.of_inv Devm.getStor (by unfold loadWord; line_inv) loadRun).trans
      ((Line.of_inv Devm.getStor (by line_inv) shiftRunInv).trans
        ((Line.of_inv Devm.getStor
            (by unfold mstoreAt; line_inv) storeRun).trans
          ((Line.of_inv Devm.getStor (by line_inv) addLineInv).trans
            (by
              funext address
              exact getStor_eq_of_state_eq burn.state address))))
  have prefixCode : Devm.getCode pre = Devm.getCode q :=
    (Line.of_inv Devm.getCode (by unfold loadWord; line_inv) loadRun).trans
      ((Line.of_inv Devm.getCode (by line_inv) shiftRunInv).trans
        ((Line.of_inv Devm.getCode
            (by unfold mstoreAt; line_inv) storeRun).trans
          ((Line.of_inv Devm.getCode (by line_inv) addLineInv).trans
            (by
              funext address
              exact getCode_eq_of_state_eq burn.state address))))
  have nativeQ : NativeShaEntry sevm q := by
    refine ⟨?_, native.precompile⟩
    rw [← congrFun prefixCode 2]
    exact native.nondelegated
  have storageQ : Devm.getStor q sevm.currentTarget = stor := by
    rw [← congrFun prefixStorage sevm.currentTarget]
    exact hstor
  exact ⟨q, hpQ, bodyRun, ⟨qCarrier⟩, nativeQ, storageQ⟩

/-- Invert the loop's low-bit test and expose exactly the selected source
arm, carrying the insertion image and native-SHA admission facts across the
dispatch machinery. -/
theorem insertionLoop_dispatch_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount : B256} {s : InsertionLoopState} {tail : Stack}
    {stor : Stor}
    (native : NativeShaEntry sevm pre)
    (hmem : InsertionMemoryCarrier pre.memory oldCount s.size s.node)
    (hstor : Devm.getStor pre sevm.currentTarget = stor)
    (hp : s.height :: tail <<+ pre.stack)
    (run : Func.Run fs sevm pre insertionLoop post) :
    (¬ s.live ∧
      ∃ q,
        s.height :: tail <<+ q.stack ∧
        Func.Run fs sevm q insertionDead post ∧
        Nonempty (InsertionMemoryCarrier q.memory oldCount s.size s.node) ∧
        NativeShaEntry sevm q ∧
        Devm.getStor q sevm.currentTarget = stor) ∨
    (s.live ∧
      ∃ q,
        s.height :: tail <<+ q.stack ∧
        Func.Run fs sevm q insertionLive post ∧
        Nonempty (InsertionMemoryCarrier q.memory oldCount s.size s.node) ∧
        NativeShaEntry sevm q ∧
        Devm.getStor q sevm.currentTarget = stor) := by
  unfold insertionLoop at run
  rcases of_run_prepend
      (loadWord shiftedSizeWord ++ [pushB256 1, Ninst.and]) _ run with
    ⟨afterBit, bitRun, branchRun⟩
  have bitRunInv := bitRun
  rcases of_run_append (loadWord shiftedSizeWord) bitRun with
    ⟨afterLoad, loadRun, bitRun⟩
  have bitTailRunInv := bitRun
  obtain ⟨hpLoad, _wfLoad, _readsLoad, _stateLoad, loadMemory⟩ :=
    of_run_loadWordAt_image_memory hp hmem.wf hmem.reads
      (by
        rw [show (shiftedSizeWord * 32 : B256).toNat = 608 by
            decide +kernel,
          hmem.shiftedSize_read, B256.toB256_toBytes])
      loadRun
  rcases Line.of_run_cons bitRun with ⟨afterOne, oneRun, bitRun⟩
  have hpOne : (1 : B256) :: s.size :: s.height :: tail <<+
      afterOne.stack :=
    prefix_of_push (of_run_pushB256 oneRun) hpLoad
  rcases Line.of_run_cons bitRun with ⟨_, andRun, bitNil⟩
  cases bitNil
  have hpBit : ((1 : B256) &&& s.size) :: s.height :: tail <<+
      afterBit.stack := prefix_of_and andRun hpOne
  have loadCovered : pre.memory.extend
      (shiftedSizeWord * 32).toNat 32 = pre.memory := by
    change (pre.memory.read (shiftedSizeWord * 32).toNat 32).2 = pre.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hmem.size_eq]
    · rw [hmem.size_eq]
      decide +kernel
  have bitMemory : afterBit.memory = pre.memory := by
    calc
      afterBit.memory = afterLoad.memory :=
        (Line.of_inv Devm.memory (by line_inv) bitTailRunInv).symm
      _ = pre.memory := by rw [loadMemory, loadCovered]
  have bitStorage : Devm.getStor pre = Devm.getStor afterBit :=
    Line.of_inv Devm.getStor
      (by unfold loadWord; line_inv) bitRunInv
  have bitCode : Devm.getCode pre = Devm.getCode afterBit :=
    Line.of_inv Devm.getCode
      (by unfold loadWord; line_inv) bitRunInv
  rcases of_run_branch branchRun with
    ⟨q, pop, deadRun⟩ |
      ⟨word, popped, q, wordNe, pop, burn, liveRun⟩
  · have flagZero : ((1 : B256) &&& s.size) = 0 :=
      (popBurn_pref pop hpBit).1.symm
    have dead : ¬ s.live := by
      intro live
      exact live flagZero
    have hpQ : s.height :: tail <<+ q.stack :=
      (popBurn_pref pop hpBit).2
    have qCarrier : InsertionMemoryCarrier q.memory oldCount
        s.size s.node := by
      rw [← pop.memory, bitMemory]
      exact hmem
    have qCode : Devm.getCode pre = Devm.getCode q :=
      bitCode.trans (by
        funext address
        exact getCode_eq_of_state_eq pop.state address)
    have nativeQ : NativeShaEntry sevm q := by
      refine ⟨?_, native.precompile⟩
      rw [← congrFun qCode 2]
      exact native.nondelegated
    have qStorage : Devm.getStor q sevm.currentTarget = stor := by
      calc
        Devm.getStor q sevm.currentTarget =
            Devm.getStor afterBit sevm.currentTarget := by
          rw [getStor_eq_of_state_eq pop.state sevm.currentTarget]
        _ = Devm.getStor pre sevm.currentTarget := by
          rw [congrFun bitStorage sevm.currentTarget]
        _ = stor := hstor
    exact Or.inl ⟨dead, q, hpQ, deadRun, ⟨qCarrier⟩,
      nativeQ, qStorage⟩
  · have combined : Devm.PopBurn [word] afterBit q :=
      Devm.popBurn_of_popBurn_of_pop pop burn
    have wordEq : word = ((1 : B256) &&& s.size) :=
      (popBurn_pref combined hpBit).1
    have live : s.live := by
      intro flagZero
      exact wordNe (wordEq.trans flagZero)
    have hpQ : s.height :: tail <<+ q.stack :=
      (popBurn_pref combined hpBit).2
    have qCarrier : InsertionMemoryCarrier q.memory oldCount
        s.size s.node := by
      rw [← combined.memory, bitMemory]
      exact hmem
    have qCode : Devm.getCode pre = Devm.getCode q :=
      bitCode.trans (by
        funext address
        exact getCode_eq_of_state_eq combined.state address)
    have nativeQ : NativeShaEntry sevm q := by
      refine ⟨?_, native.precompile⟩
      rw [← congrFun qCode 2]
      exact native.nondelegated
    have qStorage : Devm.getStor q sevm.currentTarget = stor := by
      calc
        Devm.getStor q sevm.currentTarget =
            Devm.getStor afterBit sevm.currentTarget := by
          rw [getStor_eq_of_state_eq combined.state sevm.currentTarget]
        _ = Devm.getStor pre sevm.currentTarget := by
          rw [congrFun bitStorage sevm.currentTarget]
        _ = stor := hstor
    exact Or.inr ⟨live, q, hpQ, liveRun, ⟨qCarrier⟩,
      nativeQ, qStorage⟩

/-- A successful loop run with a proved dead prefix and live endpoint has the
exact one-cell terminal storage update predicted by the insertion fold. -/
theorem insertionLoop_deadLive_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount : B256} {s : InsertionLoopState} {tail : Stack}
    {stor : Stor} {n : Nat}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hcontinuation : fs[insertionContinuationSlot]? =
      some insertionContinuation)
    (hloop : fs[insertionLoopSlot]? = some insertionLoop)
    (native : NativeShaEntry sevm pre)
    (hmem : InsertionMemoryCarrier pre.memory oldCount s.size s.node)
    (hstor : Devm.getStor pre sevm.currentTarget = stor)
    (hp : s.height :: tail <<+ pre.stack)
    (hdead : InsertionLoopDead sevm.currentTarget stor n s)
    (hlive : (insertionLoopIter sevm.currentTarget stor n s).live)
    (run : Func.Run fs sevm pre insertionLoop post) :
    Devm.getStor post sevm.currentTarget =
      stor.set
        (insertionLoopIter sevm.currentTarget stor n s).key
        (insertionLoopIter sevm.currentTarget stor n s).node := by
  induction n generalizing pre s with
  | zero =>
      have liveS : s.live := by
        simpa only [insertionLoopIter] using hlive
      rcases insertionLoop_dispatch_success_of_run native hmem hstor hp run with
        deadCase | liveCase
      · exact (deadCase.1 liveS).elim
      · rcases liveCase with
          ⟨_live, q, hpQ, liveRun, ⟨qMem⟩, _qNative, qStorage⟩
        have stored := insertionLive_success_of_run qMem hpQ liveRun
        rw [qStorage] at stored
        simpa only [insertionLoopIter] using stored
  | succ n ih =>
      change ¬ s.live ∧
        InsertionLoopDead sevm.currentTarget stor n
          (s.step sevm.currentTarget stor) at hdead
      have liveTail :
          (insertionLoopIter sevm.currentTarget stor n
            (s.step sevm.currentTarget stor)).live := by
        simpa only [insertionLoopIter] using hlive
      rcases insertionLoop_dispatch_success_of_run native hmem hstor hp run with
        deadCase | liveCase
      · rcases deadCase with
          ⟨_dead, q, hpQ, deadRun, ⟨qMem⟩, qNative, qStorage⟩
        obtain ⟨shaQ, hpSha, continuationCall, ⟨shaMem⟩,
            shaNative, shaStorage⟩ :=
          insertionDeadStage_success_of_run hbubble hrev qNative qMem
            qStorage hpQ deadRun
        rcases of_run_call continuationCall with
          ⟨found, continuationPre, foundGet, burn, continuationRun⟩
        have foundEq : insertionContinuation = found :=
          Option.some.inj (hcontinuation.symm.trans foundGet)
        subst found
        have hpContinuation : s.height :: tail <<+
            continuationPre.stack := by
          rw [← burn.stack]
          exact hpSha
        have memContinuation : InsertionMemoryCarrier
            continuationPre.memory oldCount s.size
              (s.step sevm.currentTarget stor).node := by
          rw [← burn.memory]
          simpa only [InsertionLoopState.step] using shaMem
        have nativeContinuation : NativeShaEntry sevm continuationPre := by
          refine ⟨?_, shaNative.precompile⟩
          rw [← getCode_eq_of_state_eq burn.state 2]
          exact shaNative.nondelegated
        have storageContinuation :
            Devm.getStor continuationPre sevm.currentTarget = stor := by
          calc
            Devm.getStor continuationPre sevm.currentTarget =
                Devm.getStor shaQ sevm.currentTarget := by
              rw [getStor_eq_of_state_eq burn.state sevm.currentTarget]
            _ = stor := shaStorage
        obtain ⟨next, hpNext, loopRun, ⟨nextMem⟩,
            nextNative, nextStorage⟩ :=
          insertionContinuation_success_of_run hloop nativeContinuation
            memContinuation storageContinuation hpContinuation continuationRun
        have result := ih nextNative nextMem nextStorage hpNext
          hdead.2 liveTail loopRun
        simpa only [insertionLoopIter] using result
      · exact (hdead.1 liveCase.1).elim

/-- Invert the complete commit: first write the incremented count, then run
the insertion loop through the supplied unique first-live height. -/
theorem commitDeposit_firstLive_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {oldCount node : B256} {tail : Stack} {size n : Nat}
    (hbubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hcontinuation : fs[insertionContinuationSlot]? =
      some insertionContinuation)
    (hloop : fs[insertionLoopSlot]? = some insertionLoop)
    (native : NativeShaEntry sevm pre)
    (hmem : InsertionStartMemoryCarrier pre.memory oldCount node)
    (hshift : oldCount + 1 = Nat.toB256 size)
    (hheight : n < 32)
    (hsize : size < 2 ^ 32)
    (hfirst : FirstLive size n)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre commitDeposit post) :
    Devm.getStor post sevm.currentTarget =
      ((Devm.getStor pre sevm.currentTarget).set depositCountSlot
        (oldCount + 1)).set (branchSlot n)
          (accumulatedNode Bytes.sha256
            (accOfStor
              ((Devm.getStor pre sevm.currentTarget).set depositCountSlot
                (oldCount + 1))).branch
            0 n node) := by
  unfold commitDeposit at run
  rcases of_run_prepend (loadWord oldCountWord) _ run with
    ⟨afterLoad, loadRun, run⟩
  obtain ⟨hpLoad, _wfLoad, _readsLoad, _stateLoad, loadMemory⟩ :=
    of_run_loadWordAt_image_memory hp hmem.wf hmem.reads
      (by
        rw [show (oldCountWord * 32 : B256).toNat = 576 by
            decide +kernel,
          hmem.oldCount_read, B256.toB256_toBytes])
      loadRun
  have loadCovered : pre.memory.extend
      (oldCountWord * 32).toNat 32 = pre.memory := by
    change (pre.memory.read (oldCountWord * 32).toNat 32).2 = pre.memory
    apply Mem.read_snd_eq_self
    apply memExtSize_of_le
    · rw [hmem.size_eq]
    · rw [hmem.size_eq]
      decide +kernel
  have loadMemoryEq : afterLoad.memory = pre.memory := by
    rw [loadMemory, loadCovered]
  rcases of_run_prepend [pushB256 1, add, dup 0] _ run with
    ⟨afterCount, countLine, run⟩
  have countLineInv := countLine
  rcases Line.of_run_cons countLine with ⟨afterOne, oneRun, countLine⟩
  have hpOne : (1 : B256) :: oldCount :: tail <<+ afterOne.stack :=
    prefix_of_push (of_run_pushB256 oneRun) hpLoad
  rcases Line.of_run_cons countLine with ⟨afterAdd, addRun, countLine⟩
  have hpAdd : (oldCount + 1) :: tail <<+ afterAdd.stack := by
    simpa only [B256.add_comm] using prefix_of_add addRun hpOne
  rcases Line.of_run_cons countLine with ⟨_, dupRun, countNil⟩
  cases countNil
  have hpCount : (oldCount + 1) :: (oldCount + 1) :: tail <<+
      afterCount.stack :=
    prefix_of_dup_val dupRun (Stack.Nth.head _ _) hpAdd
  rcases of_run_prepend (mstoreAt shiftedSizeWord) _ run with
    ⟨afterMemory, memoryRun, run⟩
  obtain ⟨hpMemory, memoryWrite⟩ :=
    of_run_mstoreAt_val memoryRun hpCount
  have countMemory : InsertionMemoryCarrier afterMemory.memory oldCount
      (oldCount + 1) node := by
    rw [memoryWrite,
      ← Line.of_inv Devm.memory (by line_inv) countLineInv,
      loadMemoryEq,
      show (shiftedSizeWord * 32 : B256).toNat = 608 by decide +kernel]
    exact hmem.writeShiftedSize (oldCount + 1)
  rcases of_run_prepend
      [pushB256 depositCountSlot, sstore, pushB256 0] _ run with
    ⟨afterZero, storeLine, loopCall⟩
  have storeLineInv := storeLine
  rcases Line.of_run_cons storeLine with
    ⟨beforeStore, slotRun, storeLine⟩
  have hpSlot : depositCountSlot :: (oldCount + 1) :: tail <<+
      beforeStore.stack :=
    prefix_of_push (of_run_pushB256 slotRun) hpMemory
  rcases Line.of_run_cons storeLine with
    ⟨afterStore, storeRun, storeLine⟩
  have hpStored : tail <<+ afterStore.stack :=
    prefix_of_sstore storeRun hpSlot
  have stored : Devm.getStor afterStore sevm.currentTarget =
      (Devm.getStor beforeStore sevm.currentTarget).set
        depositCountSlot (oldCount + 1) :=
    sstore_getStor_set storeRun hpSlot
  rcases Line.of_run_cons storeLine with ⟨_, zeroRun, storeNil⟩
  cases storeNil
  have hpZero : (0 : B256) :: tail <<+ afterZero.stack :=
    prefix_of_push (of_run_pushB256 zeroRun) hpStored
  rcases of_run_call loopCall with
    ⟨found, loopPre, foundGet, burn, loopRun⟩
  have foundEq : insertionLoop = found :=
    Option.some.inj (hloop.symm.trans foundGet)
  subst found
  have hpLoop : (Nat.toB256 0) :: tail <<+ loopPre.stack := by
    have hpRaw : (0 : B256) :: tail <<+ loopPre.stack := by
      rw [← burn.stack]
      exact hpZero
    simpa only [show Nat.toB256 0 = (0 : B256) by decide +kernel]
      using hpRaw
  have prefixStorage : Devm.getStor pre = Devm.getStor beforeStore :=
    (Line.of_inv Devm.getStor (by unfold loadWord; line_inv) loadRun).trans
      ((Line.of_inv Devm.getStor (by line_inv) countLineInv).trans
        ((Line.of_inv Devm.getStor
            (by unfold mstoreAt; line_inv) memoryRun).trans
          (Ninst.Hinv.inv (f := Devm.getStor) slotRun)))
  let countStor :=
    (Devm.getStor pre sevm.currentTarget).set depositCountSlot
      (oldCount + 1)
  have afterStoreStorage :
      Devm.getStor afterStore sevm.currentTarget = countStor := by
    dsimp only [countStor]
    rw [stored, ← congrFun prefixStorage sevm.currentTarget]
  have loopStorage :
      Devm.getStor loopPre sevm.currentTarget = countStor := by
    calc
      Devm.getStor loopPre sevm.currentTarget =
          Devm.getStor afterZero sevm.currentTarget := by
        rw [getStor_eq_of_state_eq burn.state sevm.currentTarget]
      _ = Devm.getStor afterStore sevm.currentTarget := by
        rw [← congrFun (Ninst.Hinv.inv (f := Devm.getStor) zeroRun)
          sevm.currentTarget]
      _ = countStor := afterStoreStorage
  have afterMemoryEq : afterMemory.memory = afterZero.memory :=
    Line.of_inv Devm.memory (by line_inv) storeLineInv
  have loopMemory : InsertionMemoryCarrier loopPre.memory oldCount
      (Nat.toB256 size) node := by
    rw [← burn.memory, ← afterMemoryEq, ← hshift]
    exact countMemory
  have prefixCode : Devm.getCode pre = Devm.getCode loopPre :=
    (Line.of_inv Devm.getCode (by unfold loadWord; line_inv) loadRun).trans
      ((Line.of_inv Devm.getCode (by line_inv) countLineInv).trans
        ((Line.of_inv Devm.getCode
            (by unfold mstoreAt; line_inv) memoryRun).trans
          ((Line.of_inv Devm.getCode (by line_inv) storeLineInv).trans
            (by
              funext address
              exact getCode_eq_of_state_eq burn.state address))))
  have loopNative : NativeShaEntry sevm loopPre := by
    refine ⟨?_, native.precompile⟩
    rw [← congrFun prefixCode 2]
    exact native.nondelegated
  let keys := loopPre.accessedStorageKeys
  let start := insertionNatState 0 size node keys
  have startMem : InsertionMemoryCarrier loopPre.memory oldCount
      start.size start.node := by
    simpa only [start, insertionNatState] using loopMemory
  have startStack : start.height :: tail <<+ loopPre.stack := by
    simpa only [start, insertionNatState] using hpLoop
  have deadPrefix : InsertionLoopDead sevm.currentTarget countStor n start := by
    simpa only [start] using
      insertionLoopDead_insertionNatState_of_firstLive
        sevm.currentTarget countStor n 0 size node keys
        (by omega) hsize hfirst
  have liveEndpoint :
      (insertionLoopIter sevm.currentTarget countStor n start).live := by
    simpa only [start] using
      insertionLoopIter_live_of_firstLive
        sevm.currentTarget countStor n 0 size node keys
        (by omega) hsize hfirst
  have loopResult := insertionLoop_deadLive_success_of_run
    hbubble hrev hcontinuation hloop loopNative startMem loopStorage
      startStack deadPrefix liveEndpoint loopRun
  have keyEq :
      (insertionLoopIter sevm.currentTarget countStor n start).key =
        branchSlot n := by
    simpa only [start, Nat.zero_add] using
      insertionLoopIter_key sevm.currentTarget countStor n 0 size node keys
        (by omega) hsize
  have nodeEq :
      (insertionLoopIter sevm.currentTarget countStor n start).node =
        accumulatedNode Bytes.sha256 (accOfStor countStor).branch
          0 n node := by
    simpa only [start] using
      insertionLoopIter_node sevm.currentTarget countStor n 0 size node keys
        (by omega)
  rw [keyEq, nodeEq] at loopResult
  simpa only [countStor] using loopResult

/-- One successful decoded-length guard identifies the loaded word and
retains the proof-carrying decoder image for the following guard. -/
private theorem depositLengthGuard_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {word expected actual : B256} {slot : Nat} {reason : String}
    {tail : Stack} {image : Bytes} {rest : Func}
    (hget : fs[slot]? = some (Func.revertWith reason))
    (hp : tail <<+ pre.stack)
    (hwf : Mem.Wf pre.memory)
    (hreads : Mem.Reads pre.memory image)
    (hmod : pre.memory.size % 32 = 0)
    (hcovered : (word * 32).toNat + 32 ≤ pre.memory.size)
    (hvalue : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = actual)
    (run : Func.Run fs sevm pre
      (loadWord word +++ pushB256 expected ::: eq ::: iszero :::
        ((.call slot) <?> rest)) post) :
    actual = expected ∧
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next rest post ∧
      Mem.Wf next.memory ∧
      Mem.Reads next.memory image ∧
      next.memory = pre.memory ∧
      pre.state = next.state := by
  rcases of_run_prepend (loadWord word) _ run with
    ⟨afterLoad, loadRun, run⟩
  obtain ⟨hpLoad, wfLoad, readsLoad, stateLoad, memoryLoad⟩ :=
    of_run_loadWordAt_image_memory hp hwf hreads hvalue loadRun
  rcases of_run_prepend [pushB256 expected, eq, iszero] _ run with
    ⟨afterTest, testRun, branchRun⟩
  have testRunInv := testRun
  rcases Line.of_run_cons testRun with ⟨afterPush, pushRun, testRun⟩
  have hpPush : expected :: actual :: tail <<+ afterPush.stack :=
    prefix_of_push (of_run_pushB256 pushRun) hpLoad
  rcases Line.of_run_cons testRun with ⟨afterEq, eqRun, testRun⟩
  have hpEq : (expected =? actual) :: tail <<+ afterEq.stack :=
    prefix_of_eq eqRun hpPush
  rcases Line.of_run_cons testRun with ⟨_, zeroRun, nilRun⟩
  cases nilRun
  have hpTest : ((expected =? actual) =? 0) :: tail <<+
      afterTest.stack := prefix_of_iszero zeroRun hpEq
  obtain ⟨hflag, next, hpNext, restRun, memoryNext, stateNext⟩ :=
    branchRevWith_success_of_prefix hget hpTest branchRun
  have heq : actual = expected := by
    by_contra hne
    have hne' : expected ≠ actual := Ne.symm hne
    simp [B256.eqCheck, hne'] at hflag
    exact (by decide +kernel : (1 : B256) ≠ 0) hflag
  have covered : pre.memory.extend (word * 32).toNat 32 = pre.memory := by
    change (pre.memory.read (word * 32).toNat 32).2 = pre.memory
    exact Mem.read_snd_eq_self (memExtSize_of_le hmod hcovered)
  have memoryEq : next.memory = pre.memory := by
    rw [memoryNext,
      ← Line.of_inv Devm.memory (by line_inv) testRunInv,
      memoryLoad, covered]
  refine ⟨heq, next, hpNext, restRun, ?_, ?_, memoryEq, ?_⟩
  · rw [memoryNext,
      ← Line.of_inv Devm.memory (by line_inv) testRunInv]
    exact wfLoad
  · rw [memoryNext,
      ← Line.of_inv Devm.memory (by line_inv) testRunInv]
    exact readsLoad
  · exact stateLoad.trans
      ((Line.of_inv Devm.state (by line_inv) testRunInv).trans stateNext)

/-- Successful fall-through of the lower-value guard. -/
private theorem depositValueLowerGuard_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {slot : Nat} {reason : String} {tail : Stack} {rest : Func}
    (hget : fs[slot]? = some (Func.revertWith reason))
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (pushB256 (Nat.toB256 oneEther) ::: callvalue ::: lt :::
        ((.call slot) <?> rest)) post) :
    Nat.toB256 oneEther ≤ sevm.value ∧
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next rest post ∧
      next.memory = pre.memory ∧
      pre.state = next.state := by
  rcases of_run_prepend
      [pushB256 (Nat.toB256 oneEther), callvalue, lt] _ run with
    ⟨afterTest, testRun, branchRun⟩
  have testRunInv := testRun
  rcases Line.of_run_cons testRun with ⟨afterPush, pushRun, testRun⟩
  have hpPush := prefix_of_push (of_run_pushB256 pushRun) hp
  rcases Line.of_run_cons testRun with ⟨afterValue, valueRun, testRun⟩
  have hpValue := prefix_of_push (of_run_callvalue valueRun) hpPush
  rcases Line.of_run_cons testRun with ⟨_, ltRun, nilRun⟩
  cases nilRun
  have hpTest : (sevm.value <? Nat.toB256 oneEther) :: tail <<+
      afterTest.stack := prefix_of_lt ltRun hpValue
  obtain ⟨hflag, next, hpNext, restRun, memoryNext, stateNext⟩ :=
    branchRevWith_success_of_prefix hget hpTest branchRun
  have hlower : Nat.toB256 oneEther ≤ sevm.value := by
    apply B256.not_lt.mp
    intro hlt
    have hone : (sevm.value <? Nat.toB256 oneEther) = 1 := by
      simp [B256.ltCheck, hlt]
    exact (by decide +kernel : (1 : B256) ≠ 0) (hone.symm.trans hflag)
  refine ⟨hlower, next, hpNext, restRun, ?_, ?_⟩
  · exact memoryNext.trans
      (Line.of_inv Devm.memory (by line_inv) testRunInv).symm
  · exact (Line.of_inv Devm.state (by line_inv) testRunInv).trans stateNext

/-- Successful fall-through of the exact-gwei-multiple guard. -/
private theorem depositGweiMultipleGuard_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {slot : Nat} {reason : String} {tail : Stack} {rest : Func}
    (hget : fs[slot]? = some (Func.revertWith reason))
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: mod :::
        ((.call slot) <?> rest)) post) :
    sevm.value % Nat.toB256 oneGwei = 0 ∧
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next rest post ∧
      next.memory = pre.memory ∧
      pre.state = next.state := by
  rcases of_run_prepend
      [pushB256 (Nat.toB256 oneGwei), callvalue, mod] _ run with
    ⟨afterTest, testRun, branchRun⟩
  have testRunInv := testRun
  rcases Line.of_run_cons testRun with ⟨afterPush, pushRun, testRun⟩
  have hpPush := prefix_of_push (of_run_pushB256 pushRun) hp
  rcases Line.of_run_cons testRun with ⟨afterValue, valueRun, testRun⟩
  have hpValue := prefix_of_push (of_run_callvalue valueRun) hpPush
  rcases Line.of_run_cons testRun with ⟨_, modRun, nilRun⟩
  cases nilRun
  have hpTest : (sevm.value % Nat.toB256 oneGwei) :: tail <<+
      afterTest.stack := prefix_of_mod modRun hpValue
  obtain ⟨hflag, next, hpNext, restRun, memoryNext, stateNext⟩ :=
    branchRevWith_success_of_prefix hget hpTest branchRun
  exact ⟨hflag, next, hpNext, restRun,
    memoryNext.trans (Line.of_inv Devm.memory (by line_inv) testRunInv).symm,
    (Line.of_inv Devm.state (by line_inv) testRunInv).trans stateNext⟩

/-- Successful fall-through of the upper-value guard retains the exact amount
word written for event staging. -/
private theorem depositAmountUpperGuard_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {slot : Nat} {reason : String} {tail : Stack} {rest : Func}
    (hget : fs[slot]? = some (Func.revertWith reason))
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (pushB256 (Nat.toB256 oneGwei) ::: callvalue ::: div ::: dup 0 :::
        mstoreAt amountWord +++
        pushB256 (Nat.toB256 (2 ^ 64 - 1)) ::: lt :::
        ((.call slot) <?> rest)) post) :
    let amount := sevm.value / Nat.toB256 oneGwei
    amount ≤ Nat.toB256 (2 ^ 64 - 1) ∧
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next rest post ∧
      next.memory = pre.memory.write 672 amount.toBytes ∧
      pre.state = next.state := by
  dsimp only
  rcases of_run_prepend
      [pushB256 (Nat.toB256 oneGwei), callvalue, div, dup 0] _ run with
    ⟨afterAmount, amountRun, run⟩
  have amountRunInv := amountRun
  rcases Line.of_run_cons amountRun with ⟨afterPush, pushRun, amountRun⟩
  have hpPush := prefix_of_push (of_run_pushB256 pushRun) hp
  rcases Line.of_run_cons amountRun with ⟨afterValue, valueRun, amountRun⟩
  have hpValue := prefix_of_push (of_run_callvalue valueRun) hpPush
  rcases Line.of_run_cons amountRun with ⟨afterDiv, divRun, amountRun⟩
  have hpDiv : (sevm.value / Nat.toB256 oneGwei) :: tail <<+
      afterDiv.stack := prefix_of_div divRun hpValue
  rcases Line.of_run_cons amountRun with ⟨_, dupRun, nilRun⟩
  cases nilRun
  have hpAmount : (sevm.value / Nat.toB256 oneGwei) ::
      (sevm.value / Nat.toB256 oneGwei) :: tail <<+ afterAmount.stack :=
    prefix_of_dup_val dupRun (Stack.Nth.head _ _) hpDiv
  rcases of_run_prepend (mstoreAt amountWord) _ run with
    ⟨afterStore, storeRun, run⟩
  obtain ⟨hpStored, memoryStored⟩ :=
    of_run_mstoreAt_val storeRun hpAmount
  rcases of_run_prepend
      [pushB256 (Nat.toB256 (2 ^ 64 - 1)), lt] _ run with
    ⟨afterTest, testRun, branchRun⟩
  have testRunInv := testRun
  rcases Line.of_run_cons testRun with ⟨afterMax, maxRun, testRun⟩
  have hpMax := prefix_of_push (of_run_pushB256 maxRun) hpStored
  rcases Line.of_run_cons testRun with ⟨_, ltRun, nilRun⟩
  cases nilRun
  have hpTest : (Nat.toB256 (2 ^ 64 - 1) <?
      (sevm.value / Nat.toB256 oneGwei)) :: tail <<+
      afterTest.stack := prefix_of_lt ltRun hpMax
  obtain ⟨hflag, next, hpNext, restRun, memoryNext, stateNext⟩ :=
    branchRevWith_success_of_prefix hget hpTest branchRun
  have hupper : sevm.value / Nat.toB256 oneGwei ≤
      Nat.toB256 (2 ^ 64 - 1) := by
    apply B256.not_lt.mp
    intro hlt
    have hone : (Nat.toB256 (2 ^ 64 - 1) <?
        (sevm.value / Nat.toB256 oneGwei)) = 1 := by
      simp only [B256.ltCheck]
      rw [if_pos hlt]
    exact (by decide +kernel : (1 : B256) ≠ 0) (hone.symm.trans hflag)
  refine ⟨hupper, next, hpNext, restRun, ?_, ?_⟩
  · rw [memoryNext,
      ← Line.of_inv Devm.memory (by line_inv) testRunInv,
      memoryStored,
      show (amountWord * 32 : B256).toNat = 672 by decide +kernel,
      ← Line.of_inv Devm.memory (by line_inv) amountRunInv]
  · exact (Line.of_inv Devm.state (by line_inv) amountRunInv).trans
      ((Line.of_inv Devm.state (by line_inv) storeRun).trans
        ((Line.of_inv Devm.state (by line_inv) testRunInv).trans stateNext))

/-- The source guard facts and the unique first-live height determine the
exact successful pure-model result used by the history bridge. -/
theorem deposit_ok_of_guard_facts
    (s : Acc) (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (value height : Nat)
    (hpubkey : pubkey.length = 48)
    (hwithdrawal : withdrawalCredentials.length = 32)
    (hsignature : signature.length = 96)
    (hlower : oneEther ≤ value)
    (hgwei : value % oneGwei = 0)
    (hupper : value / oneGwei ≤ 2 ^ 64 - 1)
    (hroot : depositDataNode Bytes.sha256 pubkey withdrawalCredentials
      signature (le64 (value / oneGwei)) = depositDataRoot)
    (hcap : s.count < 2 ^ 32 - 1)
    (hheight : height < 32)
    (hfirst : FirstLive (s.count + 1) height) :
    deposit Bytes.sha256 s pubkey withdrawalCredentials signature
      depositDataRoot value =
      .ok
        (⟨setSlot s.branch height
            (accumulatedNode Bytes.sha256 s.branch 0 height depositDataRoot),
            s.count + 1⟩,
          ⟨pubkey, withdrawalCredentials, le64 (value / oneGwei), signature,
            le64 s.count⟩) := by
  unfold deposit
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by simpa only [not_not] using hroot), if_neg (by omega),
    walk_eq_some_firstLive Bytes.sha256 s.branch
      (depositDataNode Bytes.sha256 pubkey withdrawalCredentials signature
        (le64 (value / oneGwei))) hheight hfirst]
  simp only [hroot, Nat.zero_add]

/-- A successful execution of the actual deposit endpoint extends the fixed
history baseline by exactly the reconstructed deposit-data node.  Every
source guard, native SHA boundary, and committing storage write is recovered
from the existing run; no model-success premise is assumed. -/
theorem depositEndpoint_history_success_of_run
    {baseline : List B256} {sevm : Sevm} {pre post : Devm}
    (native : NativeShaEntry sevm pre)
    (hmemory : pre.memory = Mem.empty)
    (history : HistoryExtends baseline
      (Devm.getStor pre sevm.currentTarget))
    (run : Func.Run (runtime.main :: aux) sevm pre depositEndpoint post) :
    HistoryExtends baseline (Devm.getStor post sevm.currentTarget) := by
  have hp : ([] : Stack) <<+ pre.stack := by
    simpa only [List.nil_append] using
      (pref_append ([] : Stack) pre.stack)
  unfold depositEndpoint at run
  obtain ⟨decoded, hdec, hpDecoded, bodyRun, decodedMemory,
      decodedStorage, decodedCode⟩ :=
    validateDepositAbi_success_of_run (fs := runtime.main :: aux)
      (body := depositBody) (by rfl) hp hmemory run
  have decodedCarrier :
      DepositDecodedMemoryCarrier decoded.memory sevm.data := by
    rw [decodedMemory]
    exact depositDecodedMemory_carrier sevm.data
  unfold depositBody at bodyRun
  obtain ⟨hlen0, afterLen0, hpLen0, bodyRun, _wf0, _reads0,
      memoryLen0, stateLen0⟩ :=
    depositLengthGuard_success_of_run
      (fs := runtime.main :: aux) (word := 3) (expected := 48)
      (actual := depositLengthWord sevm.data 0)
      (slot := pubkeyLengthErrorSlot) (by rfl) hpDecoded
      decodedCarrier.wf decodedCarrier.reads
      (by rw [decodedCarrier.size_eq])
      (by rw [decodedCarrier.size_eq]; decide +kernel)
      (by
        rw [show (3 * 32 : B256).toNat = 96 by decide +kernel,
          decodedCarrier.length0_read, B256.toB256_toBytes])
      bodyRun
  have carrierLen0 :
      DepositDecodedMemoryCarrier afterLen0.memory sevm.data := by
    rw [memoryLen0]
    exact decodedCarrier
  obtain ⟨hlen1, afterLen1, hpLen1, bodyRun, _wf1, _reads1,
      memoryLen1, stateLen1⟩ :=
    depositLengthGuard_success_of_run
      (fs := runtime.main :: aux) (word := 4) (expected := 32)
      (actual := depositLengthWord sevm.data 1)
      (slot := withdrawalLengthErrorSlot) (by rfl) hpLen0
      carrierLen0.wf carrierLen0.reads
      (by rw [carrierLen0.size_eq])
      (by rw [carrierLen0.size_eq]; decide +kernel)
      (by
        rw [show (4 * 32 : B256).toNat = 128 by decide +kernel,
          carrierLen0.length1_read, B256.toB256_toBytes])
      bodyRun
  have carrierLen1 :
      DepositDecodedMemoryCarrier afterLen1.memory sevm.data := by
    rw [memoryLen1]
    exact carrierLen0
  obtain ⟨hlen2, afterLen2, hpLen2, bodyRun, _wf2, _reads2,
      memoryLen2, stateLen2⟩ :=
    depositLengthGuard_success_of_run
      (fs := runtime.main :: aux) (word := 5) (expected := 96)
      (actual := depositLengthWord sevm.data 2)
      (slot := signatureLengthErrorSlot) (by rfl) hpLen1
      carrierLen1.wf carrierLen1.reads
      (by rw [carrierLen1.size_eq])
      (by rw [carrierLen1.size_eq]; decide +kernel)
      (by
        rw [show (5 * 32 : B256).toNat = 160 by decide +kernel,
          carrierLen1.length2_read, B256.toB256_toBytes])
      bodyRun
  obtain ⟨hlower, afterLower, hpLower, bodyRun, memoryLower,
      stateLower⟩ :=
    depositValueLowerGuard_success_of_run
      (fs := runtime.main :: aux) (slot := valueTooLowErrorSlot)
      (by rfl) hpLen2 bodyRun
  obtain ⟨hgwei, afterGwei, hpGwei, bodyRun, memoryGwei, stateGwei⟩ :=
    depositGweiMultipleGuard_success_of_run
      (fs := runtime.main :: aux) (slot := valueNotGweiErrorSlot)
      (by rfl) hpLower bodyRun
  obtain ⟨hupper, afterUpper, hpUpper, suffixRun, memoryUpper,
      stateUpper⟩ :=
    depositAmountUpperGuard_success_of_run
      (fs := runtime.main :: aux) (slot := valueTooHighErrorSlot)
      (by rfl) hpGwei bodyRun
  let amount := sevm.value / Nat.toB256 oneGwei
  have upperMemory :
      afterUpper.memory = depositEventInputMemory sevm.data amount := by
    rw [memoryUpper, memoryGwei, memoryLower, memoryLen2, memoryLen1,
      memoryLen0, decodedMemory]
    rfl
  rcases of_run_prepend stageDepositEvent depositAfterEvent suffixRun with
    ⟨staged, eventRun, afterEventRun⟩
  obtain ⟨oldCount, oldCountEq, hpStaged, stagedMemory, stagedStorage,
      stagedCode⟩ :=
    stageDepositEvent_success_of_run hdec.pubkeyTail
      hdec.withdrawalCredentialsTail hdec.signatureTail hpUpper upperMemory
      eventRun
  have hpubkey : (dynamicPayload sevm.data 0).length = 48 := by
    have h := congrArg B256.toNat hlen0
    rw [depositLengthWord_toNat (by
      have := hdec.pubkeyTail.2.2.1
      omega),
      show (48 : B256).toNat = 48 by decide +kernel] at h
    simpa only [dynamicPayload, List.length_sliceD] using h
  have hwithdrawal : (dynamicPayload sevm.data 1).length = 32 := by
    have h := congrArg B256.toNat hlen1
    rw [depositLengthWord_toNat (by
      have := hdec.withdrawalCredentialsTail.2.2.1
      omega),
      show (32 : B256).toNat = 32 by decide +kernel] at h
    simpa only [dynamicPayload, List.length_sliceD] using h
  have hsignature : (dynamicPayload sevm.data 2).length = 96 := by
    have h := congrArg B256.toNat hlen2
    rw [depositLengthWord_toNat (by
      have := hdec.signatureTail.2.2.1
      omega),
      show (96 : B256).toNat = 96 by decide +kernel] at h
    simpa only [dynamicPayload, List.length_sliceD] using h
  have stagedCarrier : DepositEventMemoryCarrier staged.memory
      (stagedDepositEvent sevm.data amount oldCount) amount oldCount := by
    rw [stagedMemory]
    exact depositEventMemory_carrier sevm.data amount oldCount
  have source := stagedCarrier.toDecodedReconstructSource hdec
    hpubkey hwithdrawal hsignature
  have reconstructRun : Func.Run (runtime.main :: aux) sevm staged
      (reconstructDepositDataNode depositSuccessGuards) post := by
    simpa only [depositAfterEvent, depositSuccessGuards] using afterEventRun
  have afterUpperStoragePre :
      Devm.getStor afterUpper = Devm.getStor pre := by
    calc
      Devm.getStor afterUpper = Devm.getStor afterGwei := by
        funext a
        exact (getStor_eq_of_state_eq stateUpper a).symm
      _ = Devm.getStor afterLower := by
        funext a
        exact (getStor_eq_of_state_eq stateGwei a).symm
      _ = Devm.getStor afterLen2 := by
        funext a
        exact (getStor_eq_of_state_eq stateLower a).symm
      _ = Devm.getStor afterLen1 := by
        funext a
        exact (getStor_eq_of_state_eq stateLen2 a).symm
      _ = Devm.getStor afterLen0 := by
        funext a
        exact (getStor_eq_of_state_eq stateLen1 a).symm
      _ = Devm.getStor decoded := by
        funext a
        exact (getStor_eq_of_state_eq stateLen0 a).symm
      _ = Devm.getStor pre := decodedStorage
  have stagedStoragePre : Devm.getStor staged = Devm.getStor pre :=
    stagedStorage.trans afterUpperStoragePre
  have stagedCodePre : Devm.getCode staged = Devm.getCode pre := by
    calc
      Devm.getCode staged = Devm.getCode afterUpper := stagedCode
      _ = Devm.getCode afterGwei := by
        funext a
        exact (getCode_eq_of_state_eq stateUpper a).symm
      _ = Devm.getCode afterLower := by
        funext a
        exact (getCode_eq_of_state_eq stateGwei a).symm
      _ = Devm.getCode afterLen2 := by
        funext a
        exact (getCode_eq_of_state_eq stateLower a).symm
      _ = Devm.getCode afterLen1 := by
        funext a
        exact (getCode_eq_of_state_eq stateLen2 a).symm
      _ = Devm.getCode afterLen0 := by
        funext a
        exact (getCode_eq_of_state_eq stateLen1 a).symm
      _ = Devm.getCode decoded := by
        funext a
        exact (getCode_eq_of_state_eq stateLen0 a).symm
      _ = Devm.getCode pre := decodedCode
  have stagedNative : NativeShaEntry sevm staged := by
    refine ⟨?_, native.precompile⟩
    rw [congrFun stagedCodePre 2]
    exact native.nondelegated
  obtain ⟨afterReconstruct, depositNode, amountSignatureNode,
      signatureSecondNode, hpReconstruct, guardsRun, registers, nodeEq,
      reconstructStorage, reconstructCode⟩ :=
    reconstructDepositDataNode_success_of_run
      (fs := runtime.main :: aux) (by rfl) (by rfl)
      stagedNative.precompile stagedNative.nondelegated
      hwithdrawal hsignature source hpStaged reconstructRun
  obtain ⟨registers⟩ := registers
  obtain ⟨commitPre, hroot, hcap, hpCommit, commitRun, startMemory,
      guardsState⟩ :=
    depositSuccessGuards_success_of_run
      (fs := runtime.main :: aux) (by rfl) (by rfl)
      registers.toInsertionStart hpReconstruct guardsRun
  obtain ⟨startMemory⟩ := startMemory
  have commitStoragePre :
      Devm.getStor commitPre = Devm.getStor pre := by
    calc
      Devm.getStor commitPre = Devm.getStor afterReconstruct := by
        funext a
        exact (getStor_eq_of_state_eq guardsState a).symm
      _ = Devm.getStor staged := reconstructStorage
      _ = Devm.getStor pre := stagedStoragePre
  have commitCodePre : Devm.getCode commitPre = Devm.getCode pre := by
    calc
      Devm.getCode commitPre = Devm.getCode afterReconstruct := by
        funext a
        exact (getCode_eq_of_state_eq guardsState a).symm
      _ = Devm.getCode staged := reconstructCode
      _ = Devm.getCode pre := stagedCodePre
  have commitNative : NativeShaEntry sevm commitPre := by
    refine ⟨?_, native.precompile⟩
    rw [congrFun commitCodePre 2]
    exact native.nondelegated
  have oldCountPre :
      oldCount = pre.getStorVal sevm.currentTarget depositCountSlot := by
    calc
      oldCount =
          afterUpper.getStorVal sevm.currentTarget depositCountSlot :=
        oldCountEq
      _ = pre.getStorVal sevm.currentTarget depositCountSlot := by
        change (Devm.getStor afterUpper sevm.currentTarget).get
            depositCountSlot =
          (Devm.getStor pre sevm.currentTarget).get depositCountSlot
        rw [congrFun afterUpperStoragePre sevm.currentTarget]
  let model := accOfStor (Devm.getStor pre sevm.currentTarget)
  have oldCountModel : oldCount.toNat = model.count := by
    change oldCount.toNat =
      (pre.getStorVal sevm.currentTarget depositCountSlot).toNat
    rw [oldCountPre]
  have hcapNat : oldCount.toNat < 2 ^ 32 - 1 := by
    have h := (B256.lt_iff_toNat_lt_toNat).mp hcap
    rw [B256.toNat_toB256_of_lt (by omega)] at h
    exact h
  obtain ⟨height, ⟨hheight, hfirst⟩, _unique⟩ :=
    firstLive_existsUnique (oldCount.toNat + 1) (by omega) (by omega)
  have hshift :
      oldCount + 1 = Nat.toB256 (oldCount.toNat + 1) := by
    have h := Blanc.toB256_add_one_of_lt oldCount.toNat (by omega)
    rw [Jaune.toB256_toNat oldCount] at h
    exact h
  have postStorage := commitDeposit_firstLive_success_of_run
    (fs := runtime.main :: aux) (by rfl) (by rfl) (by rfl) (by rfl)
    commitNative startMemory hshift hheight (by omega) hfirst hpCommit
    commitRun
  have hdenNe : Nat.toB256 oneGwei ≠ 0 := by
    intro hzero
    have h := congrArg B256.toNat hzero
    rw [B256.toNat_toB256_of_lt (by norm_num [oneGwei])] at h
    simp only [B256.toNat_zero] at h
    norm_num [oneGwei] at h
  have hdenNat : (Nat.toB256 oneGwei).toNat = oneGwei :=
    B256.toNat_toB256_of_lt (by norm_num [oneGwei])
  have amountNat : amount.toNat = sevm.value.toNat / oneGwei := by
    dsimp only [amount]
    rw [B256.toNat_div hdenNe, hdenNat]
  have lowerNat : oneEther ≤ sevm.value.toNat := by
    have h := (B256.le_iff_toNat_le_toNat).mp hlower
    rw [B256.toNat_toB256_of_lt (by norm_num [oneEther])] at h
    exact h
  have gweiNat : sevm.value.toNat % oneGwei = 0 := by
    have h := congrArg B256.toNat hgwei
    rw [B256.toNat_mod hdenNe, hdenNat, B256.toNat_zero] at h
    exact h
  have upperNat : sevm.value.toNat / oneGwei ≤ 2 ^ 64 - 1 := by
    have h := (B256.le_iff_toNat_le_toNat).mp hupper
    rw [B256.toNat_toB256_of_lt (by omega), amountNat] at h
    exact h
  have argRoot :
      Sevm.argWord sevm 3 = calldataWord sevm.data 100 := by
    unfold Sevm.argWord
    rw [show 32 * (3 : B256) + 4 = Nat.toB256 100 by decide +kernel,
      dataWord_toB256 (by omega)]
  have depositNodeRoot :
      depositNode = calldataWord sevm.data 100 :=
    hroot.symm.trans argRoot
  have modelRoot :
      depositDataNode Bytes.sha256 (dynamicPayload sevm.data 0)
          (dynamicPayload sevm.data 1) (dynamicPayload sevm.data 2)
          (le64 (sevm.value.toNat / oneGwei)) =
        calldataWord sevm.data 100 := by
    rw [← amountNat]
    exact nodeEq.symm.trans depositNodeRoot
  have firstModel : FirstLive (model.count + 1) height := by
    rw [← oldCountModel]
    exact hfirst
  have heightModel : model.count < 2 ^ 32 - 1 := by
    rw [← oldCountModel]
    exact hcapNat
  have modelSuccess := deposit_ok_of_guard_facts model
    (dynamicPayload sevm.data 0) (dynamicPayload sevm.data 1)
    (dynamicPayload sevm.data 2) (calldataWord sevm.data 100)
    sevm.value.toNat height hpubkey hwithdrawal hsignature lowerNat gweiNat
    upperNat modelRoot heightModel hheight firstModel
  have oldCountWord : oldCount = Nat.toB256 model.count := by
    rw [← oldCountModel, Jaune.toB256_toNat]
  have exactPost :
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set depositCountSlot
          (Nat.toB256 model.count + 1)).set (branchSlot height)
            (accumulatedNode Bytes.sha256
              (accOfStor
                ((Devm.getStor pre sevm.currentTarget).set depositCountSlot
                  (Nat.toB256 model.count + 1))).branch
              0 height (calldataWord sevm.data 100)) := by
    rw [congrFun commitStoragePre sevm.currentTarget, oldCountWord,
      depositNodeRoot] at postStorage
    exact postStorage
  rcases history with ⟨suffix, artifact⟩
  refine ⟨suffix ++
    [depositDataNode Bytes.sha256 (dynamicPayload sevm.data 0)
      (dynamicPayload sevm.data 1) (dynamicPayload sevm.data 2)
      (le64 (sevm.value.toNat / oneGwei))], ?_⟩
  have preserved := ArtifactInv.of_depositSuccessStorage artifact
    modelSuccess hheight firstModel exactPost
  simpa only [List.append_assoc] using preserved

end Blanc.BeaconDeposit
