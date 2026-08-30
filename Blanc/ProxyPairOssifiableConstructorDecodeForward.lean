import Blanc.ProxyPairOssifiableConstructorInitializeForward
import Blanc.ProxyPairOssifiableArtifacts

/-!
# OssifiableProxy canonical constructor forward execution

This module constructs the successful canonical empty-data constructor walk
from the actual appended ABI bytes.  It executes every strict decoder guard
and memory copy, composes the decoded image with implementation/admin
initialization, then lifts the result through the nonpayable main-function
guard and whole-program entry.  No total evaluator or semantic shortcut is
used.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

private def decodeForwardHeadMemory (sevm : Sevm) : Mem :=
  Mem.empty.write 0 (sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop))

private def decodeForwardPointerMemory (sevm : Sevm) : Mem :=
  (decodeForwardHeadMemory sevm).write 96 (Nat.toB256 3533).toBytes

private def decodeForwardLengthMemory (sevm : Sevm) : Mem :=
  (decodeForwardPointerMemory sevm).write 128
    (sevm.code.sliceD 3533 32 (Linst.toUInt8 .stop))

private def decodeForwardHeadImage (sevm : Sevm) : Bytes :=
  Bytes.writeAt [] 0 (sevm.code.toList.sliceD 3437 96 0)

private def decodeForwardPointerImage (sevm : Sevm) : Bytes :=
  Bytes.writeAt (decodeForwardHeadImage sevm) 96
    (Nat.toB256 3533).toBytes

private def decodeForwardLengthImage (sevm : Sevm) : Bytes :=
  Bytes.writeAt (decodeForwardPointerImage sevm) 128
    (sevm.code.toList.sliceD 3533 32 0)

private theorem Mem.size_write_of_lt {memory : Mem} {offset : Nat}
    {bytes : Bytes} (hne : bytes ≠ [])
    (hlt : memory.size < offset + bytes.length) :
    (memory.write offset bytes).size = ceil32 (offset + bytes.length) := by
  rcases bytes with _ | ⟨byte, bytes⟩
  · exact absurd rfl hne
  · simp only [Mem.write]
    rw [if_neg (by simpa only [List.length_cons] using Nat.not_le.mpr hlt)]

private theorem decodeForwardHeadMemory_size (sevm : Sevm) :
    (decodeForwardHeadMemory sevm).size = 96 := by
  unfold decodeForwardHeadMemory
  have hlength := ByteArray.length_sliceD sevm.code 3437 96
    (Linst.toUInt8 .stop)
  have hne : sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop) ≠ [] := by
    intro hnil
    rw [hnil] at hlength
    simp at hlength
  have hlt : Mem.empty.size < 0 +
      (sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop)).length := by
    rw [hlength]
    decide
  rw [Mem.size_write_of_lt hne hlt, hlength]
  decide

private theorem decodeForwardHeadMemory_wf (sevm : Sevm) :
    Mem.Wf (decodeForwardHeadMemory sevm) := by
  exact Mem.Wf.write Mem.wf_empty 0
    (sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop))

private theorem decodeForwardHeadMemory_reads (sevm : Sevm) :
    Mem.Reads (decodeForwardHeadMemory sevm) (decodeForwardHeadImage sevm) := by
  have hread := Mem.Reads.write Mem.wf_empty Mem.reads_empty 0
    (sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop))
  simpa [decodeForwardHeadMemory, decodeForwardHeadImage,
    ByteArray.sliceD_eq, show Linst.toUInt8 .stop = 0 by decide] using hread

private theorem decodeForwardHeadImage_implementation
    {sevm : Sevm} {implementation : Adr}
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256) :
    Bytes.toB256 ((decodeForwardHeadImage sevm).sliceD 0 32 0) =
      implementation.toB256 := by
  unfold decodeForwardHeadImage
  rw [Bytes.sliceD_writeAt_inside _ _ 0 0 32 (by omega) (by
    rw [List.length_sliceD]
    omega)]
  exact himplementation

private theorem decodeForwardHeadImage_admin
    {sevm : Sevm} {requestedAdmin : Adr}
    (hadmin : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256) :
    Bytes.toB256 ((decodeForwardHeadImage sevm).sliceD 32 32 0) =
      requestedAdmin.toB256 := by
  unfold decodeForwardHeadImage
  rw [Bytes.sliceD_writeAt_inside _ _ 0 32 32 (by omega) (by
    rw [List.length_sliceD]
    omega),
    Bytes.sliceD_sliceD_of_le _ 3437 96 32 32 (by omega)]
  exact hadmin

private theorem decodeForwardHeadImage_offset
    {sevm : Sevm}
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96) :
    Bytes.toB256 ((decodeForwardHeadImage sevm).sliceD 64 32 0) = 96 := by
  unfold decodeForwardHeadImage
  rw [Bytes.sliceD_writeAt_inside _ _ 0 64 32 (by omega) (by
    rw [List.length_sliceD]),
    Bytes.sliceD_sliceD_of_le _ 3437 96 64 32 (by omega)]
  exact hoffset

private theorem decodeForwardPointerMemory_size (sevm : Sevm) :
    (decodeForwardPointerMemory sevm).size = 128 := by
  unfold decodeForwardPointerMemory
  have hlength := B256.length_toBytes (Nat.toB256 3533)
  have hne : (Nat.toB256 3533).toBytes ≠ [] := by
    intro hnil
    rw [hnil] at hlength
    simp at hlength
  have hlt : (decodeForwardHeadMemory sevm).size <
      96 + (Nat.toB256 3533).toBytes.length := by
    rw [decodeForwardHeadMemory_size, hlength]
    decide
  rw [Mem.size_write_of_lt hne hlt, hlength]
  decide

private theorem decodeForwardPointerMemory_wf (sevm : Sevm) :
    Mem.Wf (decodeForwardPointerMemory sevm) := by
  exact Mem.Wf.write (decodeForwardHeadMemory_wf sevm) 96
    (Nat.toB256 3533).toBytes

private theorem decodeForwardPointerMemory_reads (sevm : Sevm) :
    Mem.Reads (decodeForwardPointerMemory sevm)
      (decodeForwardPointerImage sevm) := by
  have hread := Mem.Reads.write (decodeForwardHeadMemory_wf sevm)
    (decodeForwardHeadMemory_reads sevm) 96 (Nat.toB256 3533).toBytes
  simpa [decodeForwardPointerMemory, decodeForwardPointerImage] using hread

private theorem decodeForwardPointerImage_pointer (sevm : Sevm) :
    Bytes.toB256 ((decodeForwardPointerImage sevm).sliceD 96 32 0) =
      Nat.toB256 3533 := by
  unfold decodeForwardPointerImage
  rw [show (32 : Nat) = (Nat.toB256 3533).toBytes.length from
      (B256.length_toBytes _).symm,
    Bytes.sliceD_writeAt]
  exact B256.toB256_toBytes _

private theorem decodeForwardLengthMemory_size (sevm : Sevm) :
    (decodeForwardLengthMemory sevm).size = 160 := by
  unfold decodeForwardLengthMemory
  have hlength := ByteArray.length_sliceD sevm.code 3533 32
    (Linst.toUInt8 .stop)
  have hne : sevm.code.sliceD 3533 32 (Linst.toUInt8 .stop) ≠ [] := by
    intro hnil
    rw [hnil] at hlength
    simp at hlength
  have hlt : (decodeForwardPointerMemory sevm).size < 128 +
      (sevm.code.sliceD 3533 32 (Linst.toUInt8 .stop)).length := by
    rw [decodeForwardPointerMemory_size, hlength]
    decide
  rw [Mem.size_write_of_lt hne hlt, hlength]
  decide

private theorem decodeForwardLengthMemory_wf (sevm : Sevm) :
    Mem.Wf (decodeForwardLengthMemory sevm) := by
  exact Mem.Wf.write
    (Mem.Wf.write
      (Mem.Wf.write Mem.wf_empty 0
        (sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop)))
      96 (Nat.toB256 3533).toBytes)
    128 (sevm.code.sliceD 3533 32 (Linst.toUInt8 .stop))

private theorem decodeForwardLengthMemory_reads (sevm : Sevm) :
    Mem.Reads (decodeForwardLengthMemory sevm)
      (decodeForwardLengthImage sevm) := by
  have hhead := Mem.Reads.write Mem.wf_empty Mem.reads_empty 0
    (sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop))
  have hwfHead := Mem.Wf.write Mem.wf_empty 0
    (sevm.code.sliceD 3437 96 (Linst.toUInt8 .stop))
  have hpointer := Mem.Reads.write hwfHead hhead 96
    (Nat.toB256 3533).toBytes
  have hwfPointer := Mem.Wf.write hwfHead 96
    (Nat.toB256 3533).toBytes
  have hlength := Mem.Reads.write hwfPointer hpointer 128
    (sevm.code.sliceD 3533 32 (Linst.toUInt8 .stop))
  simpa [decodeForwardLengthMemory, decodeForwardPointerMemory,
    decodeForwardHeadMemory, decodeForwardLengthImage,
    decodeForwardPointerImage, decodeForwardHeadImage,
    ByteArray.sliceD_eq, show Linst.toUInt8 .stop = 0 by decide] using hlength

private theorem decodeForwardLengthImage_implementation
    {sevm : Sevm} {implementation : Adr}
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256) :
    Bytes.toB256 ((decodeForwardLengthImage sevm).sliceD 0 32 0) =
      implementation.toB256 := by
  unfold decodeForwardLengthImage decodeForwardPointerImage
    decodeForwardHeadImage
  rw [Bytes.sliceD_writeAt_before _ _ 0 32 128 (by omega),
    Bytes.sliceD_writeAt_before _ _ 0 32 96 (by omega),
    Bytes.sliceD_writeAt_inside _ _ 0 0 32 (by omega) (by
      rw [List.length_sliceD]
      omega)]
  exact himplementation

private theorem decodeForwardLengthImage_admin
    {sevm : Sevm} {requestedAdmin : Adr}
    (hadmin : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256) :
    Bytes.toB256 ((decodeForwardLengthImage sevm).sliceD 32 32 0) =
      requestedAdmin.toB256 := by
  unfold decodeForwardLengthImage decodeForwardPointerImage
    decodeForwardHeadImage
  rw [Bytes.sliceD_writeAt_before _ _ 32 32 128 (by omega),
    Bytes.sliceD_writeAt_before _ _ 32 32 96 (by omega),
    Bytes.sliceD_writeAt_inside _ _ 0 32 32 (by omega) (by
      rw [List.length_sliceD]
      omega)]
  rw [Bytes.sliceD_sliceD_of_le _ 3437 96 32 32 (by omega)]
  exact hadmin

private theorem decodeForwardLengthImage_length
    {sevm : Sevm}
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 0) :
    Bytes.toB256 ((decodeForwardLengthImage sevm).sliceD 128 32 0) = 0 := by
  unfold decodeForwardLengthImage
  rw [Bytes.sliceD_writeAt_inside _ _ 128 128 32 (by omega) (by
    rw [List.length_sliceD])]
  exact hlength

private theorem decodeForwardLengthImage_length_word
    {sevm : Sevm} {lengthWord : B256}
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 =
      lengthWord) :
    Bytes.toB256 ((decodeForwardLengthImage sevm).sliceD 128 32 0) =
      lengthWord := by
  unfold decodeForwardLengthImage
  rw [Bytes.sliceD_writeAt_inside _ _ 128 128 32 (by omega) (by
    rw [List.length_sliceD])]
  exact hlength

private theorem decodeForwardLengthImage_pointer (sevm : Sevm) :
    Bytes.toB256 ((decodeForwardLengthImage sevm).sliceD 96 32 0) =
      Nat.toB256 3533 := by
  unfold decodeForwardLengthImage
  rw [Bytes.sliceD_writeAt_before _ _ 96 32 128 (by omega)]
  exact decodeForwardPointerImage_pointer sevm

private def decodeForwardLoadWord (word : B256) : Line :=
  [pushB256 (word * 32), mload]

private def decodeForwardAfterPayloadBound (body : Func) : Func :=
  decodeForwardLoadWord 4 +++
    decodeForwardLoadWord 3 +++ pushB256 32 ::: add :::
      pushB256 0x100 ::: codecopy ::: body

private def decodeForwardAfterLengthBound (body : Func) : Func :=
  decodeForwardLoadWord 3 +++ pushB256 32 ::: add :::
    decodeForwardLoadWord 4 +++ add ::: codesize ::: lt :::
      ((.call 1) <?> decodeForwardAfterPayloadBound body)

private def decodeForwardAfterLengthCopy (body : Func) : Func :=
  pushB256 ossifiableConstructorAbiMaxUint64 :::
    decodeForwardLoadWord 4 +++ gt :::
      ((.call 7) <?> decodeForwardAfterLengthBound body)

private def decodeForwardAfterLengthComplete (body : Func) : Func :=
  pushB256 32 ::: decodeForwardLoadWord 3 +++
    pushB256 128 ::: codecopy ::: decodeForwardAfterLengthCopy body

private def decodeForwardAfterPointer (body : Func) : Func :=
  decodeForwardLoadWord 3 +++ pushB256 32 ::: add :::
    codesize ::: lt :::
      ((.call 1) <?> decodeForwardAfterLengthComplete body)

private def decodeForwardAfterOffsetBound (body : Func) : Func :=
  decodeForwardLoadWord 2 +++
    ossifiablePushCreationCoordinate 3437 ::: add :::
      mstoreAt 3 +++ decodeForwardAfterPointer body

private def decodeForwardAfterAdmin (body : Func) : Func :=
  pushB256 ossifiableConstructorAbiMaxUint64 :::
    decodeForwardLoadWord 2 +++ gt :::
      ((.call 1) <?> decodeForwardAfterOffsetBound body)

private def decodeForwardAfterImplementation (body : Func) : Func :=
  decodeForwardLoadWord 1 +++ checkNonAddress +++
    ((.call 1) <?> decodeForwardAfterAdmin body)

private def decodeForwardAfterHeadCopy (body : Func) : Func :=
  decodeForwardLoadWord 0 +++ checkNonAddress +++
    ((.call 1) <?> decodeForwardAfterImplementation body)

private def decodeForwardAfterHead (body : Func) : Func :=
  pushB256 96 ::: ossifiablePushCreationCoordinate 3437 :::
    pushB256 0 ::: codecopy ::: decodeForwardAfterHeadCopy body

private theorem decodeForwardImplementationStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {implementation : Adr} {G : Nat}
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G⟩)
      (decodeForwardAfterImplementation body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G + 32⟩)
      (decodeForwardAfterHeadCopy body) post := by
  have hv : Bytes.toB256
      ((decodeForwardHeadMemory sevm).read 0 32).1 =
        implementation.toB256 := by
    rw [Mem.Reads.read (decodeForwardHeadMemory_reads sevm)]
    exact decodeForwardHeadImage_implementation himplementation
  have hm : ((decodeForwardHeadMemory sevm).read 0 32).2 =
      decodeForwardHeadMemory sevm := by
    have hext : memExtSize (decodeForwardHeadMemory sevm).size 0 32 =
        (decodeForwardHeadMemory sevm).size := by
      rw [decodeForwardHeadMemory_size]
      decide
    unfold Mem.read Mem.extend
    simp only [hext]
  unfold decodeForwardAfterHeadCopy decodeForwardLoadWord checkNonAddress
    pushAddressMask
  func_run (2) [3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardHeadMemory_size sevm) (by decide)
  try rw [hm, hv]
  have hvalid : ValidAdr implementation.toB256 := ⟨implementation, rfl⟩
  have hclean : addressMask &&& implementation.toB256 = 0 :=
    validAdr_iff.mp hvalid
  have hclean' :
      ((fun x y : B256 => y <<< x.toNat) (Nat.toB256 160) (~~~(0 : B256))).and
          implementation.toB256 = 0 := by
    change (((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) &&&
      implementation.toB256) = 0
    simpa only [addressMask_eq_shl] using hclean
  func_run (2) [~~~(0 : B256)]
  func_run (2)
  func_run (1)
  rw [show (((0 : B256) * 32).toNat) = 0 by decide, hv, hclean', hm]
  have hg : G + 32 - 19 = G + 13 := by omega
  rw [hg]
  apply Func.runCompiled_branch_zero (s := []) (G := G)
  · rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach]
    norm_num [gVerylow, gHigh]
  · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hrest

private theorem decodeForwardAdminStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {requestedAdmin : Adr} {G : Nat}
    (hadmin : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G⟩)
      (decodeForwardAfterAdmin body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G + 33⟩)
      (decodeForwardAfterImplementation body) post := by
  have hv : Bytes.toB256
      ((decodeForwardHeadMemory sevm).read 32 32).1 =
        requestedAdmin.toB256 := by
    rw [Mem.Reads.read (decodeForwardHeadMemory_reads sevm)]
    exact decodeForwardHeadImage_admin hadmin
  have hm : ((decodeForwardHeadMemory sevm).read 32 32).2 =
      decodeForwardHeadMemory sevm := by
    have hext : memExtSize (decodeForwardHeadMemory sevm).size 32 32 =
        (decodeForwardHeadMemory sevm).size := by
      rw [decodeForwardHeadMemory_size]
      decide
    unfold Mem.read Mem.extend
    simp only [hext]
  unfold decodeForwardAfterImplementation decodeForwardLoadWord
    checkNonAddress pushAddressMask
  func_run (2) [3]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardHeadMemory_size sevm) (by decide)
  try rw [hm, hv]
  have hvalid : ValidAdr requestedAdmin.toB256 := ⟨requestedAdmin, rfl⟩
  have hclean : addressMask &&& requestedAdmin.toB256 = 0 :=
    validAdr_iff.mp hvalid
  have hclean' :
      ((fun x y : B256 => y <<< x.toNat) (Nat.toB256 160) (~~~(0 : B256))).and
          requestedAdmin.toB256 = 0 := by
    change (((~~~(0 : B256)) <<< (Nat.toB256 160).toNat) &&&
      requestedAdmin.toB256) = 0
    simpa only [addressMask_eq_shl] using hclean
  func_run (2) [~~~(0 : B256)]
  func_run (2)
  func_run (1)
  rw [show (((1 : B256) * 32).toNat) = 32 by decide, hv, hclean', hm]
  have hg : G + 33 - 20 = G + 13 := by omega
  rw [hg]
  apply Func.runCompiled_branch_zero (s := []) (G := G)
  · rfl
  · simp only [Devm.stack_setMach]
    decide
  · simp only [Devm.gasLeft_setMach]
    norm_num [gVerylow, gHigh]
  · simpa only [Devm.setMach_setMach, Devm.memory_setMach] using hrest

private theorem decodeForwardOffsetBoundStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G⟩)
      (decodeForwardAfterOffsetBound body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G + 25⟩)
      (decodeForwardAfterAdmin body) post := by
  have hv : Bytes.toB256
      ((decodeForwardHeadMemory sevm).read 64 32).1 = 96 := by
    rw [Mem.Reads.read (decodeForwardHeadMemory_reads sevm)]
    exact decodeForwardHeadImage_offset hoffset
  have hm : ((decodeForwardHeadMemory sevm).read 64 32).2 =
      decodeForwardHeadMemory sevm := by
    have hext : memExtSize (decodeForwardHeadMemory sevm).size 64 32 =
        (decodeForwardHeadMemory sevm).size := by
      rw [decodeForwardHeadMemory_size]
      decide
    unfold Mem.read Mem.extend
    simp only [hext]
  unfold decodeForwardAfterAdmin decodeForwardLoadWord
  func_run (4) [3, 0]
  all_goals try
    rw [show (((2 : B256) * 32).toNat) = 64 by decide, hv]
  all_goals try
    rw [show (((2 : B256) * 32).toNat) = 64 by decide, hm]
  all_goals try decide +kernel
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardHeadMemory_size sevm) (by decide)
  func_run (1)
  simpa using hrest

private theorem decodeForwardPointerStoreStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardPointerMemory sevm, G⟩)
      (decodeForwardAfterPointer body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G + 21⟩)
      (decodeForwardAfterOffsetBound body) post := by
  have hv : Bytes.toB256
      ((decodeForwardHeadMemory sevm).read 64 32).1 = 96 := by
    rw [Mem.Reads.read (decodeForwardHeadMemory_reads sevm)]
    exact decodeForwardHeadImage_offset hoffset
  have hm : ((decodeForwardHeadMemory sevm).read 64 32).2 =
      decodeForwardHeadMemory sevm := by
    have hext : memExtSize (decodeForwardHeadMemory sevm).size 64 32 =
        (decodeForwardHeadMemory sevm).size := by
      rw [decodeForwardHeadMemory_size]
      decide
    unfold Mem.read Mem.extend
    simp only [hext]
  unfold decodeForwardAfterOffsetBound decodeForwardLoadWord
  simp only [ossifiablePushCreationCoordinate_shape]
  func_run (6) [3, Nat.toB256 3533, 3]
  all_goals try
    rw [show (((2 : B256) * 32).toNat) = 64 by decide, hv]
  all_goals try
    rw [show (((2 : B256) * 32).toNat) = 64 by decide, hm]
  all_goals try decide +kernel
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardHeadMemory_size sevm) (by decide)
  all_goals try
    exact Devm.extCost_of_size
      (decodeForwardHeadMemory_size sevm) (by decide)
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], decodeForwardPointerMemory sevm, G⟩)
    (decodeForwardAfterPointer body) post
  exact hrest

private theorem decodeForwardLengthCompleteStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hcodeSize : sevm.code.size = 3565)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardPointerMemory sevm, G⟩)
      (decodeForwardAfterLengthComplete body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardPointerMemory sevm, G + 30⟩)
      (decodeForwardAfterPointer body) post := by
  have hv : Bytes.toB256
      ((decodeForwardPointerMemory sevm).read 96 32).1 =
        Nat.toB256 3533 := by
    rw [Mem.Reads.read (decodeForwardPointerMemory_reads sevm)]
    exact decodeForwardPointerImage_pointer sevm
  have hm : ((decodeForwardPointerMemory sevm).read 96 32).2 =
      decodeForwardPointerMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardPointerMemory_size]
      decide)
  unfold decodeForwardAfterPointer decodeForwardLoadWord
  func_run (6) [3, Nat.toB256 3565, 0]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hv]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hm]
  all_goals try simp only [hcodeSize]
  all_goals try decide +kernel
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardPointerMemory_size sevm) (by decide)
  func_run (1)
  simpa using hrest

private theorem decodeForwardLengthCopyStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩)
      (decodeForwardAfterLengthCopy body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardPointerMemory sevm, G + 21⟩)
      (decodeForwardAfterLengthComplete body) post := by
  have hv : Bytes.toB256
      ((decodeForwardPointerMemory sevm).read 96 32).1 =
        Nat.toB256 3533 := by
    rw [Mem.Reads.read (decodeForwardPointerMemory_reads sevm)]
    exact decodeForwardPointerImage_pointer sevm
  have hm : ((decodeForwardPointerMemory sevm).read 96 32).2 =
      decodeForwardPointerMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardPointerMemory_size]
      decide)
  unfold decodeForwardAfterLengthComplete decodeForwardLoadWord
  func_run (5) [3, 9]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hv]
  all_goals try
    rw [hm]
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardPointerMemory_size sevm) (by decide)
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 32 32)
      (decodeForwardPointerMemory_size sevm) (by decide)
  simp only [show (Nat.toB256 3533).toNat = 3533 by decide,
    show (128 : B256).toNat = 128 by decide,
    show (32 : B256).toNat = 32 by decide]
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩)
    (decodeForwardAfterLengthCopy body) post
  exact hrest

private theorem decodeForwardLengthBoundStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 0)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩)
      (decodeForwardAfterLengthBound body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G + 25⟩)
      (decodeForwardAfterLengthCopy body) post := by
  have hv : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 128 32).1 = 0 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_length hlength
  have hm : ((decodeForwardLengthMemory sevm).read 128 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  unfold decodeForwardAfterLengthCopy decodeForwardLoadWord
  func_run (4) [3, 0]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hv]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hm]
  all_goals try decide +kernel
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardLengthMemory_size sevm) (by decide)
  func_run (1)
  simpa using hrest

private theorem decodeForwardPayloadBoundStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hcodeSize : sevm.code.size = 3565)
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 0)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩)
      (decodeForwardAfterPayloadBound body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G + 39⟩)
      (decodeForwardAfterLengthBound body) post := by
  have hv3 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 96 32).1 =
        Nat.toB256 3533 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_pointer sevm
  have hv4 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 128 32).1 = 0 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_length hlength
  have hm3 : ((decodeForwardLengthMemory sevm).read 96 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  have hm4 : ((decodeForwardLengthMemory sevm).read 128 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  unfold decodeForwardAfterLengthBound decodeForwardLoadWord
  func_run (9) [3, Nat.toB256 3565, 3, Nat.toB256 3565, 0]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hv3]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hm3]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hm4]
  all_goals try simp only [hcodeSize]
  all_goals try decide +kernel
  all_goals try
    simpa only [show (((4 : B256) * 32).toNat) = 128 by decide, hv4]
      using (show (0 : B256) + Nat.toB256 3565 = Nat.toB256 3565 by decide)
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardLengthMemory_size sevm) (by decide)
  func_run (1)
  simpa using hrest

private theorem decodeForwardPayloadCopyStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 0)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩)
      body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G + 24⟩)
      (decodeForwardAfterPayloadBound body) post := by
  have hv3 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 96 32).1 =
        Nat.toB256 3533 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_pointer sevm
  have hv4 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 128 32).1 = 0 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_length hlength
  have hm3 : ((decodeForwardLengthMemory sevm).read 96 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  have hm4 : ((decodeForwardLengthMemory sevm).read 128 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  have hsize3 :
      (((decodeForwardLengthMemory sevm).read
        (((3 : B256) * 32).toNat) 32).2).size = 160 := by
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hm3,
      decodeForwardLengthMemory_size]
  unfold decodeForwardAfterPayloadBound decodeForwardLoadWord
  func_run (8) [3, 3, Nat.toB256 3565, 3]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hv4]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hm4]
  all_goals try rw [hm4]
  all_goals try
    simpa only [show (((3 : B256) * 32).toNat) = 96 by decide, hv3]
      using (show (32 : B256) + Nat.toB256 3533 = Nat.toB256 3565 by decide)
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardLengthMemory_size sevm) (by decide)
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 0 32) hsize3 (by decide)
  simp only [show (((3 : B256) * 32).toNat) = 96 by decide, hm3,
    show (0 : B256).toNat = 0 by decide,
    show (Nat.toB256 3565).toNat = 3565 by decide,
    show (256 : B256).toNat = 256 by decide]
  simp
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩) body post
  exact hrest

private theorem decodeForwardHeadStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hcodeSize : sevm.code.size = 3565)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G⟩)
      (decodeForwardAfterHeadCopy body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + 50⟩)
      (ossifiableConstructorDecode 3437 body) post := by
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], Mem.empty, G + 50⟩)
    (ossifiablePushCreationCoordinate 3533 ::: codesize ::: lt :::
      ((.call 1) <?> decodeForwardAfterHead body)) post
  simp only [ossifiablePushCreationCoordinate_shape]
  func_run (3)
  simp only [hcodeSize]
  have hguard :
      (Nat.toB256 3565 <? Nat.toB256 3533) = 0 := by
    decide +kernel
  rw [hguard]
  func_run (1)
  unfold decodeForwardAfterHead
  simp only [ossifiablePushCreationCoordinate_shape]
  func_run (4) [21]
  · exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 96 32) rfl (by decide)
  simp only [show (0 : B256).toNat = 0 by decide,
    show (Nat.toB256 3437).toNat = 3437 by decide,
    show (96 : B256).toNat = 96 by decide,
    show (0 : UInt8) = Linst.toUInt8 .stop by decide]
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], decodeForwardHeadMemory sevm, G⟩)
    (decodeForwardAfterHeadCopy body) post
  exact hrest

/-! ## Fixed one-word nonempty setup decoder -/

/-- Decoder memory after copying the frozen one-word setup payload from the
complete creation image into the constructor's `0x100` scratch window. -/
def decodeForwardOneWordPayloadMemory (sevm : Sevm) : Mem :=
  (decodeForwardLengthMemory sevm).write 0x100
    (sevm.code.sliceD 3565 32 (Linst.toUInt8 .stop))

/-- Proof-carrying byte image corresponding to
`decodeForwardOneWordPayloadMemory`. -/
def decodeForwardOneWordPayloadImage (sevm : Sevm) : Bytes :=
  Bytes.writeAt (decodeForwardLengthImage sevm) 0x100
    (sevm.code.toList.sliceD 3565 32 0)

theorem decodeForwardOneWordPayloadMemory_size (sevm : Sevm) :
    (decodeForwardOneWordPayloadMemory sevm).size = 288 := by
  unfold decodeForwardOneWordPayloadMemory
  have hlength := ByteArray.length_sliceD sevm.code 3565 32
    (Linst.toUInt8 .stop)
  have hne : sevm.code.sliceD 3565 32 (Linst.toUInt8 .stop) ≠ [] := by
    intro hnil
    rw [hnil] at hlength
    simp at hlength
  have hlt : (decodeForwardLengthMemory sevm).size < 0x100 +
      (sevm.code.sliceD 3565 32 (Linst.toUInt8 .stop)).length := by
    rw [decodeForwardLengthMemory_size, hlength]
    decide
  rw [Mem.size_write_of_lt hne hlt, hlength]
  decide

theorem decodeForwardOneWordPayloadMemory_wf (sevm : Sevm) :
    Mem.Wf (decodeForwardOneWordPayloadMemory sevm) := by
  exact Mem.Wf.write (decodeForwardLengthMemory_wf sevm) 0x100
    (sevm.code.sliceD 3565 32 (Linst.toUInt8 .stop))

theorem decodeForwardOneWordPayloadMemory_reads (sevm : Sevm) :
    Mem.Reads (decodeForwardOneWordPayloadMemory sevm)
      (decodeForwardOneWordPayloadImage sevm) := by
  have hread := Mem.Reads.write (decodeForwardLengthMemory_wf sevm)
    (decodeForwardLengthMemory_reads sevm) 0x100
    (sevm.code.sliceD 3565 32 (Linst.toUInt8 .stop))
  simpa [decodeForwardOneWordPayloadMemory,
    decodeForwardOneWordPayloadImage, ByteArray.sliceD_eq,
    show Linst.toUInt8 .stop = 0 by decide] using hread

theorem decodeForwardOneWordPayloadImage_implementation
    {sevm : Sevm} {implementation : Adr}
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256) :
    Bytes.toB256
        ((decodeForwardOneWordPayloadImage sevm).sliceD 0 32 0) =
      implementation.toB256 := by
  unfold decodeForwardOneWordPayloadImage
  rw [Bytes.sliceD_writeAt_before _ _ 0 32 0x100 (by omega)]
  exact decodeForwardLengthImage_implementation himplementation

theorem decodeForwardOneWordPayloadImage_admin
    {sevm : Sevm} {requestedAdmin : Adr}
    (hadmin : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256) :
    Bytes.toB256
        ((decodeForwardOneWordPayloadImage sevm).sliceD 32 32 0) =
      requestedAdmin.toB256 := by
  unfold decodeForwardOneWordPayloadImage
  rw [Bytes.sliceD_writeAt_before _ _ 32 32 0x100 (by omega)]
  exact decodeForwardLengthImage_admin hadmin

theorem decodeForwardOneWordPayloadImage_length
    {sevm : Sevm}
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 32) :
    Bytes.toB256
        ((decodeForwardOneWordPayloadImage sevm).sliceD 128 32 0) = 32 := by
  unfold decodeForwardOneWordPayloadImage
  rw [Bytes.sliceD_writeAt_before _ _ 128 32 0x100 (by omega)]
  exact decodeForwardLengthImage_length_word hlength

theorem decodeForwardOneWordPayloadImage_setup
    {sevm : Sevm} {setupData : Bytes}
    (hsetup : sevm.code.toList.sliceD 3565 32 0 = setupData) :
    (decodeForwardOneWordPayloadImage sevm).sliceD 0x100 32 0 =
      setupData := by
  unfold decodeForwardOneWordPayloadImage
  have hread := Bytes.sliceD_writeAt (decodeForwardLengthImage sevm)
    (sevm.code.toList.sliceD 3565 32 0) 0x100
  rw [List.length_sliceD] at hread
  exact hread.trans hsetup

private theorem decodeForwardOneWordHeadStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hcodeSize : sevm.code.size = 3597)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardHeadMemory sevm, G⟩)
      (decodeForwardAfterHeadCopy body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + 50⟩)
      (ossifiableConstructorDecode 3437 body) post := by
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], Mem.empty, G + 50⟩)
    (ossifiablePushCreationCoordinate 3533 ::: codesize ::: lt :::
      ((.call 1) <?> decodeForwardAfterHead body)) post
  simp only [ossifiablePushCreationCoordinate_shape]
  func_run (3)
  simp only [hcodeSize]
  have hguard :
      (Nat.toB256 3597 <? Nat.toB256 3533) = 0 := by
    decide +kernel
  rw [hguard]
  func_run (1)
  unfold decodeForwardAfterHead
  simp only [ossifiablePushCreationCoordinate_shape]
  func_run (4) [21]
  · exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 96 32) rfl (by decide)
  simp only [show (0 : B256).toNat = 0 by decide,
    show (Nat.toB256 3437).toNat = 3437 by decide,
    show (96 : B256).toNat = 96 by decide,
    show (0 : UInt8) = Linst.toUInt8 .stop by decide]
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], decodeForwardHeadMemory sevm, G⟩)
    (decodeForwardAfterHeadCopy body) post
  exact hrest

private theorem decodeForwardOneWordLengthCompleteStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hcodeSize : sevm.code.size = 3597)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardPointerMemory sevm, G⟩)
      (decodeForwardAfterLengthComplete body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardPointerMemory sevm, G + 30⟩)
      (decodeForwardAfterPointer body) post := by
  have hv : Bytes.toB256
      ((decodeForwardPointerMemory sevm).read 96 32).1 =
        Nat.toB256 3533 := by
    rw [Mem.Reads.read (decodeForwardPointerMemory_reads sevm)]
    exact decodeForwardPointerImage_pointer sevm
  have hm : ((decodeForwardPointerMemory sevm).read 96 32).2 =
      decodeForwardPointerMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardPointerMemory_size]
      decide)
  unfold decodeForwardAfterPointer decodeForwardLoadWord
  func_run (6) [3, Nat.toB256 3565, 0]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hv]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hm]
  all_goals try simp only [hcodeSize]
  all_goals try decide +kernel
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardPointerMemory_size sevm) (by decide)
  func_run (1)
  simpa using hrest

private theorem decodeForwardOneWordLengthBoundStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 32)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩)
      (decodeForwardAfterLengthBound body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G + 25⟩)
      (decodeForwardAfterLengthCopy body) post := by
  have hv : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 128 32).1 = 32 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_length_word hlength
  have hm : ((decodeForwardLengthMemory sevm).read 128 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  unfold decodeForwardAfterLengthCopy decodeForwardLoadWord
  func_run (4) [3, 0]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hv]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hm]
  all_goals try decide +kernel
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardLengthMemory_size sevm) (by decide)
  func_run (1)
  simpa using hrest

private theorem decodeForwardOneWordPayloadBoundStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hcodeSize : sevm.code.size = 3597)
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 32)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G⟩)
      (decodeForwardAfterPayloadBound body) post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G + 39⟩)
      (decodeForwardAfterLengthBound body) post := by
  have hv3 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 96 32).1 =
        Nat.toB256 3533 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_pointer sevm
  have hv4 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 128 32).1 = 32 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_length_word hlength
  have hm3 : ((decodeForwardLengthMemory sevm).read 96 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  have hm4 : ((decodeForwardLengthMemory sevm).read 128 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  unfold decodeForwardAfterLengthBound decodeForwardLoadWord
  func_run (9) [3, Nat.toB256 3565, 3, Nat.toB256 3597, 0]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hv3]
  all_goals try
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hm3]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hm4]
  all_goals try simp only [hcodeSize]
  all_goals try decide +kernel
  all_goals try
    simpa only [show (((4 : B256) * 32).toNat) = 128 by decide, hv4]
      using (show (32 : B256) + Nat.toB256 3565 =
        Nat.toB256 3597 by decide)
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardLengthMemory_size sevm) (by decide)
  func_run (1)
  simpa using hrest

private theorem decodeForwardOneWordPayloadCopyStage_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {G : Nat}
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 32)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardOneWordPayloadMemory sevm, G⟩)
      body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardLengthMemory sevm, G + 39⟩)
      (decodeForwardAfterPayloadBound body) post := by
  have hv3 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 96 32).1 =
        Nat.toB256 3533 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_pointer sevm
  have hv4 : Bytes.toB256
      ((decodeForwardLengthMemory sevm).read 128 32).1 = 32 := by
    rw [Mem.Reads.read (decodeForwardLengthMemory_reads sevm)]
    exact decodeForwardLengthImage_length_word hlength
  have hm3 : ((decodeForwardLengthMemory sevm).read 96 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  have hm4 : ((decodeForwardLengthMemory sevm).read 128 32).2 =
      decodeForwardLengthMemory sevm := by
    exact Mem.read_snd_eq_self (by
      rw [decodeForwardLengthMemory_size]
      decide)
  have hsize3 :
      (((decodeForwardLengthMemory sevm).read
        (((3 : B256) * 32).toNat) 32).2).size = 160 := by
    rw [show (((3 : B256) * 32).toNat) = 96 by decide, hm3,
      decodeForwardLengthMemory_size]
  unfold decodeForwardAfterPayloadBound decodeForwardLoadWord
  func_run (8) [3, 3, Nat.toB256 3565, 18]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hv4]
  all_goals try
    rw [show (((4 : B256) * 32).toNat) = 128 by decide, hm4]
  all_goals try rw [hm4]
  all_goals try
    simpa only [show (((3 : B256) * 32).toNat) = 96 by decide, hv3]
      using (show (32 : B256) + Nat.toB256 3533 =
        Nat.toB256 3565 by decide)
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow) (decodeForwardLengthMemory_size sevm) (by decide)
  all_goals try
    exact Devm.extCost_add_of_size
      (a := gVerylow + gasCopy * ceilDiv 32 32) hsize3 (by decide)
  simp only [show (((3 : B256) * 32).toNat) = 96 by decide, hm3,
    show (32 : B256).toNat = 32 by decide,
    show (Nat.toB256 3565).toNat = 3565 by decide,
    show (256 : B256).toNat = 256 by decide,
    show (0 : UInt8) = Linst.toUInt8 .stop by decide]
  change Func.RunCompiled fs sevm
    (base.setMach ⟨[], decodeForwardOneWordPayloadMemory sevm, G⟩)
    body post
  exact hrest

/-- Execute the strict canonical-coordinate decoder for an exact 32-byte
setup payload, then hand control to an arbitrary already-proved initializer.
The accepted decoder costs 315 gas: the empty decoder's 300 plus one copy word
and the `160 → 288` memory expansion. -/
theorem ossifiableConstructorDecode_oneWordSetup_runCompiled
    {fs : List Func} {sevm : Sevm} {base post : Devm}
    {body : Func} {implementation requestedAdmin : Adr} {G : Nat}
    (hcodeSize : sevm.code.size = 3597)
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256)
    (hrequested : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256)
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96)
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 32)
    (hrest : Func.RunCompiled fs sevm
      (base.setMach ⟨[], decodeForwardOneWordPayloadMemory sevm, G⟩)
      body post) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], Mem.empty, G + 315⟩)
      (ossifiableConstructorDecode 3437 body) post := by
  have hcopy :=
    decodeForwardOneWordPayloadCopyStage_runCompiled hlength hrest
  have hpayload := decodeForwardOneWordPayloadBoundStage_runCompiled
    hcodeSize hlength hcopy
  have hlengthBound :=
    decodeForwardOneWordLengthBoundStage_runCompiled hlength hpayload
  have hlengthCopy := decodeForwardLengthCopyStage_runCompiled hlengthBound
  have hlengthComplete :=
    decodeForwardOneWordLengthCompleteStage_runCompiled hcodeSize hlengthCopy
  have hpointer :=
    decodeForwardPointerStoreStage_runCompiled hoffset hlengthComplete
  have hoffsetBound :=
    decodeForwardOffsetBoundStage_runCompiled hoffset hpointer
  have hadmin := decodeForwardAdminStage_runCompiled hrequested hoffsetBound
  have himplementation :=
    decodeForwardImplementationStage_runCompiled himplementation hadmin
  have hdecode :=
    decodeForwardOneWordHeadStage_runCompiled hcodeSize himplementation
  simpa only [Nat.add_assoc] using hdecode

/-- Execute the strict canonical-coordinate decoder and the complete empty-data
initializer.  The 300-gas prefix is the exact sum of its accepted guards,
head/pointer/length copies, and zero-byte payload copy. -/
theorem ossifiableConstructorDecodeInitialize_emptySetup_runCompiled
    {sevm : Sevm} {base : Devm} {runtimeBytes : Bytes}
    {implementation requestedAdmin : Adr} {G : Nat}
    (hcodeSize : sevm.code.size = 3565)
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256)
    (hrequested : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256)
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96)
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 0)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold : (sevm.currentTarget, implementationSlotLit) ∉
      base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2188)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : 200000 ≤ G) :
    ∃ post,
      Func.RunCompiled (ossifiableConstructorFunctions 1249 2188) sevm
        (base.setMach ⟨[], Mem.empty, G + 300⟩)
        (ossifiableConstructorDecode 3437
          ossifiableConstructorInitializeImplementation) post ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor base sevm.currentTarget).set implementationSlotLit
          implementation.toB256).set adminSlotLit requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [rawUpgradedLog sevm.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget 0
          requestedAdmin] ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 49894 ∧
      post.error = base.error := by
  obtain ⟨post, hbody, hstorage, hlogs, houtput, hgasPost, herrorPost⟩ :=
    ossifiableConstructorInitializeImplementation_zeroSetup_runCompiled
      (sevm := sevm) (base := base)
      (memory := decodeForwardLengthMemory sevm)
      (image := decodeForwardLengthImage sevm)
      (runtimeBytes := runtimeBytes) (implementation := implementation)
      (requestedAdmin := requestedAdmin) (G := G)
      (decodeForwardLengthMemory_wf sevm)
      (decodeForwardLengthMemory_reads sevm)
      (decodeForwardLengthImage_implementation himplementation)
      (decodeForwardLengthImage_admin hrequested)
      (decodeForwardLengthImage_length hlength)
      himplementationNonzero hrequestedNonzero hcodeSizeNonzero
      haddressCold himplementationRaw himplementationOriginal
      himplementationCold hadminRaw hadminOriginal hadminCold
      (decodeForwardLengthMemory_size sevm) hstatic hcode
      hruntimeLength hruntimeNonempty hgas
  have hcopy := decodeForwardPayloadCopyStage_runCompiled hlength hbody
  have hpayload :=
    decodeForwardPayloadBoundStage_runCompiled hcodeSize hlength hcopy
  have hlengthBound :=
    decodeForwardLengthBoundStage_runCompiled hlength hpayload
  have hlengthCopy := decodeForwardLengthCopyStage_runCompiled hlengthBound
  have hlengthComplete :=
    decodeForwardLengthCompleteStage_runCompiled hcodeSize hlengthCopy
  have hpointer :=
    decodeForwardPointerStoreStage_runCompiled hoffset hlengthComplete
  have hoffsetBound :=
    decodeForwardOffsetBoundStage_runCompiled hoffset hpointer
  have hadmin := decodeForwardAdminStage_runCompiled hrequested hoffsetBound
  have himplementation :=
    decodeForwardImplementationStage_runCompiled himplementation hadmin
  have hdecode := decodeForwardHeadStage_runCompiled hcodeSize himplementation
  refine ⟨post, ?_, hstorage, hlogs, houtput, hgasPost, herrorPost⟩
  simpa only [Nat.add_assoc] using hdecode

private theorem decodeForwardProgramMainStage_runCompiled
    {sevm : Sevm} {base post : Devm} {G : Nat}
    (hvalue : sevm.value = 0)
    (hrest : Func.RunCompiled (ossifiableConstructorFunctions 1249 2188) sevm
      (base.setMach ⟨[], Mem.empty, G⟩)
      (ossifiableConstructorDecode 3437
        ossifiableConstructorInitializeImplementation) post) :
    Func.RunCompiled (ossifiableConstructorFunctions 1249 2188) sevm
      (base.setMach ⟨[], Mem.empty, G + 19⟩)
      (ossifiableConstructorProgram 1249 3437 2188).main post := by
  rw [ossifiableConstructorProgram_main_shape]
  func_run (3) [1]
  all_goals try simp [B256.eqCheck, hvalue]
  simpa using hrest

/-- Execute the complete canonical-coordinate creation program from its real
program entry.  The additional 20 gas consists of the value guard's accepted
arm (19) and the compiled program's leading `JUMPDEST` (1). -/
theorem ossifiableConstructorProgram_emptySetup_runCompiled
    {sevm : Sevm} {base : Devm} {runtimeBytes : Bytes}
    {implementation requestedAdmin : Adr} {G : Nat}
    (hvalue : sevm.value = 0)
    (hcodeSize : sevm.code.size = 3565)
    (himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256)
    (hrequested : ossifiableConstructorCodeWord sevm.code.toList 3469 =
      requestedAdmin.toB256)
    (hoffset : ossifiableConstructorCodeWord sevm.code.toList 3501 = 96)
    (hlength : ossifiableConstructorCodeWord sevm.code.toList 3533 = 0)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold : (sevm.currentTarget, implementationSlotLit) ∉
      base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2188)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : 200000 ≤ G) :
    ∃ post,
      Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, G + 320⟩)
        (ossifiableConstructorProgram 1249 3437 2188) post ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor base sevm.currentTarget).set implementationSlotLit
          implementation.toB256).set adminSlotLit requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [rawUpgradedLog sevm.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget 0
          requestedAdmin] ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 49894 ∧
      post.error = base.error := by
  obtain ⟨post, hdecode, hstorage, hlogs, houtput, hgasPost, herrorPost⟩ :=
    ossifiableConstructorDecodeInitialize_emptySetup_runCompiled
      hcodeSize himplementation hrequested
      hoffset hlength himplementationNonzero hrequestedNonzero
      hcodeSizeNonzero haddressCold himplementationRaw
      himplementationOriginal himplementationCold hadminRaw hadminOriginal
      hadminCold hstatic hcode hruntimeLength hruntimeNonempty hgas
  have hmain :=
    decodeForwardProgramMainStage_runCompiled hvalue hdecode
  refine ⟨post, ?_, hstorage, hlogs, houtput, hgasPost, herrorPost⟩
  apply Prog.runCompiled_intro (G := G + 319)
  · norm_num [gJumpdest]
  · rfl
  · change Func.RunCompiled
      (ossifiableConstructorFunctions 1249 2188) sevm
      (base.setMach ⟨[], Mem.empty, G + 319⟩)
      (ossifiableConstructorProgram 1249 3437 2188).main post
    simpa only [Nat.add_assoc] using hmain

/-! ## Complete canonical empty-data input -/

private theorem ossifiableCreationTemplate_length_exact :
    ossifiableCreationTemplate.length = 3437 := by
  rw [ossifiableCreationTemplate_eq_artifact,
    creationTemplateArtifactBytes_length]

private theorem ossifiableEmptyDataCreateInput_length_exact
    (implementation admin : Adr) :
    (ossifiableEmptyDataCreateInput implementation admin).length = 3565 := by
  simp only [ossifiableEmptyDataCreateInput, ossifiableFullCreateInput,
    List.length_append, ossifiableCreationTemplate_length_exact,
    abiEncodeOssifiableConstructorArgs, abiBytesTail,
    B256.length_toBytes, List.length_replicate, List.length_nil]
  decide

private theorem creationBaselineBytes_length_exact :
    creationBaselineBytes.length = 1249 := by
  have hliteral : creationBaselineArtifactBytes = creationBaselineBytes :=
    Option.some.inj
      (creationBaselineArtifact_compile.symm.trans creationBaseline_compile)
  rw [← hliteral, creationBaselineArtifactBytes_length]

private theorem runtimeBaselineBytes_length_exact :
    runtimeBaselineBytes.length = 2188 := by
  have hliteral : runtimeBaselineArtifactBytes = runtimeBaselineBytes :=
    Option.some.inj
      (runtimeBaselineArtifact_compile.symm.trans runtimeBaseline_compile)
  rw [← hliteral, runtimeBaselineArtifactBytes_length]

private theorem ossifiableEmptyDataCreateInput_runtime
    (implementation admin : Adr) :
    (ossifiableEmptyDataCreateInput implementation admin).sliceD
      1249 2188 0 = runtimeBaselineBytes := by
  unfold ossifiableEmptyDataCreateInput ossifiableFullCreateInput
    ossifiableCreationTemplate List.sliceD
  simp only [List.append_assoc]
  rw [List.drop_length_append' creationBaselineBytes_length_exact.symm]
  rw [List.takeD_eq_take _ (by
      simp only [List.length_append, runtimeBaselineBytes_length_exact]
      omega),
    show 2188 = runtimeBaselineBytes.length from
      runtimeBaselineBytes_length_exact.symm,
    List.take_length_append]

private theorem ossifiableEmptyDataCreateInput_slice_word
    (implementation admin : Adr) (k : Nat) :
    (ossifiableEmptyDataCreateInput implementation admin).sliceD
        (3437 + k) 32 0 =
      (abiEncodeOssifiableConstructorArgs implementation admin []).sliceD
        k 32 0 := by
  unfold ossifiableEmptyDataCreateInput ossifiableFullCreateInput
  unfold List.sliceD
  rw [← List.drop_drop]
  rw [List.drop_length_append'
    ossifiableCreationTemplate_length_exact.symm]

private theorem ossifiableEmptyDataCreateInput_implementation
    (implementation admin : Adr) :
    ossifiableConstructorCodeWord
      (ossifiableEmptyDataCreateInput implementation admin) 3437 =
        implementation.toB256 := by
  unfold ossifiableConstructorCodeWord
  rw [show 3437 = 3437 + 0 by omega,
    ossifiableEmptyDataCreateInput_slice_word]
  unfold abiEncodeOssifiableConstructorArgs abiBytesTail List.sliceD
  simp only [List.drop_zero, List.append_assoc]
  rw [List.takeD_eq_take _ (by
      simp only [List.length_append, B256.length_toBytes]
      omega),
    show 32 = implementation.toB256.toBytes.length from
      (B256.length_toBytes _).symm,
    List.take_length_append]
  exact B256.toB256_toBytes _

private theorem ossifiableEmptyDataCreateInput_admin
    (implementation admin : Adr) :
    ossifiableConstructorCodeWord
      (ossifiableEmptyDataCreateInput implementation admin) 3469 =
        admin.toB256 := by
  unfold ossifiableConstructorCodeWord
  rw [show 3469 = 3437 + 32 by omega,
    ossifiableEmptyDataCreateInput_slice_word]
  unfold abiEncodeOssifiableConstructorArgs abiBytesTail List.sliceD
  simp only [List.append_assoc]
  rw [List.drop_length_append'
    (show 32 = implementation.toB256.toBytes.length from
      (B256.length_toBytes _).symm)]
  rw [List.takeD_eq_take _ (by
      simp only [List.length_append, B256.length_toBytes]
      omega),
    show 32 = admin.toB256.toBytes.length from
      (B256.length_toBytes _).symm,
    List.take_length_append]
  exact B256.toB256_toBytes _

private theorem ossifiableEmptyDataCreateInput_offset
    (implementation admin : Adr) :
    ossifiableConstructorCodeWord
      (ossifiableEmptyDataCreateInput implementation admin) 3501 = 96 := by
  unfold ossifiableConstructorCodeWord
  rw [show 3501 = 3437 + 64 by omega,
    ossifiableEmptyDataCreateInput_slice_word]
  unfold abiEncodeOssifiableConstructorArgs abiBytesTail List.sliceD
  simp only [List.append_assoc]
  rw [show 64 = 32 + 32 by omega, ← List.drop_drop,
    List.drop_length_append'
      (show 32 = implementation.toB256.toBytes.length from
        (B256.length_toBytes _).symm),
    List.drop_length_append'
      (show 32 = admin.toB256.toBytes.length from
        (B256.length_toBytes _).symm)]
  rw [List.takeD_eq_take _ (by
      simp only [List.length_append, B256.length_toBytes]
      omega),
    show 32 = (96 : B256).toBytes.length from
      (B256.length_toBytes _).symm,
    List.take_length_append]
  exact B256.toB256_toBytes _

private theorem ossifiableEmptyDataCreateInput_length
    (implementation admin : Adr) :
    ossifiableConstructorCodeWord
      (ossifiableEmptyDataCreateInput implementation admin) 3533 = 0 := by
  unfold ossifiableConstructorCodeWord
  rw [show 3533 = 3437 + 96 by omega,
    ossifiableEmptyDataCreateInput_slice_word]
  unfold abiEncodeOssifiableConstructorArgs abiBytesTail List.sliceD
  simp only [List.append_assoc, List.length_nil, ceil32]
  rw [show 96 = 32 + 64 by omega, ← List.drop_drop,
    List.drop_length_append'
      (show 32 = implementation.toB256.toBytes.length from
        (B256.length_toBytes _).symm),
    show 64 = 32 + 32 by omega, ← List.drop_drop,
    List.drop_length_append'
      (show 32 = admin.toB256.toBytes.length from
        (B256.length_toBytes _).symm),
    List.drop_length_append'
      (show 32 = (96 : B256).toBytes.length from
        (B256.length_toBytes _).symm)]
  rw [List.takeD_eq_take _ (by
      simp only [List.length_append, B256.length_toBytes,
        List.length_replicate]
      omega),
    show 32 = (Nat.toB256 0).toBytes.length from
      (B256.length_toBytes _).symm,
    List.take_length_append]
  exact B256.toB256_toBytes _

private theorem ossifiableEmptyDataCreateInput_decodeSpec
    (implementation admin : Adr) :
    ossifiableConstructorDecodeSpec
        (ossifiableEmptyDataCreateInput implementation admin) 3437 =
      .accepted implementation.toB256 admin.toB256 [] := by
  have himplementationClean :
      addressMask &&& implementation.toB256 = 0 :=
    validAdr_iff.mp ⟨implementation, rfl⟩
  have hadminClean : addressMask &&& admin.toB256 = 0 :=
    validAdr_iff.mp ⟨admin, rfl⟩
  have hpointer :
      (ossifiableConstructorDataPointer 3437 (96 : B256)).toNat = 3533 := by
    decide +kernel
  have hstart :
      (ossifiableConstructorDataStart 3437 (96 : B256)).toNat = 3565 := by
    decide +kernel
  have hfinish :
      (ossifiableConstructorDataEnd 3437 (96 : B256) 0).toNat = 3565 := by
    decide +kernel
  have haccepted := ossifiableConstructorDecodeSpec_accepted
    (code := ossifiableEmptyDataCreateInput implementation admin)
    (argsOffset := 3437)
    (by rw [ossifiableEmptyDataCreateInput_length_exact]; omega)
    (by
      rw [ossifiableEmptyDataCreateInput_implementation]
      exact himplementationClean)
    (by
      rw [show 3437 + 32 = 3469 by omega,
        ossifiableEmptyDataCreateInput_admin]
      exact hadminClean)
    (by
      rw [show 3437 + 64 = 3501 by omega,
        ossifiableEmptyDataCreateInput_offset]
      decide +kernel)
    (by
      rw [show 3437 + 64 = 3501 by omega,
        ossifiableEmptyDataCreateInput_offset]
      change
        (ossifiableConstructorDataStart 3437 (96 : B256)).toNat ≤
          (ossifiableEmptyDataCreateInput implementation admin).length
      rw [hstart, ossifiableEmptyDataCreateInput_length_exact])
    (by
      rw [show 3437 + 64 = 3501 by omega,
        ossifiableEmptyDataCreateInput_offset, hpointer,
        ossifiableEmptyDataCreateInput_length]
      decide +kernel)
    (by
      rw [show 3437 + 64 = 3501 by omega,
        ossifiableEmptyDataCreateInput_offset, hpointer,
        ossifiableEmptyDataCreateInput_length, hfinish,
        ossifiableEmptyDataCreateInput_length_exact])
  rw [ossifiableEmptyDataCreateInput_implementation,
    show 3437 + 32 = 3469 by omega,
    ossifiableEmptyDataCreateInput_admin,
    show 3437 + 64 = 3501 by omega,
    ossifiableEmptyDataCreateInput_offset, hpointer,
    ossifiableEmptyDataCreateInput_length, hstart] at haccepted
  simpa only [List.sliceD, B256.toNat_zero, List.takeD_zero] using haccepted

/-- Specialize the forward constructor theorem to the exact complete
`creation-template ++ abi.encode(implementation, admin, bytes(""))` input.
The returned bytes are the compiler-owned 2,188-byte runtime. -/
theorem ossifiableConstructorProgram_canonicalEmptyInput_runCompiled
    {sevm : Sevm} {base : Devm}
    {implementation requestedAdmin : Adr} {G : Nat}
    (hvalue : sevm.value = 0)
    (hinput : sevm.code.toList =
      ossifiableEmptyDataCreateInput implementation requestedAdmin)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold : (sevm.currentTarget, implementationSlotLit) ∉
      base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hgas : 200000 ≤ G) :
    ∃ post,
      Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, G + 320⟩)
        (ossifiableConstructorProgram 1249 3437 2188) post ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor base sevm.currentTarget).set implementationSlotLit
          implementation.toB256).set adminSlotLit requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [rawUpgradedLog sevm.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget 0
          requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = G - 49894 ∧
      post.error = base.error := by
  have hcodeSize : sevm.code.size = 3565 := by
    rw [ByteArray.size_eq_length_toList, hinput,
      ossifiableEmptyDataCreateInput_length_exact]
  have himplementation :
      ossifiableConstructorCodeWord sevm.code.toList 3437 =
        implementation.toB256 := by
    rw [hinput]
    exact ossifiableEmptyDataCreateInput_implementation _ _
  have hrequested :
      ossifiableConstructorCodeWord sevm.code.toList 3469 =
        requestedAdmin.toB256 := by
    rw [hinput]
    exact ossifiableEmptyDataCreateInput_admin _ _
  have hoffset :
      ossifiableConstructorCodeWord sevm.code.toList 3501 = 96 := by
    rw [hinput]
    exact ossifiableEmptyDataCreateInput_offset _ _
  have hlength :
      ossifiableConstructorCodeWord sevm.code.toList 3533 = 0 := by
    rw [hinput]
    exact ossifiableEmptyDataCreateInput_length _ _
  have hcode :
      sevm.code.sliceD 1249 2188 (Linst.toUInt8 .stop) =
        runtimeBaselineBytes := by
    simpa [ByteArray.sliceD_eq,
      show Linst.toUInt8 .stop = 0 by decide, hinput] using
      ossifiableEmptyDataCreateInput_runtime implementation requestedAdmin
  have hruntimeNonempty : runtimeBaselineBytes ≠ [] := by
    intro hnil
    have hlengthExact := runtimeBaselineBytes_length_exact
    rw [hnil] at hlengthExact
    simp at hlengthExact
  exact ossifiableConstructorProgram_emptySetup_runCompiled
    hvalue hcodeSize himplementation hrequested hoffset hlength
    himplementationNonzero hrequestedNonzero hcodeSizeNonzero haddressCold
    himplementationRaw himplementationOriginal himplementationCold
    hadminRaw hadminOriginal hadminCold hstatic hcode
    runtimeBaselineBytes_length_exact hruntimeNonempty hgas

/-- Exact semantic observations carried by the same constructive canonical
constructor walk.  The decoder's accepted value fixes the setup payload to
empty, so the execution-derived prepared route supplies the two ERC-1967
writes and source-ordered logs without consulting the total evaluator. -/
theorem ossifiableConstructorProgram_canonicalEmptyInput_forward_exact
    {sevm : Sevm} {base : Devm}
    {implementation requestedAdmin : Adr} {G : Nat}
    (hvalue : sevm.value = 0)
    (hinput : sevm.code.toList =
      ossifiableEmptyDataCreateInput implementation requestedAdmin)
    (himplementationNonzero : implementation ≠ 0)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hcodeSizeNonzero : (base.getCode implementation).size.toB256 ≠ 0)
    (haddressCold : implementation ∉ base.accessedAddresses)
    (himplementationRaw :
      base.getStorVal sevm.currentTarget implementationSlotLit = 0)
    (himplementationOriginal :
      getOrigStorVal sevm sevm.currentTarget implementationSlotLit = 0)
    (himplementationCold : (sevm.currentTarget, implementationSlotLit) ∉
      base.accessedStorageKeys)
    (hadminRaw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (hadminOriginal :
      getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hadminCold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hstatic : sevm.isStatic = false)
    (hgas : 200000 ≤ G) :
    ∃ post,
      Prog.RunCompiled sevm (base.setMach ⟨[], Mem.empty, G + 320⟩)
        (ossifiableConstructorProgram 1249 3437 2188) post ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor base sevm.currentTarget).set implementationSlotLit
          implementation.toB256).set adminSlotLit
            requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [rawUpgradedLog sevm.currentTarget implementation.toB256] ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget 0
          requestedAdmin] ∧
      post.output = runtimeBaselineBytes ∧
      post.gasLeft = G - 49894 ∧
      post.error = base.error :=
  ossifiableConstructorProgram_canonicalEmptyInput_runCompiled
    hvalue hinput himplementationNonzero hrequestedNonzero
    hcodeSizeNonzero haddressCold himplementationRaw
    himplementationOriginal himplementationCold hadminRaw hadminOriginal
    hadminCold hstatic hgas

end Blanc.ProxyPair
