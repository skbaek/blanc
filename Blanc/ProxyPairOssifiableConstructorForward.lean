import Blanc.ProxyPairOssifiableConstructorExecution

/-!
# OssifiableProxy constructor forward execution

This module constructs the concrete successful walk through the constructor's
post-setup phase.  The first public boundary covers the canonical empty-data
case: the admin slot is cold and zero, the requested admin is nonzero, and the
function emits `AdminChanged`, performs the packed write, copies the appended
runtime, and returns it.
-/

namespace Blanc.ProxyPair

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- A zero packed slot discards every preserved-mask bit before the new address
word is merged. -/
theorem b256_and_zero_or (mask value : B256) :
    (mask &&& 0) ||| value = value := by
  rcases mask with ⟨⟨mh0, mh1⟩, ⟨ml0, ml1⟩⟩
  rcases value with ⟨⟨vh0, vh1⟩, ⟨vl0, vl1⟩⟩
  apply Prod.ext <;> apply Prod.ext <;>
    change (_ &&& (0 : UInt64)) ||| _ = _ <;>
    rw [UInt64.and_zero, UInt64.zero_or]

private def stageReturnEnd : Func :=
  ossifiablePushCreationCoordinate 2197 ::: pushB256 0 ::: Func.ret

private def stageCopy : Func :=
  ossifiablePushCreationCoordinate 2197 :::
    ossifiablePushCreationCoordinate 1250 :::
    pushB256 0 ::: codecopy ::: stageReturnEnd

private def stageSstore : Func :=
  pushB256 adminSlotLit ::: sstore ::: stageCopy

private def stageMerge : Func :=
  Ninst.and ::: Ninst.or ::: stageSstore

private def stageHighMask : Func :=
  pushB256 0 ::: Ninst.not ::: pushB256 160 ::: shl ::: stageMerge

private def stagePackedStore : Func :=
  pushB256 adminSlotLit ::: sload ::: stageHighMask

private def stageAdminStore : Func :=
  [pushB256 32, mload] +++ stagePackedStore

private def stageBranch : Func :=
  (.call 4) <?> stageAdminStore

private def stageAdminTest : Func :=
  [pushB256 32, mload] +++ iszero ::: stageBranch

private def stageLog : Func :=
  pushB256 adminChangedEventTopic ::: logWith 0 5 2 +++ stageAdminTest

private def stageRequestedStore : Func :=
  [pushB256 32, mload] +++ mstoreAt 6 +++ stageLog

private def stageOldStore : Func :=
  mstoreAt 5 +++ stageRequestedStore

private def stageClean : Func :=
  Ninst.not ::: Ninst.and ::: stageOldStore

private def stageMask : Func :=
  pushB256 160 ::: shl ::: stageClean

private theorem stageReturnEnd_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {runtimeBytes : Bytes} {G : Nat}
    (hsize : memory.size = 2208)
    (houtput : (memory.read 0 2197).1 = runtimeBytes)
    (hgas : 10 ≤ G) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G⟩) stageReturnEnd
      ((((base.setMach ⟨[], memory, G - 5⟩).memRead
        0 2197).2).withOutput runtimeBytes) := by
  unfold stageReturnEnd
  simp only [ossifiablePushCreationCoordinate_shape]
  func_run (2)
  apply Func.runCompiled_ret_word
    (devm := base.setMach
      ⟨[(0 : B256), Nat.toB256 2197], memory, G - 5⟩)
    (i := 0) (sz := Nat.toB256 2197) (s := [])
    (out := runtimeBytes) (G := G - 5) (e := 0)
  · rfl
  · exact Devm.extCost_zero_of_le
      (by rw [hsize])
      (by
        simp only [show B256.toNat (0 : B256) = 0 by rfl,
          B256.toNat_toB256_of_lt (show 2197 < 2 ^ 256 by decide)]
        rw [hsize]
        omega)
  · simp only [Devm.gasLeft_setMach]
    omega
  · rw [Devm.memRead_fst]
    simpa only [Devm.memory_setMach,
      show (0 : B256).toNat = 0 by rfl,
      B256.toNat_toB256_of_lt (show 2197 < 2 ^ 256 by decide)]
      using houtput

private theorem stageCopy_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {runtimeBytes : Bytes} {G n copyCost : Nat}
    (hsize : memory.size = n)
    (hsmall : n < 2197)
    (hcopyCost :
      gVerylow + gasCopy * ceilDiv 2197 32 +
        (calculateMemoryGasCost (memExtSize n 0 2197) -
          calculateMemoryGasCost n) = copyCost)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : copyCost + 18 ≤ G) :
    Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory, G⟩) stageCopy
      ((((base.setMach
          ⟨[], memory.write 0 runtimeBytes, G - (copyCost + 13)⟩).memRead
            0 2197).2).withOutput runtimeBytes) := by
  let copiedMemory : Mem := memory.write 0 runtimeBytes
  have hsizeCopied : copiedMemory.size = 2208 := by
    unfold copiedMemory
    rw [Mem.size_write_of_length hruntimeLength (by omega), hsize,
      if_neg (by omega)]
    decide
  have houtputCopied : (copiedMemory.read 0 2197).1 = runtimeBytes := by
    unfold copiedMemory
    rw [← hruntimeLength]
    exact Mem.read_write_zero memory hruntimeNonempty
  have hcopy : memory.write (B256.toNat (0 : B256))
      (sevm.code.sliceD (Nat.toB256 1250).toNat
        (Nat.toB256 2197).toNat (0 : UInt8)) = copiedMemory := by
    unfold copiedMemory
    simpa only [show B256.toNat (0 : B256) = 0 by rfl,
      B256.toNat_toB256_of_lt (show 1250 < 2 ^ 256 by decide),
      B256.toNat_toB256_of_lt (show 2197 < 2 ^ 256 by decide),
      show Linst.toUInt8 .stop = (0 : UInt8) by rfl]
      using congrArg (fun bytes => memory.write 0 bytes) hcode
  unfold stageCopy
  simp only [ossifiablePushCreationCoordinate_shape]
  have hreturn := stageReturnEnd_runCompiled
    (fs := fs) (sevm := sevm) (base := base)
    (memory := copiedMemory) (runtimeBytes := runtimeBytes)
    (G := G - (copyCost + 8)) hsizeCopied houtputCopied (by omega)
  have hgasTail :
      (G - (copyCost + 8)) - 5 = G - (copyCost + 13) := by
    omega
  func_run (3)
  apply Func.RunCompiled.next
  · apply Ninst.runCompiled_codecopy_of
      (c := copyCost) (G := G - (copyCost + 8))
      (M := copiedMemory)
    · rfl
    · simp only [show (0 : B256).toNat = 0 by rfl,
        B256.toNat_toB256_of_lt (show 2197 < 2 ^ 256 by decide)]
      exact Devm.extCost_add_of_size
        (a := gVerylow + gasCopy * ceilDiv 2197 32) hsize hcopyCost
    · simpa only [Devm.memory_setMach,
        show Linst.toUInt8 .stop = (0 : UInt8) by rfl] using hcopy
    · simp only [Devm.gasLeft_setMach]
      omega
  · simpa only [Devm.setMach_setMach, hgasTail] using hreturn

private theorem stageMask_complete
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {image runtimeBytes : Bytes}
    {oldRaw requested : B256} {G : Nat}
    (hwf : Mem.Wf memory)
    (hreads : Mem.Reads memory image)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) = requested)
    (hrequestedNonzero : requested ≠ 0)
    (hraw : base.getStorVal sevm.currentTarget adminSlotLit = oldRaw)
    (hrawZero : oldRaw = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hwarm : (sevm.currentTarget, adminSlotLit) ∈
      base.accessedStorageKeys)
    (hsize : memory.size = 160)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : 100000 ≤ G) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[~~~(0 : B256), oldRaw], memory, G⟩)
        stageMask post ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 21876 ∧
      post.error = base.error := by
  let cleaned : B256 :=
    ((fun x : B256 => ~~~x)
      ((fun x y : B256 => y <<< x.toNat) 160 (~~~(0 : B256)))).and oldRaw
  let memory1 : Mem := memory.write 160 cleaned.toBytes
  have hsize1 : memory1.size = 192 := by
    unfold memory1
    rw [Mem.size_write_word_at, hsize]
    decide
  have hwf1 : Mem.Wf memory1 := by
    unfold memory1
    exact Mem.Wf.write hwf 160 cleaned.toBytes
  have hreads1 : Mem.Reads memory1
      (Bytes.writeAt image 160 cleaned.toBytes) := by
    unfold memory1
    exact Mem.Reads.write hwf hreads 160 cleaned.toBytes
  have hvalue1 :
      Bytes.toB256 ((memory1.read 32 32).1) = requested := by
    rw [Mem.Reads.read hreads1,
      Bytes.readWord_writeAt_of_disjoint image 32 160 cleaned (by omega),
      hrequested]
  have hmemory1 :
      (memory1.read 32 32).2 = memory1 := by
    apply Mem.read_snd_eq_self
    rw [hsize1]
    decide
  let memory2 : Mem := memory1.write 192 requested.toBytes
  have hsize2 : memory2.size = 224 := by
    unfold memory2
    rw [Mem.size_write_word_at, hsize1]
    decide
  have hwf2 : Mem.Wf memory2 := by
    unfold memory2
    exact Mem.Wf.write hwf1 192 requested.toBytes
  have hreads2 : Mem.Reads memory2
      (Bytes.writeAt (Bytes.writeAt image 160 cleaned.toBytes)
        192 requested.toBytes) := by
    unfold memory2
    exact Mem.Reads.write hwf1 hreads1 192 requested.toBytes
  have hlogData :
      (memory2.read 160 64).1 = cleaned.toBytes ++ requested.toBytes := by
    unfold memory2 memory1
    exact Mem.read_two_word_writes_at hwf hreads 160 cleaned requested
  have hlogMemory : (memory2.read 160 64).2 = memory2 := by
    apply Mem.read_snd_eq_self
    rw [hsize2]
    decide
  have hvalue2 : Bytes.toB256 ((memory2.read 32 32).1) = requested := by
    rw [Mem.Reads.read hreads2,
      Bytes.readWord_writeAt_of_disjoint _ 32 192 requested (by omega),
      Bytes.readWord_writeAt_of_disjoint image 32 160 cleaned (by omega),
      hrequested]
  have hmemory2 : (memory2.read 32 32).2 = memory2 := by
    apply Mem.read_snd_eq_self
    rw [hsize2]
    decide
  let adminLog : Log :=
    ⟨sevm.currentTarget, [adminChangedEventTopic],
      cleaned.toBytes ++ requested.toBytes⟩
  have hrawLog :
      (base.addLog adminLog).getStorVal sevm.currentTarget adminSlotLit =
        oldRaw := by
    exact hraw
  have hnew :
      ((((fun x y : B256 => y <<< x.toNat) 160
        ((fun x : B256 => ~~~x) 0)).and oldRaw).or requested) = requested := by
    rw [hrawZero]
    exact b256_and_zero_or _ _
  eapply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold stageMask
    func_run (2)
    unfold stageClean
    func_run (2)
    unfold stageOldStore
    func_run (2) [3]
    · exact Devm.extCost_of_size hsize (by decide)
    unfold stageRequestedStore
    func_run (2) [3]
    · exact Devm.extCost_add_of_size hsize1 (by decide)
    simp only [show ((5 : B256) * 32).toNat = 160 by decide,
      show (32 : B256).toNat = 32 by decide] at hvalue1 hmemory1 ⊢
    rw [hvalue1, hmemory1]
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[requested], memory1, G - 27⟩)
      (mstoreAt 6 +++ stageLog) _
    func_run (2) [3]
    · exact Devm.extCost_of_size hsize1 (by decide)
    simp only [prepend, show ((6 : B256) * 32).toNat = 192 by decide]
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory2, G - 36⟩) stageLog _
    unfold stageLog
    func_run (4) [1262]
    · exact Devm.extCost_add_of_size hsize2 (by decide)
    simp only [prepend,
      show ((5 : B256) * 32).toNat = 160 by decide,
      show ((2 : B256) * 32).toNat = 64 by decide]
    rw [hlogData, hlogMemory]
    change Func.RunCompiled fs sevm
      ((base.addLog adminLog).setMach ⟨[], memory2, G - 1307⟩)
      stageAdminTest _
    unfold stageAdminTest
    func_run (3) [3, 0]
    · exact Devm.extCost_add_of_size hsize2 (by decide)
    · simp only [show (32 : B256).toNat = 32 by decide]
      rw [hvalue2]
      simp [B256.eqCheck, hrequestedNonzero]
    simp only [show (32 : B256).toNat = 32 by decide]
    rw [hmemory2]
    unfold stageBranch
    func_run (1)
    unfold stageAdminStore
    func_run (2) [3]
    · exact Devm.extCost_add_of_size hsize2 (by decide)
    simp only [prepend, show (32 : B256).toNat = 32 by decide]
    rw [hvalue2, hmemory2]
    unfold stagePackedStore
    func_run (2)
    simp only [Devm.getStorVal_setMach, hrawLog]
    unfold stageHighMask
    func_run (4)
    unfold stageMerge
    func_run (2)
    unfold stageSstore
    func_run (2) [20000]
    · simp only [Devm.getStorVal_setMach, hrawLog, horiginal, hnew]
      rw [hrawZero, sstoreValueCost,
        if_pos ⟨rfl, fun h => hrequestedNonzero h.symm⟩, if_pos rfl]
      norm_num [gasStorageSet]
    exact stageCopy_runCompiled
      (fs := fs) (sevm := sevm) (memory := memory2)
      (runtimeBytes := runtimeBytes) (G := G - 21458)
      (n := 224) (copyCost := 405)
      hsize2 (by omega) (by decide) hcode hruntimeLength
      hruntimeNonempty (by omega)
  · rfl
  · simp only [Devm.withOutput_gasLeft, Devm.memRead_gasLeft,
      Devm.gasLeft_setMach]
    omega
  · rfl

private theorem stageMask_dirtyCovered_complete
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {image runtimeBytes : Bytes}
    {oldRaw requested : B256} {G : Nat}
    (hwf : Mem.Wf memory)
    (hreads : Mem.Reads memory image)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) = requested)
    (hrequestedNonzero : requested ≠ 0)
    (hraw : base.getStorVal sevm.currentTarget adminSlotLit = oldRaw)
    (hrawNonzero : oldRaw ≠ 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hwarm : (sevm.currentTarget, adminSlotLit) ∈
      base.accessedStorageKeys)
    (hsize : memory.size = 288)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : 100000 ≤ G) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[~~~(0 : B256), oldRaw], memory, G⟩)
        stageMask post ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 1964 ∧
      post.error = base.error := by
  let cleaned : B256 :=
    ((fun x : B256 => ~~~x)
      ((fun x y : B256 => y <<< x.toNat) 160 (~~~(0 : B256)))).and oldRaw
  let memory1 : Mem := memory.write 160 cleaned.toBytes
  have hsize1 : memory1.size = 288 := by
    unfold memory1
    rw [Mem.size_write_word_at, hsize]
    decide
  have hwf1 : Mem.Wf memory1 := by
    unfold memory1
    exact Mem.Wf.write hwf 160 cleaned.toBytes
  have hreads1 : Mem.Reads memory1
      (Bytes.writeAt image 160 cleaned.toBytes) := by
    unfold memory1
    exact Mem.Reads.write hwf hreads 160 cleaned.toBytes
  have hvalue1 :
      Bytes.toB256 ((memory1.read 32 32).1) = requested := by
    rw [Mem.Reads.read hreads1,
      Bytes.readWord_writeAt_of_disjoint image 32 160 cleaned (by omega),
      hrequested]
  have hmemory1 :
      (memory1.read 32 32).2 = memory1 := by
    apply Mem.read_snd_eq_self
    rw [hsize1]
    decide
  let memory2 : Mem := memory1.write 192 requested.toBytes
  have hsize2 : memory2.size = 288 := by
    unfold memory2
    rw [Mem.size_write_word_at, hsize1]
    decide
  have hwf2 : Mem.Wf memory2 := by
    unfold memory2
    exact Mem.Wf.write hwf1 192 requested.toBytes
  have hreads2 : Mem.Reads memory2
      (Bytes.writeAt (Bytes.writeAt image 160 cleaned.toBytes)
        192 requested.toBytes) := by
    unfold memory2
    exact Mem.Reads.write hwf1 hreads1 192 requested.toBytes
  have hlogData :
      (memory2.read 160 64).1 = cleaned.toBytes ++ requested.toBytes := by
    unfold memory2 memory1
    exact Mem.read_two_word_writes_at hwf hreads 160 cleaned requested
  have hlogMemory : (memory2.read 160 64).2 = memory2 := by
    apply Mem.read_snd_eq_self
    rw [hsize2]
    decide
  have hvalue2 : Bytes.toB256 ((memory2.read 32 32).1) = requested := by
    rw [Mem.Reads.read hreads2,
      Bytes.readWord_writeAt_of_disjoint _ 32 192 requested (by omega),
      Bytes.readWord_writeAt_of_disjoint image 32 160 cleaned (by omega),
      hrequested]
  have hmemory2 : (memory2.read 32 32).2 = memory2 := by
    apply Mem.read_snd_eq_self
    rw [hsize2]
    decide
  let adminLog : Log :=
    ⟨sevm.currentTarget, [adminChangedEventTopic],
      cleaned.toBytes ++ requested.toBytes⟩
  have hrawLog :
      (base.addLog adminLog).getStorVal sevm.currentTarget adminSlotLit =
        oldRaw := by
    exact hraw
  eapply Exists.intro
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold stageMask
    func_run (2)
    unfold stageClean
    func_run (2)
    unfold stageOldStore
    func_run (2) [0]
    · exact Devm.extCost_of_size hsize (by decide)
    unfold stageRequestedStore
    func_run (2) [3]
    · exact Devm.extCost_add_of_size hsize1 (by decide)
    simp only [show ((5 : B256) * 32).toNat = 160 by decide,
      show (32 : B256).toNat = 32 by decide] at hvalue1 hmemory1 ⊢
    rw [hvalue1, hmemory1]
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[requested], memory1, G - 24⟩)
      (mstoreAt 6 +++ stageLog) _
    func_run (2) [0]
    · exact Devm.extCost_of_size hsize1 (by decide)
    simp only [prepend, show ((6 : B256) * 32).toNat = 192 by decide]
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[], memory2, G - 30⟩) stageLog _
    unfold stageLog
    func_run (4) [1262]
    · exact Devm.extCost_add_of_size hsize2 (by decide)
    simp only [prepend,
      show ((5 : B256) * 32).toNat = 160 by decide,
      show ((2 : B256) * 32).toNat = 64 by decide]
    rw [hlogData, hlogMemory]
    change Func.RunCompiled fs sevm
      ((base.addLog adminLog).setMach ⟨[], memory2, G - 1301⟩)
      stageAdminTest _
    unfold stageAdminTest
    func_run (3) [3, 0]
    · exact Devm.extCost_add_of_size hsize2 (by decide)
    · simp only [show (32 : B256).toNat = 32 by decide]
      rw [hvalue2]
      simp [B256.eqCheck, hrequestedNonzero]
    simp only [show (32 : B256).toNat = 32 by decide]
    rw [hmemory2]
    unfold stageBranch
    func_run (1)
    unfold stageAdminStore
    func_run (2) [3]
    · exact Devm.extCost_add_of_size hsize2 (by decide)
    simp only [prepend, show (32 : B256).toNat = 32 by decide]
    rw [hvalue2, hmemory2]
    unfold stagePackedStore
    func_run (2)
    simp only [Devm.getStorVal_setMach, hrawLog]
    unfold stageHighMask
    func_run (4)
    unfold stageMerge
    func_run (2)
    unfold stageSstore
    func_run (2) [100]
    · simp only [Devm.getStorVal_setMach, hrawLog, horiginal]
      rw [sstoreValueCost, if_neg (by
        intro hclean
        exact hrawNonzero hclean.1.symm)]
      norm_num [gasWarmAccess]
    exact stageCopy_runCompiled
      (fs := fs) (sevm := sevm) (memory := memory2)
      (runtimeBytes := runtimeBytes) (G := G - 1552)
      (n := 288) (copyCost := 399)
      hsize2 (by omega) (by decide) hcode hruntimeLength
      hruntimeNonempty (by omega)
  · rfl
  · simp only [Devm.withOutput_gasLeft, Devm.memRead_gasLeft,
      Devm.gasLeft_setMach]
    omega
  · rfl

/-- Construct the exact canonical post-setup path from a cold, zero admin slot.
The conservative gas premise leaves a large explicit reserve for the later
whole-constructor and CREATE composition. -/
theorem ossifiableConstructorAfterSetup_zeroAdmin_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {image runtimeBytes : Bytes}
    {requestedAdmin : Adr} {G : Nat}
    (hwf : Mem.Wf memory)
    (hreads : Mem.Reads memory image)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hraw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hcold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hsize : memory.size = 160)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : 102108 ≤ G) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory, G⟩)
        (ossifiableConstructorAfterSetup 1250 2197) post ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 23984 ∧
      post.error = base.error := by
  let warmBase : Devm :=
    addAccessedStorageKey base sevm.currentTarget adminSlotLit
  have hwarm : (sevm.currentTarget, adminSlotLit) ∈
      warmBase.accessedStorageKeys := by
    exact Std.HashSet.mem_insert_self
  have hrawWarm :
      warmBase.getStorVal sevm.currentTarget adminSlotLit = 0 := by
    exact hraw
  have hrequestedWordNonzero : requestedAdmin.toB256 ≠ 0 := by
    intro hzero
    apply hrequestedNonzero
    apply Adr.toB256_inj
    rw [hzero]
    decide
  have htail := stageMask_complete
    (fs := fs) (sevm := sevm) (base := warmBase)
    (memory := memory) (image := image) (runtimeBytes := runtimeBytes)
    (oldRaw := 0) (requested := requestedAdmin.toB256) (G := G - 2108)
    hwf hreads hrequested hrequestedWordNonzero hrawWarm rfl horiginal
    hwarm hsize hstatic hcode hruntimeLength hruntimeNonempty (by omega)
  rcases htail with ⟨post, htail, houtput, hgasPost, herrorPost⟩
  refine ⟨post, ?_, houtput, ?_, ?_⟩
  · rw [ossifiableConstructorAfterSetup_shape]
    func_run (4)
    simp only [Devm.getStorVal_setMach, hraw]
    change Func.RunCompiled fs sevm
      (warmBase.setMach ⟨[~~~(0 : B256), 0], memory, G - 2108⟩)
      stageMask post
    exact htail
  · rw [hgasPost]
    omega
  · calc
      post.error = warmBase.error := herrorPost
      _ = base.error := rfl

/-- Construct the successful post-setup path when the child has already
written a canonical nonzero admin word.  The slot and 288-byte decoder memory
are warm/covered, so the final admin write is a 100-gas dirty `SSTORE`; the
complete path consumes exactly 2,072 gas. -/
theorem ossifiableConstructorAfterSetup_dirtyAdmin_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {image runtimeBytes : Bytes}
    {oldRaw : B256} {requestedAdmin : Adr} {G : Nat}
    (hwf : Mem.Wf memory)
    (hreads : Mem.Reads memory image)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hraw : base.getStorVal sevm.currentTarget adminSlotLit = oldRaw)
    (hrawNonzero : oldRaw ≠ 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hwarm : (sevm.currentTarget, adminSlotLit) ∈
      base.accessedStorageKeys)
    (hsize : memory.size = 288)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hgas : 100108 ≤ G) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory, G⟩)
        (ossifiableConstructorAfterSetup 1250 2197) post ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 2072 ∧
      post.error = base.error := by
  have hrequestedWordNonzero : requestedAdmin.toB256 ≠ 0 := by
    intro hzero
    apply hrequestedNonzero
    apply Adr.toB256_inj
    rw [hzero]
    decide
  have htail := stageMask_dirtyCovered_complete
    (fs := fs) (sevm := sevm) (base := base)
    (memory := memory) (image := image) (runtimeBytes := runtimeBytes)
    (oldRaw := oldRaw) (requested := requestedAdmin.toB256) (G := G - 108)
    (hwf := hwf) (hreads := hreads) (hrequested := hrequested)
    (hrequestedNonzero := hrequestedWordNonzero) (hraw := hraw)
    (hrawNonzero := hrawNonzero)
    (horiginal := horiginal) (hwarm := hwarm) (hsize := hsize)
    (hstatic := hstatic) (hcode := hcode)
    (hruntimeLength := hruntimeLength)
    (hruntimeNonempty := hruntimeNonempty) (hgas := by omega)
  rcases htail with ⟨post, htail, houtput, hgasPost, herrorPost⟩
  refine ⟨post, ?_, houtput, ?_, herrorPost⟩
  · rw [ossifiableConstructorAfterSetup_shape]
    func_run (4)
    simp only [Devm.getStorVal_setMach, hraw]
    change Func.RunCompiled fs sevm
      (base.setMach ⟨[~~~(0 : B256), oldRaw], memory, G - 108⟩)
      stageMask post
    exact htail
  · rw [hgasPost]
    omega

/-- Exact storage/log/output certificate for the dirty post-setup admin path.
The event records the child-written admin word before the requested admin is
installed. -/
theorem ossifiableConstructorAfterSetup_dirtyAdmin_forward_exact
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {image runtimeBytes : Bytes}
    {oldRaw : B256} {requestedAdmin : Adr} {G : Nat}
    (hwf : Mem.Wf memory)
    (hreads : Mem.Reads memory image)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hraw : base.getStorVal sevm.currentTarget adminSlotLit = oldRaw)
    (hrawNonzero : oldRaw ≠ 0)
    (hnew : addressSlotWriteWord oldRaw requestedAdmin.toB256 =
      requestedAdmin.toB256)
    (horiginal : getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hwarm : (sevm.currentTarget, adminSlotLit) ∈
      base.accessedStorageKeys)
    (hsize : memory.size = 288)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hZeroAdmin : fs[4]? = some (Func.revData zeroAdminErrorData))
    (hgas : 100108 ≤ G) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory, G⟩)
        (ossifiableConstructorAfterSetup 1250 2197) post ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor base sevm.currentTarget).set adminSlotLit
          requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget oldRaw
          requestedAdmin] ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 2072 ∧
      post.error = base.error := by
  rcases ossifiableConstructorAfterSetup_dirtyAdmin_runCompiled
      (fs := fs) (sevm := sevm) (base := base)
      (memory := memory) (image := image) (runtimeBytes := runtimeBytes)
      (oldRaw := oldRaw) (requestedAdmin := requestedAdmin) (G := G)
      hwf hreads hrequested hrequestedNonzero hraw hrawNonzero
      horiginal hwarm hsize hstatic hcode hruntimeLength hruntimeNonempty
      hgas with
    ⟨post, run, houtput, hgasPost, herrorPost⟩
  have effects := ossifiableConstructorAfterSetup_success
    (runtimeOffset := 1250) (runtimeLength := 2197)
    (fs := fs) (sevm := sevm)
    (pre := base.setMach ⟨[], memory, G⟩) (post := post)
    (tail := []) (image := image) (runtimeBytes := runtimeBytes)
    (requestedAdmin := requestedAdmin)
    hZeroAdmin
    (by simpa only [Devm.memory_setMach] using hwf)
    (by simpa only [Devm.memory_setMach] using hreads)
    hrequested hcode hruntimeLength hruntimeNonempty (by decide) (by decide)
    nil_pref (Func.RunCompiledTo.of_runCompiled run)
  rcases effects with ⟨_, hstorage, hlogs, _⟩
  refine ⟨post, run, ?_, ?_, houtput, hgasPost, herrorPost⟩
  · have hpreStorage :
        Devm.getStor (base.setMach ⟨[], memory, G⟩) sevm.currentTarget =
          Devm.getStor base sevm.currentTarget := rfl
    rw [hpreStorage, Devm.getStorVal_setMach, hraw, hnew] at hstorage
    exact hstorage
  · have hpreLogs :
        (base.setMach ⟨[], memory, G⟩).logs = base.logs := rfl
    rw [hpreLogs, Devm.getStorVal_setMach, hraw] at hlogs
    exact hlogs

/-- The constructed canonical path discharges the semantic postcondition as
an exact storage/log/output certificate. -/
theorem ossifiableConstructorAfterSetup_zeroAdmin_forward_exact
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {memory : Mem} {image runtimeBytes : Bytes}
    {requestedAdmin : Adr} {G : Nat}
    (hwf : Mem.Wf memory)
    (hreads : Mem.Reads memory image)
    (hrequested : Bytes.toB256 (image.sliceD 32 32 0) =
      requestedAdmin.toB256)
    (hrequestedNonzero : requestedAdmin ≠ 0)
    (hraw : base.getStorVal sevm.currentTarget adminSlotLit = 0)
    (horiginal : getOrigStorVal sevm sevm.currentTarget adminSlotLit = 0)
    (hcold : (sevm.currentTarget, adminSlotLit) ∉
      base.accessedStorageKeys)
    (hsize : memory.size = 160)
    (hstatic : sevm.isStatic = false)
    (hcode : sevm.code.sliceD 1250 2197 (Linst.toUInt8 .stop) =
      runtimeBytes)
    (hruntimeLength : runtimeBytes.length = 2197)
    (hruntimeNonempty : runtimeBytes ≠ [])
    (hZeroAdmin : fs[4]? = some (Func.revData zeroAdminErrorData))
    (hgas : 102108 ≤ G) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], memory, G⟩)
        (ossifiableConstructorAfterSetup 1250 2197) post ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor base sevm.currentTarget).set adminSlotLit
          requestedAdmin.toB256 ∧
      post.logs = base.logs ++
        [ossifiableConstructorAdminChangedLog sevm.currentTarget 0
          requestedAdmin] ∧
      post.output = runtimeBytes ∧
      post.gasLeft = G - 23984 ∧
      post.error = base.error := by
  rcases ossifiableConstructorAfterSetup_zeroAdmin_runCompiled
      (fs := fs) (sevm := sevm) (base := base)
      (memory := memory) (image := image) (runtimeBytes := runtimeBytes)
      (requestedAdmin := requestedAdmin) (G := G)
      hwf hreads hrequested hrequestedNonzero hraw horiginal hcold hsize
      hstatic hcode hruntimeLength hruntimeNonempty hgas with
    ⟨post, run, houtput, hgasPost, herrorPost⟩
  have effects := ossifiableConstructorAfterSetup_success
    (runtimeOffset := 1250) (runtimeLength := 2197)
    (fs := fs) (sevm := sevm)
    (pre := base.setMach ⟨[], memory, G⟩) (post := post)
    (tail := []) (image := image) (runtimeBytes := runtimeBytes)
    (requestedAdmin := requestedAdmin)
    hZeroAdmin
    (by simpa only [Devm.memory_setMach] using hwf)
    (by simpa only [Devm.memory_setMach] using hreads)
    hrequested hcode hruntimeLength hruntimeNonempty (by decide) (by decide)
    nil_pref (Func.RunCompiledTo.of_runCompiled run)
  rcases effects with ⟨_, hstorage, hlogs, _⟩
  refine ⟨post, run, ?_, ?_, houtput, hgasPost, herrorPost⟩
  · have hpreStorage :
        Devm.getStor (base.setMach ⟨[], memory, G⟩) sevm.currentTarget =
          Devm.getStor base sevm.currentTarget := rfl
    rw [hpreStorage, Devm.getStorVal_setMach, hraw,
      addressSlotWriteWord, b256_and_zero_or] at hstorage
    exact hstorage
  · have hpreLogs :
        (base.setMach ⟨[], memory, G⟩).logs = base.logs := rfl
    rw [hpreLogs, Devm.getStorVal_setMach, hraw] at hlogs
    exact hlogs

end Blanc.ProxyPair
