import Blanc.Lift.Usdc.ProxyCreation.ConstantsCheck
import Blanc.Lift.Usdc.ProxyCreation.RuntimeReturn
import Blanc.Lift.Deploy
import Blanc.MemoryLayout

/-!
# The original proxy constructor's entry prefix

The actual registered entry decodes its constructor argument and checks the
fixed implementation label before invoking the first internal callee.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune

/-- Exact ordered word writes completed before the first internal call. -/
def prefixWords : List (Nat × B256) :=
  [(64, 128), (128, initialImplementation), (64, 160),
    (160, implementationLabelLeft), (192, implementationLabelRight)]

def prefixMemory : Mem :=
  (MemoryStage.words prefixWords).applyMemory Mem.empty

theorem prefixMemory_size : prefixMemory.size = 224 := by
  unfold prefixMemory
  rw [MemoryStage.applyMemory_words_size _ _ (by decide)]
  decide

theorem prefixMemory_wf : Mem.Wf prefixMemory :=
  (MemoryStage.wf_reads (MemoryStage.words prefixWords) Mem.wf_empty Mem.reads_empty).1

theorem prefixMemory_reads :
    Mem.Reads prefixMemory ((MemoryStage.words prefixWords).applyImage []) :=
  (MemoryStage.wf_reads (MemoryStage.words prefixWords) Mem.wf_empty Mem.reads_empty).2

theorem prefixMemory_freePointer :
    Bytes.toB256 (prefixMemory.read 64 32).1 = 160 := by
  rw [prefixMemory_reads.read]
  have word := MemoryStage.read_written_word [(64, 128), (128, initialImplementation)]
    [(160, implementationLabelLeft), (192, implementationLabelRight)] [] 64 160 (by
      simp only [MemoryStage.avoids, MemoryStage.words, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, B256.length_toBytes]
      decide)
  rw [show prefixWords = [(64, 128), (128, initialImplementation)] ++
    (64, 160) :: [(160, implementationLabelLeft), (192, implementationLabelRight)] by rfl,
    word]
  exact B256.toB256_toBytes _

/-- Memory after the later fixed admin-label store. -/
def adminMemory : Mem := prefixMemory.write 160 adminLabelWord.toBytes

/-- A returning actual first callee and its actual continuation compose with
this entry prefix. No callee postcondition is assumed by the prefix. -/
theorem prefix_runExact
    {sevm : Sevm} {b D : Devm} {G : Nat} {o : Outcome}
    (hvalue : sevm.value = 0) (hcode : sevm.code = code)
    (hcallee : SFunc.RunExact cert.prog sevm
      (St b [initialImplementation, 0xde, initialImplementation,
        initialImplementation, initialImplementation] prefixMemory G) t_0169_c1 (.returned D))
    (hcont : SFunc.RunExact cert.prog sevm D t_00de_c0 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 341)) t_0000_c0 o := by
  obtain ⟨m1, hm1⟩ : ∃ m : Mem, Mem.empty.write 64 (128 : B256).toBytes = m :=
    ⟨_, rfl⟩
  obtain ⟨m2, hm2⟩ : ∃ m : Mem, m1.write 128 initialImplementation.toBytes = m :=
    ⟨_, rfl⟩
  obtain ⟨m3, hm3⟩ : ∃ m : Mem, m2.write 64 (160 : B256).toBytes = m :=
    ⟨_, rfl⟩
  obtain ⟨m4, hm4⟩ : ∃ m : Mem, m3.write 160 implementationLabelLeft.toBytes = m :=
    ⟨_, rfl⟩
  obtain ⟨m5, hm5⟩ : ∃ m : Mem, m4.write 192 implementationLabelRight.toBytes = m :=
    ⟨_, rfl⟩
  have hprefix : prefixMemory = m5 := by
    simp only [prefixMemory, prefixWords, MemoryStage.words, List.map_cons, List.map_nil,
      MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil,
      hm1, hm2, hm3, hm4, hm5]
  rw [hprefix] at hcallee
  have wf1 : Mem.Wf m1 := hm1 ▸ Mem.Wf.write Mem.wf_empty 64 (128 : B256).toBytes
  have wf2 : Mem.Wf m2 := hm2 ▸ wf1.write 128 initialImplementation.toBytes
  have wf3 : Mem.Wf m3 := hm3 ▸ wf2.write 64 (160 : B256).toBytes
  have wf4 : Mem.Wf m4 := hm4 ▸ wf3.write 160 implementationLabelLeft.toBytes
  have r1 := hm1 ▸ Mem.Reads.write Mem.wf_empty Mem.reads_empty 64 (128 : B256).toBytes
  have r2 := hm2 ▸ r1.write wf1 128 initialImplementation.toBytes
  have r3 := hm3 ▸ r2.write wf2 64 (160 : B256).toBytes
  have r4 := hm4 ▸ r3.write wf3 160 implementationLabelLeft.toBytes
  have r5 := hm5 ▸ r4.write wf4 192 implementationLabelRight.toBytes
  have size1 : m1.size = 96 := by
    rw [← hm1, Mem.size_write_of_size (show Mem.empty.size = 0 from rfl)
      (by decide) (B256.length_toBytes _)]
    rfl
  have size2 : m2.size = 160 := by
    rw [← hm2, Mem.size_write_of_size size1 (by decide) (B256.length_toBytes _)]
    rfl
  have size3 : m3.size = 160 := by
    rw [← hm3, Mem.size_write_of_size size2 (by decide) (B256.length_toBytes _)]
    rfl
  have size4 : m4.size = 192 := by
    rw [← hm4, Mem.size_write_of_size size3 (by decide) (B256.length_toBytes _)]
    rfl
  have size5 : m5.size = 224 := by
    rw [← hm5, Mem.size_write_of_size size4 (by decide) (B256.length_toBytes _)]
    rfl
  have load1 : Bytes.toB256 (m1.read 64 32).1 = 128 := by
    rw [r1.read]
    exact Bytes.readWord_writeAt_self _ _ _
  have load2 : Bytes.toB256 (m3.read 128 32).1 = initialImplementation := by
    rw [r3.read, Bytes.readWord_writeAt_of_disjoint _ 128 64 _ (Or.inr (by decide))]
    exact Bytes.readWord_writeAt_self _ _ _
  have load3 : Bytes.toB256 (m3.read 64 32).1 = 160 := by
    rw [r3.read]
    exact Bytes.readWord_writeAt_self _ _ _
  have load5 : Bytes.toB256 (m5.read 64 32).1 = 160 := by
    rw [r5.read,
      Bytes.readWord_writeAt_of_disjoint _ 64 192 _ (Or.inl (by decide)),
      Bytes.readWord_writeAt_of_disjoint _ 64 160 _ (Or.inl (by decide))]
    exact Bytes.readWord_writeAt_self _ _ _
  have hash5 : (m5.read 160 35).1.keccak = implSlot := by
    rw [r5.read]
    have image64 := Bytes.read_two_word_writes_at
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt [] 64 (128 : B256).toBytes)
        128 initialImplementation.toBytes) 64 (160 : B256).toBytes)
      160 implementationLabelLeft implementationLabelRight
    have image35 := Bytes.sliceD_of_sliceD_eq image64 (by decide : 0 + 35 ≤ 64)
    rw [show 160 = 160 + 0 from rfl, image35, implementationLabel_bytes,
      implementationLabel_hash]
  have copied : sevm.code.sliceD 2857 32 (Linst.toUInt8 .stop) =
      initialImplementation.toBytes := by
    rw [hcode, ByteArray.sliceD_eq]
    exact argument_window
  unfold t_0000_c0
  apply rx_push (w := 128) (by decide) (by decide)
  apply rx_push (w := 64) (by decide) (by decide)
  refine rx_mstore (c := 12) (M' := m1) ?_ hm1 ?_
  · rw [St.extCost_eq (show Mem.empty.size = 0 from rfl)]
    decide
  · apply rx_callvalue (by decide)
    rw [hvalue]
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_iszero (v := 1) (by decide) (by decide)
    apply rx_push (w := 16) (by decide) (by decide)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    unfold t_0010_c0
    apply rx_dest
    apply rx_pop
    apply rx_push (w := 64) (by decide) (by decide)
    refine rx_mload (v := 128) (c := 3) (by rw [St.extCost_eq size1]; decide)
      load1 (read_covered size1 (by decide) (by decide)) (by decide) ?_
    apply rx_push (w := 32) (by decide) (by decide)
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_push (w := 2857) (by decide) (by decide)
    apply rx_dup (n := 3) rfl (by decide)
    refine rx_codecopy (c := 12) (M' := m2)
      (by rw [St.extCost_eq size1]; decide) (by
        change m1.write 128 (sevm.code.sliceD 2857 32 (Linst.toUInt8 .stop)) = m2
        rw [copied]
        exact hm2) ?_
    apply rx_dup (n := 1) rfl (by decide)
    apply rx_add' (v := 160) (by decide) (by decide)
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_push (w := 64) (by decide) (by decide)
    refine rx_mstore (c := 3) (M' := m3)
      (by rw [St.extCost_eq size2]; decide) hm3 ?_
    apply rx_dup (n := 1) rfl (by decide)
    apply rx_add' (v := 288) (by decide) (by decide)
    apply rx_swap1
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_dup (n := 0) rfl (by decide)
    refine rx_mload (v := initialImplementation) (c := 3)
      (by rw [St.extCost_eq size3]; decide)
      load2 (read_covered size3 (by decide) (by decide)) (by decide) ?_
    apply rx_swap1
    apply rx_push (w := 32) (by decide) (by decide)
    apply rx_add' (v := 160) (by decide) (by decide)
    apply rx_swap1
    apply rx_swap3
    apply rx_swap2
    apply rx_swap1
    apply rx_pop
    apply rx_pop
    apply rx_pop
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_push (w := 64) (by decide) (by decide)
    refine rx_mload (v := 160) (c := 3) (by rw [St.extCost_eq size3]; decide)
      load3 (read_covered size3 (by decide) (by decide)) (by decide) ?_
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_push (w := implementationLabelLeft) (by decide) (by decide)
    apply rx_dup (n := 1) rfl (by decide)
    refine rx_mstore (c := 6) (M' := m4)
      (by rw [St.extCost_eq size3]; decide) hm4 ?_
    apply rx_push (w := 32) (by decide) (by decide)
    apply rx_add' (v := 192) (by decide) (by decide)
    apply rx_push (w := implementationLabelRight) (by decide) (by decide)
    apply rx_dup (n := 1) rfl (by decide)
    refine rx_mstore (c := 6) (M' := m5)
      (by rw [St.extCost_eq size4]; decide) hm5 ?_
    apply rx_pop
    apply rx_push (w := 35) (by decide) (by decide)
    apply rx_add' (v := 195) (by decide) (by decide)
    apply rx_swap1
    apply rx_pop
    apply rx_push (w := 64) (by decide) (by decide)
    refine rx_mload (v := 160) (c := 3) (by rw [St.extCost_eq size5]; decide)
      load5 (read_covered size5 (by decide) (by decide)) (by decide) ?_
    apply rx_dup (n := 0) rfl (by decide)
    apply rx_swap2
    apply rx_sub' (v := 35) (by decide) (by decide)
    apply rx_swap1
    refine rx_keccak (v := implSlot) (c := 42)
      (by rw [St.extCost_eq size5]; decide) hash5
      (Mem.read_snd_eq_self (by rw [size5]; decide)) (by decide) ?_
    apply rx_push (w := 0) (by decide) (by decide)
    apply rx_not (v := ~~~ (0 : B256)) rfl (by decide)
    apply rx_and (v := implSlot) (by decide) (by decide)
    apply rx_push (w := implSlot) (by decide) (by decide)
    apply rx_push (w := 1) (by decide) (by decide)
    apply rx_mul (v := implSlot) (by decide) (by decide)
    apply rx_push (w := 0) (by decide) (by decide)
    apply rx_not (v := ~~~ (0 : B256)) rfl (by decide)
    apply rx_and (v := implSlot) (by decide) (by decide)
    apply rx_eq (v := 1) (by decide) (by decide)
    apply rx_iszero (v := 0) (by decide) (by decide)
    apply rx_iszero (v := 1) (by decide) (by decide)
    apply rx_push (w := 0xc6) (by decide) (by decide)
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    unfold t_00c6_c0
    apply rx_dest
    apply rx_push (w := 0xde) (by decide) (by decide)
    apply rx_dup (n := 1) rfl (by decide)
    apply rx_push (w := 0x169) (by decide) (by decide)
    apply rx_push (w := 4294967296) (by decide) (by decide)
    apply rx_mul (v := 1550483193856) (by decide) (by decide)
    apply rx_push (w := 4294967296) (by decide) (by decide)
    apply rx_swap1
    apply rx_div (v := 0x169) (by decide) (by decide)
    exact rx_callRet rfl hcallee hcont

/-- The actual post-first-callee continuation checks the admin label and
invokes the admin writer with the executing message's actual caller. -/
theorem adminPrefix_runExact
    {sevm : Sevm} {b D : Devm} {G : Nat} {o : Outcome}
    (hcallee : SFunc.RunExact cert.prog sevm
      (St b [sevm.caller.toB256, 0x162, initialImplementation,
        initialImplementation] adminMemory G) t_024e_c2 (.returned D))
    (hcont : SFunc.RunExact cert.prog sevm D t_0162_c0 o) :
    SFunc.RunExact cert.prog sevm
      (St b [initialImplementation, initialImplementation, initialImplementation]
        prefixMemory (G + 178)) t_00de_c0 o := by
  obtain ⟨M, hM⟩ : ∃ M : Mem, prefixMemory = M := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Mem, M.write 160 adminLabelWord.toBytes = A := ⟨_, rfl⟩
  have hadmin : adminMemory = A := by rw [adminMemory, hM, hA]
  rw [hM]
  rw [hadmin] at hcallee
  have wf : Mem.Wf M := hM ▸ prefixMemory_wf
  have reads := hM ▸ prefixMemory_reads
  have size : M.size = 224 := hM ▸ prefixMemory_size
  have free : Bytes.toB256 (M.read 64 32).1 = 160 := hM ▸ prefixMemory_freePointer
  have readsA := hA ▸ reads.write wf 160 adminLabelWord.toBytes
  have sizeA : A.size = 224 := by
    rw [← hA, Mem.size_write_of_size size (by decide) (B256.length_toBytes _)]
    rfl
  have freeA : Bytes.toB256 (A.read 64 32).1 = 160 := by
    rw [readsA.read,
      Bytes.readWord_writeAt_of_disjoint _ 64 160 _ (Or.inl (by decide)),
      ← reads.read 64 32]
    exact free
  have hashA : (A.read 160 26).1.keccak = adminSlot := by
    rw [readsA.read,
      Bytes.sliceD_writeAt_inside _ _ 160 160 26 (by decide)
        (by rw [B256.length_toBytes]; decide)]
    change Bytes.keccak (adminLabelWord.toBytes.sliceD 0 26 0) = adminSlot
    rw [adminLabel_bytes, adminLabel_hash]
  unfold t_00de_c0
  apply rx_dest
  apply rx_pop
  apply rx_push (w := 64) (by decide) (by decide)
  refine rx_mload (v := 160) (c := 3) (by rw [St.extCost_eq size]; decide)
    free (read_covered size (by decide) (by decide)) (by decide) ?_
  apply rx_dup (n := 0) rfl (by decide)
  apply rx_dup (n := 0) rfl (by decide)
  apply rx_push (w := adminLabelWord) (by decide) (by decide)
  apply rx_dup (n := 1) rfl (by decide)
  refine rx_mstore (c := 3) (M' := A)
    (by rw [St.extCost_eq size]; decide) hA ?_
  apply rx_pop
  apply rx_push (w := 26) (by decide) (by decide)
  apply rx_add' (v := 186) (by decide) (by decide)
  apply rx_swap1
  apply rx_pop
  apply rx_push (w := 64) (by decide) (by decide)
  refine rx_mload (v := 160) (c := 3) (by rw [St.extCost_eq sizeA]; decide)
    freeA (read_covered sizeA (by decide) (by decide)) (by decide) ?_
  apply rx_dup (n := 0) rfl (by decide)
  apply rx_swap2
  apply rx_sub' (v := 26) (by decide) (by decide)
  apply rx_swap1
  refine rx_keccak (v := adminSlot) (c := 36)
    (by rw [St.extCost_eq sizeA]; decide) hashA
    (Mem.read_snd_eq_self (by rw [sizeA]; decide)) (by decide) ?_
  apply rx_push (w := 0) (by decide) (by decide)
  apply rx_not (v := ~~~ (0 : B256)) rfl (by decide)
  apply rx_and (v := adminSlot) (by decide) (by decide)
  apply rx_push (w := adminSlot) (by decide) (by decide)
  apply rx_push (w := 1) (by decide) (by decide)
  apply rx_mul (v := adminSlot) (by decide) (by decide)
  apply rx_push (w := 0) (by decide) (by decide)
  apply rx_not (v := ~~~ (0 : B256)) rfl (by decide)
  apply rx_and (v := adminSlot) (by decide) (by decide)
  apply rx_eq (v := 1) (by decide) (by decide)
  apply rx_iszero (v := 0) (by decide) (by decide)
  apply rx_iszero (v := 1) (by decide) (by decide)
  apply rx_push (w := 0x14a) (by decide) (by decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_014a_c0
  apply rx_dest
  apply rx_push (w := 0x162) (by decide) (by decide)
  apply rx_caller (by decide)
  apply rx_push (w := 0x24e) (by decide) (by change 4 < 1024; decide)
  apply rx_push (w := 4294967296) (by decide) (by change 5 < 1024; decide)
  apply rx_mul (v := 2534030704640) (by decide) (by change 4 < 1024; decide)
  apply rx_push (w := 4294967296) (by decide) (by change 5 < 1024; decide)
  apply rx_swap1
  apply rx_div (v := 0x24e) (by decide) (by change 4 < 1024; decide)
  exact rx_callRet rfl hcallee hcont

/-- The actual final caller continuation discards the retained arguments and
jumps to the registered runtime-return entry. -/
theorem terminal_runExact
    {sevm : Sevm} {b : Devm} {x y : B256} {M : Mem} {G : Nat} {o : Outcome}
    (hcont : SFunc.RunExact cert.prog sevm (St b [] M G) t_0290_c3 o) :
    SFunc.RunExact cert.prog sevm (St b [x, y] M (G + 16)) t_0162_c0 o := by
  unfold t_0162_c0
  apply rx_dest
  apply rx_pop
  apply rx_pop
  apply rx_push (w := 0x290) (by decide) (by decide)
  exact rx_jump rfl hcont

/-- Compose the terminal caller with the accepted runtime-copy/return producer,
retaining its actual expansion and the arbitrary contextual base. -/
theorem terminal_runtimeReturn
    {sevm : Sevm} {b : Devm} {x y : B256} {M : Mem} {G : Nat}
    (halign : M.size % 32 = 0) :
    SFunc.RunExact cert.prog sevm
      (St b [x, y] M (G + (calculateMemoryGasCost (memExtSize M.size 0 2186) -
        calculateMemoryGasCost M.size) + 242)) t_0162_c0
      (.halted ((St b [] (M.write 0
        (sevm.code.sliceD 671 2186 (Linst.toUInt8 .stop))) G).withOutput
          (sevm.code.sliceD 671 2186 (Linst.toUInt8 .stop)))) := by
  exact terminal_runExact (runtimeReturn_runExact halign (by decide))

end Blanc.Lift.Usdc.ProxyCreation
