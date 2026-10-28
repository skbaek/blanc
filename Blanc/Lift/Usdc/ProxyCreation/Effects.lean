import Blanc.Lift.Usdc.ProxyCreation.Prefix
import Blanc.Lift.InvWalkWorld
import Blanc.LadderBase
import Blanc.CodeReadInversion

/-!
# Storage effects of the original proxy constructor

Successful runs of the actual registered source derive their two storage
updates and returned code window. Historical bytecode lifting is separate.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune

/-- The actual code-size callee preserves storage/memory and its caller's
retained stack prefix, independently of access pricing or read metadata. -/
theorem isContract_effects
    {sevm : Sevm} {b post : Devm} {x rho : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.Run cert.prog sevm (St b (x :: rho :: S) M G)
      t_027d_c4 (.returned post)) :
    post.stack = B256.gtCheck (b.getCode x.toAdr).size.toB256 0 :: S ∧
      post.memory = M ∧ post.getStor = b.getStor := by
  have state := SFunc.Run.state_of_silent (S := []) (by decide)
    (by decide) (by decide) run
  have storage : post.getStor = b.getStor := funext (getStor_eq_of_state_eq state)
  have run := run.cut
  unfold t_027d_c4 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 2) rfl step
  obtain ⟨codePost, codeStep, run⟩ := ric_next run
  have codeObs := prefix_of_extcodesize_val (show x :: 0 :: 0 :: x :: rho :: S <<+
    (St b (x :: 0 :: 0 :: x :: rho :: S) M _).stack from ⟨[], by simp only [Split, St.stack, List.append_nil]⟩) codeStep
  have codeStack := Ninst.extcodesize_stack rfl codeStep
  have stack : codePost.stack =
      (b.getCode x.toAdr).size.toB256 :: 0 :: 0 :: x :: rho :: S := by
    simpa only [St, Devm.getCode_setMach, show Bytes.toB256 [0] = (0 : B256) by decide] using codeStack
  have memory : codePost.memory = M := codeObs.2.symm
  rw [St.self stack memory] at run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := 0 :: (b.getCode x.toAdr).size.toB256 :: 0 :: x :: rho :: S) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_gt step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := 0 :: (b.getCode x.toAdr).size.toB256 ::
    B256.gtCheck (b.getCode x.toAdr).size.toB256 0 :: x :: rho :: S) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := rho :: x ::
    B256.gtCheck (b.getCode x.toAdr).size.toB256 0 :: S) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := x :: rho ::
    B256.gtCheck (b.getCode x.toAdr).size.toB256 0 :: S) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, returned⟩ := ric_ret run
  simp only [Seg.done.injEq, Outcome.returned.injEq] at returned
  subst post
  exact ⟨rfl, rfl, storage⟩

/-- The actual admin writer returns after setting its literal slot. -/
theorem adminWriter_effects
    {sevm : Sevm} {b post : Devm} {x rho : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.Run cert.prog sevm (St b (x :: rho :: S) M G)
      t_024e_c2 (.returned post)) :
    post.stack = S ∧ post.memory = M ∧
    post.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set adminSlot x ∧
    (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) := by
  have run := run.cut
  unfold t_024e_c2 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_mul step
  change _ = St b (adminSlot :: 0 :: x :: rho :: S) M _ at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := 0 :: adminSlot :: x :: rho :: S) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
  obtain ⟨written, store, run⟩ := ric_next run
  have storage := sstore_getStor_set (xs := []) store
    (show adminSlot :: x :: [] <<+ (St b
      (adminSlot :: x :: adminSlot :: x :: rho :: S) M _).stack from ⟨_, rfl⟩)
  have memory : written.memory = M := (Ninst.Hinv.inv (f := Devm.memory) store).symm
  obtain ⟨key, value, popped⟩ := of_run_sstore store
  have stack : written.stack = adminSlot :: x :: rho :: S := by
    change adminSlot :: x :: adminSlot :: x :: rho :: S = key :: value :: written.stack at popped
    injection popped with _ tail
    injection tail with _ tail
    exact tail.symm
  have foreign : ∀ a, a ≠ sevm.currentTarget → written.getStor a = b.getStor a := by
    intro a different
    obtain ⟨pc, regular⟩ := of_run_reg store
    have preserved := sstore_preserves_getStor_ne regular different.symm
    exact preserved
  rw [St.self stack memory] at run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, returned⟩ := ric_ret run
  simp only [Seg.done.injEq, Outcome.returned.injEq] at returned
  subst post
  exact ⟨rfl, rfl, storage, foreign⟩

/-- The actual return entry emits its executing code window and preserves storage. -/
theorem runtimeReturn_effects
    {sevm : Sevm} {b post : Devm} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.Run cert.prog sevm (St b S M G) t_0290_c3 (.halted post)) :
    post.getStor = b.getStor ∧
      post.output = sevm.code.sliceD 671 2186 (Linst.toUInt8 .stop) := by
  exact solcRuntimeReturn_effects (sizeBytes := [0x08, 0x8a])
    (offsetBytes := [0x02, 0x9f]) (sizeBound := by decide) (offsetBound := by decide)
    (size := 2186) (offset := 671) (by decide) (by decide) (by decide) run

/-- Every registered internal writer/predicate returns rather than halting. -/
theorem internal_noHalt : NoHaltSet cert.prog [1, 2, 4] = true := by decide

/-- The actual first writer's successful return derives its literal implementation update. -/
theorem implementationWriter_effects
    {sevm : Sevm} {b post : Devm} {x rho : B256} {S : List B256} {M : Mem} {G : Nat}
    (run : SFunc.Run cert.prog sevm (St b (x :: rho :: S) M G)
      t_0169_c1 (.returned post)) :
    post.stack = S ∧ post.memory = M ∧
    post.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set implSlot x ∧
    (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) := by
  have run := run.cut
  unfold t_0169_c1 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 2) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mul step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_or step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_div step
  obtain ⟨g, called⟩ := ric_call (show cert.prog[4]? = some t_027d_c4 from rfl) run
  rcases called with ⟨D, callee, run⟩ | ⟨D, callee, _⟩
  · obtain ⟨stackD, memoryD, storageD⟩ := isContract_effects callee
    rw [St.self stackD memoryD] at run
    unfold t_0187_c1 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_iszero step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_iszero step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    rcases ric_branch run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
    · exact (SFunc.RunCutP.false_of_noOk failed (by decide)).elim
    · unfold t_0221_c1 at run
      obtain ⟨_, run⟩ := ric_dest run
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, e⟩ := ri_mul step
      change _ = St D (implSlot :: 0 :: x :: rho :: S) M _ at e
      subst e
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
      obtain ⟨written, store, run⟩ := ric_next run
      have storage := sstore_getStor_set (xs := []) store
        (show implSlot :: x :: [] <<+ (St D
          (implSlot :: x :: implSlot :: x :: rho :: S) M _).stack from ⟨_, rfl⟩)
      have memory : written.memory = M := (Ninst.Hinv.inv (f := Devm.memory) store).symm
      obtain ⟨key, value, popped⟩ := of_run_sstore store
      have stack : written.stack = implSlot :: x :: rho :: S := by
        change implSlot :: x :: implSlot :: x :: rho :: S = key :: value :: written.stack at popped
        injection popped with _ tail
        injection tail with _ tail
        exact tail.symm
      have foreign : ∀ a, a ≠ sevm.currentTarget → written.getStor a = b.getStor a := by
        intro a different
        obtain ⟨pc, regular⟩ := of_run_reg store
        have preserved := sstore_preserves_getStor_ne regular different.symm
        exact preserved.trans (congrFun storageD a)
      change written.getStor sevm.currentTarget = (D.getStor sevm.currentTarget).set implSlot x at storage
      rw [storageD] at storage
      rw [St.self stack memory] at run
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, returned⟩ := ric_ret run
      simp only [Seg.done.injEq, Outcome.returned.injEq] at returned
      subst post
      exact ⟨rfl, rfl, storage, foreign⟩
  · exact (SFunc.RunP.not_halted_entry internal_noHalt
      (by decide : 4 ∈ [1, 2, 4]) rfl callee rfl).elim

/-- A whole successful entry reaches its actual first callee and continuation. -/
theorem firstCall_inv
    {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (hcode : sevm.code = code)
    (run : SFunc.Run cert.prog sevm (St b [] Mem.empty G) t_0000_c0 o) :
    ∃ G' D, SFunc.Run cert.prog sevm
      (St b [initialImplementation, 0xde, initialImplementation,
        initialImplementation, initialImplementation] prefixMemory G')
      t_0169_c1 (.returned D) ∧ SFunc.Run cert.prog sevm D t_00de_c0 o := by
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
  rw [hprefix]
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
  have copied : sevm.code.sliceD 2857 32 (Linst.toUInt8 .stop) =
      initialImplementation.toBytes := by
    rw [hcode, ByteArray.sliceD_eq]
    exact argument_window
  have run := run.cut
  unfold t_0000_c0 at run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_mstore step
  change _ = St b [] (Mem.empty.write 64 (128 : B256).toBytes) _ at e
  rw [hm1] at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_callvalue step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  rcases ric_branch run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk failed (by decide)).elim
  · unfold t_0010_c0 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_mload step
    change _ = St b ((m1.read 64 32).1.toB256 :: _) (m1.read 64 32).2 _ at e
    rw [load1, read_covered size1 (by decide) (by decide)] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 3) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_codecopy step
    change _ = St b _ (m1.write 128 (sevm.code.sliceD 2857 32 (Linst.toUInt8 .stop))) _ at e
    rw [copied, hm2] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_add step
    change _ = St b (160 :: _) m2 _ at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_mstore step
    change _ = St b _ (m2.write 64 (160 : B256).toBytes) _ at e
    rw [hm3] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_add step
    change _ = St b (288 :: _) m3 _ at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_mload step
    change _ = St b ((m3.read 128 32).1.toB256 :: _) (m3.read 128 32).2 _ at e
    rw [load2, read_covered size3 (by decide) (by decide)] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_add step
    change _ = St b (160 :: _) m3 _ at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_mload step
    change _ = St b ((m3.read 64 32).1.toB256 :: _) (m3.read 64 32).2 _ at e
    rw [load3, read_covered size3 (by decide) (by decide)] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_mstore step
    change _ = St b _ (m3.write 160 implementationLabelLeft.toBytes) _ at e
    rw [hm4] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_add step
    change _ = St b (192 :: _) m4 _ at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_mstore step
    change _ = St b _ (m4.write 192 implementationLabelRight.toBytes) _ at e
    rw [hm5] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_add step
    change _ = St b (195 :: _) m5 _ at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_pop step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_mload step
    change _ = St b ((m5.read 64 32).1.toB256 :: _) (m5.read 64 32).2 _ at e
    rw [load5, read_covered size5 (by decide) (by decide)] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_sub step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, e⟩ := ri_keccak step
    change _ = St b ((m5.read 160 35).1.keccak :: _) (m5.read 160 35).2 _ at e
    rw [Mem.read_snd_eq_self (show memExtSize m5.size 160 35 = m5.size by rw [size5]; decide)] at e
    subst e
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_not step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_and step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_mul step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_not step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_and step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_eq step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_iszero step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_iszero step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    rcases ric_branch run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
    · exact (SFunc.RunCutP.false_of_noOk failed (by decide)).elim
    · unfold t_00c6_c0 at run
      obtain ⟨_, run⟩ := ric_dest run
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_mul step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
      obtain ⟨_, step, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_div step
      obtain ⟨g, called⟩ := ric_call (show cert.prog[1]? = some t_0169_c1 from rfl) run
      rcases called with ⟨D, callee, cont⟩ | ⟨D, callee, _⟩
      · exact ⟨g, D, callee, cont.uncut⟩
      · exact (SFunc.RunP.not_halted_entry internal_noHalt
          (by decide : 1 ∈ [1, 2, 4]) rfl callee rfl).elim

/-- The actual caller continuation reaches the admin writer with the real caller. -/
theorem secondCall_inv
    {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (run : SFunc.Run cert.prog sevm
      (St b [initialImplementation, initialImplementation, initialImplementation]
        prefixMemory G) t_00de_c0 o) :
    ∃ G' D, SFunc.Run cert.prog sevm
      (St b [sevm.caller.toB256, 0x162, initialImplementation,
        initialImplementation] adminMemory G') t_024e_c2 (.returned D) ∧
      SFunc.Run cert.prog sevm D t_0162_c0 o := by
  obtain ⟨M, hM⟩ : ∃ M : Mem, prefixMemory = M := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Mem, M.write 160 adminLabelWord.toBytes = A := ⟨_, rfl⟩
  have hadmin : adminMemory = A := by rw [adminMemory, hM, hA]
  rw [hadmin]
  rw [hM] at run
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
  have run := run.cut
  unfold t_00de_c0 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_mload step
  change _ = St b ((M.read 64 32).1.toB256 :: _) (M.read 64 32).2 _ at e
  rw [free, read_covered size (by decide) (by decide)] at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 1) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_mstore step
  change _ = St b _ (M.write 160 adminLabelWord.toBytes) _ at e
  rw [hA] at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_add step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_mload step
  change _ = St b ((A.read 64 32).1.toB256 :: _) (A.read 64 32).2 _ at e
  rw [freeA, read_covered sizeA (by decide) (by decide)] at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_sub step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, e⟩ := ri_keccak step
  change _ = St b ((A.read 160 26).1.keccak :: _) (A.read 160 26).2 _ at e
  rw [Mem.read_snd_eq_self (show memExtSize A.size 160 26 = A.size by rw [sizeA]; decide)] at e
  subst e
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_not step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_mul step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_not step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_and step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_eq step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  rcases ric_branch run with ⟨_, _, failed⟩ | ⟨_, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk failed (by decide)).elim
  · unfold t_014a_c0 at run
    obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_caller step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_mul step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl step
    obtain ⟨_, step, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_div step
    obtain ⟨g, called⟩ := ric_call (show cert.prog[2]? = some t_024e_c2 from rfl) run
    rcases called with ⟨D, callee, cont⟩ | ⟨D, callee, _⟩
    · exact ⟨g, D, callee, cont.uncut⟩
    · exact (SFunc.RunP.not_halted_entry internal_noHalt
        (by decide : 2 ∈ [1, 2, 4]) rfl callee rfl).elim

/-- The actual terminal caller reaches and returns the runtime window. -/
theorem terminal_effects
    {sevm : Sevm} {b post : Devm} {x y : B256} {M : Mem} {G : Nat}
    (run : SFunc.Run cert.prog sevm (St b [x, y] M G) t_0162_c0 (.halted post)) :
    post.getStor = b.getStor ∧
      post.output = sevm.code.sliceD 671 2186 (Linst.toUInt8 .stop) := by
  have run := run.cut
  unfold t_0162_c0 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop step
  obtain ⟨_, step, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push step
  obtain ⟨_, run⟩ := ric_jump (by decide) (show cert.prog[3]? = some t_0290_c3 from rfl) run
  exact runtimeReturn_effects run.uncut

/-- The actual successful whole entry determines storage and runtime output. -/
theorem constructor_effects_of_run
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (hcode : sevm.code = code)
    (run : SFunc.Run cert.prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post)) :
    post.getStor sevm.currentTarget =
      ((b.getStor sevm.currentTarget).set implSlot initialImplementation).set
        adminSlot sevm.caller.toB256 ∧
    post.output = code.toList.sliceD 671 2186 0 ∧
    (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) := by
  obtain ⟨_, first, firstRun, continuation⟩ := firstCall_inv hcode run
  obtain ⟨firstStack, firstMemory, firstStorage, firstForeign⟩ :=
    implementationWriter_effects firstRun
  rw [St.self firstStack firstMemory] at continuation
  obtain ⟨_, second, secondRun, continuation⟩ := secondCall_inv continuation
  obtain ⟨secondStack, secondMemory, secondStorage, secondForeign⟩ :=
    adminWriter_effects secondRun
  rw [St.self secondStack secondMemory] at continuation
  obtain ⟨terminalStorage, output⟩ := terminal_effects continuation
  refine ⟨?_, ?_, ?_⟩
  · rw [terminalStorage, secondStorage, firstStorage]
  · rw [hcode, ByteArray.sliceD_eq] at output
    exact output
  · intro a different
    rw [terminalStorage, secondForeign a different, firstForeign a different]

/-- A demanded row distinct from both literal constructor slots is preserved. -/
theorem constructor_row_preserved
    {sevm : Sevm} {b post : Devm} {G : Nat} {key : B256}
    (hcode : sevm.code = code)
    (run : SFunc.Run cert.prog sevm (St b [] Mem.empty G) t_0000_c0 (.halted post))
    (implementation : key ≠ implSlot) (admin : key ≠ adminSlot) :
    post.getStorVal sevm.currentTarget key = b.getStorVal sevm.currentTarget key := by
  change (post.getStor sevm.currentTarget).get key =
    (b.getStor sevm.currentTarget).get key
  rw [(constructor_effects_of_run hcode run).1,
    Stor.get_set_ne _ admin.symm, Stor.get_set_ne _ implementation.symm]

end Blanc.Lift.Usdc.ProxyCreation
