-- ProrataWethVaultArithmeticExec.lean : compiled full-width arithmetic walks.

import Blanc.ProrataWethVaultFunctional

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace ProrataWethVault

/-!
# Compiled arithmetic execution

This module connects the vault's compiled full-width arithmetic helpers to
their word-level results.  It is downstream of the mathematical model and the
compiled functional substrate so those owners remain acyclic.
-/

/-- A successful floor-mode walk through the single-word arm of `divide512`
passes the exact EVM quotient to its continuation.  The theorem deliberately
states no magnitude premise: selection of this arm is handled separately from
the correctness of the arm itself. -/
theorem divideSimple_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {denominator low : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divideSimple .down continuation) (.ok final)) :
    ∃ bodyPre,
      (low / denominator) :: tail <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  unfold divideSimple at run

  obtain ⟨s1, denominatorRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun

  obtain ⟨s2, lowRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, -⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 lowAt lowRun

  obtain ⟨s3, modRun, run⟩ := runCompiledTo_next_inv run
  have modSource := Ninst.Run.of_runCompiled modRun
  have p3 : (low % denominator) :: tail <<+ s3.stack :=
    prefix_of_mod modSource p2
  have memory3 : s2.memory = s3.memory :=
    Ninst.Hinv.inv (f := Devm.memory) modSource
  have wf3 : Mem.Wf s3.memory := by
    rw [← memory3]
    exact wf2
  have reads3 : Mem.Reads s3.memory image := by
    rw [← memory3]
    exact reads2

  obtain ⟨s4, remainderStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_mstoreAt_image p3 wf3 reads3 remainderStoreRun
  let image1 := Bytes.writeAt image
    (remainderWord * 32).toNat (low % denominator).toBytes
  change Mem.Reads s4.memory image1 at reads4

  have denominatorAt1 : Bytes.toB256
      (image1.sliceD (denominatorWord * 32).toNat 32 0) = denominator := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact denominatorAt
    · left
      decide +kernel
  obtain ⟨s5, denominatorRun2, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨p5, wf5, reads5, -⟩ :=
    of_run_loadWordAt_image p4 wf4 reads4 denominatorAt1
      denominatorRun2

  have lowAt1 : Bytes.toB256
      (image1.sliceD (lowWord * 32).toNat 32 0) = low := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt
    · left
      decide +kernel
  obtain ⟨s6, lowRun2, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨p6, wf6, reads6, -⟩ :=
    of_run_loadWordAt_image p5 wf5 reads5 lowAt1 lowRun2

  obtain ⟨s7, divRun, run⟩ := runCompiledTo_next_inv run
  have divSource := Ninst.Run.of_runCompiled divRun
  have p7 : (low / denominator) :: tail <<+ s7.stack :=
    prefix_of_div divSource p6
  have memory7 : s6.memory = s7.memory :=
    Ninst.Hinv.inv (f := Devm.memory) divSource
  have wf7 : Mem.Wf s7.memory := by
    rw [← memory7]
    exact wf6
  have reads7 : Mem.Reads s7.memory image1 := by
    rw [← memory7]
    exact reads6

  obtain ⟨s8, quotientStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨p8, wf8, reads8, -⟩ :=
    of_run_mstoreAt_image p7 wf7 reads7 quotientStoreRun
  let image2 := Bytes.writeAt image1
    (quotientWord * 32).toNat (low / denominator).toBytes
  change Mem.Reads s8.memory image2 at reads8

  simp only [finishQuotient] at run
  obtain ⟨callPre, quotientRun, callRun⟩ :=
    runCompiledTo_prepend_inv run
  have quotientAt : Bytes.toB256
      (image2.sliceD (quotientWord * 32).toNat 32 0) =
        low / denominator := by
    unfold image2
    exact Bytes.readWord_writeAt_self _ _ _
  obtain ⟨quotientPrefix, -, -, -⟩ :=
    of_run_loadWordAt_image p8 wf8 reads8 quotientAt quotientRun
  obtain ⟨bodyPre, callBurn, bodyRun⟩ :=
    runCompiledTo_call_inv lookup callRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  rw [← callBurn.stack]
  exact quotientPrefix

/-- A successful floor-mode `divide512` walk with a zero high word reaches the
simple arm and passes its exact quotient to the continuation.  Success itself
eliminates the zero-denominator revert arm, so the theorem needs neither a
nonzero-denominator premise nor a numerator-magnitude premise. -/
theorem divide512_down_high_zero_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {denominator low : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = 0)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divide512 .down continuation) (.ok final)) :
    ∃ bodyPre,
      (low / denominator) :: tail <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  unfold divide512 at run

  obtain ⟨denominatorPost, denominatorRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨denominatorPrefix, denominatorWf, denominatorReads, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun

  obtain ⟨denominatorTest, denominatorZeroRun, branchRun⟩ :=
    runCompiledTo_next_inv run
  have denominatorZeroSource :=
    Ninst.Run.of_runCompiled denominatorZeroRun
  have denominatorTestPrefix :=
    prefix_of_iszero denominatorZeroSource denominatorPrefix
  have denominatorTestMemory :
      denominatorPost.memory = denominatorTest.memory :=
    Ninst.Hinv.inv (f := Devm.memory) denominatorZeroSource
  have denominatorTestWf : Mem.Wf denominatorTest.memory := by
    rw [← denominatorTestMemory]
    exact denominatorWf
  have denominatorTestReads : Mem.Reads denominatorTest.memory image := by
    rw [← denominatorTestMemory]
    exact denominatorReads

  rcases runCompiledTo_branch_inv branchRun with
    denominatorNonzeroRoute | denominatorZeroRoute
  · rcases denominatorNonzeroRoute with
      ⟨highPre, denominatorStack, denominatorPop, highGuardRun⟩
    have highPrePrefix : tail <<+ highPre.stack :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy denominatorPop)
        denominatorTestPrefix).2
    have highPreWf : Mem.Wf highPre.memory := by
      rw [← denominatorPop.memory]
      exact denominatorTestWf
    have highPreReads : Mem.Reads highPre.memory image := by
      rw [← denominatorPop.memory]
      exact denominatorTestReads

    obtain ⟨highPost, highRun, highGuardRun⟩ :=
      runCompiledTo_prepend_inv highGuardRun
    obtain ⟨highPrefix, highWf, highReads, -⟩ :=
      of_run_loadWordAt_image highPrePrefix highPreWf highPreReads highAt
        highRun

    obtain ⟨highTest, highZeroRun, highBranchRun⟩ :=
      runCompiledTo_next_inv highGuardRun
    have highZeroSource := Ninst.Run.of_runCompiled highZeroRun
    have highTestPrefix := prefix_of_iszero highZeroSource highPrefix
    have highTestMemory : highPost.memory = highTest.memory :=
      Ninst.Hinv.inv (f := Devm.memory) highZeroSource
    have highTestWf : Mem.Wf highTest.memory := by
      rw [← highTestMemory]
      exact highWf
    have highTestReads : Mem.Reads highTest.memory image := by
      rw [← highTestMemory]
      exact highReads
    have highOnePrefix : (1 : B256) :: tail <<+ highTest.stack := by
      simpa [B256.eqCheck] using highTestPrefix

    obtain ⟨simplePre, branchWord, branchWordNe, simplePop,
        simpleRun, simplePrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) highOnePrefix highBranchRun
    have simpleWf : Mem.Wf simplePre.memory := by
      rw [← simplePop.memory]
      exact highTestWf
    have simpleReads : Mem.Reads simplePre.memory image := by
      rw [← simplePop.memory]
      exact highTestReads
    exact divideSimple_down_trace simpleWf simpleReads denominatorAt lowAt
      simplePrefix lookup simpleRun
  · rcases denominatorZeroRoute with
      ⟨branchWord, revertPre, branchWordNe, denominatorStack,
        denominatorPop, revertRun⟩
    obtain ⟨revertPost, impossible, -⟩ :=
      runCompiledTo_rev_inv revertRun
    cases impossible

end ProrataWethVault

end Blanc
