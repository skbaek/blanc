-- ProrataWethVaultArithmeticExec.lean : compiled full-width arithmetic walks.

import Blanc.ProrataWethVaultArithmetic
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

/-! ## Modular-inverse refinement -/

/-- The seed-producing suffix of `divideWideCore`, named independently so its
exact memory effect composes with the six Newton lines below. -/
def inverseSeedLine : Line :=
  loadWord denominatorWord ++
    [pushB256 3, mul, pushB256 2, xor] ++
    mstoreAt inverseWord

/-- The compiled seed line writes the shared `(3 * denominator) xor 2`
inverse seed while preserving the surrounding stack and persistent state. -/
theorem inverseSeed_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {denominator : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre inverseSeedLine post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt image (inverseWord * 32).toNat
          (inverseSeedWord denominator).toBytes) ∧
      pre.state = post.state := by
  have state :=
    Line.of_inv Devm.state
      (by unfold inverseSeedLine loadWord mstoreAt; line_inv) run
  unfold inverseSeedLine at run

  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s1, denominatorRun, run⟩
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun

  rcases of_run_append [pushB256 3, mul, pushB256 2, xor] run with
    ⟨s5, arithmeticRun, run⟩
  rcases Line.of_run_cons arithmeticRun with
    ⟨s2, pushThreeRun, arithmeticRun⟩
  rcases Line.of_run_cons arithmeticRun with
    ⟨s3, mulRun, arithmeticRun⟩
  rcases Line.of_run_cons arithmeticRun with
    ⟨s4, pushTwoRun, arithmeticRun⟩
  rcases Line.of_run_cons arithmeticRun with
    ⟨s5', xorRun, arithmeticRun⟩
  cases arithmeticRun
  have p2 := prefix_of_push (of_run_pushB256 pushThreeRun) p1
  have p3 := prefix_of_mul mulRun p2
  have p4 := prefix_of_push (of_run_pushB256 pushTwoRun) p3
  have p5raw := prefix_of_xor xorRun p4
  have p5 : inverseSeedWord denominator :: tail <<+ s5.stack := by
    simpa [inverseSeedWord, B256.xor_comm] using p5raw
  have arithmeticMemory : s1.memory = s5.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons pushThreeRun
        (Line.Run.cons mulRun
          (Line.Run.cons pushTwoRun
            (Line.Run.cons xorRun Line.Run.nil))))
  have wf5 : Mem.Wf s5.memory := by
    rw [← arithmeticMemory]
    exact wf1
  have reads5 : Mem.Reads s5.memory image := by
    rw [← arithmeticMemory]
    exact reads1

  obtain ⟨p6, wf6, reads6, -⟩ :=
    of_run_mstoreAt_image p5 wf5 reads5 run
  exact ⟨p6, wf6, reads6, state⟩

/-- One compiled Newton line replaces the staged inverse by the exact word
operation used by the source helper.  The memory image advances at the written
word while the operand stack and persistent state are preserved. -/
theorem newtonStep_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {denominator inverse : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (inverseAt : Bytes.toB256
      (image.sliceD (inverseWord * 32).toNat 32 0) = inverse)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre newtonStep post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (Bytes.writeAt image (inverseWord * 32).toNat
          (inverseNewtonStepWord denominator inverse).toBytes) ∧
      pre.state = post.state := by
  have state :=
    Line.of_inv Devm.state
      (by unfold newtonStep loadWord mstoreAt; line_inv) run
  unfold newtonStep at run

  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s1, denominatorRun, run⟩
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun

  rcases of_run_append (loadWord inverseWord) run with
    ⟨s2, inverseRun, run⟩
  obtain ⟨p2, wf2, reads2, -⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 inverseAt inverseRun

  rcases of_run_append [mul, pushB256 2, sub] run with
    ⟨s3, arithmeticRun, run⟩
  rcases Line.of_run_cons arithmeticRun with
    ⟨sMul, mulRun, arithmeticRun⟩
  rcases Line.of_run_cons arithmeticRun with
    ⟨sPush, pushRun, arithmeticRun⟩
  rcases Line.of_run_cons arithmeticRun with
    ⟨sSub, subRun, arithmeticRun⟩
  cases arithmeticRun
  have pMul := prefix_of_mul mulRun p2
  have pPush := prefix_of_push (of_run_pushB256 pushRun) pMul
  have p3 := prefix_of_sub subRun pPush
  have arithmeticMemory : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons mulRun
        (Line.Run.cons pushRun (Line.Run.cons subRun Line.Run.nil)))
  have wf3 : Mem.Wf s3.memory := by
    rw [← arithmeticMemory]
    exact wf2
  have reads3 : Mem.Reads s3.memory image := by
    rw [← arithmeticMemory]
    exact reads2

  rcases of_run_append (loadWord inverseWord) run with
    ⟨s4, inverseRun2, run⟩
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_loadWordAt_image p3 wf3 reads3 inverseAt inverseRun2

  rcases of_run_append [mul] run with
    ⟨s5, productRun, run⟩
  rcases Line.of_run_cons productRun with
    ⟨sProduct, finalMulRun, productRun⟩
  cases productRun
  have p5raw := prefix_of_mul finalMulRun p4
  have p5 :
      inverseNewtonStepWord denominator inverse :: tail <<+ s5.stack := by
    simpa [inverseNewtonStepWord] using p5raw
  have productMemory : s4.memory = s5.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons finalMulRun Line.Run.nil)
  have wf5 : Mem.Wf s5.memory := by
    rw [← productMemory]
    exact wf4
  have reads5 : Mem.Reads s5.memory image := by
    rw [← productMemory]
    exact reads4

  obtain ⟨p6, wf6, reads6, -⟩ :=
    of_run_mstoreAt_image p5 wf5 reads5 run
  exact ⟨p6, wf6, reads6, state⟩

/-- The exact proof-carrying memory image after repeated Newton writes.  Only
the staged inverse word changes; the definition retains that write history so
all other scratch-word reads remain available without an extensional memory
assumption. -/
def inverseNewtonTraceImage
    (image : Bytes) (denominator inverse : B256) : Nat → Bytes
  | 0 => image
  | count + 1 =>
      let next := inverseNewtonStepWord denominator inverse
      inverseNewtonTraceImage
        (Bytes.writeAt image (inverseWord * 32).toNat next.toBytes)
        denominator next count

private def newtonStepsLine : Nat → Line
  | 0 => []
  | count + 1 => newtonStep ++ newtonStepsLine count

private theorem newtonSteps_trace
    (count : Nat)
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {denominator inverse : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (inverseAt : Bytes.toB256
      (image.sliceD (inverseWord * 32).toNat 32 0) = inverse)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre (newtonStepsLine count) post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (inverseNewtonTraceImage image denominator inverse count) ∧
      pre.state = post.state ∧
      Bytes.toB256
          ((inverseNewtonTraceImage image denominator inverse count).sliceD
            (denominatorWord * 32).toNat 32 0) = denominator ∧
      Bytes.toB256
          ((inverseNewtonTraceImage image denominator inverse count).sliceD
            (inverseWord * 32).toNat 32 0) =
        inverseNewtonIter denominator count inverse := by
  induction count generalizing pre post image inverse with
  | zero =>
      simp only [newtonStepsLine] at run
      cases run
      exact ⟨stack, memoryWf, memoryReads, rfl, denominatorAt, inverseAt⟩
  | succ count ih =>
      simp only [newtonStepsLine] at run
      rcases of_run_append newtonStep run with
        ⟨mid, stepRun, restRun⟩
      obtain ⟨midStack, midWf, midReads, midState⟩ :=
        newtonStep_trace memoryWf memoryReads denominatorAt inverseAt stack
          stepRun
      let next := inverseNewtonStepWord denominator inverse
      let nextImage :=
        Bytes.writeAt image (inverseWord * 32).toNat next.toBytes
      change Mem.Reads mid.memory nextImage at midReads
      have nextDenominatorAt : Bytes.toB256
          (nextImage.sliceD (denominatorWord * 32).toNat 32 0) =
          denominator := by
        unfold nextImage
        rw [Bytes.readWord_writeAt_of_disjoint]
        · exact denominatorAt
        · left
          decide +kernel
      have nextInverseAt : Bytes.toB256
          (nextImage.sliceD (inverseWord * 32).toNat 32 0) = next := by
        unfold nextImage
        exact Bytes.readWord_writeAt_self _ _ _
      obtain ⟨finalStack, finalWf, finalReads, finalState,
          finalDenominatorAt, finalInverseAt⟩ :=
        ih midWf midReads nextDenominatorAt nextInverseAt midStack restRun
      refine ⟨finalStack, finalWf, ?_, midState.trans finalState, ?_, ?_⟩
      · simpa [inverseNewtonTraceImage, nextImage, next] using finalReads
      · simpa [inverseNewtonTraceImage, nextImage, next] using
          finalDenominatorAt
      · simpa [inverseNewtonTraceImage, inverseNewtonIter, nextImage, next]
          using finalInverseAt

/-- The runtime's exact six Newton lines preserve the surrounding stack and
advance the staged inverse to six word-level refinements. -/
theorem sixNewtonSteps_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {denominator inverse : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (inverseAt : Bytes.toB256
      (image.sliceD (inverseWord * 32).toNat 32 0) = inverse)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre sixNewtonSteps post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (inverseNewtonTraceImage image denominator inverse 6) ∧
      pre.state = post.state ∧
      Bytes.toB256
          ((inverseNewtonTraceImage image denominator inverse 6).sliceD
            (denominatorWord * 32).toNat 32 0) = denominator ∧
      Bytes.toB256
          ((inverseNewtonTraceImage image denominator inverse 6).sliceD
            (inverseWord * 32).toNat 32 0) =
        inverseNewtonIter denominator 6 inverse := by
  apply newtonSteps_trace 6 memoryWf memoryReads denominatorAt inverseAt stack
  simpa [sixNewtonSteps, newtonStepsLine, List.append_assoc] using run

/-- The complete compiled inverse block writes the standard seed and performs
all six Newton refinements, retaining exact reads for every other scratch word.
The shared arithmetic theorem can turn the final word equality into a modular
inverse as soon as the caller proves that the staged denominator is odd. -/
theorem inverseSeedAndSixNewtonSteps_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {denominator : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre (inverseSeedLine ++ sixNewtonSteps) post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (inverseNewtonTraceImage
          (Bytes.writeAt image (inverseWord * 32).toNat
            (inverseSeedWord denominator).toBytes)
          denominator (inverseSeedWord denominator) 6) ∧
      pre.state = post.state ∧
      Bytes.toB256
          ((inverseNewtonTraceImage
            (Bytes.writeAt image (inverseWord * 32).toNat
              (inverseSeedWord denominator).toBytes)
            denominator (inverseSeedWord denominator) 6).sliceD
            (denominatorWord * 32).toNat 32 0) = denominator ∧
      Bytes.toB256
          ((inverseNewtonTraceImage
            (Bytes.writeAt image (inverseWord * 32).toNat
              (inverseSeedWord denominator).toBytes)
            denominator (inverseSeedWord denominator) 6).sliceD
            (inverseWord * 32).toNat 32 0) =
        inverseNewtonIter denominator 6 (inverseSeedWord denominator) := by
  rcases of_run_append inverseSeedLine run with
    ⟨mid, seedRun, newtonRun⟩
  obtain ⟨midStack, midWf, midReads, seedState⟩ :=
    inverseSeed_trace memoryWf memoryReads denominatorAt stack seedRun
  let seed := inverseSeedWord denominator
  let seedImage :=
    Bytes.writeAt image (inverseWord * 32).toNat seed.toBytes
  change Mem.Reads mid.memory seedImage at midReads
  have nextDenominatorAt : Bytes.toB256
      (seedImage.sliceD (denominatorWord * 32).toNat 32 0) =
      denominator := by
    unfold seedImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact denominatorAt
    · left
      decide +kernel
  have seedAt : Bytes.toB256
      (seedImage.sliceD (inverseWord * 32).toNat 32 0) = seed := by
    unfold seedImage
    exact Bytes.readWord_writeAt_self _ _ _
  obtain ⟨finalStack, finalWf, finalReads, finalState,
      finalDenominatorAt, finalInverseAt⟩ :=
    sixNewtonSteps_trace midWf midReads nextDenominatorAt seedAt midStack
      newtonRun
  refine ⟨finalStack, finalWf, ?_, seedState.trans finalState, ?_, ?_⟩
  · simpa [seedImage, seed] using finalReads
  · simpa [seedImage, seed] using finalDenominatorAt
  · simpa [seedImage, seed] using finalInverseAt

/-! ## Division arms -/

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
