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

/-- Newton refinement only writes `inverseWord`, so any disjoint 32-byte word
read is preserved across an arbitrary refinement count. -/
theorem inverseNewtonTraceImage_readWord_of_disjoint
    (image : Bytes) (denominator inverse : B256) (count offset : Nat)
    (disjoint :
      offset + 32 ≤ (inverseWord * 32).toNat ∨
        (inverseWord * 32).toNat + 32 ≤ offset) :
    Bytes.toB256
        ((inverseNewtonTraceImage image denominator inverse count).sliceD
          offset 32 0) =
      Bytes.toB256 (image.sliceD offset 32 0) := by
  induction count generalizing image inverse with
  | zero => rfl
  | succ count ih =>
      simp only [inverseNewtonTraceImage]
      rw [ih]
      rw [Bytes.readWord_writeAt_of_disjoint]
      exact disjoint

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

/-! ## Full-width remainder staging -/

/-- The initial `ADDMOD`/`MULMOD` prefix of `divideWideCore`, through the
exact two-word numerator remainder store. -/
def wideRemainderLine : Line :=
  loadWord denominatorWord ++
  [pushB256 1, pushB256 B256.max, addmod] ++
  mstoreAt factorWord ++
  loadWord denominatorWord ++ loadWord factorWord ++ loadWord highWord ++
  [mulmod] ++ mstoreAt scratchWord ++
  loadWord denominatorWord ++ loadWord lowWord ++ loadWord scratchWord ++
  [addmod] ++ mstoreAt remainderWord

/-- The proof-carrying memory image produced by `wideRemainderLine`. -/
def wideRemainderTraceImage
    (image : Bytes) (high low denominator : B256) : Bytes :=
  let factor := wordModulusFactorWord denominator
  let scratch := B256.mulmod high factor denominator
  let remainder := B256.addmod scratch low denominator
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt image (factorWord * 32).toNat factor.toBytes)
      (scratchWord * 32).toNat scratch.toBytes)
    (remainderWord * 32).toNat remainder.toBytes

theorem wideRemainderTraceImage_denominator
    {image : Bytes} {high low denominator : B256}
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator) :
    Bytes.toB256
        ((wideRemainderTraceImage image high low denominator).sliceD
          (denominatorWord * 32).toNat 32 0) = denominator := by
  unfold wideRemainderTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact denominatorAt
      · left
        decide +kernel
    · left
      decide +kernel
  · left
    decide +kernel

theorem wideRemainderTraceImage_high
    {image : Bytes} {high low denominator : B256}
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high) :
    Bytes.toB256
        ((wideRemainderTraceImage image high low denominator).sliceD
          (highWord * 32).toNat 32 0) = high := by
  unfold wideRemainderTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact highAt
      · left
        decide +kernel
    · left
      decide +kernel
  · left
    decide +kernel

theorem wideRemainderTraceImage_low
    {image : Bytes} {high low denominator : B256}
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low) :
    Bytes.toB256
        ((wideRemainderTraceImage image high low denominator).sliceD
          (lowWord * 32).toNat 32 0) = low := by
  unfold wideRemainderTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact lowAt
      · left
        decide +kernel
    · left
      decide +kernel
  · left
    decide +kernel

theorem wideRemainderTraceImage_remainder
    (image : Bytes) (high low denominator : B256) :
    Bytes.toB256
        ((wideRemainderTraceImage image high low denominator).sliceD
          (remainderWord * 32).toNat 32 0) =
      wideRemainderWord high low denominator := by
  unfold wideRemainderTraceImage wideRemainderWord wordModulusFactorWord
  exact Bytes.readWord_writeAt_self _ _ _

/-- The compiled remainder prefix computes and stores the exact shared
`wideRemainderWord`, preserving the surrounding stack and persistent state. -/
theorem wideRemainder_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {high low denominator : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre wideRemainderLine post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (wideRemainderTraceImage image high low denominator) ∧
      pre.state = post.state := by
  have state :=
    Line.of_inv Devm.state
      (by unfold wideRemainderLine loadWord mstoreAt; line_inv) run
  unfold wideRemainderLine at run

  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s1, denominatorRun, run⟩
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun
  rcases of_run_append [pushB256 1, pushB256 B256.max, addmod] run with
    ⟨s4, factorRun, run⟩
  rcases Line.of_run_cons factorRun with
    ⟨s2, pushOneRun, factorRun⟩
  rcases Line.of_run_cons factorRun with
    ⟨s3, pushMaxRun, factorRun⟩
  rcases Line.of_run_cons factorRun with
    ⟨s4', addmodRun, factorRun⟩
  cases factorRun
  have p2 := prefix_of_push (of_run_pushB256 pushOneRun) p1
  have p3 := prefix_of_push (of_run_pushB256 pushMaxRun) p2
  have p4raw := prefix_of_addmod addmodRun p3
  have p4 :
      wordModulusFactorWord denominator :: tail <<+ s4.stack := by
    simpa [wordModulusFactorWord] using p4raw
  have factorMemory : s1.memory = s4.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons pushOneRun
        (Line.Run.cons pushMaxRun
          (Line.Run.cons addmodRun Line.Run.nil)))
  have wf4 : Mem.Wf s4.memory := by
    rw [← factorMemory]
    exact wf1
  have reads4 : Mem.Reads s4.memory image := by
    rw [← factorMemory]
    exact reads1
  rcases of_run_append (mstoreAt factorWord) run with
    ⟨s5, factorStoreRun, run⟩
  obtain ⟨p5, wf5, reads5, -⟩ :=
    of_run_mstoreAt_image p4 wf4 reads4 factorStoreRun
  let factor := wordModulusFactorWord denominator
  let image1 :=
    Bytes.writeAt image (factorWord * 32).toNat factor.toBytes
  change Mem.Reads s5.memory image1 at reads5
  have denominatorAt1 : Bytes.toB256
      (image1.sliceD (denominatorWord * 32).toNat 32 0) = denominator := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact denominatorAt
    · left
      decide +kernel
  have factorAt1 : Bytes.toB256
      (image1.sliceD (factorWord * 32).toNat 32 0) = factor := by
    unfold image1
    exact Bytes.readWord_writeAt_self _ _ _
  have highAt1 : Bytes.toB256
      (image1.sliceD (highWord * 32).toNat 32 0) = high := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact highAt
    · left
      decide +kernel

  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s6, denominatorRun2, run⟩
  obtain ⟨p6, wf6, reads6, -⟩ :=
    of_run_loadWordAt_image p5 wf5 reads5 denominatorAt1 denominatorRun2
  rcases of_run_append (loadWord factorWord) run with
    ⟨s7, factorLoadRun, run⟩
  obtain ⟨p7, wf7, reads7, -⟩ :=
    of_run_loadWordAt_image p6 wf6 reads6 factorAt1 factorLoadRun
  rcases of_run_append (loadWord highWord) run with
    ⟨s8, highRun, run⟩
  obtain ⟨p8, wf8, reads8, -⟩ :=
    of_run_loadWordAt_image p7 wf7 reads7 highAt1 highRun
  rcases of_run_append [mulmod] run with
    ⟨s9, mulmodLineRun, run⟩
  rcases Line.of_run_cons mulmodLineRun with
    ⟨s9', mulmodRun, mulmodLineRun⟩
  cases mulmodLineRun
  have p9raw := prefix_of_mulmod mulmodRun p8
  let scratch := B256.mulmod high factor denominator
  have p9 : scratch :: tail <<+ s9.stack := by
    simpa [scratch] using p9raw
  have mulmodMemory : s8.memory = s9.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons mulmodRun Line.Run.nil)
  have wf9 : Mem.Wf s9.memory := by
    rw [← mulmodMemory]
    exact wf8
  have reads9 : Mem.Reads s9.memory image1 := by
    rw [← mulmodMemory]
    exact reads8
  rcases of_run_append (mstoreAt scratchWord) run with
    ⟨s10, scratchStoreRun, run⟩
  obtain ⟨p10, wf10, reads10, -⟩ :=
    of_run_mstoreAt_image p9 wf9 reads9 scratchStoreRun
  let image2 :=
    Bytes.writeAt image1 (scratchWord * 32).toNat scratch.toBytes
  change Mem.Reads s10.memory image2 at reads10
  have denominatorAt2 : Bytes.toB256
      (image2.sliceD (denominatorWord * 32).toNat 32 0) = denominator := by
    unfold image2
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact denominatorAt1
    · left
      decide +kernel
  have lowAt1 : Bytes.toB256
      (image1.sliceD (lowWord * 32).toNat 32 0) = low := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt
    · left
      decide +kernel
  have lowAt2 : Bytes.toB256
      (image2.sliceD (lowWord * 32).toNat 32 0) = low := by
    unfold image2
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt1
    · left
      decide +kernel
  have scratchAt2 : Bytes.toB256
      (image2.sliceD (scratchWord * 32).toNat 32 0) = scratch := by
    unfold image2
    exact Bytes.readWord_writeAt_self _ _ _

  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s11, denominatorRun3, run⟩
  obtain ⟨p11, wf11, reads11, -⟩ :=
    of_run_loadWordAt_image p10 wf10 reads10 denominatorAt2 denominatorRun3
  rcases of_run_append (loadWord lowWord) run with
    ⟨s12, lowRun, run⟩
  obtain ⟨p12, wf12, reads12, -⟩ :=
    of_run_loadWordAt_image p11 wf11 reads11 lowAt2 lowRun
  rcases of_run_append (loadWord scratchWord) run with
    ⟨s13, scratchRun, run⟩
  obtain ⟨p13, wf13, reads13, -⟩ :=
    of_run_loadWordAt_image p12 wf12 reads12 scratchAt2 scratchRun
  rcases of_run_append [addmod] run with
    ⟨s14, addmodLineRun2, run⟩
  rcases Line.of_run_cons addmodLineRun2 with
    ⟨s14', addmodRun2, addmodLineRun2⟩
  cases addmodLineRun2
  have p14raw := prefix_of_addmod addmodRun2 p13
  let remainder := B256.addmod scratch low denominator
  have p14 : remainder :: tail <<+ s14.stack := by
    simpa [remainder] using p14raw
  have addmodMemory : s13.memory = s14.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons addmodRun2 Line.Run.nil)
  have wf14 : Mem.Wf s14.memory := by
    rw [← addmodMemory]
    exact wf13
  have reads14 : Mem.Reads s14.memory image2 := by
    rw [← addmodMemory]
    exact reads13
  obtain ⟨p15, wf15, reads15, -⟩ :=
    of_run_mstoreAt_image p14 wf14 reads14 run
  refine ⟨p15, wf15, ?_, state⟩
  simpa [wideRemainderTraceImage, image2, image1, remainder, scratch,
    factor, wideRemainderWord, wordModulusFactorWord] using reads15

/-- The exact remainder-subtraction block of `divideWideCore`. -/
def wideSubtractRemainderLine : Line :=
  loadWord remainderWord ++ loadWord lowWord ++ [lt] ++
  mstoreAt borrowWord ++
  loadWord remainderWord ++ loadWord lowWord ++ [sub] ++
  mstoreAt lowWord ++
  loadWord borrowWord ++ loadWord highWord ++ [sub] ++
  mstoreAt highWord

/-- Proof-carrying image after subtracting the staged remainder from the
two-word numerator and propagating the low-word borrow. -/
def wideSubtractRemainderTraceImage
    (image : Bytes) (high low remainder : B256) : Bytes :=
  let borrow := wideBorrowWord low remainder
  let low' := wideSubLowWord low remainder
  let high' := wideSubHighWord high low remainder
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt image (borrowWord * 32).toNat borrow.toBytes)
      (lowWord * 32).toNat low'.toBytes)
    (highWord * 32).toNat high'.toBytes

theorem wideSubtractRemainderTraceImage_denominator
    {image : Bytes} {high low remainder denominator : B256}
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator) :
    Bytes.toB256
        ((wideSubtractRemainderTraceImage image high low remainder).sliceD
          (denominatorWord * 32).toNat 32 0) = denominator := by
  unfold wideSubtractRemainderTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact denominatorAt
      · left
        decide +kernel
    · left
      decide +kernel
  · left
    decide +kernel

theorem wideSubtractRemainderTraceImage_remainder
    {image : Bytes} {high low remainder : B256}
    (remainderAt : Bytes.toB256
      (image.sliceD (remainderWord * 32).toNat 32 0) = remainder) :
    Bytes.toB256
        ((wideSubtractRemainderTraceImage image high low remainder).sliceD
          (remainderWord * 32).toNat 32 0) = remainder := by
  unfold wideSubtractRemainderTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact remainderAt
      · left
        decide +kernel
    · right
      decide +kernel
  · right
    decide +kernel

theorem wideSubtractRemainderTraceImage_low
    (image : Bytes) (high low remainder : B256) :
    Bytes.toB256
        ((wideSubtractRemainderTraceImage image high low remainder).sliceD
          (lowWord * 32).toNat 32 0) = wideSubLowWord low remainder := by
  unfold wideSubtractRemainderTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · right
    decide +kernel

theorem wideSubtractRemainderTraceImage_high
    (image : Bytes) (high low remainder : B256) :
    Bytes.toB256
        ((wideSubtractRemainderTraceImage image high low remainder).sliceD
          (highWord * 32).toNat 32 0) =
      wideSubHighWord high low remainder := by
  unfold wideSubtractRemainderTraceImage
  exact Bytes.readWord_writeAt_self _ _ _

/-- The compiled subtraction block writes the shared exact high/low
subtraction words while preserving the surrounding stack and persistent
state. -/
theorem wideSubtractRemainder_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {high low remainder : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (remainderAt : Bytes.toB256
      (image.sliceD (remainderWord * 32).toNat 32 0) = remainder)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre wideSubtractRemainderLine post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (wideSubtractRemainderTraceImage image high low remainder) ∧
      pre.state = post.state := by
  have state :=
    Line.of_inv Devm.state
      (by unfold wideSubtractRemainderLine loadWord mstoreAt; line_inv) run
  unfold wideSubtractRemainderLine at run

  rcases of_run_append (loadWord remainderWord) run with
    ⟨s1, remainderRun, run⟩
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads remainderAt remainderRun
  rcases of_run_append (loadWord lowWord) run with
    ⟨s2, lowRun, run⟩
  obtain ⟨p2, wf2, reads2, -⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 lowAt lowRun
  rcases of_run_append [lt] run with
    ⟨s3, ltLineRun, run⟩
  rcases Line.of_run_cons ltLineRun with
    ⟨s3', ltRun, ltLineRun⟩
  cases ltLineRun
  have p3raw := prefix_of_lt ltRun p2
  let borrow := wideBorrowWord low remainder
  have p3 : borrow :: tail <<+ s3.stack := by
    change B256.ltCheck low remainder :: tail <<+ s3.stack
    exact p3raw
  have ltMemory : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons ltRun Line.Run.nil)
  have wf3 : Mem.Wf s3.memory := by
    rw [← ltMemory]
    exact wf2
  have reads3 : Mem.Reads s3.memory image := by
    rw [← ltMemory]
    exact reads2
  rcases of_run_append (mstoreAt borrowWord) run with
    ⟨s4, borrowStoreRun, run⟩
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_mstoreAt_image p3 wf3 reads3 borrowStoreRun
  let image1 :=
    Bytes.writeAt image (borrowWord * 32).toNat borrow.toBytes
  change Mem.Reads s4.memory image1 at reads4
  have remainderAt1 : Bytes.toB256
      (image1.sliceD (remainderWord * 32).toNat 32 0) = remainder := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact remainderAt
    · left
      decide +kernel
  have lowAt1 : Bytes.toB256
      (image1.sliceD (lowWord * 32).toNat 32 0) = low := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt
    · left
      decide +kernel
  have highAt1 : Bytes.toB256
      (image1.sliceD (highWord * 32).toNat 32 0) = high := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact highAt
    · left
      decide +kernel
  have borrowAt1 : Bytes.toB256
      (image1.sliceD (borrowWord * 32).toNat 32 0) = borrow := by
    unfold image1
    exact Bytes.readWord_writeAt_self _ _ _

  rcases of_run_append (loadWord remainderWord) run with
    ⟨s5, remainderRun2, run⟩
  obtain ⟨p5, wf5, reads5, -⟩ :=
    of_run_loadWordAt_image p4 wf4 reads4 remainderAt1 remainderRun2
  rcases of_run_append (loadWord lowWord) run with
    ⟨s6, lowRun2, run⟩
  obtain ⟨p6, wf6, reads6, -⟩ :=
    of_run_loadWordAt_image p5 wf5 reads5 lowAt1 lowRun2
  rcases of_run_append [sub] run with
    ⟨s7, lowSubLineRun, run⟩
  rcases Line.of_run_cons lowSubLineRun with
    ⟨s7', lowSubRun, lowSubLineRun⟩
  cases lowSubLineRun
  have p7raw := prefix_of_sub lowSubRun p6
  let low' := wideSubLowWord low remainder
  have p7 : low' :: tail <<+ s7.stack := by
    simpa [low', wideSubLowWord] using p7raw
  have lowSubMemory : s6.memory = s7.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons lowSubRun Line.Run.nil)
  have wf7 : Mem.Wf s7.memory := by
    rw [← lowSubMemory]
    exact wf6
  have reads7 : Mem.Reads s7.memory image1 := by
    rw [← lowSubMemory]
    exact reads6
  rcases of_run_append (mstoreAt lowWord) run with
    ⟨s8, lowStoreRun, run⟩
  obtain ⟨p8, wf8, reads8, -⟩ :=
    of_run_mstoreAt_image p7 wf7 reads7 lowStoreRun
  let image2 :=
    Bytes.writeAt image1 (lowWord * 32).toNat low'.toBytes
  change Mem.Reads s8.memory image2 at reads8
  have borrowAt2 : Bytes.toB256
      (image2.sliceD (borrowWord * 32).toNat 32 0) = borrow := by
    unfold image2
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact borrowAt1
    · right
      decide +kernel
  have highAt2 : Bytes.toB256
      (image2.sliceD (highWord * 32).toNat 32 0) = high := by
    unfold image2
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact highAt1
    · left
      decide +kernel

  rcases of_run_append (loadWord borrowWord) run with
    ⟨s9, borrowRun, run⟩
  obtain ⟨p9, wf9, reads9, -⟩ :=
    of_run_loadWordAt_image p8 wf8 reads8 borrowAt2 borrowRun
  rcases of_run_append (loadWord highWord) run with
    ⟨s10, highRun, run⟩
  obtain ⟨p10, wf10, reads10, -⟩ :=
    of_run_loadWordAt_image p9 wf9 reads9 highAt2 highRun
  rcases of_run_append [sub] run with
    ⟨s11, highSubLineRun, run⟩
  rcases Line.of_run_cons highSubLineRun with
    ⟨s11', highSubRun, highSubLineRun⟩
  cases highSubLineRun
  have p11raw := prefix_of_sub highSubRun p10
  let high' := wideSubHighWord high low remainder
  have p11 : high' :: tail <<+ s11.stack := by
    simpa [high', wideSubHighWord] using p11raw
  have highSubMemory : s10.memory = s11.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons highSubRun Line.Run.nil)
  have wf11 : Mem.Wf s11.memory := by
    rw [← highSubMemory]
    exact wf10
  have reads11 : Mem.Reads s11.memory image2 := by
    rw [← highSubMemory]
    exact reads10
  obtain ⟨p12, wf12, reads12, -⟩ :=
    of_run_mstoreAt_image p11 wf11 reads11 run
  refine ⟨p12, wf12, ?_, state⟩
  simpa [wideSubtractRemainderTraceImage, image2, image1, high', low',
    borrow] using reads12

/-- The exact reduction prefix of `divideWideCore`: compute the two-word
remainder and subtract it from the staged numerator. -/
def wideReductionLine : Line :=
  wideRemainderLine ++ wideSubtractRemainderLine

/-- Proof-carrying image after the exact remainder has been computed and
subtracted from the two-word numerator. -/
def wideReductionTraceImage
    (image : Bytes) (high low denominator : B256) : Bytes :=
  wideSubtractRemainderTraceImage
    (wideRemainderTraceImage image high low denominator)
    high low (wideRemainderWord high low denominator)

theorem wideReductionTraceImage_denominator
    {image : Bytes} {high low denominator : B256}
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator) :
    Bytes.toB256
        ((wideReductionTraceImage image high low denominator).sliceD
          (denominatorWord * 32).toNat 32 0) = denominator := by
  unfold wideReductionTraceImage
  apply wideSubtractRemainderTraceImage_denominator
  exact wideRemainderTraceImage_denominator denominatorAt

theorem wideReductionTraceImage_remainder
    (image : Bytes) (high low denominator : B256) :
    Bytes.toB256
        ((wideReductionTraceImage image high low denominator).sliceD
          (remainderWord * 32).toNat 32 0) =
      wideRemainderWord high low denominator := by
  unfold wideReductionTraceImage
  apply wideSubtractRemainderTraceImage_remainder
  exact wideRemainderTraceImage_remainder image high low denominator

theorem wideReductionTraceImage_low
    (image : Bytes) (high low denominator : B256) :
    Bytes.toB256
        ((wideReductionTraceImage image high low denominator).sliceD
          (lowWord * 32).toNat 32 0) =
      wideSubLowWord low (wideRemainderWord high low denominator) := by
  unfold wideReductionTraceImage
  exact wideSubtractRemainderTraceImage_low _ _ _ _

theorem wideReductionTraceImage_high
    (image : Bytes) (high low denominator : B256) :
    Bytes.toB256
        ((wideReductionTraceImage image high low denominator).sliceD
          (highWord * 32).toNat 32 0) =
      wideSubHighWord high low (wideRemainderWord high low denominator) := by
  unfold wideReductionTraceImage
  exact wideSubtractRemainderTraceImage_high _ _ _ _

/-- The compiled reduction prefix realizes the generic full-width remainder
and subtraction words while preserving the surrounding stack and persistent
state. -/
theorem wideReduction_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {high low denominator : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre wideReductionLine post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (wideReductionTraceImage image high low denominator) ∧
      pre.state = post.state := by
  unfold wideReductionLine at run
  rcases of_run_append wideRemainderLine run with
    ⟨mid, remainderRun, subtractionRun⟩
  obtain ⟨midPrefix, midWf, midReads, state1⟩ :=
    wideRemainder_trace memoryWf memoryReads denominatorAt highAt lowAt stack
      remainderRun
  have midHighAt : Bytes.toB256
      ((wideRemainderTraceImage image high low denominator).sliceD
        (highWord * 32).toNat 32 0) = high :=
    wideRemainderTraceImage_high highAt
  have midLowAt : Bytes.toB256
      ((wideRemainderTraceImage image high low denominator).sliceD
        (lowWord * 32).toNat 32 0) = low :=
    wideRemainderTraceImage_low lowAt
  have midRemainderAt : Bytes.toB256
      ((wideRemainderTraceImage image high low denominator).sliceD
        (remainderWord * 32).toNat 32 0) =
      wideRemainderWord high low denominator :=
    wideRemainderTraceImage_remainder image high low denominator
  obtain ⟨finalPrefix, finalWf, finalReads, state2⟩ :=
    wideSubtractRemainder_trace midWf midReads midHighAt midLowAt
      midRemainderAt midPrefix subtractionRun
  exact ⟨finalPrefix, finalWf, finalReads, state1.trans state2⟩

/-! ## Power-of-two factor and fold staging -/

/-- The factor-and-fold block of `divideWideCore`, from isolation of the
denominator's lowest set bit through the folded low-word dividend store. -/
def wideFactorFoldLine : Line :=
  loadWord denominatorWord ++ [pushB256 0, sub] ++
  loadWord denominatorWord ++ [Ninst.and] ++ mstoreAt twosWord ++
  loadWord twosWord ++ loadWord denominatorWord ++ [div] ++
  mstoreAt denominatorWord ++
  loadWord twosWord ++ loadWord lowWord ++ [div] ++ mstoreAt lowWord ++
  loadWord twosWord ++ loadWord twosWord ++
  [pushB256 0, sub, div, pushB256 1, add] ++ mstoreAt factorWord ++
  loadWord factorWord ++ loadWord highWord ++ [mul] ++
  loadWord lowWord ++ [Ninst.or] ++ mstoreAt lowWord

/-- Exact proof-carrying image after the factor-and-fold block. The nested
writes intentionally retain both writes to `lowWord`, matching execution. -/
def wideFactorFoldTraceImage
    (image : Bytes) (high low denominator : B256) : Bytes :=
  let twos := lowestSetBitWord denominator
  let reducedDenominator := removeLowestSetBitWord denominator
  let dividedLow := low / twos
  let factor := wordModulusDivFactorWord twos
  let folded := foldDividedWords high low twos
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt image (twosWord * 32).toNat twos.toBytes)
          (denominatorWord * 32).toNat reducedDenominator.toBytes)
        (lowWord * 32).toNat dividedLow.toBytes)
      (factorWord * 32).toNat factor.toBytes)
    (lowWord * 32).toNat folded.toBytes

theorem wideFactorFoldTraceImage_denominator
    (image : Bytes) (high low denominator : B256) :
    Bytes.toB256
        ((wideFactorFoldTraceImage image high low denominator).sliceD
          (denominatorWord * 32).toNat 32 0) =
      removeLowestSetBitWord denominator := by
  unfold wideFactorFoldTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact Bytes.readWord_writeAt_self _ _ _
      · left
        decide +kernel
    · left
      decide +kernel
  · left
    decide +kernel

theorem wideFactorFoldTraceImage_high
    {image : Bytes} {high low denominator : B256}
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high) :
    Bytes.toB256
        ((wideFactorFoldTraceImage image high low denominator).sliceD
          (highWord * 32).toNat 32 0) = high := by
  unfold wideFactorFoldTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · rw [Bytes.readWord_writeAt_of_disjoint]
        · rw [Bytes.readWord_writeAt_of_disjoint]
          · exact highAt
          · left
            decide +kernel
        · right
          decide +kernel
      · left
        decide +kernel
    · left
      decide +kernel
  · left
    decide +kernel

theorem wideFactorFoldTraceImage_remainder
    {image : Bytes} {high low denominator remainder : B256}
    (remainderAt : Bytes.toB256
      (image.sliceD (remainderWord * 32).toNat 32 0) = remainder) :
    Bytes.toB256
        ((wideFactorFoldTraceImage image high low denominator).sliceD
          (remainderWord * 32).toNat 32 0) = remainder := by
  unfold wideFactorFoldTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · rw [Bytes.readWord_writeAt_of_disjoint]
        · rw [Bytes.readWord_writeAt_of_disjoint]
          · exact remainderAt
          · left
            decide +kernel
        · right
          decide +kernel
      · right
        decide +kernel
    · left
      decide +kernel
  · right
    decide +kernel

theorem wideFactorFoldTraceImage_low
    (image : Bytes) (high low denominator : B256) :
    Bytes.toB256
        ((wideFactorFoldTraceImage image high low denominator).sliceD
          (lowWord * 32).toNat 32 0) =
      foldDividedWords high low (lowestSetBitWord denominator) := by
  unfold wideFactorFoldTraceImage
  exact Bytes.readWord_writeAt_self _ _ _

/-- The compiled factor-and-fold block isolates the denominator's power-of-two
factor, divides it out of both operands, and folds the high word into the
single-word dividend consumed by the modular inverse. -/
theorem wideFactorFold_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {high low denominator : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre wideFactorFoldLine post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (wideFactorFoldTraceImage image high low denominator) ∧
      pre.state = post.state := by
  have state :=
    Line.of_inv Devm.state
      (by unfold wideFactorFoldLine loadWord mstoreAt; line_inv) run
  unfold wideFactorFoldLine at run

  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s1, denominatorRun1, run⟩
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun1
  rcases of_run_append [pushB256 0, sub] run with
    ⟨s3, complementRun, run⟩
  rcases Line.of_run_cons complementRun with
    ⟨s2, pushZeroRun1, complementRun⟩
  rcases Line.of_run_cons complementRun with
    ⟨s3', subRun1, complementRun⟩
  cases complementRun
  have p2 := prefix_of_push (of_run_pushB256 pushZeroRun1) p1
  have p3 := prefix_of_sub subRun1 p2
  have complementMemory : s1.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons pushZeroRun1 (Line.Run.cons subRun1 Line.Run.nil))
  have wf3 : Mem.Wf s3.memory := by
    rw [← complementMemory]
    exact wf1
  have reads3 : Mem.Reads s3.memory image := by
    rw [← complementMemory]
    exact reads1

  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s4, denominatorRun2, run⟩
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_loadWordAt_image p3 wf3 reads3 denominatorAt denominatorRun2
  rcases of_run_append [Ninst.and] run with
    ⟨s5, andLineRun, run⟩
  rcases Line.of_run_cons andLineRun with
    ⟨s5', andRun, andLineRun⟩
  cases andLineRun
  have p5raw := prefix_of_and andRun p4
  let twos := lowestSetBitWord denominator
  have twosEq :
      denominator &&& ((0 : B256) - denominator) = twos := by
    unfold twos lowestSetBitWord
    rw [show (0 : B256) = B256.zero by rfl]
  have p5 : twos :: tail <<+ s5.stack := by
    rw [twosEq] at p5raw
    exact p5raw
  have andMemory : s4.memory = s5.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons andRun Line.Run.nil)
  have wf5 : Mem.Wf s5.memory := by
    rw [← andMemory]
    exact wf4
  have reads5 : Mem.Reads s5.memory image := by
    rw [← andMemory]
    exact reads4

  rcases of_run_append (mstoreAt twosWord) run with
    ⟨s6, twosStoreRun, run⟩
  obtain ⟨p6, wf6, reads6, -⟩ :=
    of_run_mstoreAt_image p5 wf5 reads5 twosStoreRun
  let image1 :=
    Bytes.writeAt image (twosWord * 32).toNat twos.toBytes
  change Mem.Reads s6.memory image1 at reads6
  have twosAt1 : Bytes.toB256
      (image1.sliceD (twosWord * 32).toNat 32 0) = twos := by
    unfold image1
    exact Bytes.readWord_writeAt_self _ _ _
  have denominatorAt1 : Bytes.toB256
      (image1.sliceD (denominatorWord * 32).toNat 32 0) = denominator := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact denominatorAt
    · left
      decide +kernel
  have highAt1 : Bytes.toB256
      (image1.sliceD (highWord * 32).toNat 32 0) = high := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact highAt
    · left
      decide +kernel
  have lowAt1 : Bytes.toB256
      (image1.sliceD (lowWord * 32).toNat 32 0) = low := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt
    · left
      decide +kernel

  rcases of_run_append (loadWord twosWord) run with
    ⟨s7, twosRun1, run⟩
  obtain ⟨p7, wf7, reads7, -⟩ :=
    of_run_loadWordAt_image p6 wf6 reads6 twosAt1 twosRun1
  rcases of_run_append (loadWord denominatorWord) run with
    ⟨s8, denominatorRun3, run⟩
  obtain ⟨p8, wf8, reads8, -⟩ :=
    of_run_loadWordAt_image p7 wf7 reads7 denominatorAt1 denominatorRun3
  rcases of_run_append [div] run with
    ⟨s9, denominatorDivLineRun, run⟩
  rcases Line.of_run_cons denominatorDivLineRun with
    ⟨s9', denominatorDivRun, denominatorDivLineRun⟩
  cases denominatorDivLineRun
  have p9raw := prefix_of_div denominatorDivRun p8
  let reducedDenominator := removeLowestSetBitWord denominator
  have p9 : reducedDenominator :: tail <<+ s9.stack := by
    simpa [reducedDenominator, removeLowestSetBitWord, twos] using p9raw
  have denominatorDivMemory : s8.memory = s9.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons denominatorDivRun Line.Run.nil)
  have wf9 : Mem.Wf s9.memory := by
    rw [← denominatorDivMemory]
    exact wf8
  have reads9 : Mem.Reads s9.memory image1 := by
    rw [← denominatorDivMemory]
    exact reads8

  rcases of_run_append (mstoreAt denominatorWord) run with
    ⟨s10, denominatorStoreRun, run⟩
  obtain ⟨p10, wf10, reads10, -⟩ :=
    of_run_mstoreAt_image p9 wf9 reads9 denominatorStoreRun
  let image2 := Bytes.writeAt image1
    (denominatorWord * 32).toNat reducedDenominator.toBytes
  change Mem.Reads s10.memory image2 at reads10
  have denominatorAt2 : Bytes.toB256
      (image2.sliceD (denominatorWord * 32).toNat 32 0) =
        reducedDenominator := by
    unfold image2
    exact Bytes.readWord_writeAt_self _ _ _
  have twosAt2 : Bytes.toB256
      (image2.sliceD (twosWord * 32).toNat 32 0) = twos := by
    unfold image2
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact twosAt1
    · right
      decide +kernel
  have highAt2 : Bytes.toB256
      (image2.sliceD (highWord * 32).toNat 32 0) = high := by
    unfold image2
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact highAt1
    · right
      decide +kernel
  have lowAt2 : Bytes.toB256
      (image2.sliceD (lowWord * 32).toNat 32 0) = low := by
    unfold image2
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt1
    · right
      decide +kernel

  rcases of_run_append (loadWord twosWord) run with
    ⟨s11, twosRun2, run⟩
  obtain ⟨p11, wf11, reads11, -⟩ :=
    of_run_loadWordAt_image p10 wf10 reads10 twosAt2 twosRun2
  rcases of_run_append (loadWord lowWord) run with
    ⟨s12, lowRun1, run⟩
  obtain ⟨p12, wf12, reads12, -⟩ :=
    of_run_loadWordAt_image p11 wf11 reads11 lowAt2 lowRun1
  rcases of_run_append [div] run with
    ⟨s13, lowDivLineRun, run⟩
  rcases Line.of_run_cons lowDivLineRun with
    ⟨s13', lowDivRun, lowDivLineRun⟩
  cases lowDivLineRun
  have p13raw := prefix_of_div lowDivRun p12
  let dividedLow := low / twos
  have p13 : dividedLow :: tail <<+ s13.stack := by
    simpa [dividedLow] using p13raw
  have lowDivMemory : s12.memory = s13.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons lowDivRun Line.Run.nil)
  have wf13 : Mem.Wf s13.memory := by
    rw [← lowDivMemory]
    exact wf12
  have reads13 : Mem.Reads s13.memory image2 := by
    rw [← lowDivMemory]
    exact reads12

  rcases of_run_append (mstoreAt lowWord) run with
    ⟨s14, lowStoreRun1, run⟩
  obtain ⟨p14, wf14, reads14, -⟩ :=
    of_run_mstoreAt_image p13 wf13 reads13 lowStoreRun1
  let image3 :=
    Bytes.writeAt image2 (lowWord * 32).toNat dividedLow.toBytes
  change Mem.Reads s14.memory image3 at reads14
  have lowAt3 : Bytes.toB256
      (image3.sliceD (lowWord * 32).toNat 32 0) = dividedLow := by
    unfold image3
    exact Bytes.readWord_writeAt_self _ _ _
  have twosAt3 : Bytes.toB256
      (image3.sliceD (twosWord * 32).toNat 32 0) = twos := by
    unfold image3
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact twosAt2
    · right
      decide +kernel
  have highAt3 : Bytes.toB256
      (image3.sliceD (highWord * 32).toNat 32 0) = high := by
    unfold image3
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact highAt2
    · left
      decide +kernel

  rcases of_run_append (loadWord twosWord) run with
    ⟨s15, twosRun3, run⟩
  obtain ⟨p15, wf15, reads15, -⟩ :=
    of_run_loadWordAt_image p14 wf14 reads14 twosAt3 twosRun3
  rcases of_run_append (loadWord twosWord) run with
    ⟨s16, twosRun4, run⟩
  obtain ⟨p16, wf16, reads16, -⟩ :=
    of_run_loadWordAt_image p15 wf15 reads15 twosAt3 twosRun4
  rcases of_run_append [pushB256 0, sub, div, pushB256 1, add] run with
    ⟨s21, factorRun, run⟩
  rcases Line.of_run_cons factorRun with
    ⟨s17, pushZeroRun2, factorRun⟩
  rcases Line.of_run_cons factorRun with
    ⟨s18, subRun2, factorRun⟩
  rcases Line.of_run_cons factorRun with
    ⟨s19, factorDivRun, factorRun⟩
  rcases Line.of_run_cons factorRun with
    ⟨s20, pushOneRun, factorRun⟩
  rcases Line.of_run_cons factorRun with
    ⟨s21', addRun, factorRun⟩
  cases factorRun
  have p17 := prefix_of_push (of_run_pushB256 pushZeroRun2) p16
  have p18 := prefix_of_sub subRun2 p17
  have p19 := prefix_of_div factorDivRun p18
  have p20 := prefix_of_push (of_run_pushB256 pushOneRun) p19
  have p21raw := prefix_of_add addRun p20
  let factor := wordModulusDivFactorWord twos
  have factorEq :
      (1 : B256) + ((0 : B256) - twos) / twos = factor := by
    unfold factor wordModulusDivFactorWord
    rw [show (0 : B256) = B256.zero by rfl, B256.add_comm]
  have p21 : factor :: tail <<+ s21.stack := by
    rw [factorEq] at p21raw
    exact p21raw
  have factorMemory : s16.memory = s21.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons pushZeroRun2
        (Line.Run.cons subRun2
          (Line.Run.cons factorDivRun
            (Line.Run.cons pushOneRun
              (Line.Run.cons addRun Line.Run.nil)))))
  have wf21 : Mem.Wf s21.memory := by
    rw [← factorMemory]
    exact wf16
  have reads21 : Mem.Reads s21.memory image3 := by
    rw [← factorMemory]
    exact reads16

  rcases of_run_append (mstoreAt factorWord) run with
    ⟨s22, factorStoreRun, run⟩
  obtain ⟨p22, wf22, reads22, -⟩ :=
    of_run_mstoreAt_image p21 wf21 reads21 factorStoreRun
  let image4 :=
    Bytes.writeAt image3 (factorWord * 32).toNat factor.toBytes
  change Mem.Reads s22.memory image4 at reads22
  have factorAt4 : Bytes.toB256
      (image4.sliceD (factorWord * 32).toNat 32 0) = factor := by
    unfold image4
    exact Bytes.readWord_writeAt_self _ _ _
  have highAt4 : Bytes.toB256
      (image4.sliceD (highWord * 32).toNat 32 0) = high := by
    unfold image4
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact highAt3
    · left
      decide +kernel
  have lowAt4 : Bytes.toB256
      (image4.sliceD (lowWord * 32).toNat 32 0) = dividedLow := by
    unfold image4
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt3
    · left
      decide +kernel

  rcases of_run_append (loadWord factorWord) run with
    ⟨s23, factorLoadRun, run⟩
  obtain ⟨p23, wf23, reads23, -⟩ :=
    of_run_loadWordAt_image p22 wf22 reads22 factorAt4 factorLoadRun
  rcases of_run_append (loadWord highWord) run with
    ⟨s24, highRun, run⟩
  obtain ⟨p24, wf24, reads24, -⟩ :=
    of_run_loadWordAt_image p23 wf23 reads23 highAt4 highRun
  rcases of_run_append [mul] run with
    ⟨s25, mulLineRun, run⟩
  rcases Line.of_run_cons mulLineRun with
    ⟨s25', mulRun, mulLineRun⟩
  cases mulLineRun
  have p25 := prefix_of_mul mulRun p24
  have mulMemory : s24.memory = s25.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons mulRun Line.Run.nil)
  have wf25 : Mem.Wf s25.memory := by
    rw [← mulMemory]
    exact wf24
  have reads25 : Mem.Reads s25.memory image4 := by
    rw [← mulMemory]
    exact reads24

  rcases of_run_append (loadWord lowWord) run with
    ⟨s26, lowRun2, run⟩
  obtain ⟨p26, wf26, reads26, -⟩ :=
    of_run_loadWordAt_image p25 wf25 reads25 lowAt4 lowRun2
  rcases of_run_append [Ninst.or] run with
    ⟨s27, orLineRun, run⟩
  rcases Line.of_run_cons orLineRun with
    ⟨s27', orRun, orLineRun⟩
  cases orLineRun
  have p27raw := prefix_of_or orRun p26
  let folded := foldDividedWords high low twos
  have p27 : folded :: tail <<+ s27.stack := by
    simpa [folded, foldDividedWords, dividedLow, factor] using p27raw
  have orMemory : s26.memory = s27.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons orRun Line.Run.nil)
  have wf27 : Mem.Wf s27.memory := by
    rw [← orMemory]
    exact wf26
  have reads27 : Mem.Reads s27.memory image4 := by
    rw [← orMemory]
    exact reads26

  obtain ⟨p28, wf28, reads28, -⟩ :=
    of_run_mstoreAt_image p27 wf27 reads27 run
  refine ⟨p28, wf28, ?_, state⟩
  simpa [wideFactorFoldTraceImage, image4, image3, image2, image1,
    folded, factor, dividedLow, reducedDenominator, twos] using reads28

/-! ## Quotient store -/

/-- The final multiply-and-store block of `divideWideCore`. -/
def wideQuotientStoreLine : Line :=
  loadWord inverseWord ++ loadWord lowWord ++ [mul] ++
  mstoreAt quotientWord

def wideQuotientStoreTraceImage
    (image : Bytes) (low inverse : B256) : Bytes :=
  Bytes.writeAt image (quotientWord * 32).toNat (low * inverse).toBytes

theorem wideQuotientStoreTraceImage_quotient
    (image : Bytes) (low inverse : B256) :
    Bytes.toB256
        ((wideQuotientStoreTraceImage image low inverse).sliceD
          (quotientWord * 32).toNat 32 0) =
      low * inverse := by
  unfold wideQuotientStoreTraceImage
  exact Bytes.readWord_writeAt_self _ _ _

theorem wideQuotientStore_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {low inverse : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (inverseAt : Bytes.toB256
      (image.sliceD (inverseWord * 32).toNat 32 0) = inverse)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre wideQuotientStoreLine post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory
        (wideQuotientStoreTraceImage image low inverse) ∧
      pre.state = post.state := by
  have state :=
    Line.of_inv Devm.state
      (by unfold wideQuotientStoreLine loadWord mstoreAt; line_inv) run
  unfold wideQuotientStoreLine at run
  rcases of_run_append (loadWord inverseWord) run with
    ⟨s1, inverseRun, run⟩
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads inverseAt inverseRun
  rcases of_run_append (loadWord lowWord) run with
    ⟨s2, lowRun, run⟩
  obtain ⟨p2, wf2, reads2, -⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 lowAt lowRun
  rcases of_run_append [mul] run with
    ⟨s3, mulLineRun, run⟩
  rcases Line.of_run_cons mulLineRun with
    ⟨s3', mulRun, mulLineRun⟩
  cases mulLineRun
  have p3 := prefix_of_mul mulRun p2
  have mulMemory : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons mulRun Line.Run.nil)
  have wf3 : Mem.Wf s3.memory := by
    rw [← mulMemory]
    exact wf2
  have reads3 : Mem.Reads s3.memory image := by
    rw [← mulMemory]
    exact reads2
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_mstoreAt_image p3 wf3 reads3 run
  exact ⟨p4, wf4, reads4, state⟩

/-- The complete straight-line arithmetic prefix of `divideWideCore`. -/
def wideCoreArithmeticLine : Line :=
  wideReductionLine ++ wideFactorFoldLine ++
  inverseSeedLine ++ sixNewtonSteps ++ wideQuotientStoreLine

theorem divideWideCore_eq_arithmeticLine
    (mode : QuotientMode) (continuation : Nat) :
    divideWideCore mode continuation =
      wideCoreArithmeticLine +++ finishQuotient mode continuation := by
  simp [divideWideCore, wideCoreArithmeticLine, wideReductionLine,
    wideRemainderLine, wideSubtractRemainderLine, wideFactorFoldLine,
    inverseSeedLine, sixNewtonSteps, wideQuotientStoreLine,
    prepend_append, List.append_assoc, prepend]

/-! ## Division arms -/

/-- Floor-mode finishing loads the staged quotient and transfers it unchanged
to the selected continuation body. -/
theorem finishQuotient_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {quotient : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (quotientAt : Bytes.toB256
      (image.sliceD (quotientWord * 32).toNat 32 0) = quotient)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (finishQuotient .down continuation) (.ok final)) :
    ∃ bodyPre,
      quotient :: tail <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  simp only [finishQuotient] at run
  obtain ⟨callPre, quotientRun, callRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨quotientPrefix, -, -, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads quotientAt quotientRun
  obtain ⟨bodyPre, callBurn, bodyRun⟩ :=
    runCompiledTo_call_inv lookup callRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  rw [← callBurn.stack]
  exact quotientPrefix

/-- Ceiling-mode finishing selects the staged quotient when the staged
remainder is zero. Otherwise it rejects the all-ones quotient through the
compiled revert arm and passes the word successor to the continuation. -/
theorem finishQuotient_up_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {quotient remainder : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (quotientAt : Bytes.toB256
      (image.sliceD (quotientWord * 32).toNat 32 0) = quotient)
    (remainderAt : Bytes.toB256
      (image.sliceD (remainderWord * 32).toNat 32 0) = remainder)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (finishQuotient .up continuation) (.ok final)) :
    ∃ bodyPre,
      (if remainder = 0 then quotient else quotient + 1) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  simp only [finishQuotient] at run
  obtain ⟨remainderPost, remainderRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨remainderPrefix, remainderWf, remainderReads, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads remainderAt
      remainderRun
  obtain ⟨remainderTest, remainderZeroRun, branchRun⟩ :=
    runCompiledTo_next_inv run
  have remainderZeroSource := Ninst.Run.of_runCompiled remainderZeroRun
  have remainderTestPrefix :=
    prefix_of_iszero remainderZeroSource remainderPrefix
  have remainderTestMemory :
      remainderPost.memory = remainderTest.memory :=
    Ninst.Hinv.inv (f := Devm.memory) remainderZeroSource
  have remainderTestWf : Mem.Wf remainderTest.memory := by
    rw [← remainderTestMemory]
    exact remainderWf
  have remainderTestReads : Mem.Reads remainderTest.memory image := by
    rw [← remainderTestMemory]
    exact remainderReads

  by_cases remainderZero : remainder = 0
  · have onePrefix : (1 : B256) :: tail <<+ remainderTest.stack := by
      simpa [B256.eqCheck, remainderZero] using remainderTestPrefix
    obtain ⟨exactPre, branchWord, branchWordNe, exactPop, exactRun,
        exactPrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have exactWf : Mem.Wf exactPre.memory := by
      rw [← exactPop.memory]
      exact remainderTestWf
    have exactReads : Mem.Reads exactPre.memory image := by
      rw [← exactPop.memory]
      exact remainderTestReads
    obtain ⟨callPre, quotientRun, callRun⟩ :=
      runCompiledTo_prepend_inv exactRun
    obtain ⟨quotientPrefix, -, -, -⟩ :=
      of_run_loadWordAt_image exactPrefix exactWf exactReads quotientAt
        quotientRun
    obtain ⟨bodyPre, callBurn, bodyRun⟩ :=
      runCompiledTo_call_inv lookup callRun
    refine ⟨bodyPre, ?_, bodyRun⟩
    simp only [if_pos remainderZero]
    rw [← callBurn.stack]
    exact quotientPrefix
  · have zeroPrefix : (0 : B256) :: tail <<+ remainderTest.stack := by
      simpa [B256.eqCheck, remainderZero] using remainderTestPrefix
    obtain ⟨roundPre, roundPop, roundRun, roundPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    have roundWf : Mem.Wf roundPre.memory := by
      rw [← roundPop.memory]
      exact remainderTestWf
    have roundReads : Mem.Reads roundPre.memory image := by
      rw [← roundPop.memory]
      exact remainderTestReads

    obtain ⟨quotientPost, quotientRun, roundRun⟩ :=
      runCompiledTo_prepend_inv roundRun
    obtain ⟨quotientPrefix, -, -, -⟩ :=
      of_run_loadWordAt_image roundPrefix roundWf roundReads quotientAt
        quotientRun
    obtain ⟨dupPost, dupRun, roundRun⟩ :=
      runCompiledTo_next_inv roundRun
    have dupSource := Ninst.Run.of_runCompiled dupRun
    have dupPrefix : quotient :: quotient :: tail <<+ dupPost.stack :=
      prefix_of_dup_val dupSource (by show_nth) quotientPrefix
    obtain ⟨notPost, notRun, roundRun⟩ :=
      runCompiledTo_next_inv roundRun
    have notSource := Ninst.Run.of_runCompiled notRun
    have notPrefix := prefix_of_not notSource dupPrefix
    obtain ⟨maxTest, maxZeroRun, maxBranchRun⟩ :=
      runCompiledTo_next_inv roundRun
    have maxZeroSource := Ninst.Run.of_runCompiled maxZeroRun
    have maxTestPrefix := prefix_of_iszero maxZeroSource notPrefix

    by_cases quotientMax : quotient = B256.max
    · have maxOnePrefix :
          (1 : B256) :: quotient :: tail <<+ maxTest.stack := by
        simpa [quotientMax, B256.not_max, B256.eqCheck] using maxTestPrefix
      obtain ⟨overflowPre, branchWord, branchWordNe, overflowPop,
          overflowRun, overflowPrefix⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) maxOnePrefix maxBranchRun
      obtain ⟨overflowPost, impossible, -⟩ :=
        runCompiledTo_rev_inv overflowRun
      cases impossible
    · have notNonzero : (~~~ quotient) ≠ 0 := by
        intro notZero
        exact quotientMax (B256.eq_max_of_not_eq_zero notZero)
      have maxZeroPrefix :
          (0 : B256) :: quotient :: tail <<+ maxTest.stack := by
        simpa [B256.eqCheck, notNonzero] using maxTestPrefix
      obtain ⟨addPre, maxPop, addRun, addPrefix⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix maxZeroPrefix maxBranchRun
      obtain ⟨onePost, oneRun, addRun⟩ := runCompiledTo_next_inv addRun
      have oneSource := Ninst.Run.of_runCompiled oneRun
      have onePrefix := prefix_of_push (of_run_pushB256 oneSource) addPrefix
      obtain ⟨sumPost, sumRun, callRun⟩ := runCompiledTo_next_inv addRun
      have sumSource := Ninst.Run.of_runCompiled sumRun
      have sumPrefix : (quotient + 1) :: tail <<+ sumPost.stack := by
        simpa only [B256.add_comm] using prefix_of_add sumSource onePrefix
      obtain ⟨bodyPre, callBurn, bodyRun⟩ :=
        runCompiledTo_call_inv lookup callRun
      refine ⟨bodyPre, ?_, bodyRun⟩
      simp only [if_neg remainderZero]
      rw [← callBurn.stack]
      exact sumPrefix

/-- Capped floor finishing has the same successful continuation effect as
ordinary floor finishing; only the earlier wide-overflow branch differs. -/
theorem finishQuotient_capDown_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {quotient : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (quotientAt : Bytes.toB256
      (image.sliceD (quotientWord * 32).toNat 32 0) = quotient)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (finishQuotient .capDown continuation) (.ok final)) :
    ∃ bodyPre,
      quotient :: tail <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  apply finishQuotient_down_trace memoryWf memoryReads quotientAt stack
    lookup
  simpa only [finishQuotient] using run

/-- Capped ceiling-predecessor finishing returns `quotient - 1` on an exact
division and `quotient` otherwise.  The subtraction is intentionally stated
as a word operation here; the positive-numerator bridge belongs to the
capacity theorem that rules out the zero-underflow case. -/
theorem finishQuotient_capCeilPred_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {quotient remainder : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (quotientAt : Bytes.toB256
      (image.sliceD (quotientWord * 32).toNat 32 0) = quotient)
    (remainderAt : Bytes.toB256
      (image.sliceD (remainderWord * 32).toNat 32 0) = remainder)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (finishQuotient .capCeilPred continuation) (.ok final)) :
    ∃ bodyPre,
      (if remainder = 0 then quotient - 1 else quotient) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  simp only [finishQuotient] at run
  obtain ⟨remainderPost, remainderRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨remainderPrefix, remainderWf, remainderReads, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads remainderAt
      remainderRun
  obtain ⟨remainderTest, remainderZeroRun, branchRun⟩ :=
    runCompiledTo_next_inv run
  have remainderZeroSource := Ninst.Run.of_runCompiled remainderZeroRun
  have remainderTestPrefix :=
    prefix_of_iszero remainderZeroSource remainderPrefix
  have remainderTestMemory :
      remainderPost.memory = remainderTest.memory :=
    Ninst.Hinv.inv (f := Devm.memory) remainderZeroSource
  have remainderTestWf : Mem.Wf remainderTest.memory := by
    rw [← remainderTestMemory]
    exact remainderWf
  have remainderTestReads : Mem.Reads remainderTest.memory image := by
    rw [← remainderTestMemory]
    exact remainderReads

  by_cases remainderZero : remainder = 0
  · have onePrefix : (1 : B256) :: tail <<+ remainderTest.stack := by
      simpa [B256.eqCheck, remainderZero] using remainderTestPrefix
    obtain ⟨exactPre, branchWord, branchWordNe, exactPop, exactRun,
        exactPrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have exactWf : Mem.Wf exactPre.memory := by
      rw [← exactPop.memory]
      exact remainderTestWf
    have exactReads : Mem.Reads exactPre.memory image := by
      rw [← exactPop.memory]
      exact remainderTestReads
    obtain ⟨onePost, oneRun, exactRun⟩ :=
      runCompiledTo_next_inv exactRun
    have oneSource := Ninst.Run.of_runCompiled oneRun
    have oneValuePrefix : (1 : B256) :: tail <<+ onePost.stack :=
      prefix_of_push (of_run_pushB256 oneSource) exactPrefix
    have oneMemory : exactPre.memory = onePost.memory :=
      Ninst.Hinv.inv (f := Devm.memory) oneSource
    have oneWf : Mem.Wf onePost.memory := by
      rw [← oneMemory]
      exact exactWf
    have oneReads : Mem.Reads onePost.memory image := by
      rw [← oneMemory]
      exact exactReads
    obtain ⟨quotientPost, quotientRun, exactRun⟩ :=
      runCompiledTo_prepend_inv exactRun
    obtain ⟨quotientPrefix, quotientWf, quotientReads, -⟩ :=
      of_run_loadWordAt_image oneValuePrefix oneWf oneReads quotientAt
        quotientRun
    obtain ⟨differencePost, differenceRun, callRun⟩ :=
      runCompiledTo_next_inv exactRun
    have differenceSource := Ninst.Run.of_runCompiled differenceRun
    have differencePrefix : (quotient - 1) :: tail <<+
        differencePost.stack :=
      prefix_of_sub differenceSource quotientPrefix
    obtain ⟨bodyPre, callBurn, bodyRun⟩ :=
      runCompiledTo_call_inv lookup callRun
    refine ⟨bodyPre, ?_, bodyRun⟩
    simp only [if_pos remainderZero]
    rw [← callBurn.stack]
    exact differencePrefix
  · have zeroPrefix : (0 : B256) :: tail <<+ remainderTest.stack := by
      simpa [B256.eqCheck, remainderZero] using remainderTestPrefix
    obtain ⟨inexactPre, inexactPop, inexactRun, inexactPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    have inexactWf : Mem.Wf inexactPre.memory := by
      rw [← inexactPop.memory]
      exact remainderTestWf
    have inexactReads : Mem.Reads inexactPre.memory image := by
      rw [← inexactPop.memory]
      exact remainderTestReads
    obtain ⟨callPre, quotientRun, callRun⟩ :=
      runCompiledTo_prepend_inv inexactRun
    obtain ⟨quotientPrefix, -, -, -⟩ :=
      of_run_loadWordAt_image inexactPrefix inexactWf inexactReads quotientAt
        quotientRun
    obtain ⟨bodyPre, callBurn, bodyRun⟩ :=
      runCompiledTo_call_inv lookup callRun
    refine ⟨bodyPre, ?_, bodyRun⟩
    simp only [if_neg remainderZero]
    rw [← callBurn.stack]
    exact quotientPrefix

/-- The mode-independent arithmetic prefix of `divideWideCore` stages its
exact full-width quotient and remainder before handing control to the selected
rounding finisher. -/
theorem divideWideCore_staging_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high low denominator : B256} {continuation : Nat}
    {mode : QuotientMode} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (divideWideCore mode continuation) (.ok final)) :
    ∃ finishPre finishImage,
      tail <<+ finishPre.stack ∧
      Mem.Wf finishPre.memory ∧
      Mem.Reads finishPre.memory finishImage ∧
      Bytes.toB256
          (finishImage.sliceD (quotientWord * 32).toNat 32 0) =
        wideQuotientWord high low denominator ∧
      Bytes.toB256
          (finishImage.sliceD (remainderWord * 32).toNat 32 0) =
        wideRemainderWord high low denominator ∧
      Func.RunCompiledTo fs sevm finishPre
        (finishQuotient mode continuation) (.ok final) := by
  rw [divideWideCore_eq_arithmeticLine] at run
  obtain ⟨arithmeticPost, arithmeticRun, finishRun⟩ :=
    runCompiledTo_prepend_inv run
  unfold wideCoreArithmeticLine at arithmeticRun

  rcases of_run_append wideReductionLine arithmeticRun with
    ⟨reductionPost, reductionRun, arithmeticRun⟩
  obtain ⟨reductionStack, reductionWf, reductionReads, -⟩ :=
    wideReduction_trace memoryWf memoryReads denominatorAt highAt lowAt stack
      reductionRun
  let reductionImage :=
    wideReductionTraceImage image high low denominator
  change Mem.Reads reductionPost.memory reductionImage at reductionReads
  let reducedHigh := wideReducedHighWord high low denominator
  let reducedLow := wideReducedLowWord high low denominator
  have reductionDenominatorAt : Bytes.toB256
      (reductionImage.sliceD (denominatorWord * 32).toNat 32 0) =
        denominator := by
    unfold reductionImage
    exact wideReductionTraceImage_denominator denominatorAt
  have reductionHighAt : Bytes.toB256
      (reductionImage.sliceD (highWord * 32).toNat 32 0) =
        reducedHigh := by
    unfold reductionImage reducedHigh wideReducedHighWord
    exact wideReductionTraceImage_high _ _ _ _
  have reductionLowAt : Bytes.toB256
      (reductionImage.sliceD (lowWord * 32).toNat 32 0) =
        reducedLow := by
    unfold reductionImage reducedLow wideReducedLowWord
    exact wideReductionTraceImage_low _ _ _ _
  have reductionRemainderAt : Bytes.toB256
      (reductionImage.sliceD (remainderWord * 32).toNat 32 0) =
        wideRemainderWord high low denominator := by
    unfold reductionImage
    exact wideReductionTraceImage_remainder _ _ _ _

  rcases of_run_append wideFactorFoldLine arithmeticRun with
    ⟨factorPost, factorRun, arithmeticRun⟩
  obtain ⟨factorStack, factorWf, factorReads, -⟩ :=
    wideFactorFold_trace reductionWf reductionReads reductionDenominatorAt
      reductionHighAt reductionLowAt reductionStack factorRun
  let factorImage := wideFactorFoldTraceImage
    reductionImage reducedHigh reducedLow denominator
  change Mem.Reads factorPost.memory factorImage at factorReads
  let reducedDenominator := removeLowestSetBitWord denominator
  let folded := foldDividedWords reducedHigh reducedLow
    (lowestSetBitWord denominator)
  have factorDenominatorAt : Bytes.toB256
      (factorImage.sliceD (denominatorWord * 32).toNat 32 0) =
        reducedDenominator := by
    unfold factorImage reducedDenominator
    exact wideFactorFoldTraceImage_denominator _ _ _ _
  have factorLowAt : Bytes.toB256
      (factorImage.sliceD (lowWord * 32).toNat 32 0) = folded := by
    unfold factorImage folded
    exact wideFactorFoldTraceImage_low _ _ _ _
  have factorRemainderAt : Bytes.toB256
      (factorImage.sliceD (remainderWord * 32).toNat 32 0) =
        wideRemainderWord high low denominator := by
    unfold factorImage
    exact wideFactorFoldTraceImage_remainder reductionRemainderAt

  rcases of_run_append inverseSeedLine arithmeticRun with
    ⟨seedPost, seedRun, arithmeticRun⟩
  obtain ⟨seedStack, seedWf, seedReads, -⟩ :=
    inverseSeed_trace factorWf factorReads factorDenominatorAt factorStack
      seedRun
  let seed := inverseSeedWord reducedDenominator
  let seedImage := Bytes.writeAt factorImage
    (inverseWord * 32).toNat seed.toBytes
  change Mem.Reads seedPost.memory seedImage at seedReads
  have seedDenominatorAt : Bytes.toB256
      (seedImage.sliceD (denominatorWord * 32).toNat 32 0) =
        reducedDenominator := by
    unfold seedImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact factorDenominatorAt
    · left
      decide +kernel
  have seedLowAt : Bytes.toB256
      (seedImage.sliceD (lowWord * 32).toNat 32 0) = folded := by
    unfold seedImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact factorLowAt
    · left
      decide +kernel
  have seedRemainderAt : Bytes.toB256
      (seedImage.sliceD (remainderWord * 32).toNat 32 0) =
        wideRemainderWord high low denominator := by
    unfold seedImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact factorRemainderAt
    · left
      decide +kernel
  have seedAt : Bytes.toB256
      (seedImage.sliceD (inverseWord * 32).toNat 32 0) = seed := by
    unfold seedImage
    exact Bytes.readWord_writeAt_self _ _ _

  rcases of_run_append sixNewtonSteps arithmeticRun with
    ⟨newtonPost, newtonRun, quotientRun⟩
  obtain ⟨newtonStack, newtonWf, newtonReads, -, -,
      newtonInverseAt⟩ :=
    sixNewtonSteps_trace seedWf seedReads seedDenominatorAt seedAt seedStack
      newtonRun
  let inverse := inverseNewtonIter reducedDenominator 6 seed
  let newtonImage :=
    inverseNewtonTraceImage seedImage reducedDenominator seed 6
  change Mem.Reads newtonPost.memory newtonImage at newtonReads
  change Bytes.toB256
      (newtonImage.sliceD (inverseWord * 32).toNat 32 0) = inverse
    at newtonInverseAt
  have newtonLowAt : Bytes.toB256
      (newtonImage.sliceD (lowWord * 32).toNat 32 0) = folded := by
    calc
      Bytes.toB256
          (newtonImage.sliceD (lowWord * 32).toNat 32 0) =
        Bytes.toB256 (seedImage.sliceD (lowWord * 32).toNat 32 0) := by
          unfold newtonImage
          apply inverseNewtonTraceImage_readWord_of_disjoint
          left
          decide +kernel
      _ = folded := seedLowAt
  have newtonRemainderAt : Bytes.toB256
      (newtonImage.sliceD (remainderWord * 32).toNat 32 0) =
        wideRemainderWord high low denominator := by
    calc
      Bytes.toB256
          (newtonImage.sliceD (remainderWord * 32).toNat 32 0) =
        Bytes.toB256
          (seedImage.sliceD (remainderWord * 32).toNat 32 0) := by
            unfold newtonImage
            apply inverseNewtonTraceImage_readWord_of_disjoint
            left
            decide +kernel
      _ = wideRemainderWord high low denominator := seedRemainderAt

  obtain ⟨quotientStack, quotientWf, quotientReads, -⟩ :=
    wideQuotientStore_trace newtonWf newtonReads newtonLowAt
      newtonInverseAt newtonStack quotientRun
  let quotientImage :=
    wideQuotientStoreTraceImage newtonImage folded inverse
  change Mem.Reads arithmeticPost.memory quotientImage at quotientReads
  have quotientAt : Bytes.toB256
      (quotientImage.sliceD (quotientWord * 32).toNat 32 0) =
        wideQuotientWord high low denominator := by
    unfold quotientImage
    rw [wideQuotientStoreTraceImage_quotient]
    simp [folded, inverse, seed, reducedDenominator, reducedHigh, reducedLow,
      wideQuotientWord, wideFoldedDividendWord]
  have quotientRemainderAt : Bytes.toB256
      (quotientImage.sliceD (remainderWord * 32).toNat 32 0) =
        wideRemainderWord high low denominator := by
    unfold quotientImage wideQuotientStoreTraceImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact newtonRemainderAt
    · left
      decide +kernel
  exact ⟨arithmeticPost, quotientImage, quotientStack, quotientWf,
    quotientReads, quotientAt, quotientRemainderAt, finishRun⟩

/-- A successful floor-mode `divideWideCore` walk passes the exact composed
full-width quotient word to its continuation. Arithmetic correctness is kept
in `wideQuotientWord_toNat`; this theorem establishes the compiled walk. -/
theorem divideWideCore_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high low denominator : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divideWideCore .down continuation) (.ok final)) :
    ∃ bodyPre,
      wideQuotientWord high low denominator :: tail <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨finishPre, finishImage, finishStack, finishWf, finishReads,
      quotientAt, remainderAt, finishRun⟩ :=
    divideWideCore_staging_trace memoryWf memoryReads denominatorAt highAt
      lowAt stack run
  exact finishQuotient_down_trace finishWf finishReads quotientAt finishStack
    lookup finishRun

/-- A successful ceiling-mode `divideWideCore` walk passes the staged floor
quotient unchanged on an exact division and its word successor otherwise. -/
theorem divideWideCore_up_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high low denominator : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divideWideCore .up continuation) (.ok final)) :
    ∃ bodyPre,
      (if wideRemainderWord high low denominator = 0 then
          wideQuotientWord high low denominator
        else wideQuotientWord high low denominator + 1) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨finishPre, finishImage, finishStack, finishWf, finishReads,
      quotientAt, remainderAt, finishRun⟩ :=
    divideWideCore_staging_trace memoryWf memoryReads denominatorAt highAt
      lowAt stack run
  exact finishQuotient_up_trace finishWf finishReads quotientAt remainderAt
    finishStack lookup finishRun

/-- When a division mode rejects wide overflow, every successful `divideWide`
walk proves the guard `high < denominator` and reaches the shared wide core.
The guard walk is independent of the core's rounding policy. -/
theorem divideWide_core_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high low denominator : B256} {continuation : Nat}
    {mode : QuotientMode} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (_lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (overflowReverts : divisionOverflow mode continuation = Func.rev)
    (run : Func.RunCompiledTo fs sevm pre
      (divideWide mode continuation) (.ok final)) :
    ∃ corePre,
      high < denominator ∧
      tail <<+ corePre.stack ∧
      Mem.Wf corePre.memory ∧
      Mem.Reads corePre.memory image ∧
      Func.RunCompiledTo fs sevm corePre
        (divideWideCore mode continuation) (.ok final) := by
  unfold divideWide at run
  obtain ⟨s1, denominatorRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun
  obtain ⟨s2, highRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨p2, wf2, reads2, -⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 highAt highRun
  obtain ⟨s3, ltRun, branchRun⟩ := runCompiledTo_next_inv run
  have ltSource := Ninst.Run.of_runCompiled ltRun
  have p3 := prefix_of_lt ltSource p2
  have ltMemory : s2.memory = s3.memory :=
    Ninst.Hinv.inv (f := Devm.memory) ltSource
  have wf3 : Mem.Wf s3.memory := by
    rw [← ltMemory]
    exact wf2
  have reads3 : Mem.Reads s3.memory image := by
    rw [← ltMemory]
    exact reads2
  by_cases noOverflow : high < denominator
  · have onePrefix : (1 : B256) :: tail <<+ s3.stack := by
      simpa [B256.ltCheck, noOverflow] using p3
    obtain ⟨corePre, branchWord, branchWordNe, corePop, coreRun,
        corePrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have coreWf : Mem.Wf corePre.memory := by
      rw [← corePop.memory]
      exact wf3
    have coreReads : Mem.Reads corePre.memory image := by
      rw [← corePop.memory]
      exact reads3
    exact ⟨corePre, noOverflow, corePrefix, coreWf, coreReads, coreRun⟩
  · have zeroPrefix : (0 : B256) :: tail <<+ s3.stack := by
      simpa [B256.ltCheck, noOverflow] using p3
    obtain ⟨overflowPre, overflowPop, overflowRun, overflowPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    rw [overflowReverts] at overflowRun
    obtain ⟨overflowPost, impossible, -⟩ :=
      runCompiledTo_rev_inv overflowRun
    cases impossible

/-- A successful floor-mode wide-arm walk proves its own overflow guard and
passes the exact full-width quotient word to the continuation. The rejected
guard arm is the actual compiled empty-data revert. -/
theorem divideWide_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high low denominator : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divideWide .down continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (wideNumeratorN high low / denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨corePre, noOverflow, corePrefix, coreWf, coreReads, coreRun⟩ :=
    divideWide_core_trace memoryWf memoryReads denominatorAt highAt lowAt
      stack rfl run
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    divideWideCore_down_trace coreWf coreReads denominatorAt highAt lowAt
      corePrefix lookup coreRun
  have denominatorNonzero : denominator ≠ B256.zero := by
    intro denominatorZero
    have impossible := B256.toNat_lt_toNat noOverflow
    rw [denominatorZero] at impossible
    change high.toNat < 0 at impossible
    omega
  have quotientEq :
      wideQuotientWord high low denominator =
        Nat.toB256 (wideNumeratorN high low / denominator.toNat) :=
    wideQuotientWord_eq_toB256 denominatorNonzero noOverflow
  refine ⟨bodyPre, ?_, bodyRun⟩
  rw [quotientEq] at quotientPrefix
  exact quotientPrefix

/-- A successful ceiling-mode wide-arm walk proves the same overflow guard as
floor mode, then rounds the exact full-width quotient precisely when its
staged remainder is nonzero. -/
theorem divideWide_up_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high low denominator : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divideWide .up continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256
          (ceilDiv (wideNumeratorN high low) denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨corePre, noOverflow, corePrefix, coreWf, coreReads, coreRun⟩ :=
    divideWide_core_trace memoryWf memoryReads denominatorAt highAt lowAt
      stack rfl run
  obtain ⟨bodyPre, roundedPrefix, bodyRun⟩ :=
    divideWideCore_up_trace coreWf coreReads denominatorAt highAt lowAt
      corePrefix lookup coreRun
  have denominatorNonzero : denominator ≠ B256.zero := by
    intro denominatorZero
    have impossible := B256.toNat_lt_toNat noOverflow
    rw [denominatorZero] at impossible
    change high.toNat < 0 at impossible
    omega
  have quotientEq :
      wideQuotientWord high low denominator =
        Nat.toB256 (wideNumeratorN high low / denominator.toNat) :=
    wideQuotientWord_eq_toB256 denominatorNonzero noOverflow
  have roundedEq :
      (if wideRemainderWord high low denominator = 0 then
          wideQuotientWord high low denominator
        else wideQuotientWord high low denominator + 1) =
        Nat.toB256
          (ceilDiv (wideNumeratorN high low) denominator.toNat) :=
    roundedQuotientWord_eq_toB256_ceilDiv quotientEq
      (wideRemainderWord_eq_zero_iff denominatorNonzero)
  refine ⟨bodyPre, ?_, bodyRun⟩
  rw [roundedEq] at roundedPrefix
  exact roundedPrefix

/-- Proof-carrying memory image after the quotient/remainder staging shared by
all `divideSimple` rounding modes. -/
def simpleDivisionTraceImage
    (image : Bytes) (low denominator : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt image (remainderWord * 32).toNat
      (low % denominator).toBytes)
    (quotientWord * 32).toNat (low / denominator).toBytes

theorem simpleDivisionTraceImage_remainder
    (image : Bytes) (low denominator : B256) :
    Bytes.toB256
        ((simpleDivisionTraceImage image low denominator).sliceD
          (remainderWord * 32).toNat 32 0) =
      low % denominator := by
  unfold simpleDivisionTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · left
    decide +kernel

theorem simpleDivisionTraceImage_quotient
    (image : Bytes) (low denominator : B256) :
    Bytes.toB256
        ((simpleDivisionTraceImage image low denominator).sliceD
          (quotientWord * 32).toNat 32 0) =
      low / denominator := by
  unfold simpleDivisionTraceImage
  exact Bytes.readWord_writeAt_self _ _ _

/-- The straight-line prefix of `divideSimple` stages its exact word
remainder and quotient independently of the selected finishing mode. -/
theorem divideSimple_staging_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {denominator low : B256} {continuation : Nat}
    {mode : QuotientMode} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (divideSimple mode continuation) (.ok final)) :
    ∃ finishPre,
      tail <<+ finishPre.stack ∧
      Mem.Wf finishPre.memory ∧
      Mem.Reads finishPre.memory
        (simpleDivisionTraceImage image low denominator) ∧
      Func.RunCompiledTo fs sevm finishPre
        (finishQuotient mode continuation) (.ok final) := by
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
  refine ⟨s8, p8, wf8, ?_, run⟩
  simpa [simpleDivisionTraceImage, image2, image1] using reads8

/-- A successful floor-mode walk through the single-word arm of `divide512`
passes the exact EVM quotient to its continuation. The theorem deliberately
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
  obtain ⟨finishPre, finishStack, finishWf, finishReads, finishRun⟩ :=
    divideSimple_staging_trace memoryWf memoryReads denominatorAt lowAt stack
      run
  exact finishQuotient_down_trace finishWf finishReads
    (simpleDivisionTraceImage_quotient image low denominator) finishStack
    lookup finishRun

/-- A successful ceiling-mode single-word division passes its exact word
quotient, incremented precisely when the staged remainder is nonzero. -/
theorem divideSimple_up_trace
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
      (divideSimple .up continuation) (.ok final)) :
    ∃ bodyPre,
      (if low % denominator = 0 then low / denominator
        else low / denominator + 1) :: tail <<+ bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨finishPre, finishStack, finishWf, finishReads, finishRun⟩ :=
    divideSimple_staging_trace memoryWf memoryReads denominatorAt lowAt stack
      run
  exact finishQuotient_up_trace finishWf finishReads
    (simpleDivisionTraceImage_quotient image low denominator)
    (simpleDivisionTraceImage_remainder image low denominator) finishStack
    lookup finishRun

/-- With a nonzero divisor, the ceiling-mode simple arm agrees with natural
ceiling division re-embedded as one EVM word. -/
theorem divideSimple_up_toB256_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {denominator low : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (denominatorNonzero : denominator ≠ B256.zero)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divideSimple .up continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (ceilDiv low.toNat denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨bodyPre, roundedPrefix, bodyRun⟩ :=
    divideSimple_up_trace memoryWf memoryReads denominatorAt lowAt stack lookup
      run
  have quotientEq :
      low / denominator = Nat.toB256 (low.toNat / denominator.toNat) :=
    wordDiv_eq_toB256_div low denominator
  have roundedEq :
      (if low % denominator = 0 then low / denominator
        else low / denominator + 1) =
        Nat.toB256 (ceilDiv low.toNat denominator.toNat) :=
    roundedQuotientWord_eq_toB256_ceilDiv quotientEq
      (wordMod_eq_zero_iff denominatorNonzero)
  refine ⟨bodyPre, ?_, bodyRun⟩
  rw [roundedEq] at roundedPrefix
  exact roundedPrefix

/-- Every successful `divide512` walk proves that its denominator is nonzero
and reaches exactly one of the simple or wide arithmetic arms. The selection
walk is shared by all quotient modes. -/
theorem divide512_arm_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {denominator high : B256} {continuation : Nat}
    {mode : QuotientMode} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (divide512 mode continuation) (.ok final)) :
    denominator ≠ B256.zero ∧
      ((high = B256.zero ∧
          ∃ simplePre,
            tail <<+ simplePre.stack ∧
            Mem.Wf simplePre.memory ∧
            Mem.Reads simplePre.memory image ∧
            Func.RunCompiledTo fs sevm simplePre
              (divideSimple mode continuation) (.ok final)) ∨
        (high ≠ B256.zero ∧
          ∃ widePre,
            tail <<+ widePre.stack ∧
            Mem.Wf widePre.memory ∧
            Mem.Reads widePre.memory image ∧
            Func.RunCompiledTo fs sevm widePre
              (divideWide mode continuation) (.ok final))) := by
  unfold divide512 at run
  obtain ⟨denominatorPost, denominatorRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨denominatorPrefix, denominatorWf, denominatorReads, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt
      denominatorRun
  obtain ⟨denominatorTest, denominatorZeroRun, branchRun⟩ :=
    runCompiledTo_next_inv run
  have denominatorZeroSource := Ninst.Run.of_runCompiled denominatorZeroRun
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

  by_cases denominatorNonzero : denominator ≠ B256.zero
  · have denominatorNonzero' : denominator ≠ (0 : B256) := by
      intro denominatorZero
      apply denominatorNonzero
      exact denominatorZero
    have zeroPrefix : (0 : B256) :: tail <<+ denominatorTest.stack := by
      simpa [B256.eqCheck, denominatorNonzero'] using denominatorTestPrefix
    obtain ⟨highPre, denominatorPop, highGuardRun, highPrePrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
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
    by_cases highZero : high = B256.zero
    · have highOnePrefix : (1 : B256) :: tail <<+ highTest.stack := by
        have highZero' : high = (0 : B256) :=
          highZero.trans (show B256.zero = (0 : B256) by rfl)
        simpa [B256.eqCheck, highZero'] using highTestPrefix
      obtain ⟨simplePre, branchWord, branchWordNe, simplePop, simpleRun,
          simplePrefix⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) highOnePrefix highBranchRun
      have simpleWf : Mem.Wf simplePre.memory := by
        rw [← simplePop.memory]
        exact highTestWf
      have simpleReads : Mem.Reads simplePre.memory image := by
        rw [← simplePop.memory]
        exact highTestReads
      exact ⟨denominatorNonzero, Or.inl
        ⟨highZero, simplePre, simplePrefix, simpleWf, simpleReads, simpleRun⟩⟩
    · have highNonzero : high ≠ (0 : B256) := by
        intro highZero'
        apply highZero
        exact highZero'
      have highZeroPrefix : (0 : B256) :: tail <<+ highTest.stack := by
        simpa [B256.eqCheck, highNonzero] using highTestPrefix
      obtain ⟨widePre, highPop, wideRun, widePrefix⟩ :=
        Func.RunCompiledTo.zero_branch_of_prefix highZeroPrefix highBranchRun
      have wideWf : Mem.Wf widePre.memory := by
        rw [← highPop.memory]
        exact highTestWf
      have wideReads : Mem.Reads widePre.memory image := by
        rw [← highPop.memory]
        exact highTestReads
      exact ⟨denominatorNonzero, Or.inr
        ⟨highZero, widePre, widePrefix, wideWf, wideReads, wideRun⟩⟩
  · have denominatorZero : denominator = B256.zero :=
      not_ne_iff.mp denominatorNonzero
    have onePrefix : (1 : B256) :: tail <<+ denominatorTest.stack := by
      have denominatorZero' : denominator = (0 : B256) :=
        denominatorZero.trans (show B256.zero = (0 : B256) by rfl)
      simpa [B256.eqCheck, denominatorZero'] using denominatorTestPrefix
    obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun,
        revertPrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    obtain ⟨revertPost, impossible, -⟩ :=
      runCompiledTo_rev_inv revertRun
    cases impossible

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
  obtain ⟨denominatorNonzero, arms⟩ :=
    divide512_arm_trace (high := (0 : B256)) memoryWf memoryReads
      denominatorAt highAt stack run
  rcases arms with
    ⟨highZero, simplePre, simplePrefix, simpleWf, simpleReads, simpleRun⟩ |
    ⟨highNonzero, widePre, widePrefix, wideWf, wideReads, wideRun⟩
  · exact divideSimple_down_trace simpleWf simpleReads denominatorAt lowAt
      simplePrefix lookup simpleRun
  · exact (highNonzero rfl).elim

/-- Every successful floor-mode `divide512` walk—simple or wide—passes the
same unbounded-natural floor quotient, re-embedded as one EVM word, to its
continuation. Denominator-zero and wide-overflow executions are eliminated by
their actual compiled revert arms. -/
theorem divide512_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {denominator high low : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divide512 .down continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (wideNumeratorN high low / denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨denominatorNonzero, arms⟩ :=
    divide512_arm_trace memoryWf memoryReads denominatorAt highAt stack run
  rcases arms with
    ⟨highZero, simplePre, simplePrefix, simpleWf, simpleReads, simpleRun⟩ |
    ⟨highNonzero, widePre, widePrefix, wideWf, wideReads, wideRun⟩
  · obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
      divideSimple_down_trace simpleWf simpleReads denominatorAt lowAt
        simplePrefix lookup simpleRun
    have zeroNumerator : wideNumeratorN high low = low.toNat := by
      unfold wideNumeratorN
      rw [highZero]
      change 0 * wordModulusN + low.toNat = low.toNat
      omega
    have simpleEq :
        low / denominator =
          Nat.toB256 (wideNumeratorN high low / denominator.toNat) := by
      rw [wordDiv_eq_toB256_div, zeroNumerator]
    refine ⟨bodyPre, ?_, bodyRun⟩
    rw [simpleEq] at quotientPrefix
    exact quotientPrefix
  · exact divideWide_down_trace wideWf wideReads denominatorAt highAt lowAt
      widePrefix lookup wideRun

/-- Every successful ceiling-mode `divide512` walk—simple or wide—passes the
same unbounded-natural ceiling quotient, re-embedded as one EVM word, to its
continuation. The executed guards eliminate zero division and both possible
word overflows. -/
theorem divide512_up_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {denominator high low : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (divide512 .up continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256
          (ceilDiv (wideNumeratorN high low) denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨denominatorNonzero, arms⟩ :=
    divide512_arm_trace memoryWf memoryReads denominatorAt highAt stack run
  rcases arms with
    ⟨highZero, simplePre, simplePrefix, simpleWf, simpleReads, simpleRun⟩ |
    ⟨highNonzero, widePre, widePrefix, wideWf, wideReads, wideRun⟩
  · obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
      divideSimple_up_toB256_trace simpleWf simpleReads denominatorAt lowAt
        denominatorNonzero simplePrefix lookup simpleRun
    have zeroNumerator : wideNumeratorN high low = low.toNat := by
      unfold wideNumeratorN
      rw [highZero]
      change 0 * wordModulusN + low.toNat = low.toNat
      omega
    refine ⟨bodyPre, ?_, bodyRun⟩
    rw [zeroNumerator]
    exact quotientPrefix
  · exact divideWide_up_trace wideWf wideReads denominatorAt highAt lowAt
      widePrefix lookup wideRun

/-! ## Exact product staging -/

/-- The mode-independent arithmetic suffix of `multiply512`, after its two
word-valued producer lines have been stored at `xWord` and `yWord`. -/
def multiply512ArithmeticLine : Line :=
  loadWord xWord ++ loadWord yWord ++ [mul] ++ mstoreAt lowWord ++
  [pushB256 B256.max] ++ loadWord yWord ++ loadWord xWord ++ [mulmod] ++
  mstoreAt scratchWord ++
  loadWord lowWord ++ loadWord scratchWord ++ [sub] ++ mstoreAt highWord ++
  loadWord lowWord ++ loadWord scratchWord ++ [lt] ++ mstoreAt borrowWord ++
  loadWord borrowWord ++ loadWord highWord ++ [sub] ++ mstoreAt highWord

/-- Proof-carrying memory image for the exact low word, `MULMOD` scratch,
borrow correction, and final high word staged by `multiply512ArithmeticLine`.
The nested image intentionally retains both writes to `highWord`. -/
def multiply512ArithmeticTraceImage
    (image : Bytes) (x y : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt
        (Bytes.writeAt
          (Bytes.writeAt image (lowWord * 32).toNat
            (productLowWord x y).toBytes)
          (scratchWord * 32).toNat (productScratchWord x y).toBytes)
        (highWord * 32).toNat
          (productHighBeforeBorrowWord x y).toBytes)
      (borrowWord * 32).toNat (productBorrowWord x y).toBytes)
    (highWord * 32).toNat (productHighWord x y).toBytes

theorem multiply512ArithmeticTraceImage_low (image : Bytes) (x y : B256) :
    Bytes.toB256
        ((multiply512ArithmeticTraceImage image x y).sliceD
          (lowWord * 32).toNat 32 0) =
      productLowWord x y := by
  unfold multiply512ArithmeticTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · rw [Bytes.readWord_writeAt_of_disjoint]
        · exact Bytes.readWord_writeAt_self _ _ _
        · left
          decide +kernel
      · right
        decide +kernel
    · left
      decide +kernel
  · right
    decide +kernel

theorem multiply512ArithmeticTraceImage_high (image : Bytes) (x y : B256) :
    Bytes.toB256
        ((multiply512ArithmeticTraceImage image x y).sliceD
          (highWord * 32).toNat 32 0) =
      productHighWord x y := by
  unfold multiply512ArithmeticTraceImage
  exact Bytes.readWord_writeAt_self _ _ _

theorem multiply512ArithmeticTraceImage_denominator
    {image : Bytes} {x y denominator : B256}
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator) :
    Bytes.toB256
        ((multiply512ArithmeticTraceImage image x y).sliceD
          (denominatorWord * 32).toNat 32 0) = denominator := by
  unfold multiply512ArithmeticTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · rw [Bytes.readWord_writeAt_of_disjoint]
        · rw [Bytes.readWord_writeAt_of_disjoint]
          · exact denominatorAt
          · left
            decide +kernel
        · left
          decide +kernel
      · left
        decide +kernel
    · left
      decide +kernel
  · left
    decide +kernel

/-- The compiled arithmetic suffix reconstructs and stages the exact two-word
product while preserving the surrounding stack and persistent state. -/
theorem multiply512Arithmetic_trace
    {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {x y : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xAt : Bytes.toB256
      (image.sliceD (xWord * 32).toNat 32 0) = x)
    (yAt : Bytes.toB256
      (image.sliceD (yWord * 32).toNat 32 0) = y)
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre multiply512ArithmeticLine post) :
    tail <<+ post.stack ∧
      Mem.Wf post.memory ∧
      Mem.Reads post.memory (multiply512ArithmeticTraceImage image x y) ∧
      pre.state = post.state := by
  have state :=
    Line.of_inv Devm.state
      (by unfold multiply512ArithmeticLine loadWord mstoreAt; line_inv) run
  unfold multiply512ArithmeticLine at run

  rcases of_run_append (loadWord xWord) run with ⟨s1, xRun, run⟩
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads xAt xRun
  rcases of_run_append (loadWord yWord) run with ⟨s2, yRun, run⟩
  obtain ⟨p2, wf2, reads2, -⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 yAt yRun
  rcases of_run_append [mul] run with ⟨s3, mulLineRun, run⟩
  rcases Line.of_run_cons mulLineRun with ⟨s3', mulRun, mulLineRun⟩
  cases mulLineRun
  have p3raw := prefix_of_mul mulRun p2
  have p3 : productLowWord x y :: tail <<+ s3.stack := by
    have lowEq : y * x = productLowWord x y := by
      change (y.toNat * x.toNat).toB256 =
        (x.toNat * y.toNat).toB256
      rw [Nat.mul_comm]
    exact lowEq ▸ p3raw
  have mulMemory : s2.memory = s3.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons mulRun Line.Run.nil)
  have wf3 : Mem.Wf s3.memory := by
    rw [← mulMemory]
    exact wf2
  have reads3 : Mem.Reads s3.memory image := by
    rw [← mulMemory]
    exact reads2
  rcases of_run_append (mstoreAt lowWord) run with
    ⟨s4, lowStoreRun, run⟩
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_mstoreAt_image p3 wf3 reads3 lowStoreRun
  let image1 := Bytes.writeAt image (lowWord * 32).toNat
    (productLowWord x y).toBytes
  change Mem.Reads _ image1 at reads4
  have xAt1 : Bytes.toB256
      (image1.sliceD (xWord * 32).toNat 32 0) = x := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact xAt
    · left
      decide +kernel
  have yAt1 : Bytes.toB256
      (image1.sliceD (yWord * 32).toNat 32 0) = y := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact yAt
    · left
      decide +kernel

  rcases of_run_append [pushB256 B256.max] run with
    ⟨s5, maxLineRun, run⟩
  rcases Line.of_run_cons maxLineRun with
    ⟨s5', maxRun, maxLineRun⟩
  cases maxLineRun
  have p5 : B256.max :: tail <<+ s5.stack := by
    simpa only [List.singleton_append] using
      prefix_of_push (of_run_pushB256 maxRun) p4
  have maxMemory : s4.memory = s5.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons maxRun Line.Run.nil)
  have wf5 : Mem.Wf s5.memory := by
    rw [← maxMemory]
    exact wf4
  have reads5 : Mem.Reads s5.memory image1 := by
    rw [← maxMemory]
    exact reads4
  rcases of_run_append (loadWord yWord) run with ⟨s6, yRun2, run⟩
  obtain ⟨p6, wf6, reads6, -⟩ :=
    of_run_loadWordAt_image p5 wf5 reads5 yAt1 yRun2
  rcases of_run_append (loadWord xWord) run with ⟨s7, xRun2, run⟩
  obtain ⟨p7, wf7, reads7, -⟩ :=
    of_run_loadWordAt_image p6 wf6 reads6 xAt1 xRun2
  rcases of_run_append [mulmod] run with
    ⟨s8, mulmodLineRun, run⟩
  rcases Line.of_run_cons mulmodLineRun with
    ⟨s8', mulmodRun, mulmodLineRun⟩
  cases mulmodLineRun
  have p8raw := prefix_of_mulmod mulmodRun p7
  have p8 : productScratchWord x y :: tail <<+ s8.stack := by
    simpa only [productScratchWord, List.nil_append] using p8raw
  have mulmodMemory : s7.memory = s8.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons mulmodRun Line.Run.nil)
  have wf8 : Mem.Wf s8.memory := by
    rw [← mulmodMemory]
    exact wf7
  have reads8 : Mem.Reads s8.memory image1 := by
    rw [← mulmodMemory]
    exact reads7
  rcases of_run_append (mstoreAt scratchWord) run with
    ⟨s9, scratchStoreRun, run⟩
  obtain ⟨p9, wf9, reads9, -⟩ :=
    of_run_mstoreAt_image p8 wf8 reads8 scratchStoreRun
  let image2 := Bytes.writeAt image1 (scratchWord * 32).toNat
    (productScratchWord x y).toBytes
  change Mem.Reads _ image2 at reads9
  have lowAt2 : Bytes.toB256
      (image2.sliceD (lowWord * 32).toNat 32 0) = productLowWord x y := by
    unfold image2 image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · left
      decide +kernel
  have scratchAt2 : Bytes.toB256
      (image2.sliceD (scratchWord * 32).toNat 32 0) =
        productScratchWord x y := by
    unfold image2
    exact Bytes.readWord_writeAt_self _ _ _

  rcases of_run_append (loadWord lowWord) run with ⟨s10, lowRun, run⟩
  obtain ⟨p10, wf10, reads10, -⟩ :=
    of_run_loadWordAt_image p9 wf9 reads9 lowAt2 lowRun
  rcases of_run_append (loadWord scratchWord) run with
    ⟨s11, scratchRun, run⟩
  obtain ⟨p11, wf11, reads11, -⟩ :=
    of_run_loadWordAt_image p10 wf10 reads10 scratchAt2 scratchRun
  rcases of_run_append [sub] run with ⟨s12, subLineRun, run⟩
  rcases Line.of_run_cons subLineRun with ⟨s12', subRun, subLineRun⟩
  cases subLineRun
  have p12raw := prefix_of_sub subRun p11
  have p12 : productHighBeforeBorrowWord x y :: tail <<+ s12.stack := by
    simpa only [productHighBeforeBorrowWord, List.nil_append] using p12raw
  have subMemory : s11.memory = s12.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons subRun Line.Run.nil)
  have wf12 : Mem.Wf s12.memory := by
    rw [← subMemory]
    exact wf11
  have reads12 : Mem.Reads s12.memory image2 := by
    rw [← subMemory]
    exact reads11
  rcases of_run_append (mstoreAt highWord) run with
    ⟨s13, provisionalHighStoreRun, run⟩
  obtain ⟨p13, wf13, reads13, -⟩ :=
    of_run_mstoreAt_image p12 wf12 reads12 provisionalHighStoreRun
  let image3 := Bytes.writeAt image2 (highWord * 32).toNat
    (productHighBeforeBorrowWord x y).toBytes
  change Mem.Reads _ image3 at reads13
  have lowAt3 : Bytes.toB256
      (image3.sliceD (lowWord * 32).toNat 32 0) = productLowWord x y := by
    unfold image3
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt2
    · right
      decide +kernel
  have scratchAt3 : Bytes.toB256
      (image3.sliceD (scratchWord * 32).toNat 32 0) =
        productScratchWord x y := by
    unfold image3
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact scratchAt2
    · right
      decide +kernel

  rcases of_run_append (loadWord lowWord) run with ⟨s14, lowRun2, run⟩
  obtain ⟨p14, wf14, reads14, -⟩ :=
    of_run_loadWordAt_image p13 wf13 reads13 lowAt3 lowRun2
  rcases of_run_append (loadWord scratchWord) run with
    ⟨s15, scratchRun2, run⟩
  obtain ⟨p15, wf15, reads15, -⟩ :=
    of_run_loadWordAt_image p14 wf14 reads14 scratchAt3 scratchRun2
  rcases of_run_append [lt] run with ⟨s16, ltLineRun, run⟩
  rcases Line.of_run_cons ltLineRun with ⟨s16', ltRun, ltLineRun⟩
  cases ltLineRun
  have p16raw := prefix_of_lt ltRun p15
  have p16 : productBorrowWord x y :: tail <<+ s16.stack := by
    simpa only [productBorrowWord, List.nil_append] using p16raw
  have ltMemory : s15.memory = s16.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons ltRun Line.Run.nil)
  have wf16 : Mem.Wf s16.memory := by
    rw [← ltMemory]
    exact wf15
  have reads16 : Mem.Reads s16.memory image3 := by
    rw [← ltMemory]
    exact reads15
  rcases of_run_append (mstoreAt borrowWord) run with
    ⟨s17, borrowStoreRun, run⟩
  obtain ⟨p17, wf17, reads17, -⟩ :=
    of_run_mstoreAt_image p16 wf16 reads16 borrowStoreRun
  let image4 := Bytes.writeAt image3 (borrowWord * 32).toNat
    (productBorrowWord x y).toBytes
  change Mem.Reads _ image4 at reads17
  have borrowAt4 : Bytes.toB256
      (image4.sliceD (borrowWord * 32).toNat 32 0) =
        productBorrowWord x y := by
    unfold image4
    exact Bytes.readWord_writeAt_self _ _ _
  have highAt4 : Bytes.toB256
      (image4.sliceD (highWord * 32).toNat 32 0) =
        productHighBeforeBorrowWord x y := by
    unfold image4 image3
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · left
      decide +kernel

  rcases of_run_append (loadWord borrowWord) run with
    ⟨s18, borrowRun, run⟩
  obtain ⟨p18, wf18, reads18, -⟩ :=
    of_run_loadWordAt_image p17 wf17 reads17 borrowAt4 borrowRun
  rcases of_run_append (loadWord highWord) run with ⟨s19, highRun, run⟩
  obtain ⟨p19, wf19, reads19, -⟩ :=
    of_run_loadWordAt_image p18 wf18 reads18 highAt4 highRun
  rcases of_run_append [sub] run with ⟨s20, finalSubLineRun, run⟩
  rcases Line.of_run_cons finalSubLineRun with
    ⟨s20', finalSubRun, finalSubLineRun⟩
  cases finalSubLineRun
  have p20raw := prefix_of_sub finalSubRun p19
  have p20 : productHighWord x y :: tail <<+ s20.stack := by
    rw [productHighWord_eq_beforeBorrow_sub_borrow]
    exact p20raw
  have finalSubMemory : s19.memory = s20.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons finalSubRun Line.Run.nil)
  have wf20 : Mem.Wf s20.memory := by
    rw [← finalSubMemory]
    exact wf19
  have reads20 : Mem.Reads s20.memory image4 := by
    rw [← finalSubMemory]
    exact reads19
  obtain ⟨p21, wf21, reads21, -⟩ :=
    of_run_mstoreAt_image p20 wf20 reads20 run
  refine ⟨p21, wf21, ?_, state⟩
  simpa [multiply512ArithmeticTraceImage, image4, image3, image2, image1]
    using reads21

/-! ## Product-producer composition -/

/-- A family-local interface for a straight-line producer: against one exact
proof-carrying memory image, the line pushes its named word without disturbing
that image, memory well-formedness, the surrounding stack, or persistent
state. -/
def ProducesWord
    (sevm : Sevm) (line : Line) (image : Bytes) (value : B256) : Prop :=
  ∀ {pre post : Devm} {tail : Stack},
    Mem.Wf pre.memory →
    Mem.Reads pre.memory image →
    tail <<+ pre.stack →
    Line.Run sevm pre line post →
      value :: tail <<+ post.stack ∧
        Mem.Wf post.memory ∧
        Mem.Reads post.memory image ∧
        pre.state = post.state

theorem ProducesWord.pushB256
    (sevm : Sevm) (image : Bytes) (value : B256) :
    ProducesWord sevm [Ninst.pushB256 value] image value := by
  intro pre post tail memoryWf memoryReads stack run
  have state := Line.of_inv Devm.state (by line_inv) run
  have memory := Line.of_inv Devm.memory (by line_inv) run
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  cases run
  have valuePrefix : value :: tail <<+ post.stack := by
    simpa only [List.singleton_append] using
      prefix_of_push (of_run_pushB256 pushRun) stack
  refine ⟨valuePrefix, ?_, ?_, state⟩
  · rw [← memory]
    exact memoryWf
  · rw [← memory]
    exact memoryReads

theorem ProducesWord.loadWord
    {sevm : Sevm} {image : Bytes} {word value : B256}
    (valueAt : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value) :
    ProducesWord sevm (ProrataWethVault.loadWord word) image value := by
  intro pre post tail memoryWf memoryReads stack run
  exact of_run_loadWordAt_image stack memoryWf memoryReads valueAt run

theorem ProducesWord.arg
    (sevm : Sevm) (image : Bytes) (index : B256) :
    ProducesWord sevm (Blanc.arg index) image
      (Sevm.argWord sevm index) := by
  intro pre post tail memoryWf memoryReads stack run
  have state := Line.of_inv Devm.state (by unfold Blanc.arg cdl; line_inv) run
  have memory := Line.of_inv Devm.memory (by unfold Blanc.arg cdl; line_inv) run
  refine ⟨prefix_of_arg stack run, ?_, ?_, state⟩
  · rw [← memory]
    exact memoryWf
  · rw [← memory]
    exact memoryReads

/-- Extend a proved producer by pushing a constant and adding it.  The result
uses the source-order value even though `ADD` sees the pushed constant first. -/
theorem ProducesWord.addConst
    {sevm : Sevm} {line : Line} {image : Bytes} {value : B256}
    (produces : ProducesWord sevm line image value)
    (constant : B256) :
    ProducesWord sevm
      (line ++ [Ninst.pushB256 constant, Ninst.add]) image
      (value + constant) := by
  intro pre post tail memoryWf memoryReads stack run
  rcases of_run_append line run with ⟨linePost, lineRun, suffixRun⟩
  obtain ⟨valuePrefix, lineWf, lineReads, lineState⟩ :=
    produces memoryWf memoryReads stack lineRun
  have suffixState :=
    Line.of_inv Devm.state (by line_inv) suffixRun
  have suffixMemory :=
    Line.of_inv Devm.memory (by line_inv) suffixRun
  rcases Line.of_run_cons suffixRun with
    ⟨pushPost, pushRun, suffixRun⟩
  rcases Line.of_run_cons suffixRun with
    ⟨addPost, addRun, suffixRun⟩
  cases suffixRun
  have constantPrefix :=
    prefix_of_push (of_run_pushB256 pushRun) valuePrefix
  have resultPrefix : (value + constant) :: tail <<+ post.stack := by
    simpa only [B256.add_comm] using
      prefix_of_add addRun constantPrefix
  refine ⟨resultPrefix, ?_, ?_, lineState.trans suffixState⟩
  · rw [← suffixMemory]
    exact lineWf
  · rw [← suffixMemory]
    exact lineReads

/-- Extend a proved producer by pushing a minuend and subtracting the produced
word from it. -/
theorem ProducesWord.subFromConst
    {sevm : Sevm} {line : Line} {image : Bytes} {value : B256}
    (produces : ProducesWord sevm line image value)
    (constant : B256) :
    ProducesWord sevm
      (line ++ [Ninst.pushB256 constant, Ninst.sub]) image
      (constant - value) := by
  intro pre post tail memoryWf memoryReads stack run
  rcases of_run_append line run with ⟨linePost, lineRun, suffixRun⟩
  obtain ⟨valuePrefix, lineWf, lineReads, lineState⟩ :=
    produces memoryWf memoryReads stack lineRun
  have suffixState :=
    Line.of_inv Devm.state (by line_inv) suffixRun
  have suffixMemory :=
    Line.of_inv Devm.memory (by line_inv) suffixRun
  rcases Line.of_run_cons suffixRun with
    ⟨pushPost, pushRun, suffixRun⟩
  rcases Line.of_run_cons suffixRun with
    ⟨subPost, subRun, suffixRun⟩
  cases suffixRun
  have constantPrefix :=
    prefix_of_push (of_run_pushB256 pushRun) valuePrefix
  have resultPrefix : (constant - value) :: tail <<+ post.stack :=
    prefix_of_sub subRun constantPrefix
  refine ⟨resultPrefix, ?_, ?_, lineState.trans suffixState⟩
  · rw [← suffixMemory]
    exact lineWf
  · rw [← suffixMemory]
    exact lineReads

/-! ## Concrete vault word producers -/

/-- The staged share denominator produces the modular embedding of
`supply + virtualShares`.  Stable-supply consumers can then recover the
unwrapped natural value with `denominatorN_le_maxWord`. -/
theorem ProducesWord.stagedDenominator
    {sevm : Sevm} {image : Bytes} {supply : B256}
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply) :
    ProducesWord sevm stagedDenominator image
      (Nat.toB256 (denominatorN supply.toNat)) := by
  intro pre post tail memoryWf memoryReads stack run
  have rawRun : Line.Run sevm pre
      (ProrataWethVault.loadWord supplyWord ++
        [Ninst.pushB256 virtualShares, Ninst.add]) post := by
    simpa only [ProrataWethVault.stagedDenominator] using run
  have effect :=
    @ProducesWord.addConst sevm (ProrataWethVault.loadWord supplyWord)
      image supply (ProducesWord.loadWord (sevm := sevm) supplyAt)
      virtualShares pre post tail memoryWf memoryReads stack rawRun
  simpa [denominatorN, offsetN, wordAdd_eq_toB256_add,
    virtualShares_toNat] using effect

/-- The staged asset factor produces the word embedding of `assets + 1`.
For the all-ones asset word this is deliberately zero; callers select the
dedicated exact-`2^256` branch before using it as a denominator. -/
theorem ProducesWord.stagedAssetFactor
    {sevm : Sevm} {image : Bytes} {assets : B256}
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets) :
    ProducesWord sevm stagedAssetFactor image
      (Nat.toB256 (assetFactorN assets.toNat)) := by
  intro pre post tail memoryWf memoryReads stack run
  have rawRun : Line.Run sevm pre
      (ProrataWethVault.loadWord assetsWord ++
        [Ninst.pushB256 1, Ninst.add]) post := by
    simpa only [ProrataWethVault.stagedAssetFactor] using run
  have effect :=
    @ProducesWord.addConst sevm (ProrataWethVault.loadWord assetsWord)
      image assets (ProducesWord.loadWord (sevm := sevm) assetsAt)
      1 pre post tail memoryWf memoryReads stack rawRun
  simpa [assetFactorN, wordAdd_eq_toB256_add, B256.toNat_one] using
    effect

/-- Under the executed stable-supply guard, the compiled subtraction produces
the exact remaining mintable share room. -/
theorem ProducesWord.shareRoom
    {sevm : Sevm} {image : Bytes} {supply : B256}
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN) :
    ProducesWord sevm shareRoom image
      (Nat.toB256 (shareRoomN supply.toNat)) := by
  have wordLe : supply ≤ maxSupply := by
    rw [B256.le_iff_toNat_le_toNat, maxSupply_toNat]
    exact stable
  have roomEq :
      maxSupply - supply = Nat.toB256 (shareRoomN supply.toNat) := by
    rw [wordSub_eq_toB256_sub_of_le wordLe, shareRoomN,
      maxSupply_toNat]
  intro pre post tail memoryWf memoryReads stack run
  have rawRun : Line.Run sevm pre
      (ProrataWethVault.loadWord supplyWord ++
        [Ninst.pushB256 maxSupply, Ninst.sub]) post := by
    simpa only [ProrataWethVault.shareRoom] using run
  have effect :=
    @ProducesWord.subFromConst sevm
      (ProrataWethVault.loadWord supplyWord) image supply
      (ProducesWord.loadWord (sevm := sevm) supplyAt) maxSupply
      pre post tail memoryWf memoryReads stack rawRun
  simpa only [roomEq] using effect

/-- The threshold numerator used by `maxDeposit` is the exact successor of
the remaining stable-supply room. -/
theorem ProducesWord.shareRoomPlusOne
    {sevm : Sevm} {image : Bytes} {supply : B256}
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN) :
    ProducesWord sevm shareRoomPlusOne image
      (Nat.toB256 (shareRoomN supply.toNat + 1)) := by
  intro pre post tail memoryWf memoryReads stack run
  have rawRun : Line.Run sevm pre
      (ProrataWethVault.shareRoom ++
        [Ninst.pushB256 1, Ninst.add]) post := by
    simpa only [ProrataWethVault.shareRoomPlusOne] using run
  have effect :=
    @ProducesWord.addConst sevm ProrataWethVault.shareRoom image
      (Nat.toB256 (shareRoomN supply.toNat))
      (ProducesWord.shareRoom (sevm := sevm) supplyAt stable) 1
      pre post tail memoryWf memoryReads stack rawRun
  simpa only [toB256_add_one] using effect

/-- Store the word produced by a `ProducesWord` line and expose the following
continuation with the proof-carrying memory image advanced exactly once. -/
theorem ProducesWord.store_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {line : Line} {image : Bytes} {value word : B256}
    {body : Func} {tail : Stack}
    (produces : ProducesWord sevm line image value)
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (line +++ mstoreAt word +++ body) (.ok final)) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (Bytes.writeAt image (word * 32).toNat value.toBytes) ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨linePost, lineRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨valuePrefix, lineWf, lineReads, lineState⟩ :=
    produces memoryWf memoryReads stack lineRun
  obtain ⟨bodyPre, storeRun, bodyRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨bodyPrefix, bodyWf, bodyReads, storeState⟩ :=
    of_run_mstoreAt_image valuePrefix lineWf lineReads storeRun
  exact ⟨bodyPre, bodyPrefix, bodyWf, bodyReads,
    lineState.trans storeState, bodyRun⟩

/-- The complete proof image after the two producer values and the exact
two-word product have been staged. -/
def multiply512TraceImage (image : Bytes) (x y : B256) : Bytes :=
  multiply512ArithmeticTraceImage
    (Bytes.writeAt
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes)
      (yWord * 32).toNat y.toBytes)
    x y

theorem multiply512TraceImage_low (image : Bytes) (x y : B256) :
    Bytes.toB256
        ((multiply512TraceImage image x y).sliceD
          (lowWord * 32).toNat 32 0) =
      productLowWord x y := by
  exact multiply512ArithmeticTraceImage_low _ _ _

theorem multiply512TraceImage_high (image : Bytes) (x y : B256) :
    Bytes.toB256
        ((multiply512TraceImage image x y).sliceD
          (highWord * 32).toNat 32 0) =
      productHighWord x y := by
  exact multiply512ArithmeticTraceImage_high _ _ _

theorem multiply512TraceImage_denominator
    {image : Bytes} {x y denominator : B256}
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator) :
    Bytes.toB256
        ((multiply512TraceImage image x y).sliceD
          (denominatorWord * 32).toNat 32 0) = denominator := by
  apply multiply512ArithmeticTraceImage_denominator
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · exact denominatorAt
    · right
      decide +kernel
  · right
    decide +kernel

theorem multiply512_eq_producers_arithmetic
    (x y : Line) (body : Func) :
    multiply512 x y body =
      x +++ mstoreAt xWord +++
      y +++ mstoreAt yWord +++
      multiply512ArithmeticLine +++
      body := by
  rfl

/-- Compose two independently proved word producers with the shared exact
`multiply512` suffix and expose the continuation state. -/
theorem multiply512_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {x y : B256} {xLine yLine : Line}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xProduces : ProducesWord sevm xLine image x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (multiply512 xLine yLine body) (.ok final)) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory (multiply512TraceImage image x y) ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  rw [multiply512_eq_producers_arithmetic] at run
  obtain ⟨xPost, xRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨xPrefix, xWf, xReads, xState⟩ :=
    xProduces memoryWf memoryReads stack xRun
  obtain ⟨xStored, xStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨xStoredPrefix, xStoredWf, xStoredReads, xStoreState⟩ :=
    of_run_mstoreAt_image xPrefix xWf xReads xStoreRun
  let image1 := Bytes.writeAt image (xWord * 32).toNat x.toBytes
  change Mem.Reads xStored.memory image1 at xStoredReads

  obtain ⟨yPost, yRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨yPrefix, yWf, yReads, yState⟩ :=
    yProduces xStoredWf xStoredReads xStoredPrefix yRun
  obtain ⟨yStored, yStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨yStoredPrefix, yStoredWf, yStoredReads, yStoreState⟩ :=
    of_run_mstoreAt_image yPrefix yWf yReads yStoreRun
  let image2 := Bytes.writeAt image1 (yWord * 32).toNat y.toBytes
  change Mem.Reads yStored.memory image2 at yStoredReads
  have xAt2 : Bytes.toB256
      (image2.sliceD (xWord * 32).toNat 32 0) = x := by
    unfold image2 image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · left
      decide +kernel
  have yAt2 : Bytes.toB256
      (image2.sliceD (yWord * 32).toNat 32 0) = y := by
    unfold image2
    exact Bytes.readWord_writeAt_self _ _ _

  obtain ⟨bodyPre, arithmeticRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨bodyPrefix, bodyWf, bodyReads, arithmeticState⟩ :=
    multiply512Arithmetic_trace yStoredWf yStoredReads xAt2 yAt2
      yStoredPrefix arithmeticRun
  refine ⟨bodyPre, bodyPrefix, bodyWf, ?_, ?_, bodyRun⟩
  · simpa [multiply512TraceImage, image2, image1] using bodyReads
  · exact xState.trans
      (xStoreState.trans (yState.trans (yStoreState.trans arithmeticState)))

/-! ## Full-width multiply/divide composition -/

/-- A successful floor-mode `mulDiv` executes the exact full-width product
and passes its unbounded-natural floor quotient to the continuation. -/
theorem mulDiv_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {x y denominator : B256}
    {xLine yLine denominatorLine : Line}
    {continuation : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorProduces :
      ProducesWord sevm denominatorLine image denominator)
    (xProduces : ProducesWord sevm xLine
      (Bytes.writeAt image (denominatorWord * 32).toNat
        denominator.toBytes) x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt
        (Bytes.writeAt image (denominatorWord * 32).toNat
          denominator.toBytes)
        (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (mulDiv xLine yLine denominatorLine .down continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (x.toNat * y.toNat / denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  unfold mulDiv at run
  obtain ⟨multiplyPre, multiplyPrefix, multiplyWf, multiplyReads, -, multiplyRun⟩ :=
    denominatorProduces.store_trace memoryWf memoryReads stack run
  let denominatorImage :=
    Bytes.writeAt image (denominatorWord * 32).toNat denominator.toBytes
  change Mem.Reads multiplyPre.memory denominatorImage at multiplyReads
  obtain ⟨dividePre, dividePrefix, divideWf, divideReads, -, divideRun⟩ :=
    multiply512_trace multiplyWf multiplyReads xProduces yProduces
      multiplyPrefix multiplyRun
  have denominatorAt : Bytes.toB256
      ((multiply512TraceImage denominatorImage x y).sliceD
        (denominatorWord * 32).toNat 32 0) = denominator := by
    apply multiply512TraceImage_denominator
    unfold denominatorImage
    exact Bytes.readWord_writeAt_self _ _ _
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    divide512_down_trace divideWf divideReads denominatorAt
      (multiply512TraceImage_high denominatorImage x y)
      (multiply512TraceImage_low denominatorImage x y)
      dividePrefix lookup divideRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  simpa only [wideNumeratorN_productWords] using quotientPrefix

/-- A successful ceiling-mode `mulDiv` executes the exact full-width product
and passes its unbounded-natural ceiling quotient to the continuation. -/
theorem mulDiv_up_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {x y denominator : B256}
    {xLine yLine denominatorLine : Line}
    {continuation : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorProduces :
      ProducesWord sevm denominatorLine image denominator)
    (xProduces : ProducesWord sevm xLine
      (Bytes.writeAt image (denominatorWord * 32).toNat
        denominator.toBytes) x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt
        (Bytes.writeAt image (denominatorWord * 32).toNat
          denominator.toBytes)
        (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (mulDiv xLine yLine denominatorLine .up continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (ceilDiv (x.toNat * y.toNat) denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  unfold mulDiv at run
  obtain ⟨multiplyPre, multiplyPrefix, multiplyWf, multiplyReads, -, multiplyRun⟩ :=
    denominatorProduces.store_trace memoryWf memoryReads stack run
  let denominatorImage :=
    Bytes.writeAt image (denominatorWord * 32).toNat denominator.toBytes
  change Mem.Reads multiplyPre.memory denominatorImage at multiplyReads
  obtain ⟨dividePre, dividePrefix, divideWf, divideReads, -, divideRun⟩ :=
    multiply512_trace multiplyWf multiplyReads xProduces yProduces
      multiplyPrefix multiplyRun
  have denominatorAt : Bytes.toB256
      ((multiply512TraceImage denominatorImage x y).sliceD
        (denominatorWord * 32).toNat 32 0) = denominator := by
    apply multiply512TraceImage_denominator
    unfold denominatorImage
    exact Bytes.readWord_writeAt_self _ _ _
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    divide512_up_trace divideWf divideReads denominatorAt
      (multiply512TraceImage_high denominatorImage x y)
      (multiply512TraceImage_low denominatorImage x y)
      dividePrefix lookup divideRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  simpa only [wideNumeratorN_productWords] using quotientPrefix

/-! ## Shifted full-width division -/

def shiftedDivTraceImage
    (image : Bytes) (high denominator : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt image (highWord * 32).toNat high.toBytes)
      (lowWord * 32).toNat (0 : B256).toBytes)
    (denominatorWord * 32).toNat denominator.toBytes

theorem shiftedDivTraceImage_high
    (image : Bytes) (high denominator : B256) :
    Bytes.toB256
        ((shiftedDivTraceImage image high denominator).sliceD
          (highWord * 32).toNat 32 0) = high := by
  unfold shiftedDivTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · left
      decide +kernel
  · right
    decide +kernel

theorem shiftedDivTraceImage_low
    (image : Bytes) (high denominator : B256) :
    Bytes.toB256
        ((shiftedDivTraceImage image high denominator).sliceD
          (lowWord * 32).toNat 32 0) = 0 := by
  unfold shiftedDivTraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · right
    decide +kernel

theorem shiftedDivTraceImage_denominator
    (image : Bytes) (high denominator : B256) :
    Bytes.toB256
        ((shiftedDivTraceImage image high denominator).sliceD
          (denominatorWord * 32).toNat 32 0) = denominator := by
  unfold shiftedDivTraceImage
  exact Bytes.readWord_writeAt_self _ _ _

theorem shiftedDiv_staging_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high denominator : B256}
    {highLine denominatorLine : Line} {mode : QuotientMode}
    {continuation : Nat} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (highProduces : ProducesWord sevm highLine image high)
    (denominatorProduces : ProducesWord sevm denominatorLine
      (Bytes.writeAt
        (Bytes.writeAt image (highWord * 32).toNat high.toBytes)
        (lowWord * 32).toNat (0 : B256).toBytes) denominator)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (shiftedDiv highLine denominatorLine mode continuation) (.ok final)) :
    ∃ dividePre,
      tail <<+ dividePre.stack ∧
      Mem.Wf dividePre.memory ∧
      Mem.Reads dividePre.memory
        (shiftedDivTraceImage image high denominator) ∧
      pre.state = dividePre.state ∧
      Func.RunCompiledTo fs sevm dividePre
        (divide512 mode continuation) (.ok final) := by
  unfold shiftedDiv at run
  obtain ⟨lowPre, lowPrefix, lowWf, lowReads, highState, run⟩ :=
    highProduces.store_trace memoryWf memoryReads stack run
  let image1 := Bytes.writeAt image (highWord * 32).toNat high.toBytes
  change Mem.Reads lowPre.memory image1 at lowReads
  obtain ⟨denominatorPre, denominatorPrefix, denominatorWf,
      denominatorReads, lowState, run⟩ :=
    ProducesWord.store_trace (ProducesWord.pushB256 sevm image1 0)
      lowWf lowReads lowPrefix run
  let image2 := Bytes.writeAt image1 (lowWord * 32).toNat
    (0 : B256).toBytes
  change Mem.Reads denominatorPre.memory image2 at denominatorReads
  obtain ⟨dividePre, dividePrefix, divideWf, divideReads,
      denominatorState, divideRun⟩ :=
    denominatorProduces.store_trace denominatorWf denominatorReads
      denominatorPrefix run
  refine ⟨dividePre, dividePrefix, divideWf, ?_, ?_, divideRun⟩
  · simpa [shiftedDivTraceImage, image2, image1] using divideReads
  · exact highState.trans (lowState.trans denominatorState)

theorem shiftedDiv_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high denominator : B256}
    {highLine denominatorLine : Line}
    {continuation : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (highProduces : ProducesWord sevm highLine image high)
    (denominatorProduces : ProducesWord sevm denominatorLine
      (Bytes.writeAt
        (Bytes.writeAt image (highWord * 32).toNat high.toBytes)
        (lowWord * 32).toNat (0 : B256).toBytes) denominator)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (shiftedDiv highLine denominatorLine .down continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256
          (high.toNat * wordModulusN / denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨dividePre, dividePrefix, divideWf, divideReads, -, divideRun⟩ :=
    shiftedDiv_staging_trace memoryWf memoryReads highProduces
      denominatorProduces stack run
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    divide512_down_trace divideWf divideReads
      (shiftedDivTraceImage_denominator image high denominator)
      (shiftedDivTraceImage_high image high denominator)
      (shiftedDivTraceImage_low image high denominator)
      dividePrefix lookup divideRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  simpa only [wideNumeratorN, B256.toNat_zero, Nat.add_zero] using
    quotientPrefix

theorem shiftedDiv_up_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {high denominator : B256}
    {highLine denominatorLine : Line}
    {continuation : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (highProduces : ProducesWord sevm highLine image high)
    (denominatorProduces : ProducesWord sevm denominatorLine
      (Bytes.writeAt
        (Bytes.writeAt image (highWord * 32).toNat high.toBytes)
        (lowWord * 32).toNat (0 : B256).toBytes) denominator)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (shiftedDiv highLine denominatorLine .up continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256
          (ceilDiv (high.toNat * wordModulusN) denominator.toNat) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨dividePre, dividePrefix, divideWf, divideReads, -, divideRun⟩ :=
    shiftedDiv_staging_trace memoryWf memoryReads highProduces
      denominatorProduces stack run
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    divide512_up_trace divideWf divideReads
      (shiftedDivTraceImage_denominator image high denominator)
      (shiftedDivTraceImage_high image high denominator)
      (shiftedDivTraceImage_low image high denominator)
      dividePrefix lookup divideRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  simpa only [wideNumeratorN, B256.toNat_zero, Nat.add_zero] using
    quotientPrefix

/-! ## Product division by exactly `2^256` -/

def productOverTwoPow256TraceImage
    (image : Bytes) (x y : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt (multiply512TraceImage image x y)
      (quotientWord * 32).toNat (productHighWord x y).toBytes)
    (remainderWord * 32).toNat (productLowWord x y).toBytes

theorem productOverTwoPow256TraceImage_quotient
    (image : Bytes) (x y : B256) :
    Bytes.toB256
        ((productOverTwoPow256TraceImage image x y).sliceD
          (quotientWord * 32).toNat 32 0) = productHighWord x y := by
  unfold productOverTwoPow256TraceImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · right
    decide +kernel

theorem productOverTwoPow256TraceImage_remainder
    (image : Bytes) (x y : B256) :
    Bytes.toB256
        ((productOverTwoPow256TraceImage image x y).sliceD
          (remainderWord * 32).toNat 32 0) = productLowWord x y := by
  unfold productOverTwoPow256TraceImage
  exact Bytes.readWord_writeAt_self _ _ _

theorem productOverTwoPow256_staging_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {x y : B256} {xLine yLine : Line}
    {mode : QuotientMode} {continuation : Nat} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xProduces : ProducesWord sevm xLine image x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (productOverTwoPow256 xLine yLine mode continuation) (.ok final)) :
    ∃ finishPre,
      tail <<+ finishPre.stack ∧
      Mem.Wf finishPre.memory ∧
      Mem.Reads finishPre.memory
        (productOverTwoPow256TraceImage image x y) ∧
      pre.state = finishPre.state ∧
      Func.RunCompiledTo fs sevm finishPre
        (finishQuotient mode continuation) (.ok final) := by
  unfold productOverTwoPow256 at run
  obtain ⟨quotientPre, quotientPrefix, quotientWf, quotientReads,
      multiplyState, run⟩ :=
    multiply512_trace memoryWf memoryReads xProduces yProduces stack run
  have highAt : Bytes.toB256
      ((multiply512TraceImage image x y).sliceD
        (highWord * 32).toNat 32 0) = productHighWord x y :=
    multiply512TraceImage_high image x y
  obtain ⟨remainderPre, remainderPrefix, remainderWf, remainderReads,
      quotientState, run⟩ :=
    ProducesWord.store_trace (ProducesWord.loadWord highAt)
      quotientWf quotientReads quotientPrefix run
  let image1 := Bytes.writeAt (multiply512TraceImage image x y)
    (quotientWord * 32).toNat (productHighWord x y).toBytes
  change Mem.Reads remainderPre.memory image1 at remainderReads
  have lowAt1 : Bytes.toB256
      (image1.sliceD (lowWord * 32).toNat 32 0) =
        productLowWord x y := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact multiply512TraceImage_low image x y
    · left
      decide +kernel
  obtain ⟨finishPre, finishPrefix, finishWf, finishReads,
      remainderState, finishRun⟩ :=
    ProducesWord.store_trace (ProducesWord.loadWord lowAt1)
      remainderWf remainderReads remainderPrefix run
  refine ⟨finishPre, finishPrefix, finishWf, ?_, ?_, finishRun⟩
  · simpa [productOverTwoPow256TraceImage, image1] using finishReads
  · exact multiplyState.trans (quotientState.trans remainderState)

theorem productOverTwoPow256_down_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {x y : B256} {xLine yLine : Line}
    {continuation : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xProduces : ProducesWord sevm xLine image x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (productOverTwoPow256 xLine yLine .down continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (x.toNat * y.toNat / wordModulusN) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨finishPre, finishPrefix, finishWf, finishReads, -, finishRun⟩ :=
    productOverTwoPow256_staging_trace memoryWf memoryReads xProduces
      yProduces stack run
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    finishQuotient_down_trace finishWf finishReads
      (productOverTwoPow256TraceImage_quotient image x y)
      finishPrefix lookup finishRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  simpa only [productHighWord_eq_toB256_div_wordModulus] using
    quotientPrefix

theorem productOverTwoPow256_up_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {x y : B256} {xLine yLine : Line}
    {continuation : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xProduces : ProducesWord sevm xLine image x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (productOverTwoPow256 xLine yLine .up continuation) (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (ceilDiv (x.toNat * y.toNat) wordModulusN) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨finishPre, finishPrefix, finishWf, finishReads, -, finishRun⟩ :=
    productOverTwoPow256_staging_trace memoryWf memoryReads xProduces
      yProduces stack run
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    finishQuotient_up_trace finishWf finishReads
      (productOverTwoPow256TraceImage_quotient image x y)
      (productOverTwoPow256TraceImage_remainder image x y)
      finishPrefix lookup finishRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  simpa only [roundedProductHighWord_eq_toB256_ceilDiv] using
    quotientPrefix

theorem productOverTwoPow256_capDown_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {x y : B256} {xLine yLine : Line}
    {continuation : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xProduces : ProducesWord sevm xLine image x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (productOverTwoPow256 xLine yLine .capDown continuation)
        (.ok final)) :
    ∃ bodyPre,
      Nat.toB256 (x.toNat * y.toNat / wordModulusN) :: tail <<+
        bodyPre.stack ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨finishPre, finishPrefix, finishWf, finishReads, -, finishRun⟩ :=
    productOverTwoPow256_staging_trace memoryWf memoryReads xProduces
      yProduces stack run
  obtain ⟨bodyPre, quotientPrefix, bodyRun⟩ :=
    finishQuotient_capDown_trace finishWf finishReads
      (productOverTwoPow256TraceImage_quotient image x y)
      finishPrefix lookup finishRun
  refine ⟨bodyPre, ?_, bodyRun⟩
  simpa only [productHighWord_eq_toB256_div_wordModulus] using
    quotientPrefix

end ProrataWethVault

end Blanc
