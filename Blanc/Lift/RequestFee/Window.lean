import Blanc.Lift.CreationOps
import Blanc.Lift.WalkInvKit
import Blanc.MachineDataFacts
import Blanc.WordFakeExponential

/-!
# The request contracts' fee window

The system request contracts compute their fee with one instruction sequence: six setup
instructions, a loop over the word `fake_exponential` at fraction 17, and a postloop that divides
and branches on the calldata length. Only the pushed jump targets, the calldata length and the
continuation trees differ, so those are the parameters here: `loopTree`, `initTree` and
`postloopTree`. A generated tree is one of these definitionally, so a contract supplies the
parameters and bridges by `rfl`.

The walks stop before the postloop and at the selected continuation, retaining arbitrary base state
and memory. The word recurrence witness supplies the body count, so there is no fuel or termination
argument. Exact walks take `PUSH0`'s activation as a hypothesis and assume no other fork fact.
Neither the excess read nor the inhibitor guard is here: those differ between contracts.
-/

namespace Blanc.Lift.RequestFee

open Jaune
open WordFakeExponential (nextAccumulator)

/-- A nonempty `PUSH` immediate, the shape of a pushed jump target or length. -/
structure PushWord where
  head : UInt8
  tail : Bytes
  le : (head :: tail).length ≤ 32

/-- The word a `PushWord` pushes. -/
abbrev PushWord.word (p : PushWord) : B256 := Bytes.toB256 (p.head :: p.tail)

/-- The loop body: accumulate, step the recurrence, count, jump to the program's loop entry. -/
def loopBody (loop : PushWord) (entry : Nat) : SFunc :=
  (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg (.dup 3))
  (.next (.reg .mul) (.next (.reg (.dup 4)) (.next (.reg (.dup 3)) (.next (.reg .mul)
  (.next (.reg (.swap 0)) (.next (.reg .div) (.next (.reg (.swap 1))
  (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.reg (.swap 1))
  (.next (.reg (.swap 0)) (.next (.push (loop.head :: loop.tail) loop.le)
  (.jump entry)))))))))))))))))

/-- The loop header: a zero accumulator leaves for the postloop. -/
def loopHeader (post : PushWord) (body postloop : SFunc) : SFunc :=
  (.dest (.next (.push [] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .gt)
  (.next (.reg .iszero) (.next (.push (post.head :: post.tail) post.le)
  (.branch body postloop)))))))

/-- Header and body of one contract's loop. -/
abbrev loopTree (post loop : PushWord) (entry : Nat) (postloop : SFunc) : SFunc :=
  loopHeader post (loopBody loop entry) postloop

/-- Setup from `[excess, 17]` to the loop's five stack words, falling into `header`. -/
def initTree (header : SFunc) : SFunc :=
  (.next (.push [0x01] (by decide)) (.next (.reg (.dup 2)) (.next (.reg .mul)
  (.next (.push [0x01] (by decide)) (.next (.reg (.swap 0))
  (.next (.push [] (by decide)) header))))))

/-- Divide, drop the loop words, and branch on whether the calldata length is `len`. -/
def postloopTree (len dest : PushWord) (getter submission : SFunc) : SFunc :=
  (.dest (.next (.reg (.swap 0)) (.next (.reg (.swap 3)) (.next (.reg (.swap 0)) (.next (.reg .div)
  (.next (.reg (.swap 2)) (.next (.reg .pop) (.next (.reg .pop) (.next (.reg .pop)
  (.next (.reg .calldatasize) (.next (.push (len.head :: len.tail) len.le) (.next (.reg .eq)
  (.next (.push (dest.head :: dest.tail) dest.le) (.branch getter submission))))))))))))))

/-- JUMPDEST, PUSH0, DUP3, GT, ISZERO, PUSH1, JUMPI. -/
def feeLoopHeaderGas : Nat := gJumpdest + gBase + 4 * gVerylow + gHigh

/-- Thirteen very-low operations, two MULs, DIV, and the backedge JUMP. -/
def feeLoopBodyGas : Nat := 13 * gVerylow + 3 * gLow + gMid

/-- Every active body has a header test; one additional test exits the loop. -/
def feeLoopGas (iterations : Nat) : Nat :=
  feeLoopHeaderGas * (iterations + 1) + feeLoopBodyGas * iterations

theorem feeLoopHeaderGas_eq : feeLoopHeaderGas = 25 := rfl
theorem feeLoopBodyGas_eq : feeLoopBodyGas = 62 := rfl

theorem feeLoopGas_eq (iterations : Nat) : feeLoopGas iterations = 25 + 87 * iterations := by
  unfold feeLoopGas
  rw [feeLoopHeaderGas_eq, feeLoopBodyGas_eq, Nat.mul_add, Nat.mul_one]
  rw [Nat.add_right_comm, ← Nat.add_mul]
  exact Nat.add_comm _ _

private theorem feeLoopGas_succ (iterations : Nat) :
    feeLoopGas (iterations + 1) = feeLoopGas iterations + 62 + 25 := by
  rw [feeLoopGas_eq, feeLoopGas_eq, Nat.mul_add, Nat.mul_one]
  simp only [Nat.add_assoc]

/-- Header, four swaps, DIV, three POPs, CALLDATASIZE, two PUSHes, EQ, JUMPI. -/
def postloopFixedGas : Nat :=
  gJumpdest + 4 * gVerylow + gLow + 3 * gBase + gBase + 3 * gVerylow + gHigh

theorem postloopFixedGas_eq : postloopFixedGas = 45 := rfl

section Walks

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}

private theorem header_inv {post : PushWord} {body postloop : SFunc}
    {output accumulator counter numerator denominator : B256}
    (run : SFunc.Run fs sevm (St b [output, accumulator, counter, numerator, denominator] M G)
      (loopHeader post body postloop) o) :
    ∃ G', SFunc.Run fs sevm (St b [output, accumulator, counter, numerator, denominator] M G')
      (if accumulator = 0 then postloop else body) o := by
  obtain ⟨_, run⟩ := ric_dest run.cut
  winv 1
  change SFunc.RunCut _ _ _ (St b [0, output, accumulator, counter, numerator, denominator] M _) _ _ at run
  winv 4
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨flag, G', run⟩
  · have active : accumulator ≠ 0 := by
      intro hz
      subst accumulator
      change (1 : B256) = 0 at flag
      exact (by decide : (1 : B256) ≠ 0) flag
    exact ⟨G', (ite_eq_right active) ▸ run.uncut⟩
  · have hle := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero flag)
    have hz : accumulator = 0 := B256.toNat_inj _ _ (Nat.eq_zero_of_le_zero hle)
    exact ⟨G', (ite_eq_left hz) ▸ run.uncut⟩

private theorem header_exact {post : PushWord} {body postloop : SFunc}
    {output accumulator counter numerator denominator : B256}
    (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (tail : SFunc.RunExact fs sevm
      (St b [output, accumulator, counter, numerator, denominator] M G)
      (if accumulator = 0 then postloop else body) o) :
    SFunc.RunExact fs sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + 25))
      (loopHeader post body postloop) o := by
  have hgas : G + 25 = G + 10 + 3 + 3 + 3 + 3 + 2 + 1 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold loopHeader
  refine rx_dest ?_
  refine rx_push0 (h_push0 := h_push0) (by change 5 < 1024; decide) ?_
  refine rx_dup3 (by change 6 < 1024; decide) ?_
  refine rx_gt rfl (by change 5 < 1024; decide) ?_
  refine rx_iszero rfl (by change 5 < 1024; decide) ?_
  refine rx_push rfl (by change 6 < 1024; decide) ?_
  by_cases hz : accumulator = 0
  · subst accumulator
    change SFunc.RunExact _ _ (St b (post.word :: 1 :: _) _ _) _ _
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) tail
  · have positive : (0 : B256) < accumulator := by
      rw [B256.lt_iff_toNat_lt_toNat]
      exact Nat.pos_of_ne_zero (fun h => hz (B256.toNat_inj _ _ h))
    have flag : B256.eqCheck (B256.gtCheck accumulator 0) 0 = 0 := by
      simp only [B256.gtCheck, ite_eq_left positive, B256.eqCheck,
        ite_eq_right (by decide : (1 : B256) ≠ 0)]
    rw [flag]
    apply rx_branch_zero
    simpa only [ite_eq_right hz] using tail

private theorem body_inv {loop : PushWord} {entry : Nat} {header : SFunc}
    (hj : fs[entry]? = some header)
    {output accumulator counter numerator denominator : B256}
    (run : SFunc.Run fs sevm (St b [output, accumulator, counter, numerator, denominator] M G)
      (loopBody loop entry) o) :
    ∃ G', SFunc.Run fs sevm
      (St b [output + accumulator, nextAccumulator numerator denominator counter accumulator,
        counter + 1, numerator, denominator] M G') header o := by
  have run := run.cut
  winv 2
  rw [show accumulator + output = output + accumulator from B256.add_comm] at run
  winv 3
  rw [Blanc.B256.mul_comm numerator accumulator] at run
  winv 3
  rw [Blanc.B256.mul_comm counter denominator] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [accumulator * numerator, denominator * counter, output + accumulator, counter, numerator, denominator]) rfl h
  winv 1
  change SFunc.RunCut _ _ _
    (St b [nextAccumulator numerator denominator counter accumulator, output + accumulator,
      counter, numerator, denominator] M _) _ _ at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [counter, output + accumulator, nextAccumulator numerator denominator counter accumulator,
      numerator, denominator]) rfl h
  winv 1
  change SFunc.RunCut _ _ _ (St b
    [1, counter, output + accumulator, nextAccumulator numerator denominator counter accumulator,
      numerator, denominator] M _) _ _ at run
  winv 1
  rw [show (1 : B256) + counter = counter + 1 from B256.add_comm] at run
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [nextAccumulator numerator denominator counter accumulator, output + accumulator,
      counter + 1, numerator, denominator]) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap
    (S' := [output + accumulator, nextAccumulator numerator denominator counter accumulator,
      counter + 1, numerator, denominator]) rfl h
  obtain ⟨_, h, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push h
  obtain ⟨G', run⟩ := ric_jump (by intro h; cases h) hj run
  exact ⟨G', run.uncut⟩

private theorem body_exact {loop : PushWord} {entry : Nat} {header : SFunc}
    (hj : fs[entry]? = some header)
    {output accumulator counter numerator denominator : B256}
    (tail : SFunc.RunExact fs sevm
      (St b [output + accumulator, nextAccumulator numerator denominator counter accumulator,
        counter + 1, numerator, denominator] M G) header o) :
    SFunc.RunExact fs sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + 62))
      (loopBody loop entry) o := by
  have hgas : G + 62 = G + 8 + 3 + 3 + 3 + 3 + 3 + 3 + 5 + 3 + 5 + 3 + 3 + 5 + 3 + 3 + 3 + 3 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold loopBody
  refine rx_dup2 (by change 5 < 1024; decide) ?_
  refine rx_add' B256.add_comm (by change 4 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_dup4 (by change 5 < 1024; decide) ?_
  refine rx_mul (Blanc.B256.mul_comm numerator accumulator) (by change 4 < 1024; decide) ?_
  refine rx_dup (n := 4) rfl (by change 5 < 1024; decide) ?_
  refine rx_dup4 (by change 6 < 1024; decide) ?_
  refine rx_mul (Blanc.B256.mul_comm counter denominator) (by change 5 < 1024; decide) ?_
  refine rx_swap1 ?_
  refine rx_div (v := nextAccumulator numerator denominator counter accumulator) rfl
    (by change 4 < 1024; decide) ?_
  refine rx_swap2 ?_
  refine rx_push (w := (1 : B256)) rfl (by change 5 < 1024; decide) ?_
  refine rx_add' B256.add_comm (by change 4 < 1024; decide) ?_
  refine rx_swap2 ?_
  refine rx_swap1 ?_
  refine rx_push rfl (by change 5 < 1024; decide) ?_
  exact rx_jump hj tail

/-- Inversion follows the finite word witness and exposes the discarded final counter. -/
theorem loop_inv {post loop : PushWord} {entry : Nat} {postloop : SFunc}
    (hj : fs[entry]? = some (loopTree post loop entry postloop))
    {output accumulator counter numerator denominator finalOutput : B256} {iterations : Nat}
    (wordRun : WordFakeExponential.Run numerator denominator counter accumulator output iterations finalOutput)
    (run : SFunc.Run fs sevm (St b [output, accumulator, counter, numerator, denominator] M G)
      (loopTree post loop entry postloop) o) :
    ∃ finalCounter G', SFunc.Run fs sevm
      (St b [finalOutput, 0, finalCounter, numerator, denominator] M G') postloop o := by
  induction wordRun generalizing G with
  | stop counter output =>
    obtain ⟨G', run⟩ := header_inv run
    exact ⟨counter, G', run⟩
  | step active next ih =>
    obtain ⟨_, run⟩ := header_inv run
    simp only [ite_eq_right active] at run
    obtain ⟨_, run⟩ := body_inv hj run
    exact ih run

/-- Exact continuation transport for the word witness's body count. -/
theorem loop_exact {post loop : PushWord} {entry : Nat} {postloop : SFunc}
    (hj : fs[entry]? = some (loopTree post loop entry postloop))
    {output accumulator counter numerator denominator finalOutput : B256} {iterations : Nat}
    (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (wordRun : WordFakeExponential.Run numerator denominator counter accumulator output iterations finalOutput)
    (tail : ∀ finalCounter, SFunc.RunExact fs sevm
      (St b [finalOutput, 0, finalCounter, numerator, denominator] M G) postloop o) :
    SFunc.RunExact fs sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + feeLoopGas iterations))
      (loopTree post loop entry postloop) o := by
  induction wordRun generalizing G with
  | stop counter output =>
    exact header_exact h_push0 (tail counter)
  | @step counter accumulator output iterations finalOutput active next ih =>
    rw [feeLoopGas_succ, ← Nat.add_assoc, ← Nat.add_assoc]
    apply header_exact h_push0
    simp only [ite_eq_right active]
    exact body_exact hj (ih tail)

private theorem one_push : Bytes.toB256 [0x01] = (1 : B256) := rfl
private theorem zero_push : Bytes.toB256 [] = (0 : B256) := rfl

/-- Setup reaches the loop's initial stack. -/
theorem init_inv {header : SFunc} {excess : B256}
    (run : SFunc.Run fs sevm (St b [excess, 17] M G) (initTree header) o) :
    ∃ G', SFunc.Run fs sevm (St b [0, 17, 1, excess, 17] M G') header o := by
  unfold initTree at run
  cases run with
  | next hp k =>
    obtain ⟨_, rfl⟩ := ri_push hp
    rw [one_push] at k
    cases k with
    | next hd k =>
      obtain ⟨_, rfl⟩ := ri_dup (w := 17) rfl hd
      cases k with
      | next hm k =>
        obtain ⟨_, rfl⟩ := ri_mul hm
        rw [show (17 : B256) * 1 = 17 from rfl] at k
        cases k with
        | next hp k =>
          obtain ⟨_, rfl⟩ := ri_push hp
          rw [one_push] at k
          cases k with
          | next hs k =>
            obtain ⟨_, rfl⟩ := ri_swap (S' := [17, 1, excess, 17]) rfl hs
            cases k with
            | next hp k =>
              obtain ⟨_, rfl⟩ := ri_push hp
              rw [zero_push] at k
              exact ⟨_, k⟩

/-- Setup, forward, at its exact charge of 19. -/
theorem init_exact {header : SFunc} {excess : B256}
    (h_push0 : sevm.benvStat.rules.op.push0 = true)
    (tail : SFunc.RunExact fs sevm (St b [0, 17, 1, excess, 17] M G) header o) :
    SFunc.RunExact fs sevm (St b [excess, 17] M (G + 19)) (initTree header) o := by
  have hgas : G + 19 = G + 2 + 3 + 3 + 5 + 3 + 3 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold initTree
  refine rx_push one_push (by change 2 < 1024; decide) ?_
  refine rx_dup3 (by change 3 < 1024; decide) ?_
  refine rx_mul (v := 17) rfl (by change 2 < 1024; decide) ?_
  refine rx_push one_push (by change 3 < 1024; decide) ?_
  refine rx_swap1 ?_
  exact rx_push0 (h_push0 := h_push0) (by change 4 < 1024; decide) tail

/-- The continuation the postloop selects for the calldata length. -/
def selected (sevm : Sevm) (len : B256) (getter submission : SFunc) : SFunc :=
  if sevm.data.length.toB256 = len then submission else getter

/-- The postloop leaves the quotient alone on the stack, at the selected continuation. -/
theorem postloop_inv {len dest : PushWord} {w : B256} (hw : len.word = w)
    {getter submission : SFunc}
    {output accumulator counter numerator denominator : B256}
    (run : SFunc.Run fs sevm (St b [output, accumulator, counter, numerator, denominator] M G)
      (postloopTree len dest getter submission) o) :
    ∃ G', SFunc.Run fs sevm (St b [output / denominator] M G')
      (selected sevm w getter submission) o := by
  subst hw
  obtain ⟨_, run⟩ := ric_dest run.cut
  winv 10
  change SFunc.RunCut _ _ _ (St b [len.word, sevm.data.length.toB256, output / denominator] M _) _ _ at run
  winv 2
  rcases ric_branch run with ⟨flag, G', run⟩ | ⟨flag, G', run⟩
  · have hlen : sevm.data.length.toB256 ≠ len.word := by
      intro hlen
      simp only [hlen, B256.eqCheck, ite_true] at flag
      exact (by decide : (1 : B256) ≠ 0) flag
    refine ⟨G', ?_⟩
    simpa only [selected, ite_eq_right hlen] using run.uncut
  · have hlen : sevm.data.length.toB256 = len.word := by
      by_cases hlen : len.word = sevm.data.length.toB256
      · exact hlen.symm
      · simp only [B256.eqCheck, ite_eq_right hlen] at flag
        exact False.elim (flag rfl)
    refine ⟨G', ?_⟩
    simpa only [selected, ite_eq_left hlen] using run.uncut

/-- The postloop, forward, at its exact charge of 45. -/
theorem postloop_exact {len dest : PushWord} {w : B256} (hw : len.word = w)
    {getter submission : SFunc}
    {output accumulator counter numerator denominator : B256}
    (tail : SFunc.RunExact fs sevm (St b [output / denominator] M G)
      (selected sevm w getter submission) o) :
    SFunc.RunExact fs sevm
      (St b [output, accumulator, counter, numerator, denominator] M (G + 45))
      (postloopTree len dest getter submission) o := by
  subst hw
  have hgas : G + 45 = G + 10 + 3 + 3 + 3 + 2 + 2 + 2 + 2 + 3 + 5 + 3 + 3 + 3 + 1 := by
    simp only [Nat.add_assoc]
  rw [hgas]
  unfold postloopTree
  refine rx_dest ?_
  refine rx_swap1 ?_
  refine rx_swap (n := 3) rfl ?_
  refine rx_swap1 ?_
  refine rx_div rfl (by change 3 < 1024; decide) ?_
  refine rx_swap3 ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_calldatasize (by change 1 < 1024; decide) ?_
  refine rx_push (w := len.word) rfl (by change 2 < 1024; decide) ?_
  refine rx_eq rfl (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  by_cases hlen : sevm.data.length.toB256 = len.word
  · simp only [hlen, B256.eqCheck, ite_true]
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    simpa only [selected, ite_eq_left hlen] using tail
  · simp only [B256.eqCheck, ite_eq_right (Ne.symm hlen)]
    apply rx_branch_zero
    simpa only [selected, ite_eq_right hlen] using tail

end Walks

end Blanc.Lift.RequestFee
