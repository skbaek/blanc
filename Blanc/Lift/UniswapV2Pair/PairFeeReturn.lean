import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.UniswapV2Pair.PairFeeObservation
import Blanc.Lift.UniswapV2Pair.FeeMintWalk

/-! Actual shared Pair fee body returns through its retained caller. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def pairFeeReturnEntries : List Nat :=
  [9, 18, 23, 24, 25, 26, 58, 59, 62, 69, 72, 74]

theorem pairFeeReturnEntries_free : ExecFreeSet cert.prog pairFeeReturnEntries = true := by decide

theorem pairFeeReturnEntries_noHalt : NoHaltSet cert.prog pairFeeReturnEntries = true := by decide

/-- The physical factory reply drives the same checked body to its original
caller. The supplied caller and outer continuations may contain external calls. -/
theorem PairFeeObservation.returnCursor {root start : Exec.Deriv} {b post : Devm}
    {M : Mem} {r1 r0 ρ : B256} {R : List B256} {K : List SFunc} {caller : SFunc}
    (r : PairFeeObservation root start b M r1 r0 ρ R (caller :: K))
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ExecFreeUntil r.occurrence.call.returned N ∧
      N.sevm = start.sevm ∧ N.exn = .ok post ∧
      CursorOK code cert N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
      ∃ gas, SFunc.Run cert.prog start.sevm
        (St r.occurrence.call.returned.devm
          (Bytes.toB256 (r.out.take 32) :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeReplyMemory M r.out) gas) pairFeeAfterDecodeTree (.returned N.devm) := by
  have returnedEnv : r.occurrence.call.returned.sevm = start.sevm :=
    (Cursor.parentStep_sevm r.occurrence.call.edge).trans r.occurrence.sevm_eq
  have returnedOutcome : r.occurrence.call.returned.exn = .ok post :=
    (Blanc.Exec.Deriv.ParentPrefix.exn_eq
      (.step r.occurrence.call.edge (.refl _))).trans (r.occurrence.exn_eq.trans success)
  obtain ⟨N, next, span, env, outcome, placed, tree, conts, source⟩ :=
    r.decoded.placed.quietReturn cert_check (r.decoded.exn_eq.trans returnedOutcome)
      (by rw [r.decoded.sevm_eq, returnedEnv]; exact fork)
      pairFeeReturnEntries_free pairFeeReturnEntries_noHalt
      (by rw [r.decoded.tree]; decide) (by rw [r.decoded.tree]; decide)
      r.decoded.continuations
  obtain ⟨gas, state⟩ := r.decoded.state
  rw [r.decoded.tree, state, r.decoded.sevm_eq, returnedEnv] at source
  exact ⟨N, next, r.decoded.free.trans span,
    env.trans (r.decoded.sevm_eq.trans returnedEnv),
    outcome.trans (r.decoded.exn_eq.trans returnedOutcome), placed, tree, conts, gas, source⟩

/-- Invert the fee decoder tail already reached by the physical reply cursor. -/
theorem pair_fee_decoder_tail_inv {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {w r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm
      (St b (w :: 0 :: 0 :: r1 :: r0 :: ρ :: R) M G) pairFeeAfterDecodeTree o) :
    ∃ gas, SFunc.Run cert.prog sevm
      (St (feeKLastWorld sevm b)
        (feeKLastWord sevm b :: w :: feeOnWord w :: r1 :: r0 :: ρ :: R) M gas)
      (feeDecodedTree w) o := by
  have run := SFunc.runP_iff_runCutP_nil.mp run
  dsimp only [pairFeeAfterDecodeTree, t_2781_c68] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push hs
  rw [show Bytes.toB256 [0x0b] = (11 : B256) from by decide] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := w) rfl hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and hs
  rw [B256.and_comm w, ff20_and_word] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push hs
  by_cases addressZero : w.toAdr.toB256 = 0
  · simp only [B256.eqCheck, ite_eq_left addressZero] at run
    rcases ric_branchP run with ⟨hz, _, _⟩ | ⟨_, gas, tail⟩
    · exact (by decide : (1 : B256) ≠ 0) hz |>.elim
    · exact ⟨gas, SFunc.runP_iff_runCutP_nil.mpr (by simpa only [feeDecodedTree, ite_eq_left addressZero,
        feeKLastWorld, feeKLastWord, feeOnWord, B256.eqCheck, ite_eq_left addressZero] using tail)⟩
  · simp only [B256.eqCheck, ite_eq_right addressZero] at run
    rcases ric_branchP run with ⟨_, gas, tail⟩ | ⟨hz, _, _⟩
    · exact ⟨gas, SFunc.runP_iff_runCutP_nil.mpr (by simpa only [feeDecodedTree, ite_eq_right addressZero,
        feeKLastWorld, feeKLastWord, feeOnWord, B256.eqCheck, ite_eq_right addressZero] using tail)⟩
    · exact (hz rfl).elim

/-- The same original fee reply determines the complete actual caller state.
Both fee branch guards and residual gas are inferred from this successful suffix. -/
theorem PairFeeObservation.returnState {root start : Exec.Deriv} {b post : Devm}
    {M : Mem} {r1 r0 ρ : B256} {R : List B256} {K : List SFunc} {caller : SFunc}
    (r : PairFeeObservation root start b M r1 r0 ρ R (caller :: K))
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) (bound0 : r0.toNat < 2 ^ 112)
    (bound1 : r1.toNat < 2 ^ 112) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ExecFreeUntil r.occurrence.call.returned N ∧
      N.sevm = start.sevm ∧ N.exn = .ok post ∧
      CursorOK code cert N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
      feeBranchAccepts start.sevm (feeKLastWorld start.sevm r.occurrence.call.returned.devm)
        (feeKLastWord start.sevm r.occurrence.call.returned.devm)
        (Bytes.toB256 (r.out.take 32)) r0 r1 ∧
      ∃ gas, N.devm = feeBranchPost start.sevm
        (feeKLastWorld start.sevm r.occurrence.call.returned.devm) R (feeReplyMemory M r.out)
        (feeKLastWord start.sevm r.occurrence.call.returned.devm)
        (Bytes.toB256 (r.out.take 32)) r0 r1 gas := by
  obtain ⟨N, next, span, env, outcome, placed, tree, conts, gas, source⟩ :=
    r.returnCursor success fork
  obtain ⟨branchGas, branch⟩ := pair_fee_decoder_tail_inv fork source
  obtain ⟨guards, residual, same⟩ := feeBranch_inv fork
    (feeReplyMemory_ptr r.out (feeRequestMemory_ptr mem)) bound0 bound1 branch
  exact ⟨N, next, span, env, outcome, placed, tree, conts, guards, residual,
    Outcome.returned.inj same⟩

end Blanc.Lift.UniswapV2Pair
