import Blanc.Lift.HistCursorReturn
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

theorem PairFeeObservationH.returnCursor {root start : Exec.Deriv} {b post Wc : Devm}
    {M : Mem} {r1 r0 ρ : B256} {R : List B256} {K : List SFunc} {caller : SFunc}
    (r : PairFeeObservationH root start b Wc M r1 r0 ρ R (caller :: K))
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none) :
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
    r.decoded.placed.quietReturnH cert_check (r.decoded.exn_eq.trans returnedOutcome)
      (by rw [r.decoded.sevm_eq, returnedEnv]; exact stateGas)
      pairFeeReturnEntries_free pairFeeReturnEntries_noHalt
      (by rw [r.decoded.tree]; decide) (by rw [r.decoded.tree]; decide)
      r.decoded.continuations
  obtain ⟨gas, state⟩ := r.decoded.state
  rw [r.decoded.tree, state, r.decoded.sevm_eq, returnedEnv] at source
  exact ⟨N, next, r.decoded.free.trans span,
    env.trans (r.decoded.sevm_eq.trans returnedEnv),
    outcome.trans (r.decoded.exn_eq.trans returnedOutcome), placed, tree, conts, gas, source⟩

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
          (feeReplyMemory M r.out) gas) pairFeeAfterDecodeTree (.returned N.devm) :=
  PairFeeObservationH.returnCursor (r.toH fork) success fork.rules_stateGas_none


theorem pair_fee_decoder_tail_invH {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {w r1 r0 ρ : B256} {o : Outcome}
    (bal : sevm.benvStat.rules.bal = none)
    (run : SFunc.Run cert.prog sevm
      (St b (w :: 0 :: 0 :: r1 :: r0 :: ρ :: R) M G) pairFeeAfterDecodeTree o) :
    ∃ gas, SFunc.Run cert.prog sevm
      (St (feeKLastWorldH sevm b)
        (feeKLastWord sevm b :: w :: feeOnWord w :: r1 :: r0 :: ρ :: R) M gas)
      (feeDecodedTree w) o := by
  have run := SFunc.runP_iff_runCutP_nil.mp run
  dsimp only [pairFeeAfterDecodeTree, t_2781_c68] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push hs
  rw [show Bytes.toB256 [0x0b] = (11 : B256) from by decide] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sloadH bal hs
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
        feeKLastWorldH, feeKLastWord, feeOnWord, B256.eqCheck, ite_eq_left addressZero] using tail)⟩
  · simp only [B256.eqCheck, ite_eq_right addressZero] at run
    rcases ric_branchP run with ⟨_, gas, tail⟩ | ⟨hz, _, _⟩
    · exact ⟨gas, SFunc.runP_iff_runCutP_nil.mpr (by simpa only [feeDecodedTree, ite_eq_right addressZero,
        feeKLastWorldH, feeKLastWord, feeOnWord, B256.eqCheck, ite_eq_right addressZero] using tail)⟩
    · exact (hz rfl).elim

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
  simpa only [feeKLastWorldH_of_covered fork] using
    pair_fee_decoder_tail_invH fork.rules_bal_none run


theorem PairFeeObservationH.returnState {root start : Exec.Deriv} {b post Wc : Devm}
    {M : Mem} {r1 r0 ρ : B256} {R : List B256} {K : List SFunc} {caller : SFunc}
    (r : PairFeeObservationH root start b Wc M r1 r0 ρ R (caller :: K))
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (mem : PtrMem 128 192 M) (bound0 : r0.toNat < 2 ^ 112)
    (bound1 : r1.toNat < 2 ^ 112) :
    ∃ (N : Exec.Deriv) (next : Cursor),
      Exec.Deriv.ExecFreeUntil r.occurrence.call.returned N ∧
      N.sevm = start.sevm ∧ N.exn = .ok post ∧
      CursorOK code cert N next ∧ next.f = caller ∧ next.K.map Cont.f = K ∧
      feeBranchAcceptsH start.sevm (feeKLastWorldH start.sevm r.occurrence.call.returned.devm)
        (feeKLastWord start.sevm r.occurrence.call.returned.devm)
        (Bytes.toB256 (r.out.take 32)) r0 r1 ∧
      ∃ gas, N.devm = feeBranchPostH start.sevm
        (feeKLastWorldH start.sevm r.occurrence.call.returned.devm) R (feeReplyMemory M r.out)
        (feeKLastWord start.sevm r.occurrence.call.returned.devm)
        (Bytes.toB256 (r.out.take 32)) r0 r1 gas := by
  obtain ⟨N, next, span, env, outcome, placed, tree, conts, gas, source⟩ :=
    r.returnCursor success stateGas
  obtain ⟨branchGas, branch⟩ := pair_fee_decoder_tail_invH bal source
  obtain ⟨guards, residual, same⟩ := feeBranch_invH stateGas bal
    (feeReplyMemory_ptr r.out (feeRequestMemory_ptr mem)) bound0 bound1 branch
  exact ⟨N, next, span, env, outcome, placed, tree, conts, guards, residual,
    Outcome.returned.inj same⟩

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
  simpa only [PairFeeObservation.toH, feeBranchAcceptsH_of_covered fork, feeBranchPostH_of_covered fork,
    feeKLastWorldH_of_covered fork] using
    PairFeeObservationH.returnState (r.toH fork) success fork.rules_stateGas_none fork.rules_bal_none mem bound0 bound1


/-- Normalize this actual return as a full cursor state, retaining the guards
and complete physical fee state on that very node. -/
theorem PairFeeObservationH.returnCutData {root start : Exec.Deriv} {b post Wc : Devm}
    {M : Mem} {r1 r0 ρ : B256} {R : List B256} {K : List SFunc} {caller : SFunc}
    (r : PairFeeObservationH root start b Wc M r1 r0 ρ R (caller :: K))
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (mem : PtrMem 128 192 M) (bound0 : r0.toNat < 2 ^ 112)
    (bound1 : r1.toNat < 2 ^ 112) :
    ∃ N : Exec.Deriv, PtrMem 128 192 N.devm.memory ∧
      ∃ cut : CursorStateAt code cert r.occurrence.call.returned caller N.devm
        (feeOnWord (Bytes.toB256 (r.out.take 32)) :: R) N.devm.memory K,
        cut.node = N ∧
        feeBranchAcceptsH start.sevm (feeKLastWorldH start.sevm r.occurrence.call.returned.devm)
          (feeKLastWord start.sevm r.occurrence.call.returned.devm)
          (Bytes.toB256 (r.out.take 32)) r0 r1 ∧
        ∃ gas, N.devm = feeBranchPostH start.sevm
          (feeKLastWorldH start.sevm r.occurrence.call.returned.devm) R (feeReplyMemory M r.out)
          (feeKLastWord start.sevm r.occurrence.call.returned.devm)
          (Bytes.toB256 (r.out.take 32)) r0 r1 gas := by
  obtain ⟨N, next, span, env, outcome, placed, tree, conts, guards, gas, state⟩ :=
    r.returnState success stateGas bal mem bound0 bound1
  have machine := pairFeePost_machineH (sevm := start.sevm)
    (b := feeKLastWorldH start.sevm r.occurrence.call.returned.devm)
    (R := R) (M := feeReplyMemory M r.out)
    (K := feeKLastWord start.sevm r.occurrence.call.returned.devm)
    (w := Bytes.toB256 (r.out.take 32)) (r0 := r0) (r1 := r1) (G := gas)
    (feeReplyMemory_ptr r.out (feeRequestMemory_ptr mem))
  rw [← state] at machine
  exact ⟨N, machine.2, ⟨N, next, span,
    Blanc.Exec.Deriv.ParentPrefix.sevm_eq span.1,
    Blanc.Exec.Deriv.ParentPrefix.exn_eq span.1, placed, tree,
    ⟨N.devm.gasLeft, St.self machine.1 rfl⟩, conts⟩, rfl, guards, gas, state⟩

theorem PairFeeObservation.returnCutData {root start : Exec.Deriv} {b post : Devm}
    {M : Mem} {r1 r0 ρ : B256} {R : List B256} {K : List SFunc} {caller : SFunc}
    (r : PairFeeObservation root start b M r1 r0 ρ R (caller :: K))
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) (bound0 : r0.toNat < 2 ^ 112)
    (bound1 : r1.toNat < 2 ^ 112) :
    ∃ N : Exec.Deriv, PtrMem 128 192 N.devm.memory ∧
      ∃ cut : CursorStateAt code cert r.occurrence.call.returned caller N.devm
        (feeOnWord (Bytes.toB256 (r.out.take 32)) :: R) N.devm.memory K,
        cut.node = N ∧
        feeBranchAccepts start.sevm (feeKLastWorld start.sevm r.occurrence.call.returned.devm)
          (feeKLastWord start.sevm r.occurrence.call.returned.devm)
          (Bytes.toB256 (r.out.take 32)) r0 r1 ∧
        ∃ gas, N.devm = feeBranchPost start.sevm
          (feeKLastWorld start.sevm r.occurrence.call.returned.devm) R (feeReplyMemory M r.out)
          (feeKLastWord start.sevm r.occurrence.call.returned.devm)
          (Bytes.toB256 (r.out.take 32)) r0 r1 gas := by
  simpa only [PairFeeObservation.toH, feeBranchAcceptsH_of_covered fork, feeBranchPostH_of_covered fork,
    feeKLastWorldH_of_covered fork] using
    PairFeeObservationH.returnCutData (r.toH fork) success fork.rules_stateGas_none fork.rules_bal_none
      mem bound0 bound1

end Blanc.Lift.UniswapV2Pair
