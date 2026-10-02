import Blanc.Lift.UniswapV2Pair.UpdateArithmetic
import Blanc.Lift.UniswapV2Pair.Cert
import Blanc.Lift.PackedWord
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkOps

/-! One certified shared `_update` walk, retaining actual current metadata and
caller-cached reserves separately. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

private theorem update_overflow_noOk : t_2311_c19.noOk = true := by decide

/-- Both actual uint112 guards pass before the current timestamp load. -/
theorem update_guards_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {r0 r1 b0 b1 tag : B256} {o : Outcome}
    (bound0 : b0.toNat < 2 ^ 112) (bound1 : b1.toNat < 2 ^ 112)
    (room : R.length ≤ 1016)
    (body : SFunc.RunExact cert.prog sevm (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      t_2377_c19 o) :
    SFunc.RunExact cert.prog sevm (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M (G + 60))
      t_22e0_c60 o := by
  have gt0 : B256.gtCheck b0 reserveMask112 = 0 := by
    rw [B256.gtCheck, ite_eq_right]
    change ¬ reserveMask112 < b0
    rw [B256.lt_iff_toNat_lt_toNat]
    change ¬ (2 ^ 112 - 1 < b0.toNat)
    omega
  have gt1 : B256.gtCheck b1 reserveMask112 = 0 := by
    rw [B256.gtCheck, ite_eq_right]
    change ¬ reserveMask112 < b1
    rw [B256.lt_iff_toNat_lt_toNat]
    change ¬ (2 ^ 112 - 1 < b1.toNat)
    omega
  unfold t_22e0_c60 t_22f9_c60 t_230c_c19
  apply rx_dest
  apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := b0) rfl (by simp only [List.length_cons]; omega)
  apply rx_gt gt0 (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_push (w := 0x230c) rfl (by simp only [List.length_cons]; omega)
  apply rx_branchTo_zero
  apply rx_pop
  apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := b1) rfl (by simp only [List.length_cons]; omega)
  apply rx_gt gt1 (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dest
  apply rx_push (w := 0x2377) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  exact body

private theorem update_guard19_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {fit r0 r1 b0 b1 tag : B256} {o : Outcome}
    (run : SFunc.RunCut cert.prog sevm []
      (St b (fit :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_230c_c19 (.done o)) :
    fit ≠ 0 ∧ ∃ G', SFunc.Run cert.prog sevm
      (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M G') t_2377_c19 o := by
  unfold t_230c_c19 at run
  obtain ⟨_, h⟩ := ric_dest run
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, h⟩ | ⟨guard, g, h⟩
  · exact False.elim (h.false_of_noOk update_overflow_noOk)
  · exact ⟨guard, g, h.uncut⟩

/-- Successful update bytes derive both balance bounds at the real acceptance
control, without assuming source acceptance or an endpoint. -/
theorem update_guards_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {r0 r1 b0 b1 tag : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      t_22e0_c60 o) :
    b0.toNat < 2 ^ 112 ∧ b1.toNat < 2 ^ 112 ∧
      ∃ G', SFunc.Run cert.prog sevm (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M G')
        t_2377_c19 o := by
  have h := run.cut
  unfold t_22e0_c60 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_gt hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo (g := t_230c_c19) (by decide) rfl h with
      ⟨gt0, _, h⟩ | ⟨gtNonzero, _, h⟩
  · have bound0 := toNat_le_of_gtCheck_eq_zero gt0
    change b0.toNat ≤ 2 ^ 112 - 1 at bound0
    unfold t_22f9_c60 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_gt hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
    obtain ⟨guard, g, h⟩ := update_guard19_inv h
    have bound1 := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero guard)
    change b1.toNat ≤ 2 ^ 112 - 1 at bound1
    exact ⟨by omega, by omega, g, h⟩
  · obtain ⟨guard, _, _⟩ := update_guard19_inv h
    exact False.elim (gtNonzero (eq_zero_of_iszero_ne_zero guard))

/-- Mandated uint112 statement control at the actual acceptance guard. -/
theorem update_uint112_overflow_control {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {r0 r1 b1 tag : B256} {o : Outcome} :
    ¬ SFunc.Run cert.prog sevm
      (St b (r1 :: r0 :: b1 :: (2 ^ 112).toB256 :: tag :: R) M G) t_22e0_c60 o := by
  intro run
  have bound := (update_guards_inv run).1
  rw [B256.toNat_toB256_of_lt (by decide : 2 ^ 112 < 2 ^ 256)] at bound
  exact (Nat.lt_irrefl _) bound

/-- Actual elapsed-time zero flag before the oracle short circuit. -/
def updateElapsedZeroWord (raw timestamp : B256) : B256 :=
  B256.eqCheck (updateElapsedWord raw timestamp &&& reserveMask32) 0

/-- The first two actual oracle tests, before the cached reserve1 test. -/
def updateOraclePrefixWord (raw timestamp reserve0 : B256) : B256 :=
  if updateElapsedWord raw timestamp &&& reserveMask32 = 0 then 0
  else B256.eqCheck (B256.eqCheck (reserve0 &&& reserveMask112) 0) 0

private theorem update_header_prefix_exact {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b 8)
    (room : R.length ≤ 1014)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8)
        (0x23c7 :: updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time ::
         B256.eqCheck (updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time) 0 ::
         updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time ::
         updateTimestampWord sevm.benvStat.time :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      (.branchTo t_23b3_c19 20) o) :
    SFunc.RunExact cert.prog sevm (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M (G + c + 65))
      t_2377_c19 o := by
  unfold t_2377_c19
  apply rx_dest
  apply rx_push (w := 8) rfl (by simp only [List.length_cons]; omega)
  have gas : G + c + 61 = (G + 61) + c := by omega
  rw [gas]
  apply rx_sload_selC fork cost (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_timestamp (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := updateTimestampWord sevm.benvStat.time) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := reserveDiv224) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_div rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := reserveTimestampRead (b.getStorVal sevm.currentTarget 8))
    (B256.and_comm _ _) (by simp only [List.length_cons]; omega)
  apply rx_dup (w := updateTimestampWord sevm.benvStat.time) rfl (by simp only [List.length_cons]; omega)
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_dup (w := updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)
    rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_push (w := 0x23c7) rfl (by simp only [List.length_cons]; omega)
  exact body

/-- The actual current-slot SLOAD and TIMESTAMP header reaches entry20 with
its exact modular elapsed word and first cached-reserve test. -/
theorem update_header_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G c : Nat} {r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b 8)
    (room : R.length ≤ 1014)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8)
        (updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time r0 ::
         updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time ::
         updateTimestampWord sevm.benvStat.time :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      t_23c7_c20 o) :
    SFunc.RunExact cert.prog sevm
      (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M
        (G + c + 75 + if updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time
          &&& reserveMask32 = 0 then 0 else 17)) t_2377_c19 o := by
  by_cases elapsedZero : updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time
      &&& reserveMask32 = 0
  · simp only [elapsedZero, ite_true, Nat.add_zero, updateOraclePrefixWord] at body ⊢
    have gas : G + c + 75 = (G + 10) + c + 65 := by omega
    rw [gas]
    apply update_header_prefix_exact fork cost room
    have flag : updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time = 1 := by
      simp only [updateElapsedZeroWord, elapsedZero, B256.eqCheck, ite_true]
    rw [flag]
    apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl
    exact body
  · simp only [elapsedZero, ite_false, updateOraclePrefixWord] at body ⊢
    have gas : G + c + 75 + 17 = (G + 27) + c + 65 := by omega
    rw [gas]
    apply update_header_prefix_exact fork cost room
    have flag : updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time = 0 := by
      simp only [updateElapsedZeroWord, B256.eqCheck, ite_eq_right elapsedZero]
    rw [flag]
    apply rx_branchTo_zero
    unfold t_23b3_c19
    apply rx_pop
    apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
    apply rx_and rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero rfl (by simp only [List.length_cons]; omega)
    exact body

end Blanc.Lift.UniswapV2Pair
