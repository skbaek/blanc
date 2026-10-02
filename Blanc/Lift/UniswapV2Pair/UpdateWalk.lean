import Blanc.Lift.UniswapV2Pair.UpdateArithmetic
import Blanc.Lift.UniswapV2Pair.UpdateTailWalk
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

/-- Successful header bytes derive the actual current timestamp and oracle
prefix, preserving the SLOAD metadata and arbitrary cached reserves. -/
theorem update_header_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm (St b (r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      t_2377_c19 o) :
    ∃ G', SFunc.Run cert.prog sevm
      (St (afterSload sevm b 8)
        (updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time r0 ::
         updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time ::
         updateTimestampWord sevm.benvStat.time :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G')
      t_23c7_c20 o := by
  have h := run.cut
  unfold t_2377_c19 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_timestamp hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  have lastWord : reserveMask32 &&& (b.getStorVal sevm.currentTarget 8 / reserveDiv224) =
      reserveTimestampRead (b.getStorVal sevm.currentTarget 8) := B256.and_comm _ _
  change SFunc.RunCut cert.prog sevm []
    (St (afterSload sevm b 8)
      ((reserveMask32 &&& (b.getStorVal sevm.currentTarget 8 / reserveDiv224)) :: reserveMask32 ::
       updateTimestampWord sevm.benvStat.time :: r1 :: r0 :: b1 :: b0 :: tag :: R) M _) _ (.done o) at h
  rw [lastWord] at h
  clear * - h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  clear * - h
  rcases ric_branchTo (g := t_23c7_c20) (by decide) rfl h with
      ⟨guard, _, h⟩ | ⟨guard, g, h⟩
  · have elapsedNotZero : updateElapsedWord (b.getStorVal sevm.currentTarget 8)
        sevm.benvStat.time &&& reserveMask32 ≠ 0 := by
      intro elapsedZero
      have flag : updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time = 1 := by
        simp only [updateElapsedZeroWord, elapsedZero, B256.eqCheck, ite_true]
      change updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time = 0 at guard
      rw [flag] at guard
      exact (by decide : (1 : B256) ≠ 0) guard
    simp only [updateOraclePrefixWord, elapsedNotZero, ite_false]
    unfold t_23b3_c19 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
    exact ⟨_, h.uncut⟩
  · have elapsedZero := eq_zero_of_iszero_ne_zero guard
    change updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 = 0
      at elapsedZero
    have flag : updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time = 1 := by
      simp only [updateElapsedZeroWord, elapsedZero, B256.eqCheck, ite_true]
    change SFunc.RunCut cert.prog sevm []
      (St (afterSload sevm b 8)
        (B256.eqCheck (updateElapsedZeroWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time) 0 ::
         updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time ::
         updateTimestampWord sevm.benvStat.time :: r1 :: r0 :: b1 :: b0 :: tag :: R) M g)
      t_23c7_c20 (.done o) at h
    rw [flag] at h
    simp only [updateOraclePrefixWord, elapsedZero, ite_true]
    exact ⟨g, h.uncut⟩

/-- The actual cached reserve1 short circuit at entry20. -/
def updateOracleReserveFlagWord (prefixFlag reserve1 : B256) : B256 :=
  if prefixFlag = 0 then 0 else B256.eqCheck (B256.eqCheck (reserve1 &&& reserveMask112) 0) 0

/-- Entry20 retains a failed prefixFlag or checks the second cached reserve, with
its exact branch-dependent gas. -/
theorem update_oracle_reserve_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {prefixFlag dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (room : R.length ≤ 1014)
    (body : SFunc.RunExact cert.prog sevm
      (St b (updateOracleReserveFlagWord prefixFlag r1 :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      t_23e2_c21 o) :
    SFunc.RunExact cert.prog sevm
      (St b (prefixFlag :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M
        (G + 20 + if prefixFlag = 0 then 0 else 17)) t_23c7_c20 o := by
  by_cases prefixZero : prefixFlag = 0
  · simp only [prefixZero, updateOracleReserveFlagWord, ite_true, Nat.add_zero] at body ⊢
    unfold t_23c7_c20
    apply rx_dest
    apply rx_dup1 (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x23e2) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl
    exact body
  · simp only [prefixZero, updateOracleReserveFlagWord, ite_false] at body ⊢
    unfold t_23c7_c20 t_23ce_c20
    apply rx_dest
    apply rx_dup1 (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 0) (by simp only [B256.eqCheck, ite_eq_right prefixZero])
      (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x23e2) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    apply rx_pop
    apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
    apply rx_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
    apply rx_and rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero rfl (by simp only [List.length_cons]; omega)
    exact body

/-- Successful entry20 bytes recover their actual cached reserve1 test. -/
theorem update_oracle_reserve_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {prefixFlag dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm
      (St b (prefixFlag :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_23c7_c20 o) :
    ∃ G', SFunc.Run cert.prog sevm
      (St b (updateOracleReserveFlagWord prefixFlag r1 :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G')
      t_23e2_c21 o := by
  have h := run.cut
  unfold t_23c7_c20 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  clear * - h
  rcases ric_branchTo (g := t_23e2_c21) (by decide) rfl h with
      ⟨guard, _, h⟩ | ⟨guard, g, h⟩
  · have prefixNonzero : prefixFlag ≠ 0 := by
      intro prefixZero
      rw [prefixZero] at guard
      exact (by decide : B256.eqCheck (0 : B256) 0 ≠ 0) guard
    simp only [updateOracleReserveFlagWord, prefixNonzero, ite_false]
    unfold t_23ce_c20 at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
    exact ⟨_, h.uncut⟩
  · have prefixZero := eq_zero_of_iszero_ne_zero guard
    simp only [updateOracleReserveFlagWord, prefixZero, ite_true]
    rw [prefixZero] at h
    exact ⟨g, h.uncut⟩

/-- The actual final oracle flag chooses the accumulator path or the packed
reserve write path, preserving both header words and the cached reserves. -/
theorem update_oracle_route_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {flag dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (room : R.length ≤ 1015)
    (body : SFunc.RunExact cert.prog sevm
      (St b (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      (if flag = 0 then t_2492_c22 else t_23e8_c21) o) :
    SFunc.RunExact cert.prog sevm
      (St b (flag :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M (G + 17)) t_23e2_c21 o := by
  unfold t_23e2_c21
  apply rx_dest
  by_cases flagZero : flag = 0
  · subst flag
    simp only [ite_true] at body
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x2492) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) rfl
    exact body
  · simp only [flagZero, ite_false] at body
    apply rx_iszero (v := 0) (by simp only [B256.eqCheck, ite_eq_right flagZero])
      (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x2492) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    exact body

/-- Successful oracle routing derives the real branch from the computed flag. -/
theorem update_oracle_route_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {flag dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm
      (St b (flag :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_23e2_c21 o) :
    ∃ G', SFunc.Run cert.prog sevm
      (St b (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G')
      (if flag = 0 then t_2492_c22 else t_23e8_c21) o := by
  have h := run.cut
  unfold t_23e2_c21 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  clear * - h
  rcases ric_branchTo (g := t_2492_c22) (by decide) rfl h with
      ⟨guard, g, h⟩ | ⟨guard, g, h⟩
  · have flagNonzero : flag ≠ 0 := by
      intro flagZero
      rw [flagZero] at guard
      exact (by decide : B256.eqCheck (0 : B256) 0 ≠ 0) guard
    simp only [flagNonzero, ite_false]
    exact ⟨g, h.uncut⟩
  · have flagZero := eq_zero_of_iszero_ne_zero guard
    simp only [flagZero, ite_true]
    exact ⟨g, h.uncut⟩

/-- The bytecode's three short circuits are precisely modular elapsed time
and the two caller-cached masked reserves, independently of current storage. -/
theorem update_oracle_flag_source {raw timestamp reserve0 reserve1 : B256} :
    updateOracleReserveFlagWord (updateOraclePrefixWord raw timestamp reserve0) reserve1 =
      if updateElapsedWord raw timestamp &&& reserveMask32 ≠ 0 ∧
          reserve0 &&& reserveMask112 ≠ 0 ∧ reserve1 &&& reserveMask112 ≠ 0 then 1 else 0 := by
  by_cases elapsedZero : updateElapsedWord raw timestamp &&& reserveMask32 = 0
  · simp only [updateOracleReserveFlagWord, updateOraclePrefixWord, elapsedZero,
      ite_true, ne_eq, not_true_eq_false, false_and, ite_false]
  · by_cases reserve0Zero : reserve0 &&& reserveMask112 = 0
    · simp only [updateOracleReserveFlagWord, updateOraclePrefixWord, elapsedZero,
        reserve0Zero, B256.eqCheck, ite_false, ite_true,
        show (1 : B256) ≠ 0 from by decide, ne_eq, not_false_eq_true,
        not_true_eq_false, false_and, true_and]
    · by_cases reserve1Zero : reserve1 &&& reserveMask112 = 0
      · simp only [updateOracleReserveFlagWord, updateOraclePrefixWord, elapsedZero,
          reserve0Zero, reserve1Zero, B256.eqCheck, ite_false, ite_true,
          show (1 : B256) ≠ 0 from by decide, ne_eq, not_false_eq_true,
          not_true_eq_false, and_false]
      · simp only [updateOracleReserveFlagWord, updateOraclePrefixWord, elapsedZero,
          reserve0Zero, reserve1Zero, B256.eqCheck, ite_false, ite_true,
          show (1 : B256) ≠ 0 from by decide, ne_eq, not_false_eq_true,
          and_true]

/-- Actual masked UQ helper composition for one cached-reserve price. -/
def updatePriceWord (denominator numeratorReserve : B256) : B256 :=
  uqDivWord denominator (uqEncodeWord numeratorReserve &&& uqMask224)

/-- The first actual UQ calls reach the slot9 accumulator load, returning the
cached reserve1/reserve0 price after exactly149gas. -/
theorem update_price0_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (nonzero : r0 &&& reserveMask112 ≠ 0) (room : R.length ≤ 1008)
    (body : SFunc.RunExact cert.prog sevm
      (St b (updatePriceWord r0 r1 :: (dt &&& reserveMask32) :: dt :: ts ::
        r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_2425_c21 o) :
    SFunc.RunExact cert.prog sevm
      (St b (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M (G + 149)) t_23e8_c21 o := by
  unfold t_23e8_c21
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := dt &&& reserveMask32) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2425) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x23fb) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2a57) rfl (by simp only [List.length_cons]; omega)
  have encodeGas : G + 125 = (G + 91 + 26) + 8 := by omega
  rw [encodeGas]
  apply rx_callRet (g := t_2a57_c65) rfl (uq_encode_exact (G := G + 91)
    (by simp only [List.length_cons]; omega))
  unfold t_23fb_c21
  apply rx_dest
  apply rx_push (w := uqMask224) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := uqEncodeWord r1 &&& uqMask224) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2a7b) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x2a7b) (by decide) (by simp only [List.length_cons]; omega)
  have divGas : G + 72 = (G + 64) + 8 := by omega
  rw [divGas]
  apply rx_callRet (g := t_2a7b_c66) rfl (uq_div_exact (G := G) nonzero
    (by simp only [List.length_cons]; omega))
  exact body

/-- Successful actual UQ calls derive the denominator guard and the exact
cached price before any accumulator storage is read or written. -/
theorem update_price0_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm
      (St b (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_23e8_c21 o) :
    r0 &&& reserveMask112 ≠ 0 ∧ ∃ G', SFunc.Run cert.prog sevm
      (St b (updatePriceWord r0 r1 :: (dt &&& reserveMask32) :: dt :: ts ::
        r1 :: r0 :: b1 :: b0 :: tag :: R) M G') t_2425_c21 o := by
  have h := run.cut
  unfold t_23e8_c21 at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  change SFunc.RunCut cert.prog sevm []
    (St b ((reserveMask32 &&& dt) :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M _) _ (.done o) at h
  rw [B256.and_comm reserveMask32 dt] at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  clear * - h
  obtain ⟨_, h⟩ := ric_call (g := t_2a57_c65) rfl h
  rcases h with ⟨D, callee, h⟩ | ⟨D, callee, _⟩
  · obtain ⟨_, eq⟩ := uq_encode_inv callee
    cases eq
    unfold t_23fb_c21 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
    change SFunc.RunCut cert.prog sevm []
      (St b ((uqMask224 &&& uqEncodeWord r1) :: r0 :: 0x2425 :: (dt &&& reserveMask32) ::
        dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M _) _ (.done o) at h
    rw [B256.and_comm uqMask224 (uqEncodeWord r1)] at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
    clear * - h
    obtain ⟨_, h⟩ := ric_call (g := t_2a7b_c66) rfl h
    rcases h with ⟨D, callee, h⟩ | ⟨D, callee, _⟩
    · obtain ⟨nonzero, _, eq⟩ := uq_div_inv callee
      cases eq
      exact ⟨nonzero, _, h.uncut⟩
    · obtain ⟨_, _, eq⟩ := uq_div_inv callee
      cases eq
  · obtain ⟨_, eq⟩ := uq_encode_inv callee
    cases eq

/-- The actual word addition retains cumulative uint256 wrapping. -/
def updateAccumulatorWord (old price elapsed : B256) : B256 :=
  (price &&& uqMask224) * (elapsed &&& reserveMask32) + old

def updateAccumulatorPost (sevm : Sevm) (b : Devm) (key price elapsed : B256) : Devm :=
  afterSstore sevm (afterSload sevm b key) key
    (updateAccumulatorWord (b.getStorVal sevm.currentTarget key) price elapsed)

/-- Actual slot9 SLOAD/SSTORE followed by the second UQ price calls. The
individual SSTORE sentry and both actual mutable charges remain explicit. -/
theorem update_accumulator0_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G loadCost storeCost : Nat} {price dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (loadCharge : loadCost = sloadCost sevm b 9)
    (storeCharge : storeCost = sstoreCost sevm (afterSload sevm b 9) 9
      (updateAccumulatorWord (b.getStorVal sevm.currentTarget 9) price dt))
    (sentry : gCallStipend < G + 149 + storeCost)
    (nonzero : r1 &&& reserveMask112 ≠ 0) (room : R.length ≤ 1008)
    (body : SFunc.RunExact cert.prog sevm
      (St (updateAccumulatorPost sevm b 9 price dt)
        (updatePriceWord r1 r0 :: (dt &&& reserveMask32) :: dt :: ts ::
          r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_2465_c21 o) :
    SFunc.RunExact cert.prog sevm
      (St b (price :: (dt &&& reserveMask32) :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R)
        M (G + loadCost + storeCost + 191)) t_2425_c21 o := by
  unfold t_2425_c21
  apply rx_dest
  apply rx_push (w := 9) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  have loadGas : G + loadCost + storeCost + 184 = (G + storeCost + 184) + loadCost := by omega
  rw [loadGas]
  apply rx_sload_selC fork loadCharge (by simp only [List.length_cons]; omega)
  apply rx_push (w := uqMask224) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap1
  apply rx_swap3
  apply rx_and (v := price &&& uqMask224) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap1
  apply rx_swap3
  apply rx_mul rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := updateAccumulatorWord (b.getStorVal sevm.currentTarget 9) price dt)
    rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  have storeGas : G + storeCost + 149 = (G + 149) + storeCost := by omega
  rw [storeGas]
  apply rx_sstoreC fork storeCharge sentry static
  apply rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := dt) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2465) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x23fb) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2a57) rfl (by simp only [List.length_cons]; omega)
  have encodeGas : G + 125 = (G + 91 + 26) + 8 := by omega
  rw [encodeGas]
  apply rx_callRet (g := t_2a57_c65) rfl (uq_encode_exact (G := G + 91)
    (by simp only [List.length_cons]; omega))
  unfold t_23fb_c21_1
  apply rx_dest
  apply rx_push (w := uqMask224) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := uqEncodeWord r0 &&& uqMask224) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2a7b) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x2a7b) (by decide) (by simp only [List.length_cons]; omega)
  have divGas : G + 72 = (G + 64) + 8 := by omega
  rw [divGas]
  apply rx_callRet (g := t_2a7b_c66) rfl (uq_div_exact (G := G) nonzero
    (by simp only [List.length_cons]; omega))
  exact body

/-- Successful slot9 bytes derive non-static execution, the actual modular
accumulator write, and the second cached price from its real UQ calls. -/
theorem update_accumulator0_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {price dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm
      (St b (price :: (dt &&& reserveMask32) :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      t_2425_c21 o) :
    sevm.isStatic = false ∧ r1 &&& reserveMask112 ≠ 0 ∧ ∃ G', SFunc.Run cert.prog sevm
      (St (updateAccumulatorPost sevm b 9 price dt)
        (updatePriceWord r1 r0 :: (dt &&& reserveMask32) :: dt :: ts ::
          r1 :: r0 :: b1 :: b0 :: tag :: R) M G') t_2465_c21 o := by
  have h := run.cut
  unfold t_2425_c21 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  change SFunc.RunCut cert.prog sevm []
    (St (afterSload sevm b 9)
      ((uqMask224 &&& price) :: 9 :: b.getStorVal sevm.currentTarget 9 ::
        (dt &&& reserveMask32) :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M _) _ (.done o) at h
  rw [B256.and_comm uqMask224 price] at h
  clear * - h fork
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mul hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  change SFunc.RunCut cert.prog sevm []
    (St (updateAccumulatorPost sevm b 9 price dt)
      (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M _) _ (.done o) at h
  clear * - h nonstatic
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  clear * - h nonstatic
  obtain ⟨_, h⟩ := ric_call (g := t_2a57_c65) rfl h
  rcases h with ⟨D, callee, h⟩ | ⟨D, callee, _⟩
  · obtain ⟨_, eq⟩ := uq_encode_inv callee
    cases eq
    unfold t_23fb_c21_1 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
    change SFunc.RunCut cert.prog sevm []
      (St (updateAccumulatorPost sevm b 9 price dt)
        ((uqMask224 &&& uqEncodeWord r0) :: r1 :: 0x2465 :: (dt &&& reserveMask32) ::
          dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M _) _ (.done o) at h
    rw [B256.and_comm uqMask224 (uqEncodeWord r0)] at h
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
    clear * - h nonstatic
    obtain ⟨_, h⟩ := ric_call (g := t_2a7b_c66) rfl h
    rcases h with ⟨D, callee, h⟩ | ⟨D, callee, _⟩
    · obtain ⟨nonzero, _, eq⟩ := uq_div_inv callee
      cases eq
      exact ⟨nonstatic, nonzero, _, h.uncut⟩
    · obtain ⟨_, _, eq⟩ := uq_div_inv callee
      cases eq
  · obtain ⟨_, eq⟩ := uq_encode_inv callee
    cases eq

/-- The actual second accumulator reaches the sole packed-reserve write path,
with its own selected storage charges and SSTORE sentry. -/
theorem update_accumulator1_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G loadCost storeCost : Nat} {price dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (loadCharge : loadCost = sloadCost sevm b 10)
    (storeCharge : storeCost = sstoreCost sevm (afterSload sevm b 10) 10
      (updateAccumulatorWord (b.getStorVal sevm.currentTarget 10) price dt))
    (sentry : gCallStipend < G + storeCost) (room : R.length ≤ 1012)
    (body : SFunc.RunExact cert.prog sevm
      (St (updateAccumulatorPost sevm b 10 price dt)
        (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_2492_c22 o) :
    SFunc.RunExact cert.prog sevm
      (St b (price :: (dt &&& reserveMask32) :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R)
        M (G + loadCost + storeCost + 42)) t_2465_c21 o := by
  unfold t_2465_c21
  apply rx_dest
  apply rx_push (w := 10) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  have loadGas : G + loadCost + storeCost + 35 = (G + storeCost + 35) + loadCost := by omega
  rw [loadGas]
  apply rx_sload_selC fork loadCharge (by simp only [List.length_cons]; omega)
  apply rx_push (w := uqMask224) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap1
  apply rx_swap3
  apply rx_and (v := price &&& uqMask224) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap1
  apply rx_swap3
  apply rx_mul rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := updateAccumulatorWord (b.getStorVal sevm.currentTarget 10) price dt)
    rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sstoreC fork storeCharge sentry static
  exact body

/-- The actual slot10 inverse recovers its modular accumulator update and
non-static frame before the packed-reserve write. -/
theorem update_accumulator1_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {price dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm
      (St b (price :: (dt &&& reserveMask32) :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G)
      t_2465_c21 o) :
    sevm.isStatic = false ∧ ∃ G', SFunc.Run cert.prog sevm
      (St (updateAccumulatorPost sevm b 10 price dt)
        (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G') t_2492_c22 o := by
  have h := run.cut
  unfold t_2465_c21 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  change SFunc.RunCut cert.prog sevm []
    (St (afterSload sevm b 10)
      ((uqMask224 &&& price) :: 10 :: b.getStorVal sevm.currentTarget 10 ::
        (dt &&& reserveMask32) :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M _) _ (.done o) at h
  rw [B256.and_comm uqMask224 price] at h
  clear * - h fork
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mul hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨g, rfl⟩ := ri_sstore fork hd
  exact ⟨nonstatic, g, h.uncut⟩


/-- Actual oracle condition uses caller-cached reserves and current slot8 time. -/
abbrev updateOracleActive (sevm : Sevm) (b : Devm) (old0 old1 : B256) : Prop :=
  updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 ≠ 0 ∧
    old0 &&& reserveMask112 ≠ 0 ∧ old1 &&& reserveMask112 ≠ 0

/-- Actual world at the sole packed reserve write, including conditional oracle metadata. -/
def updateOracleWorld (sevm : Sevm) (b : Devm) (old0 old1 : B256) : Devm :=
  let elapsed := updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let start := afterSload sevm b 8
  if updateOracleActive sevm b old0 old1 then
    updateAccumulatorPost sevm
      (updateAccumulatorPost sevm start 9 (updatePriceWord old0 old1) elapsed)
      10 (updatePriceWord old1 old0) elapsed
  else start

def updateFinalPackedWord (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) : B256 :=
  updatePackedWord ((updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 8)
    balance0 balance1 (updateTimestampWord sevm.benvStat.time)

def updateWorld (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) : Devm :=
  updateSyncPost sevm (updatePackedPost sevm (updateOracleWorld sevm b old0 old1)
    balance0 balance1 (updateTimestampWord sevm.benvStat.time))
    (updateFinalPackedWord sevm b old0 old1 balance0 balance1)

def updateMemory (sevm : Sevm) (b : Devm) (M : Mem) (old0 old1 balance0 balance1 : B256) : Mem :=
  updateSyncMemory M (updateFinalPackedWord sevm b old0 old1 balance0 balance1)

/-- One actual shared update inverse, deriving acceptance and mutability from
successful bytes, with the complete metadata, log, memory and caller tail. -/
theorem update_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {old0 old1 balance0 balance1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 n M)
    (run : SFunc.Run cert.prog sevm
      (St b (old1 :: old0 :: balance1 :: balance0 :: tag :: R) M G) t_22e0_c60 o) :
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
      ∃ G', o = .returned (St (updateWorld sevm b old0 old1 balance0 balance1)
        R (updateMemory sevm b M old0 old1 balance0 balance1) G') := by
  obtain ⟨bound0, bound1, _, h⟩ := update_guards_inv run
  obtain ⟨_, h⟩ := update_header_inv fork h
  obtain ⟨_, h⟩ := update_oracle_reserve_inv h
  obtain ⟨_, h⟩ := update_oracle_route_inv h
  rw [update_oracle_flag_source] at h
  clear * - h fork mem bound0 bound1
  by_cases active : updateOracleActive sevm b old0 old1
  · change updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 ≠ 0 ∧
      old0 &&& reserveMask112 ≠ 0 ∧ old1 &&& reserveMask112 ≠ 0 at active
    rw [ite_eq_left active, ite_eq_right (by decide : (1 : B256) ≠ 0)] at h
    obtain ⟨_, _, h⟩ := update_price0_inv h
    obtain ⟨_, _, _, h⟩ := update_accumulator0_inv fork h
    obtain ⟨_, _, h⟩ := update_accumulator1_inv fork h
    obtain ⟨nonstatic, _, h⟩ := update_packed_store_inv fork h
    obtain ⟨g, eq⟩ := update_sync_event_inv mem h
    refine ⟨bound0, bound1, nonstatic, g, ?_⟩
    have oracleEq : updateOracleWorld sevm b old0 old1 =
        updateAccumulatorPost sevm
          (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
            (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time))
          10 (updatePriceWord old1 old0)
            (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time) := by
      unfold updateOracleWorld
      exact ite_eq_left active
    change o = .returned (St (updateSyncPost sevm
      (updatePackedPost sevm (updateOracleWorld sevm b old0 old1) balance0 balance1
        (updateTimestampWord sevm.benvStat.time))
      (updatePackedWord ((updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 8)
        balance0 balance1 (updateTimestampWord sevm.benvStat.time))) R
      (updateSyncMemory M
        (updatePackedWord ((updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 8)
          balance0 balance1 (updateTimestampWord sevm.benvStat.time))) g)
    rw [oracleEq]
    exact eq
  · change ¬ (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 ≠ 0 ∧
      old0 &&& reserveMask112 ≠ 0 ∧ old1 &&& reserveMask112 ≠ 0) at active
    simp only [active, ite_false, ite_true] at h
    obtain ⟨nonstatic, _, h⟩ := update_packed_store_inv fork h
    obtain ⟨g, eq⟩ := update_sync_event_inv mem h
    refine ⟨bound0, bound1, nonstatic, g, ?_⟩
    simpa only [updateWorld, updateMemory, updateFinalPackedWord, updateOracleWorld,
      updateOracleActive, active, ite_false] using eq


/-- Exact actual Sync suffix gas, including its two symbolic memory charges. -/
def updateSyncGas (n : Nat) : Nat := updateSyncStoreCost0 n + updateSyncStoreCost1 n + 1371

/-- One actual shared update forward theorem. Charges name the executed
primitives; conditional oracle charges and all three SSTORE sentries remain explicit. -/
theorem update_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n headerLoad load9 store9 load10 store10 load8 store8 : Nat}
    {old0 old1 balance0 balance1 tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 n M)
    (static : sevm.isStatic = false) (bound0 : balance0.toNat < 2 ^ 112)
    (bound1 : balance1.toNat < 2 ^ 112) (room : R.length ≤ 1008)
    (headerCharge : headerLoad = sloadCost sevm b 8)
    (packedLoadCharge : load8 = sloadCost sevm (updateOracleWorld sevm b old0 old1) 8)
    (packedStoreCharge : store8 = sstoreCost sevm
      (afterSload sevm (updateOracleWorld sevm b old0 old1) 8) 8
      (updateFinalPackedWord sevm b old0 old1 balance0 balance1))
    (oracleCharges : updateOracleActive sevm b old0 old1 →
      load9 = sloadCost sevm (afterSload sevm b 8) 9 ∧
      store9 = sstoreCost sevm (afterSload sevm (afterSload sevm b 8) 9) 9
        (updateAccumulatorWord ((afterSload sevm b 8).getStorVal sevm.currentTarget 9)
          (updatePriceWord old0 old1)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) ∧
      load10 = sloadCost sevm
        (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10 ∧
      store10 = sstoreCost sevm (afterSload sevm
        (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10) 10
        (updateAccumulatorWord
          ((updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
            (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)).getStorVal
            sevm.currentTarget 10) (updatePriceWord old1 old0)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)))
    (sentry8 : gCallStipend < G + updateSyncGas n + store8)
    (sentry10 : updateOracleActive sevm b old0 old1 →
      gCallStipend < G + updateSyncGas n + load8 + store8 + 110 + store10)
    (sentry9 : updateOracleActive sevm b old0 old1 →
      gCallStipend < G + updateSyncGas n + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) :
    SFunc.RunExact cert.prog sevm
      (St b (old1 :: old0 :: balance1 :: balance0 :: tag :: R) M
        (G + updateSyncGas n + load8 + store8 + 110 +
          (if updateOracleActive sevm b old0 old1 then load9 + store9 + load10 + store10 + 382 else 0) +
          17 + 20 +
          (if updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0 = 0
            then 0 else 17) + headerLoad + 75 +
          (if updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 = 0
            then 0 else 17) + 60)) t_22e0_c60
      (.returned (St (updateWorld sevm b old0 old1 balance0 balance1) R
        (updateMemory sevm b M old0 old1 balance0 balance1) G)) := by
  let dt := updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let ts := updateTimestampWord sevm.benvStat.time
  let prefixFlag := updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0
  let flag := updateOracleReserveFlagWord prefixFlag old1
  let tailGas := G + updateSyncGas n + load8 + store8 + 110
  let oracleGas := if updateOracleActive sevm b old0 old1 then load9 + store9 + load10 + store10 + 382 else 0
  let result := Outcome.returned (St (updateWorld sevm b old0 old1 balance0 balance1) R
    (updateMemory sevm b M old0 old1 balance0 balance1) G)
  have eventRun : SFunc.RunExact cert.prog sevm
      (St (updatePackedPost sevm (updateOracleWorld sevm b old0 old1) balance0 balance1 ts)
        (reserveDiv112 :: reserveMask112 :: updateFinalPackedWord sevm b old0 old1 balance0 balance1 ::
          dt :: ts :: old1 :: old0 :: balance1 :: balance0 :: tag :: R) M (G + updateSyncGas n))
      updateSyncTree result := by
    have eventGas : G + updateSyncGas n = G + updateSyncStoreCost0 n + updateSyncStoreCost1 n + 1371 := by
      unfold updateSyncGas
      omega
    rw [eventGas]
    exact update_sync_event_exact static mem (by omega)
  have packedRun := update_packed_store_exact fork static packedLoadCharge packedStoreCharge sentry8
    (by omega : R.length ≤ 1010) eventRun
  have packedGas : G + updateSyncGas n + load8 + store8 + 110 = tailGas := rfl
  change SFunc.RunExact cert.prog sevm
    (St (updateOracleWorld sevm b old0 old1) (dt :: ts :: old1 :: old0 :: balance1 :: balance0 :: tag :: R)
      M ((G + updateSyncGas n) + load8 + store8 + 110)) t_2492_c22 result at packedRun
  rw [packedGas] at packedRun
  have oracleRun : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8) (dt :: ts :: old1 :: old0 :: balance1 :: balance0 :: tag :: R)
        M (tailGas + oracleGas)) (if flag = 0 then t_2492_c22 else t_23e8_c21) result := by
    have flagSource : flag = if updateOracleActive sevm b old0 old1 then 1 else 0 :=
      update_oracle_flag_source
    by_cases active : updateOracleActive sevm b old0 old1
    · obtain ⟨charge9, write9, charge10, write10⟩ := oracleCharges active
      rw [flagSource, ite_eq_left active, ite_eq_right (by decide : (1 : B256) ≠ 0)]
      have oracleEq : updateOracleWorld sevm b old0 old1 =
          updateAccumulatorPost sevm
            (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1) dt)
            10 (updatePriceWord old1 old0) dt := by
        unfold updateOracleWorld
        exact ite_eq_left active
      rw [oracleEq] at packedRun
      have h10 := update_accumulator1_exact fork static charge10 write10 (sentry10 active)
        (by omega : R.length ≤ 1012) packedRun
      have h9 := update_accumulator0_exact fork static charge9 write9 (sentry9 active)
        active.2.2 room h10
      have h0 := update_price0_exact
        active.2.1 room h9
      have gas : tailGas + oracleGas = tailGas + load10 + store10 + 42 + load9 + store9 + 191 + 149 := by
        dsimp only [oracleGas]
        rw [ite_eq_left active]
        omega
      rw [gas]
      exact h0
    · rw [flagSource, ite_eq_right active, ite_eq_left (rfl : (0 : B256) = 0)]
      have oracleEq : updateOracleWorld sevm b old0 old1 = afterSload sevm b 8 := by
        unfold updateOracleWorld
        exact ite_eq_right active
      dsimp only [oracleGas]
      rw [ite_eq_right active, Nat.add_zero]
      rw [oracleEq] at packedRun
      exact packedRun
  have routeRun := update_oracle_route_exact (by omega : R.length ≤ 1015) oracleRun
  have reserveRun := update_oracle_reserve_exact (by omega : R.length ≤ 1014) routeRun
  have headerRun := update_header_exact fork headerCharge (by omega : R.length ≤ 1014) reserveRun
  have guardsRun := update_guards_exact bound0 bound1 (by omega : R.length ≤ 1016) headerRun
  exact guardsRun

end Blanc.Lift.UniswapV2Pair
