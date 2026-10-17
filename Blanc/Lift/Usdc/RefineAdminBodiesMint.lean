import Blanc.Lift.Usdc.RefineAdminCallees

/-!
# The admin calls' bodies, minters and blacklisting (U6f)

As `RefineAdminBodies.lean`, for `removeMinter`, `configureMinter`, `unBlacklist`, `blacklist`,
`mint` and `burn`.
-/

namespace Blanc.Lift.Usdc.Impl

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

/-- `removeMinter`'s body (entry 65): its guards and its storage effect. -/
theorem removeMinter_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_18bb_c65 (.returned D)) :
    ∃ b' M' G', D = St b' ((Bytes.toB256 [1]) :: S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [8])) ≠ 0 ∧
      b'.getStor sevm.currentTarget = ((b.getStor sevm.currentTarget).set (mapSlot (x0 &&& ff20) (Bytes.toB256 [12])) (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0] &&& (b.getStor sevm.currentTarget).get (mapSlot (x0 &&& ff20) (Bytes.toB256 [12])))).set (mapSlot (x0 &&& ff20) (Bytes.toB256 [13])) (Bytes.toB256 [0]) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_18bb_c65 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_eq s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_192e_c65 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch2] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log2_post s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, trivial⟩

/-- `configureMinter`'s body (entry 56): its guards and its storage effect. -/
theorem configureMinter_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 x1 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: x1 :: t :: S) M G) t_26ef_c56 (.returned D)) :
    ∃ b' M' G', D = St b' ((Bytes.toB256 [1]) :: S) M' G' ∧
       (Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1]) / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =? 0 ≠ 0 ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [8])) ≠ 0 ∧
      b'.getStor sevm.currentTarget = ((b.getStor sevm.currentTarget).set (mapSlot (x1 &&& ff20) (Bytes.toB256 [12])) (Bytes.toB256 [1] ||| Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0] &&& (b.getStor sevm.currentTarget).get (mapSlot (x1 &&& ff20) (Bytes.toB256 [12])))).set (mapSlot (x1 &&& ff20) (Bytes.toB256 [13])) x0 := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_26ef_c56 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_div s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_277c_c56 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_eq s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_27ec_c56 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch2] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log2_post s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, h2, trivial⟩

/-- `unBlacklist`'s body (entry 67): its guards and its storage effect. -/
theorem unBlacklist_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_137a_c67 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [2])) ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (mapSlot (x0 &&& ff20) (Bytes.toB256 [9])) (lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& x0) (Bytes.toB256 [9]))) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_137a_c67 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_eq s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_13ea_c67 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [10, 96, 104, 109]) (g := t_3f5f_c104) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := unBlacklist_ret hfork callee
  unfold t_13f3_c67 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log2_post s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, trivial⟩

/-- `blacklist`'s body (entry 17): its guards and its storage effect. -/
theorem blacklist_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_3d50_c17 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [2])) ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (mapSlot (x0 &&& ff20) (Bytes.toB256 [9])) (Bytes.toB256 [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ||| (b.getStor sevm.currentTarget).get (mapSlot (x0 &&& ff20) (Bytes.toB256 [9]))) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_3d50_c17 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_eq s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_3dc0_c17 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [10, 86, 96, 109]) (g := t_4224_c86) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := blacklist_ret hfork callee
  unfold t_3dc9_c17 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log2_post s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, trivial⟩

/-- `mint`'s body (entry 53): its guards and its storage effect. -/
theorem mint_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 x1 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: x1 :: t :: S) M G) t_1ec5_c53 (.returned D)) :
    ∃ b' M' G', D = St b' ((Bytes.toB256 [1]) :: S) M' G' ∧
       (Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1]) / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =? 0 ≠ 0 ∧
      Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [12])) ≠ 0 ∧
       (Bytes.toB256 [1] =? (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
       (Bytes.toB256 [1] =? (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& x1) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
       x1 &&& ff20 ≠ 0 ∧
      x0 >? Bytes.toB256 [0] ≠ 0 ∧
      (x0 >? (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [13]))) =? 0 ≠ 0 ∧
       (x0 + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11])) <? (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) = 0 ∧
       (x0 + (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (x0 + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& x1) (Bytes.toB256 [9])))) <? (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (x0 + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& x1) (Bytes.toB256 [9]))) = 0 ∧
       (x0 + (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (x0 + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& x1) (Bytes.toB256 [9])))) >? lo255 = 0 ∧
       Bytes.toB256 [1] =? ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (x0 + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& x1) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat = 0 ∧
      x0 >? (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [13])) = 0 ∧
      b'.getStor sevm.currentTarget = (((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (x0 + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).set (mapSlot (x1 &&& ff20) (Bytes.toB256 [9])) (x0 + (lo255 &&& ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) (x0 + (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]))).get (mapSlot (ff20 &&& x1) (Bytes.toB256 [9]))))).set (mapSlot sevm.caller.toB256 (Bytes.toB256 [13])) ((b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [13])) - x0) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_1ec5_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_div s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_1f52_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_1fba_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [83]) (g := t_3f6a_c83) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := isBlacklisted_ret hfork callee
  unfold t_1fc4_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h3, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_201a_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [83]) (g := t_3f6a_c83) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := isBlacklisted_ret hfork callee
  unfold t_2024_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h4, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_207a_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h5, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_20e6_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_gt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h6, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_213f_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_gt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h7, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_21a8_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [7, 98]) (g := t_43b5_c98) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, rfl, hadd3⟩ := add_ret callee
  unfold t_21b5_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [96]) (g := t_41da_c96) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := balanceOf_ret hfork callee
  unfold t_21c9_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [7, 98]) (g := t_43b5_c98) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, rfl, hadd5⟩ := add_ret callee
  unfold t_21cf_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [83, 99]) (g := t_4430_c99) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl, hcap6, hfree6⟩ := setBalance_ret hfork callee
  unfold t_21d4_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [100]) (g := t_4163_c100) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, rfl, hsub7⟩ := sub_ret callee
  unfold t_21de_c53 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log3 s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log3 s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 5) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 4) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, h2, h3, h4, h5, h6, h7, hadd3, hadd5, hcap6, hfree6, hsub7, trivial⟩

/-- `burn`'s body (entry 54): its guards and its storage effect. -/
theorem burn_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_2296_c54 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       (Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1]) / Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) =? 0 ≠ 0 ∧
      Bytes.toB256 [255] &&& (b.getStor sevm.currentTarget).get (mapSlot sevm.caller.toB256 (Bytes.toB256 [12])) ≠ 0 ∧
       (Bytes.toB256 [1] =? (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat) =? 0 ≠ 0 ∧
      x0 >? Bytes.toB256 [0] ≠ 0 ∧
       ((lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) <? x0) =? 0 ≠ 0 ∧
       ((lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) - x0) >? lo255 = 0 ∧
       Bytes.toB256 [1] =? ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) ((b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) - x0)).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat = 0 ∧
      x0 >? (b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) = 0 ∧
       x0 >? (lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) = 0 ∧
      b'.getStor sevm.currentTarget = ((b.getStor sevm.currentTarget).set (Bytes.toB256 [11]) ((b.getStor sevm.currentTarget).get (Bytes.toB256 [11]) - x0)).set (mapSlot (sevm.caller.toB256 &&& ff20) (Bytes.toB256 [9])) ((lo255 &&& (b.getStor sevm.currentTarget).get (mapSlot (ff20 &&& sevm.caller.toB256) (Bytes.toB256 [9]))) - x0) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_2296_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_div s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_2320_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_keccak s; clear s
  rw [keccak_scratch] at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_2388_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [83]) (g := t_3f6a_c83) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := isBlacklisted_ret hfork callee
  unfold t_2392_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h3, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_23e8_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [96]) (g := t_41da_c96) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := balanceOf_ret hfork callee
  unfold t_23f3_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_gt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h4, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_244e_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h5, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_24a7_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [100]) (g := t_4163_c100) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, rfl, hsub3⟩ := sub_ret callee
  unfold t_24b4_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [100]) (g := t_4163_c100) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, rfl, hsub4⟩ := sub_ret callee
  unfold t_21cf_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [83, 99]) (g := t_4430_c99) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl, hcap5, hfree5⟩ := setBalance_ret hfork callee
  unfold t_24c5_c54 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log2_post s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_caller s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log3 s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, h2, h3, h4, h5, hcap5, hfree5, hsub3, hsub4, trivial⟩

end Blanc.Lift.Usdc.Impl
