import Blanc.Lift.Usdc.RefineAdminCallees

/-!
# The admin calls' bodies, roles and pausing (U6f)

For each call, a returning run of its body tree passed its guards (the hypotheses as the code
compares them) and leaves the proxy's storage at the stated writes.
-/

namespace Blanc.Lift.Usdc.Impl

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

/-- `pause`'s body (entry 42): its guards and its storage effect. -/
theorem pause_body (hfork : CoveredFork sevm.benvStat.fork) {t  : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (t :: S) M G) t_2b3c_c42 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [1]) (Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ||| Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_2b3c_c42 at run
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
  unfold t_2bac_c42 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log1 s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, trivial⟩

/-- `unpause`'s body (entry 59): its guards and its storage effect. -/
theorem unpause_body (hfork : CoveredFork sevm.benvStat.fork) {t  : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (t :: S) M G) t_1e02_c59 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [1]) (Bytes.toB256 [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 0, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255] &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_1e02_c59 at run
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
  unfold t_1e72_c59 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log1 s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, trivial⟩

/-- `updatePauser`'s body (entry 51): its guards and its storage effect. -/
theorem updatePauser_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_28b9_c51 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       x0 &&& ff20 ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [1]) (ff20 &&& x0 ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [1])) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_28b9_c51 at run
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
  unfold t_293f_c51 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_29ab_c51 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
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
  exact ⟨h1, h2, trivial⟩

/-- `updateMasterMinter`'s body (entry 31): its guards and its storage effect. -/
theorem updateMasterMinter_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_3109_c31 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       x0 &&& ff20 ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [8]) (ff20 &&& x0 ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [8])) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_3109_c31 at run
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
  unfold t_318f_c31 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_31fb_c31 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
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
  exact ⟨h1, h2, trivial⟩

/-- `updateBlacklister`'s body (entry 33): its guards and its storage effect. -/
theorem updateBlacklister_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_329b_c33 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       x0 &&& ff20 ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [2]) (ff20 &&& x0 ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [2])) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_329b_c33 at run
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
  unfold t_3321_c33 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_338d_c33 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
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
  exact ⟨h1, h2, trivial⟩

/-- `updateRescuer`'s body (entry 69): its guards and its storage effect. -/
theorem updateRescuer_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_16f2_c69 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       x0 &&& ff20 ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [14]) (x0 &&& ff20 ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [14])) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_16f2_c69 at run
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
  unfold t_1778_c69 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_17e4_c69 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
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
  exact ⟨h1, h2, trivial⟩

/-- `transferOwnership`'s body (entry 16): its guards and its storage effect. -/
theorem transferOwnership_body (hfork : CoveredFork sevm.benvStat.fork) {t x0 : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x0 :: t :: S) M G) t_3bfd_c16 (.returned D)) :
    ∃ b' M' G', D = St b' (S) M' G' ∧
       sevm.caller.toB256 =? (ff20 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) ≠ 0 ∧
       x0 &&& ff20 ≠ 0 ∧
      b'.getStor sevm.currentTarget = (b.getStor sevm.currentTarget).set (Bytes.toB256 [0]) (ff20 &&& x0 ||| hi96 &&& (b.getStor sevm.currentTarget).get (Bytes.toB256 [0])) := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_3bfd_c16 at run
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
  unfold t_3c83_c16 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_3cef_c16 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mload s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_mstore s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
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
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_log1 s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [85]) (g := t_422f_c85) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, rfl⟩ := setOwner_ret hfork callee
  unfold t_3d4d_c16 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  refine ⟨_, _, _, rfl, ?_⟩
  simp only [getStorVal_eq, Devm.addLog_getStor, afterSstore_getStor_self, afterSload_getStor] at *
  exact ⟨h1, h2, trivial⟩

end Blanc.Lift.Usdc.Impl
