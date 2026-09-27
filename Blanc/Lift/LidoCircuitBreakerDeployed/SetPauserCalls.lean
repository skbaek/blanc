import Blanc.Lift.LidoCircuitBreakerDeployed.Prog
import Blanc.Lift.WalkSteps

/-! Inversion of the deployed CircuitBreaker's checked-arithmetic helper
entries on a successful run: entry 40 (checked decrement), entry 24 (checked
increment), entry 25 (checked subtraction).  Each helper's overflow arm
reaches a `Panic(0x11)` revert block, so a returned run excludes it. -/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune

/-- The all-ones word the checked helpers push. -/
abbrev ffWord : B256 := Bytes.toB256
  [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
   0xff, 0xff]

section

variable {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}

/-- The `Panic(0x11)` block never completes successfully. -/
theorem panic42_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_107b_c42 r) : False := by
  unfold t_107b_c42 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  exact ric_revert run

theorem panic39_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_107b_c39 r) : False :=
  panic42_not_run (show SFunc.RunCut prog sevm C (St b S M G) t_107b_c42 r from run)

theorem panic38_not_run {C : List Nat} {S : List B256} {r : Seg}
    (run : SFunc.RunCut prog sevm C (St b S M G) t_107b_c38 r) : False :=
  panic42_not_run (show SFunc.RunCut prog sevm C (St b S M G) t_107b_c42 r from run)

/-- Entry 40, the checked decrement: a returned run had a nonzero operand and
returns `ff..ff + x` (that is, `x - 1`) over the caller's remaining stack. -/
theorem entry40_returned_inv {x r : B256} {R : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (x :: r :: R) M G) t_10da_c40 (.returned D)) :
    x ≠ 0 ∧ ∃ G', D = St b ((ffWord + x) :: R) M G' := by
  have run := run.cut
  unfold t_10da_c40 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨_, G5, run⟩ | ⟨hnz, G5, run⟩
  · unfold t_10e1_c40 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G6, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G7, rfl⟩ := ri_push s1
    obtain ⟨G8, run⟩ := ric_jump (List.not_mem_nil) entry42_lookup run
    exact (panic42_not_run run).elim
  · refine ⟨hnz, ?_⟩
    unfold t_10e8_c40 at run
    obtain ⟨G6, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G7, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G9, rfl⟩ := ri_add s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G10, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨G11, hr⟩ := ric_ret run
    cases hr
    exact ⟨G11, rfl⟩

/-- Entry 24, the checked increment: a returned run had an operand other than
`ff..ff` and returns `1 + x` over the caller's remaining stack. -/
theorem entry24_returned_inv {x r : B256} {R : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (x :: r :: R) M G) t_110e_c24 (.returned D)) :
    x - ffWord ≠ 0 ∧ ∃ G', D = St b ((1 + x) :: R) M G' := by
  have run := run.cut
  unfold t_110e_c24 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨_, G7, run⟩ | ⟨hnz, G7, run⟩
  · unfold t_1137_c24 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G8, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G9, rfl⟩ := ri_push s1
    obtain ⟨G10, run⟩ := ric_jump (List.not_mem_nil) entry39_lookup run
    exact (panic39_not_run run).elim
  · refine ⟨hnz, ?_⟩
    unfold t_113e_c24 at run
    obtain ⟨G8, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G9, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G11, rfl⟩ := ri_add s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨G13, hr⟩ := ric_ret run
    cases hr
    exact ⟨G13, rfl⟩

/-- Entry 25, the checked subtraction `x - y`: a returned run had no
underflow (`x - y` not above `x`) and returns `x - y` over the caller's
remaining stack, through entry 3's return shuffle. -/
theorem entry25_returned_inv {x y r : B256} {R : List B256} {D : Devm}
    (run : SFunc.Run prog sevm (St b (x :: y :: r :: R) M G) t_1145_c25 (.returned D)) :
    B256.eqCheck (B256.gtCheck (x - y) x) 0 ≠ 0 ∧ ∃ G', D = St b ((x - y) :: R) M G' := by
  have run := run.cut
  unfold t_1145_c25 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (w := x - y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  rcases ric_branchTo (List.not_mem_nil) entry3_lookup run with
    ⟨_, G10, run⟩ | ⟨hnz, G10, run⟩
  · unfold t_1151_c25 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G11, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_push s1
    obtain ⟨G13, run⟩ := ric_jump (List.not_mem_nil) entry38_lookup run
    exact (panic38_not_run run).elim
  · refine ⟨hnz, ?_⟩
    unfold t_051a_c3 at run
    obtain ⟨G11, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G12, rfl⟩ := ri_swap (n := 2) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G13, rfl⟩ := ri_swap (n := 1) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G14, rfl⟩ := ri_pop s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G15, rfl⟩ := ri_pop s1
    obtain ⟨G16, hr⟩ := ric_ret run
    cases hr
    exact ⟨G16, rfl⟩

end

end Blanc.Lift.LidoCircuitBreakerDeployed
