import Blanc.Lift.Usdc.Impl.Check
import Blanc.Lift.WalkCutKit

/-!
# FiatTokenV2_2's internal functions the admin calls share (U6f)

Certificate-driven inversions (`Blanc/Lift/WalkCutKit.lean`) of the implementation certificate's
internal functions: `_balanceOf`, `_isBlacklisted`, SafeMath `add`/`sub`, `_setOwner`, `_setBalance`,
`_setBlacklistState` and the `_blacklist`/`_unBlacklist` wrappers.  Each inverts a returning run of
the callee's tree from its entry stack to its exact result.
-/

namespace Blanc.Lift.Usdc.Impl

open Jaune Blanc Blanc.Lift

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

/-- `_balanceOf(a)` (entry 96): the low 255 bits of `a`'s packed word. -/
theorem balanceOf_ret (hfork : CoveredFork sevm.benvStat.fork) {t a : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (a :: t :: S) M G) t_41da_c96 (.returned D)) :
    ∃ M' G', D = St (afterSload sevm b (mapSlot (ff20 &&& a) (Bytes.toB256 [9])))
      ((lo255 &&& b.getStorVal sevm.currentTarget (mapSlot (ff20 &&& a) (Bytes.toB256 [9]))) :: S) M' G' := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_41da_c96 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
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
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, _, rfl⟩

/-- `_isBlacklisted(a)` (entry 83): the top bit of `a`'s packed word. -/
theorem isBlacklisted_ret (hfork : CoveredFork sevm.benvStat.fork) {t a : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (a :: t :: S) M G) t_3f6a_c83 (.returned D)) :
    ∃ M' G', D = St (afterSload sevm b (mapSlot (ff20 &&& a) (Bytes.toB256 [9])))
      ((Bytes.toB256 [1] =? (b.getStorVal sevm.currentTarget (mapSlot (ff20 &&& a) (Bytes.toB256 [9])) >>>
        (Bytes.toB256 [255]).toNat)) :: S) M' G' := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_3f6a_c83 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
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
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_shr s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_eq s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, _, rfl⟩

/-- SafeMath `add(x, y)` (entry 98): no wrap. -/
theorem add_ret {t x y : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: t :: S) M G) t_43b5_c98 (.returned D)) :
    ∃ G', D = St b ((x + y) :: S) M G' ∧ B256.ltCheck (x + y) y = 0 := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_43b5_c98 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_add s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_lt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branchTo (g := t_4429_c7) List.not_mem_nil rfl run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_4429_c7 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, rfl, eq_of_eqCheck_ne_zero h1⟩

/-- SafeMath `sub(y, x)` (entry 100): `x ≤ y`. -/
theorem sub_ret {t x y : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: t :: S) M G) t_4163_c100 (.returned D)) :
    ∃ G', D = St b ((y - x) :: S) M G' ∧ B256.gtCheck x y = 0 := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_4163_c100 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_gt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_41d4_c100 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sub s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, rfl, eq_of_eqCheck_ne_zero h1⟩

/-- `_setOwner(a)` (entry 85): the address bits of slot 0. -/
theorem setOwner_ret (hfork : CoveredFork sevm.benvStat.fork) {t a : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (a :: t :: S) M G) t_422f_c85 (.returned D)) :
    ∃ G', D = St (afterSstore sevm (afterSload sevm b (Bytes.toB256 [0])) (Bytes.toB256 [0])
      ((ff20 &&& a) ||| (hi96 &&& b.getStorVal sevm.currentTarget (Bytes.toB256 [0])))) S M G' := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_422f_c85 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sload hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, rfl⟩

/-- `_setBalance(account, x)` (entry 99): the credit cap, not blacklisted, then the write. -/
theorem setBalance_ret (hfork : CoveredFork sevm.benvStat.fork) {t x y : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (x :: y :: t :: S) M G) t_4430_c99 (.returned D)) :
    ∃ M' G', D = St (afterSstore sevm (afterSload sevm b (mapSlot (ff20 &&& y) (Bytes.toB256 [9]))) (mapSlot (y &&& ff20) (Bytes.toB256 [9])) x)
        S M' G' ∧ B256.gtCheck x lo255 = 0 ∧
      (Bytes.toB256 [1] =? (b.getStorVal sevm.currentTarget (mapSlot (ff20 &&& y) (Bytes.toB256 [9])) >>> (Bytes.toB256 [255]).toNat)) = 0 := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_4430_c99 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_gt s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h1, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_44a9_c99 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [83]) (g := t_3f6a_c83) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := isBlacklisted_ret hfork callee
  unfold t_44b2_c99 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_iszero s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨-, _, run⟩ | ⟨h2, _, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run rfl).elim
  unfold t_4508_c99 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
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
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, _, rfl, eq_of_eqCheck_ne_zero h1, eq_of_eqCheck_ne_zero h2⟩

/-- `_setBlacklistState(a, false)` (entry 109): the balance bits only. -/
theorem setBlacklistState0_ret (hfork : CoveredFork sevm.benvStat.fork) {t a : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (Bytes.toB256 [0] :: a :: t :: S) M G) t_4cc7_c109 (.returned D)) :
    ∃ M' G', D = St (afterSstore sevm (afterSload sevm b (mapSlot (ff20 &&& a) (Bytes.toB256 [9])))
      (mapSlot (a &&& ff20) (Bytes.toB256 [9]))
      (lo255 &&& b.getStorVal sevm.currentTarget (mapSlot (ff20 &&& a) (Bytes.toB256 [9])))) S M' G' := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_4cc7_c109 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨h1, _, run⟩ | ⟨h1, _, run⟩
  swap; · exact absurd h1 (by decide)
  unfold t_4ccd_c109 at run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [96]) (g := t_41da_c96) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := balanceOf_ret hfork callee
  unfold t_4cd5_c109 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_jump (k := 10) (by simp only [List.not_mem_nil, not_false_eq_true]) rfl run; obtain ⟨_, run⟩ := run
  unfold t_4d23_c10 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
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
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, _, rfl⟩

/-- `_setBlacklistState(a, true)` (entry 109): the top bit set. -/
theorem setBlacklistState1_ret (hfork : CoveredFork sevm.benvStat.fork) {t a : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (Bytes.toB256 [1] :: a :: t :: S) M G) t_4cc7_c109 (.returned D)) :
    ∃ M' G', D = St (afterSstore sevm (afterSload sevm b (mapSlot (a &&& ff20) (Bytes.toB256 [9])))
      (mapSlot (a &&& ff20) (Bytes.toB256 [9]))
      (Bytes.toB256 [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0] ||| b.getStorVal sevm.currentTarget (mapSlot (a &&& ff20) (Bytes.toB256 [9])))) S M' G' := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_4cc7_c109 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_branch run; rcases run with ⟨h1, _, run⟩ | ⟨h1, _, run⟩
  · exact absurd h1 (by decide)
  unfold t_4cda_c109 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
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
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_or s; clear s
  unfold t_4d23_c10 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_and s; clear s
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
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_sstore hfork s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, _, rfl⟩

/-- `_unBlacklist(a)` (entry 104). -/
theorem unBlacklist_ret (hfork : CoveredFork sevm.benvStat.fork) {t a : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (a :: t :: S) M G) t_3f5f_c104 (.returned D)) :
    ∃ M' G', D = St (afterSstore sevm (afterSload sevm b (mapSlot (ff20 &&& a) (Bytes.toB256 [9])))
      (mapSlot (a &&& ff20) (Bytes.toB256 [9]))
      (lo255 &&& b.getStorVal sevm.currentTarget (mapSlot (ff20 &&& a) (Bytes.toB256 [9])))) S M' G' := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_3f5f_c104 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [10, 96, 109]) (g := t_4cc7_c109) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := setBlacklistState0_ret hfork callee
  unfold t_3d4d_c104 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, _, rfl⟩

/-- `_blacklist(a)` (entry 86). -/
theorem blacklist_ret (hfork : CoveredFork sevm.benvStat.fork) {t a : B256} {D : Devm}
    (run : SFunc.Run cert.prog sevm (St b (a :: t :: S) M G) t_4224_c86 (.returned D)) :
    ∃ M' G', D = St (afterSstore sevm (afterSload sevm b (mapSlot (a &&& ff20) (Bytes.toB256 [9])))
      (mapSlot (a &&& ff20) (Bytes.toB256 [9]))
      (Bytes.toB256 [128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0] ||| b.getStorVal sevm.currentTarget (mapSlot (a &&& ff20) (Bytes.toB256 [9])))) S M' G' := by
  replace run := SFunc.runP_iff_runCutP_nil.mp run
  unfold t_4224_c86 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_dup rfl s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_push s; clear s
  replace run := ric_callRet (E := [10, 96, 109]) (g := t_4cc7_c109) (by decide) (by decide) rfl run; obtain ⟨_, D, callee, run⟩ := run
  obtain ⟨_, _, rfl⟩ := setBlacklistState1_ret hfork callee
  unfold t_3d4d_c86 at run
  replace run := ric_dest run; obtain ⟨_, run⟩ := run
  replace run := ric_next run; obtain ⟨_, s, run⟩ := run; obtain ⟨_, rfl⟩ := ri_pop s; clear s
  obtain ⟨_, hr⟩ := ric_ret run
  obtain rfl := Outcome.returned.inj (Seg.done.inj hr)
  -- RET
  exact ⟨_, _, rfl⟩

end Blanc.Lift.Usdc.Impl
