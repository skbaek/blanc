import Blanc.Lift.UniswapV2Pair.GetterStorageDispatch
import Blanc.Lift.UniswapV2Pair.Layout

/-! Actual packed slot8 getter callee. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem reserves_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b 8)
    (room : R.length ≤ 1018) :
    SFunc.RunExact fs sevm (St b (ρ :: R) M (G + c + 70)) t_0d90_c56
      (.returned (St (afterSload sevm b 8)
        (reserveTimestampRead (b.getStorVal sevm.currentTarget 8) ::
         reserve1Read (b.getStorVal sevm.currentTarget 8) ::
         reserve0Read (b.getStorVal sevm.currentTarget 8) :: R) M G)) := by
  unfold t_0d90_c56
  refine rx_dest ?_
  refine rx_push (w := 8) rfl (by simp only [List.length_cons]; omega) ?_
  have gas : G + c + 66 = (G + 66) + c := by omega
  rw [gas]
  refine rx_sload_selC fork cost (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := reserve0Read _) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_push (w := reserveDiv112) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_div rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_and (v := reserve1Read _) (B256.and_comm _ _) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_push (w := reserveDiv224) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_div rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := reserveTimestampRead (b.getStorVal sevm.currentTarget 8)) ?_ (by simp only [List.length_cons]; omega) ?_
  · exact B256.and_comm _ _
  refine rx_swap1 ?_
  exact rx_ret

theorem reserves_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) t_0d90_c56 o) :
    ∃ G', o = .returned (St (afterSload sevm b 8)
      (reserveTimestampRead (b.getStorVal sevm.currentTarget 8) ::
       reserve1Read (b.getStorVal sevm.currentTarget 8) ::
       reserve0Read (b.getStorVal sevm.currentTarget 8) :: R) M G') := by
  have h := run.cut
  unfold t_0d90_c56 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_sload fork hd
  change d = St (afterSload sevm b 8) (b.getStorVal sevm.currentTarget 8 :: ρ :: R) M _ at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  rw [B256.and_comm] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  have eq := Seg.done.inj hg
  simp only [show ((2 : Fin 16) : Nat) = 2 from rfl,
    show ((1 : Fin 16) : Nat) = 1 from rfl, show ((0 : Fin 16) : Nat) = 0 from rfl,
    List.set_cons_zero, List.set_cons_succ,
    show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = reserveMask112 from rfl,
    show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = reserveMask32 from rfl,
    show Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = reserveDiv112 from rfl,
    show Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = reserveDiv224 from rfl] at eq
  refine ⟨g, ?_⟩
  simpa only [reserveTimestampRead, reserve1Read, reserve0Read, B256.and_comm] using eq

end Blanc.Lift.UniswapV2Pair
