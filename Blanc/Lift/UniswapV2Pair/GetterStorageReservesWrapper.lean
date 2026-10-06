import Blanc.Lift.UniswapV2Pair.GetterStorageReservesCore
import Blanc.Lift.UniswapV2Pair.GetterStorageReservesMemory

/-! Actual packed-reserve return wrapper and its internal call. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem reserves_tail_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {r0 r1 ts : B256}
    (clean0 : reserveMask112 &&& r0 = r0) (clean1 : reserveMask112 &&& r1 = r1)
    (cleant : reserveMask32 &&& ts = ts)
    (mem : PtrMem 128 96 M) (room : R.length ≤ 1015) :
    SFunc.RunExact fs sevm (St b (ts :: r1 :: r0 :: R) M (G + 109)) t_02de_c101
      (.halted (getterReservesPost b R M r0 r1 ts G)) := by
  have m1 := getterReservesMemory1_ptr mem r0
  have m2 := getterReservesMemory2_ptr mem r0 r1
  have m3 := getterReservesMemory_ptr mem r0 r1 ts
  simp only [getterReservesMemory, getterReservesMemory2, getterReservesMemory1] at m1 m2 m3
  unfold t_02de_c101
  refine rx_dest ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap (n := 4) (S' := r0 :: 128 :: 64 :: ts :: r1 :: reserveMask112 :: R) rfl ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and clean0 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 9) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_swap3 ?_
  refine rx_swap1 ?_
  refine rx_swap4 ?_
  refine rx_and clean1 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 160) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq m1.size]; decide
  refine rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and cleant (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 192) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 6) ?_ rfl ?_
  · simp only [show (128 : B256).toNat = 128 from rfl,
      show (160 : B256).toNat = 160 from rfl]
    rw [St.extCost_eq m2.size]; decide
  refine rx_swap1 ?_
  refine rx_mload (c := 3) ?_ m3.word (m3.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (192 : B256).toNat = 192 from rfl,
      show (160 : B256).toNat = 160 from rfl,
      show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq m3.size]; decide
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 96) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 96) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  exact rx_return_any rfl (by
    simp only [show (192 : B256).toNat = 192 from rfl,
      show (160 : B256).toNat = 160 from rfl,
      show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq m3.size]; decide)

theorem reserves_tail_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {r0 r1 ts : B256} {o : Outcome}
    (clean0 : reserveMask112 &&& r0 = r0) (clean1 : reserveMask112 &&& r1 = r1)
    (cleant : reserveMask32 &&& ts = ts) (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b (ts :: r1 :: r0 :: R) M G) t_02de_c101 o) :
    ∃ d, o = .halted d ∧ d.output = encodeWords [r0, r1, ts] ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have m3 := getterReservesMemory_ptr mem r0 r1 ts
  simp only [getterReservesMemory, getterReservesMemory2, getterReservesMemory1] at m3
  have h := run.cut
  unfold t_02de_c101 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl, mem.read_self (by decide : 64 + 32 ≤ 96),
    show Bytes.toB256 (M.read 64 32).1 = (128 : B256) from mem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_push hd
  rw [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = reserveMask112 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := r0 :: 128 :: 64 :: ts :: r1 :: reserveMask112 :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := reserveMask112) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  rw [clean0] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 128) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (128 : B256).toNat = 128 from rfl] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := r1 :: 64 :: ts :: 128 :: reserveMask112 :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := 64 :: r1 :: ts :: 128 :: reserveMask112 :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := reserveMask112 :: r1 :: ts :: 128 :: 64 :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  rw [clean1] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 128) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_add hd
  simp only [show (128 : B256) + Bytes.toB256 [0x20] = 160 from by decide] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (160 : B256).toNat = 160 from rfl] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_push hd
  rw [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = reserveMask32 from rfl] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  rw [cleant] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 128) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 64) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_add hd
  simp only [show (64 : B256) + 128 = 192 from by decide] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (192 : B256).toNat = 192 from rfl] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap (S' := 64 :: 128 :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl,
    m3.read_self (by decide : 64 + 32 ≤ 224),
    show Bytes.toB256 ((((M.write 128 r0.toBytes).write 160 r1.toBytes).write 192 ts.toBytes).read 64 32).1 = (128 : B256) from m3.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap (S' := 128 :: 128 :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 128) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap (S' := 128 :: 128 :: 128 :: R) rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_sub hd
  simp only [show (128 : B256) - 128 = 0 from by decide] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_add hd
  simp only [show Bytes.toB256 [0x60] + (0 : B256) = 96 from by decide] at hd; subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap (S' := 128 :: 96 :: R) rfl hd
  cases h with
  | last hr =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hr
    refine ⟨_, rfl, ?_, hstor, hlogs⟩
    rw [hout]
    exact (getterReservesPost_facts (b := b) (R := R) (G := G) mem).1

theorem reserves_entry_exact {sevm : Sevm} {b : Devm} {M : Mem} {G c : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b 8)
    (mem : PtrMem 128 96 M) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + c + 194)) t_02d6_c101
      (.halted (getterReservesPost (afterSload sevm b 8) [sel] M
        (reserve0Read (b.getStorVal sevm.currentTarget 8))
        (reserve1Read (b.getStorVal sevm.currentTarget 8))
        (reserveTimestampRead (b.getStorVal sevm.currentTarget 8)) G)) := by
  have clean0 : reserveMask112 &&& reserve0Read (b.getStorVal sevm.currentTarget 8) =
      reserve0Read (b.getStorVal sevm.currentTarget 8) := by
    change reserveMask112 &&& (_ &&& reserveMask112) = _ &&& reserveMask112
    rw [B256.and_comm reserveMask112]
    exact B256.and_idem_right _ _
  have clean1 : reserveMask112 &&& reserve1Read (b.getStorVal sevm.currentTarget 8) =
      reserve1Read (b.getStorVal sevm.currentTarget 8) := by
    change reserveMask112 &&& (_ &&& reserveMask112) = _ &&& reserveMask112
    rw [B256.and_comm reserveMask112]
    exact B256.and_idem_right _ _
  have cleant : reserveMask32 &&& reserveTimestampRead (b.getStorVal sevm.currentTarget 8) =
      reserveTimestampRead (b.getStorVal sevm.currentTarget 8) := by
    change reserveMask32 &&& (_ &&& reserveMask32) = _ &&& reserveMask32
    rw [B256.and_comm reserveMask32]
    exact B256.and_idem_right _ _
  have gas : G + c + 194 = (((G + 109) + c + 70) + 8) + 3 + 3 + 1 := by omega
  rw [gas]
  unfold t_02d6_c101
  refine rx_dest ?_
  refine rx_push (w := 0x02de) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0d90) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_callRet (show cert.prog[56]? = some t_0d90_c56 from rfl)
    (reserves_callee_exact fork cost (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact reserves_tail_exact clean0 clean1 cleant mem (by simp only [List.length_cons, List.length_nil]; decide)

theorem reserves_entry_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_02d6_c101 o) :
    ∃ d, o = .halted d ∧ d.output = encodeWords
      [reserve0Read (b.getStorVal sevm.currentTarget 8),
       reserve1Read (b.getStorVal sevm.currentTarget 8),
       reserveTimestampRead (b.getStorVal sevm.currentTarget 8)] ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have clean0 : reserveMask112 &&& reserve0Read (b.getStorVal sevm.currentTarget 8) =
      reserve0Read (b.getStorVal sevm.currentTarget 8) := by
    change reserveMask112 &&& (_ &&& reserveMask112) = _ &&& reserveMask112
    rw [B256.and_comm reserveMask112]
    exact B256.and_idem_right _ _
  have clean1 : reserveMask112 &&& reserve1Read (b.getStorVal sevm.currentTarget 8) =
      reserve1Read (b.getStorVal sevm.currentTarget 8) := by
    change reserveMask112 &&& (_ &&& reserveMask112) = _ &&& reserveMask112
    rw [B256.and_comm reserveMask112]
    exact B256.and_idem_right _ _
  have cleant : reserveMask32 &&& reserveTimestampRead (b.getStorVal sevm.currentTarget 8) =
      reserveTimestampRead (b.getStorVal sevm.currentTarget 8) := by
    change reserveMask32 &&& (_ &&& reserveMask32) = _ &&& reserveMask32
    rw [B256.and_comm reserveMask32]
    exact B256.and_idem_right _ _
  have h := run.cut
  unfold t_02d6_c101 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call (show cert.prog[56]? = some t_0d90_c56 from rfl) h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨_, eq⟩ := reserves_callee_inv fork hc
    cases eq
    obtain ⟨d, ho, out, stor, logs⟩ := reserves_tail_inv clean0 clean1 cleant mem h.uncut
    exact ⟨d, ho, out, fun a => (stor a).trans (afterSload_getStor _ _ _ _),
      logs.trans (afterSload_logs _ _ _)⟩
  · obtain ⟨_, eq⟩ := reserves_callee_inv fork hc
    cases eq

end Blanc.Lift.UniswapV2Pair
