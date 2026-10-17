import Blanc.Lift.Curve3Pool.Callee.GetYDCoins
import Blanc.Lift.Curve3Pool.Model
import Blanc.Lift.ReachWalk

/-!
# `get_y_D` (entry 753, pc `0x3999`): the callee contract

`getYD_spec`: every run of `get_y_D`'s entry tree from `St b (ρ :: A_ :: i :: xp0 :: xp1 :: xp2 ::
D :: S) M G` returns (it never halts the frame), with `i < 3`, the result word `v` on top of the
caller's stack `S`, `getYDChk A_ i xp D = some v` (the checked model of
`Blanc/Lift/StableSwapNewton/Defs.lean`), the world (`b`) unchanged, and memory changed only
in the frame `[0x140, 0x340)` and the scratch word `0` (`YDOut`).  The caller's memory must be
word-aligned and cover the frame (`0x340 ≤ M.size`); every call site's does.

The proof composes the prologue (`ric_ydEntry`), the three coin-loop stages, the post-loop and
the Newton loop (`ydLoop_sound`); `ydRes_getYDChk` identifies the bytes' evaluation order with
the model's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- `get_y_D` on naturals in the bytes' evaluation order: the three coin-loop iterations from
`(c, S_) = (D, 0)`, then the post-loop and the `y` loop. -/
def ydRes (i x0 x1 x2 D ann : Nat) : Option Nat :=
  (ydCoinStep i 0 x0 D (D, 0)).bind fun cs =>
    (ydCoinStep i 1 x1 D cs).bind fun cs =>
      (ydCoinStep i 2 x2 D cs).bind fun cs => ydPostRes cs.1 cs.2 D ann

/-! ## The bytes' evaluation order is the model's -/

theorem ydRes_core {u v D ann c1 s1 c2 s2 y : Nat}
    (h1 : ydAccN D 0 u D = some (c1, s1)) (h2 : ydAccN c1 s1 v D = some (c2, s2))
    (hp : ydPostRes c2 s2 D ann = some y) :
    ((cOfChk u v D ann).bind fun c => (bOfChk u v D ann).bind fun b =>
      loopYChk c b D 1 255 D) = some y := by
  unfold ydAccN at h1 h2
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h1 h2
  obtain ⟨sa, hsa, ma, hma, mb, hmb, ca, hca, rfl, rfl⟩ := h1
  obtain ⟨sb, hsb, mc, hmc, md, hmd, cb, hcb, rfl, rfl⟩ := h2
  unfold ydPostRes at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hp
  obtain ⟨me, hme, mf, hmf, cc, hcc, q, hq, bb, hbb, hloop⟩ := hp
  unfold cOfChk bOfChk
  simp only [Option.bind_eq_bind, hma, hmb, hca, hmc, hmd, hcb, hme, hmf, hcc, hsa, hsb, hq, hbb,
    Option.bind_some, hloop]

theorem ydRes_getYDChk {A i x0 x1 x2 D ann y : Nat} (hi : i < 3) (hann : chkMul A 3 = some ann)
    (h : ydRes i x0 x1 x2 D ann = some y) :
    getYDChk A ⟨i, hi⟩ (V3.mk x0 x1 x2).get D = some y := by
  unfold getYDChk
  rw [hann, Option.bind_eq_bind, Option.bind_some]
  unfold ydRes at h
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  · simp only [ydCoinStep_eq, Option.bind_some, ydCoinStep_ne (i := 0) (j := 1) (by decide),
      ydCoinStep_ne (i := 0) (j := 2) (by decide)] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨c1, s1⟩, h1, ⟨c2, s2⟩, h2, hp⟩ := h
    exact ydRes_core h1 h2 hp
  · simp only [ydCoinStep_ne (i := 1) (j := 0) (by decide), ydCoinStep_ne (i := 1) (j := 2) (by decide)] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨c1, s1⟩, h1, h⟩ := h
    simp only [ydCoinStep_eq, Option.bind_some] at h
    obtain ⟨a, he, ⟨c2, s2⟩, h2, hp⟩ := h
    cases he
    exact ydRes_core h1 h2 hp
  · simp only [ydCoinStep_ne (i := 2) (j := 0) (by decide), ydCoinStep_ne (i := 2) (j := 1) (by decide)] at h
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨⟨c1, s1⟩, h1, ⟨c2, s2⟩, h2, h⟩ := h
    simp only [ydCoinStep_eq, Option.bind_some] at h
    obtain ⟨a, he, hp⟩ := h
    cases he
    exact ydRes_core h1 h2 hp

section Walk

variable {sevm : Sevm} {b : Devm} {S : List B256} {M0 : Mem}

theorem ne_toNat_of_ne {i : B256} {j : Nat} (h : i ≠ Nat.toB256 j) : i.toNat ≠ j := by
  intro he; apply h; rw [← he, toB256_toNat]

theorem toNat_of_eq {i : B256} {j : Nat} (hj : j < 2 ^ 256) (h : i = Nat.toB256 j) :
    i.toNat = j := by
  rw [h, B256.toNat_toB256_of_lt hj]

-- SEGMENT: ydStage2
theorem ydStage2 {A i x0 x1 x2 D ρ c s ann xv w12 w13 w14 w15 : B256} {M : Mem} {G : Nat}
    {r : Seg}
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv (Nat.toB256 2) w12 w13 w14
      w15))
    (run : SFunc.RunCut progYD sevm [] (St b (ydCStk S) M G) (ydTest 120 121) r) :
    ydOut b S M0 ((ydCoinStep i.toNat 2 x2.toNat D.toNat (c.toNat, s.toNat)).bind fun cs =>
      ydPostRes cs.1 cs.2 D.toNat ann.toNat) r := by
  rcases ric_ydTest hF rfl rfl rfl (by decide) rfl List.not_mem_nil List.not_mem_nil
    progYD_120 progYD_121 run with ⟨heq, G1, run⟩ | ⟨hne, G1, M1, hF1, run⟩
  · obtain ⟨G2, M2, hF2, run⟩ := ric_ydCoinTail_last hF rfl rfl (by decide) run
    rw [toNat_of_eq (by decide) heq, ydCoinStep_eq, Option.bind_some]
    exact ric_ydPost hF2 run
  · obtain ⟨G2, M2, c', s', hacc, hF2, run⟩ := ric_ydAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G3, M3, hF3, run⟩ := ric_ydCoinTail_last hF2 rfl rfl (by decide) run
    rw [ydCoinStep_ne (ne_toNat_of_ne hne), hacc, Option.bind_some]
    exact ric_ydPost hF3 run

-- SEGMENT: ydStage1
theorem ydStage1 {A i x0 x1 x2 D ρ c s ann xv w12 w13 w14 w15 : B256} {M : Mem} {G : Nat}
    {r : Seg}
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv (Nat.toB256 1) w12 w13 w14
      w15))
    (run : SFunc.RunCut progYD sevm [] (St b (ydCStk S) M G) (ydTest 76 77) r) :
    ydOut b S M0 ((ydCoinStep i.toNat 1 x1.toNat D.toNat (c.toNat, s.toNat)).bind fun cs =>
      (ydCoinStep i.toNat 2 x2.toNat D.toNat cs).bind fun cs =>
        ydPostRes cs.1 cs.2 D.toNat ann.toNat) r := by
  rcases ric_ydTest hF rfl rfl rfl (by decide) rfl List.not_mem_nil List.not_mem_nil
    progYD_76 progYD_77 run with ⟨heq, G1, run⟩ | ⟨hne, G1, M1, hF1, run⟩
  · obtain ⟨G2, M2, hF2, run⟩ :=
      ric_ydCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progYD_99 run
    have h := ydStage2 hF2 run
    rw [toNat_of_eq (by decide) heq] at h ⊢
    rw [ydCoinStep_eq, Option.bind_some]
    exact h
  · obtain ⟨G2, M2, c', s', hacc, hF2, run⟩ := ric_ydAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G3, M3, hF3, run⟩ :=
      ric_ydCoinTail_next hF2 rfl rfl (by decide) List.not_mem_nil progYD_99 run
    rw [ydCoinStep_ne (ne_toNat_of_ne hne), hacc, Option.bind_some]
    exact ydStage2 hF3 run

-- SEGMENT: ydStage0
theorem ydStage0 {A i x0 x1 x2 D ρ c s ann xv w12 w13 w14 w15 : B256} {M : Mem} {G : Nat}
    {r : Seg}
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv (Nat.toB256 0) w12 w13 w14
      w15))
    (run : SFunc.RunCut progYD sevm [] (St b (ydCStk S) M G) (ydTest 763 18) r) :
    ydOut b S M0 ((ydCoinStep i.toNat 0 x0.toNat D.toNat (c.toNat, s.toNat)).bind fun cs =>
      (ydCoinStep i.toNat 1 x1.toNat D.toNat cs).bind fun cs =>
        (ydCoinStep i.toNat 2 x2.toNat D.toNat cs).bind fun cs =>
          ydPostRes cs.1 cs.2 D.toNat ann.toNat) r := by
  rcases ric_ydTest hF rfl rfl rfl (by decide) rfl List.not_mem_nil List.not_mem_nil
    progYD_763 progYD_18 run with ⟨heq, G1, run⟩ | ⟨hne, G1, M1, hF1, run⟩
  · obtain ⟨G2, M2, hF2, run⟩ :=
      ric_ydCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progYD_49 run
    have h := ydStage1 hF2 run
    rw [toNat_of_eq (by decide) heq] at h ⊢
    rw [ydCoinStep_eq, Option.bind_some]
    exact h
  · obtain ⟨G2, M2, c', s', hacc, hF2, run⟩ := ric_ydAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G3, M3, hF3, run⟩ :=
      ric_ydCoinTail_next hF2 rfl rfl (by decide) List.not_mem_nil progYD_49 run
    rw [ydCoinStep_ne (ne_toNat_of_ne hne), hacc, Option.bind_some]
    exact ydStage1 hF3 run

theorem toB256_three : Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Nat.toB256 3 := by decide

-- SEGMENT: ydEntry
/-- **The prologue and the whole callee**, inverted: `0 ≤ i < 3`, `Ann = A_ * N_COINS` checked,
and the run ends as `ydOut` of `ydRes`. -/
theorem ric_ydEntry {ρ A i x0 x1 x2 D : B256} {M : Mem} {G : Nat} {r : Seg}
    (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size)
    (run : SFunc.RunCut progYD sevm [] (St b (ρ :: A :: i :: x0 :: x1 :: x2 :: D :: S) M G)
      (ydEntry (ydTest 763 18)) r) :
    i.toNat < 3 ∧ ∃ ann, chkMul A.toNat 3 = some ann ∧
      ydOut b S M (ydRes i.toNat x0.toNat x1.toNat x2.toNat D.toNat ann) r := by
  have hF := WordFrame.init (lo := 0x140) (n := 16) hsz hcov
  unfold ydEntry at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, M1, hF, run⟩ := ric_pushMstoreF hF 6 (by decide) (lt16 (by decide)) run
  obtain ⟨G3, M2, hF, run⟩ := ric_pushMstoreF hF 0 (by decide) (lt16 (by decide)) run
  obtain ⟨G4, M3, hF, run⟩ := ric_pushMstoreF hF 1 (by decide) (lt16 (by decide)) run
  obtain ⟨G5, M4, hF, run⟩ := ric_pushMstoreF hF 2 (by decide) (lt16 (by decide)) run
  obtain ⟨G6, M5, hF, run⟩ := ric_pushMstoreF hF 3 (by decide) (lt16 (by decide)) run
  obtain ⟨G7, M6, hF, run⟩ := ric_pushMstoreF hF 4 (by decide) (lt16 (by decide)) run
  obtain ⟨G8, M7, hF, run⟩ := ric_pushMstoreF hF 5 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨G10, run⟩ := ric_pushMloadF hF 1 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_sltV s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G14, run⟩ | ⟨hw1, G14, run⟩
  · exact (run.false_of_noOk vyRevertT_noOk).elim
  obtain ⟨G15, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨G17, run⟩ := ric_pushMloadF hF 1 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_sltV s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G20, run⟩ | ⟨hw2, G20, run⟩
  · exact (run.false_of_noOk vyRevertT_noOk).elim
  have hi3 : i.toNat < 3 := by
    refine B256.toNat_lt_three_of_slt ?_ ?_
    · intro hs
      apply hw1
      have h0 : Bytes.toB256 [0x00] = 0 := by decide
      rw [h0]
      unfold B256.sltCheck; rw [ite_eq_left hs]; decide
    · by_contra hs
      apply hw2
      unfold B256.sltCheck; rw [ite_eq_right hs]
  obtain ⟨G21, run⟩ := ric_dest run
  obtain ⟨G22, run⟩ := ric_pushMloadF hF 5 (by decide) rfl run
  obtain ⟨G23, M8, hF, run⟩ := ric_pushMstoreF hF 7 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨G25, M9, hF, run⟩ := ric_pushMstoreF hF 8 (by decide) (lt16 (by decide)) run
  obtain ⟨G26, run⟩ := ric_pushMloadF hF 0 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_push s1
  obtain ⟨hm, G28, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G29, M10, hF, run⟩ := ric_pushMstoreF hF 9 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨G31, M11, hF, run⟩ := ric_pushMstoreF hF 10 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_dup (w := Bytes.toB256 [0x00]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_dup (w := Bytes.toB256 [0x02, 0xa0]) rfl s1
  obtain ⟨G37, M12, hF, run⟩ := ric_mstoreF hF 11 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_add s1
  rw [toB256_three, toB256_0x2a0] at run
  rw [toB256_zero] at hF
  have h := ydStage0 hF run
  refine ⟨hi3, (A * Bytes.toB256 [0x03]).toNat, ?_, ?_⟩
  · have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
    rw [e3]; exact chkMul_toNat_of_nofm hm
  · unfold ydRes
    rw [show (Nat.toB256 0).toNat = 0 by decide] at h
    exact h

end Walk

/-! ## The contract -/

theorem progYD_753_t : progYD[753]? = some t_3999_c753 := by decide +kernel

theorem t_3999_c753_eq : t_3999_c753 = ydEntry (ydTest 763 18) :=
  Option.some.inj (progYD_753_t.symm.trans progYD_753)

-- SEGMENT: getYD_spec
/-- **`get_y_D`'s callee contract.**  Any outcome of the entry tree from the call's state is a
return: `0 ≤ i < 3`, the result `v` over the caller's stack, `getYDChk A_ i xp D = some v`, the
world `b` unchanged, the memory's size unchanged, `v` at scratch word `0`, and (on a well-formed
memory) every byte off `get_y_D`'s windows `[0, 0x20)` and `[0x140, 0x340)` kept. -/
theorem getYD_spec {sevm : Sevm} {b : Devm} {ρ A i x0 x1 x2 D : B256} {S : List B256} {M : Mem}
    {G : Nat} {o : Outcome} (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size)
    (run : SFunc.Run cert.prog sevm (St b (ρ :: A :: i :: x0 :: x1 :: x2 :: D :: S) M G)
      t_3999_c753 o) :
    ∃ d, o = .returned d ∧ ∃ v M' G', d = St b (v :: S) M' G' ∧
      ∃ hi : i.toNat < 3,
        getYDChk A.toNat ⟨i.toNat, hi⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get D.toNat =
          some v.toNat ∧ M'.size = M.size ∧ Words M' [(0, v)] ∧
      (Mem.Wf M → Mem.KeepsOff M M' [(0, 32), (0x140, 0x340)] ∧ Mem.Wf M') := by
  have hcut := SFunc.runP_iff_runCutP_nil.mp run
  rw [t_3999_c753_eq] at hcut
  obtain ⟨hi3, ann, hann, y, hres, hy, M', G', hr, hout⟩ := ric_ydEntry hsz hcov hcut
  have ho : o = .returned (St b (Nat.toB256 y :: S) M' G') := by injection hr
  subst ho
  refine ⟨_, rfl, Nat.toB256 y, M', G', rfl, hi3, ?_, hout.size, hout.words (by omega),
    fun hwf => ⟨hout.keepsOff hwf, hout.wf hwf⟩⟩
  rw [B256.toNat_toB256_of_lt hy]
  exact ydRes_getYDChk hi3 hann hres

/-! ## Kernel facts for the frame-walk bridge (`xa_callee`) -/

/-- `get_y_D`'s entry closure. -/
def ydEntries : List Nat :=
  [753, 763, 18, 49, 76, 77, 99, 120, 121, 141, 142, 143, 163, 164, 165, 185, 186, 187, 204, 205]

theorem yd_execFreeSet : ExecFreeSet cert.prog ydEntries = true := by decide +kernel

theorem yd_free : t_3999_c753.execFreeIn ydEntries = true := by decide +kernel


end Blanc.Lift.Curve3Pool
