import Blanc.Lift.BabylonianSqrt
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.InvWalkOps
import Blanc.Lift.UniswapV2Pair.Cert

/-! Certified Babylonian square-root routine: entries 69, 74 and 26. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune
open Blanc.BabylonianSqrt

/-- Exact gas charge, with the source count including its mandatory first body. -/
def sqrtCharge (y : Nat) : Nat :=
  if 3 < y then 108 + 109 * sourceCount y else if y = 0 then 66 else 71

/-- The first inlined header and repeated cut have identical certified trees. -/
theorem sqrt_first_header_eq : t_288d_c69 = t_288d_c74 := rfl

/-- The shared source return drops the original input and preserves its suffix. -/
theorem sqrt_return_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {Y Z R : B256} :
    SFunc.RunExactCut cert.prog sevm C (St b (Z :: Y :: R :: T) M (G + 17))
      t_28c5_c26 (.done (.returned (St b (Z :: T) M G))) := by
  unfold t_28c5_c26
  apply rxc_dest
  apply rxc_swap (S' := R :: Y :: Z :: T) rfl
  apply rxc_swap (S' := Y :: R :: Z :: T) rfl
  apply rxc_pop
  exact rxc_ret

/-- One actual source body reaches the repeated certified header. Both DIV guards
are discharged, and the unchecked ADD is justified before the word conversion. -/
theorem sqrt_body_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G x : Nat} {Y Z R : B256} (hy : 3 < Y.toNat)
    (hroot : Nat.sqrt Y.toNat ≤ x) (hupper : x ≤ initialGuess Y.toNat)
    (hroom : T.length ≤ 1014) :
    SFunc.RunExactCut cert.prog sevm [74]
      (St b (x.toB256 :: Z :: Y :: R :: T) M (G + 83))
      t_2896_c74 (.at 74 (St b ((next Y.toNat x).toB256 :: x.toB256 :: Y :: R :: T) M G)) := by
  obtain ⟨hi, hp, hsum, _, _⟩ := body_bounds hy (B256.toNat_lt Y) hroot hupper
  have hxb : x < 2 ^ 256 := lt_of_le_of_lt hupper hi
  have hxnat : x.toB256.toNat = x := B256.toNat_toB256_of_lt hxb
  have hxne : x.toB256 ≠ 0 := by
    intro hz
    have hz' := congrArg B256.toNat hz
    rw [hxnat] at hz'
    change x = 0 at hz'
    omega
  have hdiv : Y / x.toB256 = (Y.toNat / x).toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_div hxne, hxnat,
      B256.toNat_toB256_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt Y))]
  have hadd : (Y.toNat / x).toB256 + x.toB256 = (bodySum Y.toNat x).toB256 :=
    toB256_add_toB256 hsum
  have hnext : (bodySum Y.toNat x).toB256 / 2 = (next Y.toNat x).toB256 :=
    toB256_div_two hsum
  unfold t_2896_c74 t_28a4_c74 t_28ad_c74
  apply rxc_dup (w := x.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_swap (S' := Z :: x.toB256 :: x.toB256 :: Y :: R :: T) rfl
  apply rxc_pop
  apply rxc_push (w := 2) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := x.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := x.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := Y) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := x.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x28a4) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_branch_succ hxne
  apply rxc_dest
  apply rxc_div hdiv (by simp only [List.length_cons]; omega)
  apply rxc_add' hadd (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := 2) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x28ad) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_branch_succ (by decide : (2 : B256) ≠ 0)
  apply rxc_dest
  apply rxc_div hnext (by simp only [List.length_cons]; omega)
  apply rxc_swap (S' := x.toB256 :: (next Y.toNat x).toB256 :: x.toB256 :: Y :: R :: T) rfl
  apply rxc_pop
  apply rxc_push (w := 0x288d) (by decide) (by simp only [List.length_cons]; omega)
  exact rxc_jumpCut (List.mem_cons_self)

/-- A true certified header performs precisely one body and back edge. -/
theorem sqrt_header_step_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G x z : Nat} {Y R : B256} (hy : 3 < Y.toNat)
    (hroot : Nat.sqrt Y.toNat ≤ x) (hupper : x ≤ initialGuess Y.toNat)
    (hz : z < 2 ^ 256) (hguard : x < z) (hroom : T.length ≤ 1014) :
    SFunc.RunExactCut cert.prog sevm [74]
      (St b (x.toB256 :: z.toB256 :: Y :: R :: T) M (G + 109))
      t_288d_c74 (.at 74 (St b ((next Y.toNat x).toB256 :: x.toB256 :: Y :: R :: T) M G)) := by
  have hx : x < 2 ^ 256 := lt_trans hguard hz
  have hlt : B256.ltCheck x.toB256 z.toB256 = 1 := by
    rw [B256.ltCheck, ite_eq_left]
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hx,
      B256.toNat_toB256_of_lt hz]
    exact hguard
  unfold t_288d_c74
  apply rxc_dest
  apply rxc_dup (w := z.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := x.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_lt hlt (by simp only [List.length_cons]; omega)
  apply rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x28b5) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_branch_zero
  exact sqrt_body_exact hy hroot hupper hroom

/-- A false certified header discards the next candidate and returns the old one. -/
theorem sqrt_header_exit_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G x z : Nat} {Y R : B256} (hx : x < 2 ^ 256) (hz : z < 2 ^ 256)
    (hguard : z ≤ x) (hroom : T.length ≤ 1014) :
    SFunc.RunExactCut cert.prog sevm [74]
      (St b (x.toB256 :: z.toB256 :: Y :: R :: T) M (G + 57))
      t_288d_c74 (.done (.returned (St b (z.toB256 :: T) M G))) := by
  have hlt : B256.ltCheck x.toB256 z.toB256 = 0 := by
    rw [B256.ltCheck, ite_eq_right]
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hx,
      B256.toNat_toB256_of_lt hz]
    omega
  unfold t_288d_c74 t_28b5_c74
  apply rxc_dest
  apply rxc_dup (w := z.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := x.toB256) rfl (by simp only [List.length_cons]; omega)
  apply rxc_lt hlt (by simp only [List.length_cons]; omega)
  apply rxc_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x28b5) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_branch_succ (by decide : (1 : B256) ≠ 0)
  apply rxc_dest
  apply rxc_pop
  apply rxc_push (w := 0x28c5) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_jump (g := t_28c5_c26) rfl (by decide)
  exact sqrt_return_exact

/-- The large entry initializes half-plus-one without wrap, retaining the first header. -/
theorem sqrt_setup_large_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} {r : Seg} (hy : 3 < Y.toNat) (hroom : T.length ≤ 1014)
    (k : SFunc.RunExactCut cert.prog sevm [74]
      (St b ((initialGuess Y.toNat).toB256 :: Y :: Y :: R :: T) M G) t_288d_c69 r) :
    SFunc.RunExactCut cert.prog sevm [74] (St b (Y :: R :: T) M (G + 51)) t_2878_c69 r := by
  have hgt : B256.gtCheck Y 3 = 1 := by
    have hw : (3 : B256) < Y := B256.lt_iff_toNat_lt_toNat.2 hy
    simp only [B256.gtCheck, ite_eq_left hw]
  obtain ⟨_, _, hi⟩ := initialGuess_bounds hy
  have hdiv : Y / 2 = (Y.toNat / 2).toB256 := by
    calc
      Y / 2 = Y.toNat.toB256 / 2 := congrArg (fun w : B256 => w / 2) (toB256_toNat Y).symm
      _ = (Y.toNat / 2).toB256 := toB256_div_two (B256.toNat_lt Y)
  have hadd : (Y.toNat / 2).toB256 + 1 = (initialGuess Y.toNat).toB256 := by
    change (Y.toNat / 2).toB256 + (1 : Nat).toB256 = _
    exact toB256_add_toB256 (lt_trans hi (B256.toNat_lt Y))
  unfold t_2878_c69 t_2884_c69
  apply rxc_dest
  apply rxc_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 3) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := Y) rfl (by simp only [List.length_cons]; omega)
  apply rxc_binary (fn := B256.gtCheck) (c := 3) (by rintro ⟨⟩) (fun _ => rfl) hgt
    (by simp only [List.length_cons]; omega)
  apply rxc_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 0x28bb) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_branch_zero
  apply rxc_pop
  apply rxc_dup (w := Y) rfl (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_push (w := 2) (by decide) (by simp only [List.length_cons]; omega)
  apply rxc_dup (w := Y) rfl (by simp only [List.length_cons]; omega)
  apply rxc_div hdiv (by simp only [List.length_cons]; omega)
  apply rxc_add' hadd (by simp only [List.length_cons]; omega)
  exact k

/-- Small inputs select the source's zero/nonzero arm before the shared return. -/
theorem sqrt_setup_small_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} {o : Outcome} (hy : Y.toNat ≤ 3) (hroom : T.length ≤ 1014)
    (k : SFunc.RunExact cert.prog sevm (St b (0 :: Y :: R :: T) M G) t_28bb_c69 o) :
    SFunc.RunExact cert.prog sevm (St b (Y :: R :: T) M (G + 29)) t_2878_c69 o := by
  have hw : ¬(3 : B256) < Y := by
    rw [B256.lt_iff_toNat_lt_toNat]
    change ¬3 < Y.toNat
    omega
  have hgt : B256.gtCheck Y 3 = 0 := by simp only [B256.gtCheck, ite_eq_right hw]
  unfold t_2878_c69
  apply rx_dest
  apply rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 3) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_dup (w := Y) rfl (by simp only [List.length_cons]; omega)
  apply rx_gt hgt (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x28bb) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  exact k

/-- The source zero branch costs exactly 66 gas. -/
theorem sqrt_zero_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {R : B256} (hroom : T.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (0 :: R :: T) M (G + 66))
      t_2878_c69 (.returned (St b (0 :: T) M G)) := by
  apply sqrt_setup_small_exact (by decide) hroom
  unfold t_28bb_c69
  apply rx_dest
  apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x28c5) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_branchTo_succ (g := t_28c5_c26) (by decide : (1 : B256) ≠ 0) rfl
  exact SFunc.runExact_iff_runExactCut_nil.mpr sqrt_return_exact

/-- Nonzero small source inputs return one, at exactly 71 gas. -/
theorem sqrt_nonzero_small_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} (hy : Y.toNat ≤ 3) (hne : Y ≠ 0) (hroom : T.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (Y :: R :: T) M (G + 71))
      t_2878_c69 (.returned (St b (1 :: T) M G)) := by
  have hiz : B256.eqCheck Y 0 = 0 := by simp only [B256.eqCheck, ite_eq_right hne]
  apply sqrt_setup_small_exact hy hroom
  unfold t_28bb_c69 t_28c2_c69
  apply rx_dest
  apply rx_dup (w := Y) rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero hiz (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x28c5) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_branchTo_zero
  apply rx_pop
  apply rx_push (w := 1) (by decide) (by simp only [List.length_cons]; omega)
  exact SFunc.runExact_iff_runExactCut_nil.mpr sqrt_return_exact

/-- The repeated certified header uses the existing strict-descent count and loop carrier. -/
theorem sqrt_repeat_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G z : Nat} {Y R : B256} (hy : 3 < Y.toNat)
    (hroot : Nat.sqrt Y.toNat ≤ z) (hupper : z ≤ initialGuess Y.toNat)
    (hroom : T.length ≤ 1014) :
    SFunc.RunExactCut cert.prog sevm []
      (St b ((next Y.toNat z).toB256 :: z.toB256 :: Y :: R :: T) M
        (G + 57 + 109 * iterCount Y.toNat z))
      t_288d_c74 (.done (.returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G))) := by
  let N := iterCount Y.toNat z
  let J : Nat → Devm → Prop := fun i d => ∃ z', Nat.sqrt Y.toNat ≤ z' ∧
    z' ≤ initialGuess Y.toNat ∧ iterCount Y.toNat z' = N - i ∧
    d = St b ((next Y.toNat z').toB256 :: z'.toB256 :: Y :: R :: T) M
      (G + 57 + 109 * (N - i))
  let Q : Seg → Prop := fun r => r = .done (.returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G))
  have hs := (initialGuess_bounds hy).1
  obtain ⟨r, hrun, hresult⟩ := SFunc.RunExactCut.iterate (C := []) (k := 74)
    (g := t_288d_c74) (fs := cert.prog) (sevm := sevm) rfl (by decide) J N Q
    (fun i hi d ⟨z', hr, hu, hc, hd⟩ => by
      have hcpos : 0 < iterCount Y.toNat z' := by omega
      have hguard := (iterCount_pos_iff Y.toNat z').mp hcpos
      obtain ⟨hib, _, _, hnr, hnu⟩ := body_bounds hy (B256.toNat_lt Y) hr hu
      have hzb : z' < 2 ^ 256 := lt_of_le_of_lt hu hib
      have hcount : iterCount Y.toNat (next Y.toNat z') = N - (i + 1) := by
        rw [iterCount_of_descend hguard] at hc
        omega
      have hgas : G + 57 + 109 * (N - i) =
          (G + 57 + 109 * (N - (i + 1))) + 109 := by omega
      refine ⟨St b ((next Y.toNat (next Y.toNat z')).toB256 ::
        (next Y.toNat z').toB256 :: Y :: R :: T) M
        (G + 57 + 109 * (N - (i + 1))), ?_, next Y.toNat z', hnr,
        Nat.le_of_lt hnu, hcount, rfl⟩
      rw [hd, hgas]
      exact sqrt_header_step_exact hy hnr (Nat.le_of_lt hnu) hzb hguard hroom)
    (fun d ⟨z', hr, hu, hc, hd⟩ => by
      have hzpos : 0 < z' := by omega
      have hc0 : iterCount Y.toNat z' = 0 := by omega
      have hzroot := (iterCount_eq_zero_iff_root hzpos hr).mp hc0
      have hguard := (iterCount_eq_zero_iff Y.toNat z').mp hc0
      obtain ⟨hib, _, _, _, hnu⟩ := body_bounds hy (B256.toNat_lt Y) hr hu
      have hzb : z' < 2 ^ 256 := lt_of_le_of_lt hu hib
      have hxb : next Y.toNat z' < 2 ^ 256 := lt_trans hnu hib
      refine ⟨.done (.returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G)), ?_,
        fun _ h => Seg.noConfusion h, rfl⟩
      rw [hd]
      simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
      rw [← hzroot]
      exact sqrt_header_exit_exact hxb hzb (by omega) hroom)
    (St b ((next Y.toNat z).toB256 :: z.toB256 :: Y :: R :: T) M
      (G + 57 + 109 * iterCount Y.toNat z))
    ⟨z, hroot, hupper, by simp only [Nat.sub_zero, N], rfl⟩
  rw [hresult] at hrun
  exact hrun

/-- Large inputs execute the mandatory inlined body before the repeated certified loop. -/
theorem sqrt_large_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} (hy : 3 < Y.toNat) (hroom : T.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (Y :: R :: T) M (G + sqrtCharge Y.toNat))
      t_2878_c69 (.returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G)) := by
  obtain ⟨_, hr, hi⟩ := initialGuess_bounds hy
  have hfirst := sqrt_header_step_exact (sevm := sevm) (G := G + 57 + 109 * iterCount Y.toNat (initialGuess Y.toNat))
    (R := R) (b := b) (M := M) hy hr (Nat.le_refl _) (B256.toNat_lt Y) hi hroom
  rw [toB256_toNat Y, ← sqrt_first_header_eq] at hfirst
  have hprefix := sqrt_setup_large_exact hy hroom hfirst
  have hrest := sqrt_repeat_exact (sevm := sevm) (G := G) (R := R) (b := b) (M := M) hy hr (Nat.le_refl _) hroom
  have hwhole := SFunc.RunExactCut.resume (C := []) (j := 74) (g := t_288d_c74)
    (fs := cert.prog) rfl (by decide) hprefix hrest
  apply SFunc.runExact_iff_runExactCut_nil.mpr
  have hgas : G + sqrtCharge Y.toNat =
      ((G + 57 + 109 * iterCount Y.toNat (initialGuess Y.toNat)) + 109) + 51 := by
    simp only [sqrtCharge, ite_eq_left hy, sourceCount_of_large hy]
    omega
  rw [hgas]
  exact hwhole

/-- Every input word, including arbitrary kLast, has a certified floor-root run at exact gas.
Stack suffix, memory, world metadata and state gas are preserved by the returned St. -/
theorem sqrt_exact {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} (hroom : T.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (Y :: R :: T) M (G + sqrtCharge Y.toNat))
      t_2878_c69 (.returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G)) := by
  by_cases hy : 3 < Y.toNat
  · exact sqrt_large_exact hy hroom
  · by_cases hz : Y = 0
    · subst Y
      exact sqrt_zero_exact hroom
    · have hp := B256.toNat_pos hz
      have hs : Nat.sqrt Y.toNat = 1 := (Nat.eq_sqrt.2 (by constructor <;> omega)).symm
      simp only [sqrtCharge, ite_eq_right hy, ite_eq_right (Nat.ne_of_gt hp), hs]
      exact sqrt_nonzero_small_exact (by omega) hz hroom

/-- Every successful shared return has the exact result stack and unchanged base. -/
theorem sqrt_return_of_run {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {C : List Nat} {Y Z R : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C (St b (Z :: Y :: R :: T) M G) t_28c5_c26 r) :
    ∃ G', r = .done (.returned (St b (Z :: T) M G')) := by
  unfold t_28c5_c26 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := R :: Y :: Z :: T) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := Y :: R :: Z :: T) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop hn
  exact ric_ret run

/-- Successful body inversion reaches the actual back-edge instruction, with proved words. -/
theorem sqrt_body_of_run {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G x : Nat} {C : List Nat} {Y Z R : B256} {r : Seg} (hy : 3 < Y.toNat)
    (hroot : Nat.sqrt Y.toNat ≤ x) (hupper : x ≤ initialGuess Y.toNat)
    (run : SFunc.RunCut cert.prog sevm C (St b (x.toB256 :: Z :: Y :: R :: T) M G) t_2896_c74 r) :
    ∃ G', SFunc.RunCut cert.prog sevm C
      (St b (0x288d :: (next Y.toNat x).toB256 :: x.toB256 :: Y :: R :: T) M G') (.jump 74) r := by
  obtain ⟨hi, hp, hsum, _, _⟩ := body_bounds hy (B256.toNat_lt Y) hroot hupper
  have hxb : x < 2 ^ 256 := lt_of_le_of_lt hupper hi
  have hxnat : x.toB256.toNat = x := B256.toNat_toB256_of_lt hxb
  have hxne : x.toB256 ≠ 0 := by
    intro hz
    have hz' := congrArg B256.toNat hz
    rw [hxnat] at hz'
    change x = 0 at hz'
    omega
  have hdiv : Y / x.toB256 = (Y.toNat / x).toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_div hxne, hxnat,
      B256.toNat_toB256_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt Y))]
  have hadd : (Y.toNat / x).toB256 + x.toB256 = (bodySum Y.toNat x).toB256 :=
    toB256_add_toB256 hsum
  have hnext : (bodySum Y.toNat x).toB256 / 2 = (next Y.toNat x).toB256 :=
    toB256_div_two hsum
  unfold t_2896_c74 t_28a4_c74 t_28ad_c74 at run
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := x.toB256) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := Z :: x.toB256 :: x.toB256 :: Y :: R :: T) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_pop hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push hn
  simp only [show Bytes.toB256 [0x02] = (2 : B256) from by decide] at run
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := x.toB256) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := x.toB256) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := Y) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := x.toB256) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push hn
  rcases ric_branch run with ⟨hz, _, run⟩ | ⟨_, _, run⟩
  · exact (hxne hz).elim
  · obtain ⟨_, run⟩ := ric_dest run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_div hn
    rw [hdiv] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_add hn
    rw [hadd] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_dup (w := 2) rfl hn
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push hn
    rcases ric_branch run with ⟨hz, _, run⟩ | ⟨_, _, run⟩
    · exact (by decide : (2 : B256) ≠ 0) hz |>.elim
    · obtain ⟨_, run⟩ := ric_dest run
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_div hn
      rw [hnext] at run
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_swap (S' := x.toB256 :: (next Y.toNat x).toB256 :: x.toB256 :: Y :: R :: T) rfl hn
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop hn
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push hn
      exact ⟨_, run⟩

/-- Invert the actual header into its body/back-edge or returned old candidate. -/
theorem sqrt_header_of_run {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G x z : Nat} {C : List Nat} {Y R : B256} {r : Seg} (hy : 3 < Y.toNat)
    (hroot : Nat.sqrt Y.toNat ≤ x) (hupper : x ≤ initialGuess Y.toNat)
    (hz : z < 2 ^ 256) (h26 : 26 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (x.toB256 :: z.toB256 :: Y :: R :: T) M G) t_288d_c74 r) :
    (x < z ∧ ∃ G', SFunc.RunCut cert.prog sevm C
      (St b (0x288d :: (next Y.toNat x).toB256 :: x.toB256 :: Y :: R :: T) M G') (.jump 74) r) ∨
      (z ≤ x ∧ ∃ G', r = .done (.returned (St b (z.toB256 :: T) M G'))) := by
  have hx : x < 2 ^ 256 := lt_of_le_of_lt hupper
    (body_bounds hy (B256.toNat_lt Y) hroot hupper).1
  have hlt : B256.ltCheck x.toB256 z.toB256 = if x < z then 1 else 0 := by
    simp only [B256.ltCheck, B256.lt_iff_toNat_lt_toNat,
      B256.toNat_toB256_of_lt hx, B256.toNat_toB256_of_lt hz]
  unfold t_288d_c74 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := z.toB256) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := x.toB256) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_lt hn
  rw [hlt] at run
  by_cases hg : x < z
  · simp only [ite_eq_left hg] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_iszero hn
    simp only [show B256.eqCheck 1 0 = (0 : B256) from by decide] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push hn
    rcases ric_branch run with ⟨_, _, run⟩ | ⟨hne, _, run⟩
    · exact .inl ⟨hg, sqrt_body_of_run hy hroot hupper run⟩
    · exact (hne rfl).elim
  · simp only [ite_eq_right hg] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_iszero hn
    simp only [show B256.eqCheck 0 0 = (1 : B256) from by decide] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push hn
    rcases ric_branch run with ⟨hz0, _, run⟩ | ⟨_, _, run⟩
    · exact (by decide : (1 : B256) ≠ 0) hz0 |>.elim
    · unfold t_28b5_c74 at run
      obtain ⟨_, run⟩ := ric_dest run
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop hn
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_push hn
      obtain ⟨_, run⟩ := ric_jump (g := t_28c5_c26) h26 rfl run
      exact .inr ⟨by omega, sqrt_return_of_run run⟩

/-- Successful runs of the repeated certified loop return the root for arbitrary initial gas. -/
theorem sqrt_repeat_of_run {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G z : Nat} {Y R : B256} {o : Outcome} (hy : 3 < Y.toNat)
    (hroot : Nat.sqrt Y.toNat ≤ z) (hupper : z ≤ initialGuess Y.toNat)
    (run : SFunc.Run cert.prog sevm
      (St b ((next Y.toNat z).toB256 :: z.toB256 :: Y :: R :: T) M G) t_288d_c74 o) :
    ∃ G', o = .returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G') := by
  let I : Devm → Prop := fun d => ∃ z' G', Nat.sqrt Y.toNat ≤ z' ∧
    z' ≤ initialGuess Y.toNat ∧
    d = St b ((next Y.toNat z').toB256 :: z'.toB256 :: Y :: R :: T) M G'
  let Q : Outcome → Prop := fun o => ∃ G', o = .returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G')
  have hs := (initialGuess_bounds hy).1
  apply SFunc.RunP.loop (P := Ninst.Run) (fs := cert.prog) (k := 74) (g := t_288d_c74)
    rfl I Q _ _ o ⟨z, G, hroot, hupper, rfl⟩ run
  intro d hI r hrun
  obtain ⟨z', G', hr, hu, rfl⟩ := hI
  obtain ⟨hib, hp, _, hnr, hnu⟩ := body_bounds hy (B256.toNat_lt Y) hr hu
  have hzb : z' < 2 ^ 256 := lt_of_le_of_lt hu hib
  rcases sqrt_header_of_run hy hnr (Nat.le_of_lt hnu) hzb (by decide : 26 ∉ [74]) hrun with
    ⟨_, G'', hjump⟩ | ⟨hg, G'', heq⟩
  · obtain ⟨G3, heq⟩ := ric_jumpCut (List.mem_cons_self) hjump
    rw [heq]
    exact ⟨next Y.toNat z', G3, hnr, Nat.le_of_lt hnu, rfl⟩
  · have hzroot : z' = Nat.sqrt Y.toNat := by
      have hstop : ¬next Y.toNat z' < z' := by omega
      have hcount := iterCount_of_stop hstop
      exact (iterCount_eq_zero_iff_root hp hr).mp hcount
    rw [heq]
    exact ⟨G'', by rw [hzroot]⟩

/-- Successful entry inversion selects the actual large setup or small-source continuation. -/
theorem sqrt_entry_of_run {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm [] (St b (Y :: R :: T) M G) t_2878_c69 r) :
    (3 < Y.toNat ∧ ∃ G', SFunc.RunCut cert.prog sevm []
      (St b ((initialGuess Y.toNat).toB256 :: Y :: Y :: R :: T) M G') t_288d_c69 r) ∨
      (Y.toNat ≤ 3 ∧ ∃ G', SFunc.RunCut cert.prog sevm []
        (St b (0 :: Y :: R :: T) M G') t_28bb_c69 r) := by
  have hgt : B256.gtCheck Y 3 = if 3 < Y.toNat then 1 else 0 := by
    simp only [B256.gtCheck, B256.lt_iff_toNat_lt_toNat, show (3 : B256).toNat = 3 from rfl]
  unfold t_2878_c69 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_push hn)
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val (w := 3) (by decide) (ri_push hn)
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := Y) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_val hgt (ri_gt hn)
  by_cases hy : 3 < Y.toNat
  · simp only [ite_eq_left hy] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_iszero hn)
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push hn
    rcases ric_branch run with ⟨_, _, run⟩ | ⟨hne, _, run⟩
    · have hi := (initialGuess_bounds hy).2.2
      have hdiv : Y / 2 = (Y.toNat / 2).toB256 := by
        calc
          Y / 2 = Y.toNat.toB256 / 2 := congrArg (fun w : B256 => w / 2) (toB256_toNat Y).symm
          _ = (Y.toNat / 2).toB256 := toB256_div_two (B256.toNat_lt Y)
      have hadd : (Y.toNat / 2).toB256 + 1 = (initialGuess Y.toNat).toB256 := by
        change (Y.toNat / 2).toB256 + (1 : Nat).toB256 = _
        exact toB256_add_toB256 (lt_trans hi (B256.toNat_lt Y))
      unfold t_2884_c69 at run
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop hn
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_dup (w := Y) rfl hn
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by decide) (ri_push hn)
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_val (w := 2) (by decide) (ri_push hn)
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_dup (w := Y) rfl hn
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_val hdiv (ri_div hn)
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_val hadd (ri_add hn)
      exact .inl ⟨hy, _, run⟩
    · exact (hne rfl).elim
  · simp only [ite_eq_right hy] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_val (w := 1) (by decide) (ri_iszero hn)
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push hn
    rcases ric_branch run with ⟨hz0, _, run⟩ | ⟨_, _, run⟩
    · exact (by decide : (1 : B256) ≠ 0) hz0 |>.elim
    · exact .inr ⟨by omega, _, run⟩

/-- The actual small continuation returns zero for zero and one otherwise. -/
theorem sqrt_small_of_run {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm [] (St b (0 :: Y :: R :: T) M G) t_28bb_c69 r) :
    ∃ G', r = .done (.returned (St b ((if Y = 0 then 0 else 1) :: T) M G')) := by
  unfold t_28bb_c69 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup (w := Y) rfl hn
  obtain ⟨d, hn, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero hn
  by_cases hy : Y = 0
  · subst Y
    simp only [show B256.eqCheck 0 0 = (1 : B256) from by decide] at run
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push hn
    cases run with
    | toZero d hp run =>
      have heq := (St.of_pop2 hp).2.1
      exact (by decide : (1 : B256) ≠ 0) heq |>.elim
    | toSuccCut d w hn hk hp => cases hk
    | toSucc d w hn hk hget hp run =>
      have hget26 : cert.prog[26]? = some t_28c5_c26 := rfl
      rw [hget26] at hget
      cases hget
      obtain ⟨_, _, heq⟩ := St.of_pop2 hp
      rw [heq] at run
      exact sqrt_return_of_run run
  · have hiz : B256.eqCheck Y 0 = 0 := by simp only [B256.eqCheck, ite_eq_right hy]
    rw [hiz] at run
    simp only [ite_eq_right hy]
    obtain ⟨d, hn, run⟩ := ric_next run
    obtain ⟨_, rfl⟩ := ri_push hn
    cases run with
    | toZero d hp run =>
      obtain ⟨_, _, heq⟩ := St.of_pop2 hp
      rw [heq] at run
      unfold t_28c2_c69 at run
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_pop hn
      obtain ⟨d, hn, run⟩ := ric_next run
      obtain ⟨_, rfl⟩ := ri_val (w := 1) (by decide) (ri_push hn)
      exact sqrt_return_of_run run
    | toSuccCut d w hn hk hp => cases hk
    | toSucc d w hn hk hget hp run =>
      have heq := (St.of_pop2 hp).2.1
      exact (hn heq.symm).elim

/-- Every already-successful certified internal sqrt run returns the floor root,
with its stack suffix, memory and all base world/metadata fields unchanged. -/
theorem sqrt_of_run {sevm : Sevm} {b : Devm} {T : List B256} {M : Mem}
    {G : Nat} {Y R : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm (St b (Y :: R :: T) M G) t_2878_c69 o) :
    ∃ G', o = .returned (St b ((Nat.sqrt Y.toNat).toB256 :: T) M G') := by
  have hcut := SFunc.runP_iff_runCutP_nil.mp run
  rcases sqrt_entry_of_run hcut with ⟨hy, G1, hlarge⟩ | ⟨hy, G1, hsmall⟩
  · obtain ⟨_, hr, hi⟩ := initialGuess_bounds hy
    rw [sqrt_first_header_eq] at hlarge
    have hlarge' : SFunc.RunCut cert.prog sevm []
        (St b ((initialGuess Y.toNat).toB256 :: Y.toNat.toB256 :: Y :: R :: T) M G1)
        t_288d_c74 (.done o) := by simpa only [toB256_toNat] using hlarge
    rcases sqrt_header_of_run hy hr (Nat.le_refl _) (B256.toNat_lt Y) (by decide : 26 ∉ []) hlarge' with
      ⟨_, G2, hjump⟩ | ⟨hg, _⟩
    · obtain ⟨_, hrepeat⟩ := ric_jump (g := t_288d_c74) (by decide : 74 ∉ []) rfl hjump
      exact sqrt_repeat_of_run hy hr (Nat.le_refl _) (SFunc.runP_iff_runCutP_nil.mpr hrepeat)
    · omega
  · obtain ⟨G2, heq⟩ := sqrt_small_of_run hsmall
    have hs : (if Y = 0 then 0 else 1) = (Nat.sqrt Y.toNat).toB256 := by
      by_cases hz : Y = 0
      · subst Y
        rfl
      · have hp := B256.toNat_pos hz
        have hr : Nat.sqrt Y.toNat = 1 := (Nat.eq_sqrt.2 (by constructor <;> omega)).symm
        simp only [ite_eq_right hz, hr]
        rfl
    rw [hs] at heq
    exact ⟨G2, Seg.done.inj heq⟩

end Blanc.Lift.UniswapV2Pair
