import Blanc.Lift.BabylonianSqrt
import Blanc.Lift.ExactWalkCutOps
import Blanc.Lift.InvWalkOps
import Blanc.Lift.UniswapV2Pair.Cert

/-! Certified Babylonian square-root routine: entries 69, 74 and 26. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune
open Blanc.BabylonianSqrt

/-- Exact source body count, including the mandatory inlined first body. -/
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

end Blanc.Lift.UniswapV2Pair
