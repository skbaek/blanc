import Blanc.Lift.Curve3Pool.Walk.AlLiveHead
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityPull2

/-!
# `add_liquidity`, forward: the pull loop's credit and loop test

`alCredit` is the path skeleton of `0x12d6` → the loop test at `0x1332` (`new_balances[i] =
old_balances[i] + in_amount`, checked; `i += 1`), its final jump a parameter; every context's
credit tree is an instance. `rx_al_credit` runs it forward.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def alCredit (a1 : SFunc) (a2 : SFunc) (a3 : SFunc) (a4 : SFunc) : SFunc :=
  (.dest (.next (.push [0x03, 0x00] (by decide)) (.next (.push [0x04, 0xc0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x12, 0xea] (by decide)) (.branch a1 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mload) (.next (.push [0x04, 0xe0] (by decide)) (.next (.reg .mload) (.next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3)) (.next (.reg .add) (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [0x13, 0x02] (by decide)) (.branch a2 (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.push [0x04, 0x60] (by decide)) (.next (.push [0x04, 0xc0] (by decide)) (.next (.reg .mload) (.next (.push [0x03] (by decide)) (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [0x13, 0x1d] (by decide)) (.branch a3 (.dest (.next (.push [0x20] (by decide)) (.next (.reg .mul) (.next (.reg .add) (.next (.reg .mstore) (.dest (.next (.reg (.dup 1)) (.next (.reg .mload) (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.reg (.dup 0)) (.next (.reg (.dup 3)) (.next (.reg .mstore) (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.reg .iszero) (.next (.push [0x10, 0x5d] (by decide)) a4)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
theorem t_12d6_c4_eq : t_12d6_c4 = alCredit .undefined t_12fe_c4 .undefined ((.branchTo .undefined 40)) := rfl
theorem t_12d6_c40_eq : t_12d6_c40 = alCredit .undefined t_12fe_c40 .undefined ((.branchTo .undefined 66)) := rfl
theorem t_12d6_c41_eq : t_12d6_c41 = alCredit t_12e6_c41 t_12fe_c41 t_1319_c41 ((.branchTo t_1333_c41 41)) := rfl
theorem t_12d6_c66_eq : t_12d6_c66 = alCredit .undefined t_12fe_c66 .undefined ((.branch t_1333_c66 .undefined)) := rfl
theorem t_12d6_c6_eq : t_12d6_c6 = alCredit t_12e6_c6 t_12fe_c6 t_1319_c6 ((.branchTo t_1333_c6 41)) := rfl

/-- The memory after a credit: `new_balances[i]` at `0x460 + 32 i`, the counter `i + 1`. -/
def alCreditMem (M : Mem) (i : Nat) (x : B256) : Mem :=
  (M.write (0x460 + 32 * i) x.toBytes).write 0x4c0 (Nat.toB256 (i + 1)).toBytes

/-- `rx_al_credit`, the continuation also receiving its memory as a term and its exact gas. -/
theorem rx_al_creditE {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G R i : Nat} {Q : Outcome → Prop} {v F AF A T D0 : B256} {old nv : Nat → B256}
    {a1 a2 a3 fin : SFunc}
    (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) {s : Nat} (hsz : M.size = s)
    (hs : 0x520 ≤ s) (hs32 : s % 32 = 0)
    (hm : AlPullImg img i F AF A T D0 old nv) (hv : WordAt img 0x4e0 v)
    (hadd : ¬ old i + v < old i) (hG : 200 + R ≤ G) (hroom : S.length + 12 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = s →
      AlPullImg img' (i + 1) F AF A T D0 old (Function.update nv i (old i + v)) →
      WordAt img' 0x4e0 v → R ≤ g → g ≤ G → G = g + 184 → M' = alCreditMem M i (old i + v) →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x10, 0x5d] ::
        B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: 0x4c0 :: S) M' g) fin Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alCredit a1 a2 a3 fin) Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 150 + 34 := ⟨G - 184, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.ctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x300 + 32 * i) (v := old i) hR hsz (al_off hi 0x300 (by decide) _ (by decide)) ⟨by omega, hs32⟩ (by wautoH (hm.m0.old hi)) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4e0) (v := v) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hv) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by rw [ltCheck_eq_zero_of_le (by rw [← B256.le_iff_toNat_le_toNat]; exact not_lt.mp hadd)]; decide) ·)
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.ctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ltCheck_ne_zero_of_lt (lt_three hi)) ·)
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreKL (o := 0x460 + 32 * i) hR hW hsz (al_off hi 0x460 (by decide) _ (by decide)) ⟨by omega, hs32⟩ ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x4c0) (v := Nat.toB256 i) hR hsz rfl ⟨by omega, hs32⟩ (by wautoH hm.ctr) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreKL (o := 0x4c0) hR hW hsz rfl ⟨by omega, hs32⟩ ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  rw [succ_lit hi] at hR ⊢
  refine k M _ g1 hR hW hsz ?_ (by wauto) (by omega) (by omega) (by omega)
    (by rw [hMq2, hMq1, succ_lit hi]; rfl)
  refine ⟨(hm.m0.keep (by simp only [B256.length_toBytes]; omega)).keep
    (by simp only [B256.length_toBytes]; omega), WordAt.write_self _ _ _, ?_, ?_, ?_⟩ <;>
  refine WordAt.write_other ?_ (by simp only [B256.length_toBytes]; omega)
  · by_cases e : i = 0
    · subst e; rw [Function.update_self]; exact WordAt.write_self _ _ _
    · rw [Function.update_of_ne (Ne.symm e)]
      exact hm.n0.write_other (by simp only [B256.length_toBytes]; omega)
  · by_cases e : i = 1
    · subst e; rw [Function.update_self]; exact WordAt.write_self _ _ _
    · rw [Function.update_of_ne (Ne.symm e)]
      exact hm.n1.write_other (by simp only [B256.length_toBytes]; omega)
  · by_cases e : i = 2
    · subst e; rw [Function.update_self]; exact WordAt.write_self _ _ _
    · rw [Function.update_of_ne (Ne.symm e)]
      exact hm.n2.write_other (by simp only [B256.length_toBytes]; omega)

/-- **The credit and the counter, forward.** -/
theorem rx_al_credit {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {img : Bytes}
    {G R i : Nat} {Q : Outcome → Prop} {v F AF A T D0 : B256} {old nv : Nat → B256}
    {a1 a2 a3 fin : SFunc}
    (hi : i < 3) (hR : Mem.Reads M img) (hW : Mem.Wf M) {s : Nat} (hsz : M.size = s)
    (hs : 0x520 ≤ s) (hs32 : s % 32 = 0)
    (hm : AlPullImg img i F AF A T D0 old nv) (hv : WordAt img 0x4e0 v)
    (hadd : ¬ old i + v < old i) (hG : 200 + R ≤ G) (hroom : S.length + 12 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = s →
      AlPullImg img' (i + 1) F AF A T D0 old (Function.update nv i (old i + v)) →
      WordAt img' 0x4e0 v → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b (Bytes.toB256 [0x10, 0x5d] ::
        B256.eqCheck (B256.eqCheck 3 (Nat.toB256 (i + 1))) 0 :: 3 :: 0x4c0 :: S) M' g) fin Q) :
    SFunc.RunEx cert.prog sevm (St b (3 :: 0x4c0 :: S) M G) (alCredit a1 a2 a3 fin) Q :=
  rx_al_creditE hi hR hW hsz hs hs32 hm hv hadd hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 _ _ => k M' img' g h1 h2 h3 h4 h5 h6 h7

end Blanc.Lift.Curve3Pool
