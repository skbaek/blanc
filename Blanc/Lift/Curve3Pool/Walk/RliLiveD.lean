import Blanc.Lift.Curve3Pool.Walk.RliLiveFront
import Blanc.Lift.Curve3Pool.Callee.GetDMemGrow
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalancePush

/-!
# `remove_liquidity_imbalance`, forward: `D0` and `new_balances`

`rx_rli_d0` (`t_31b7_c0` → the second frame save `t_32c1_c572`): the save of
`[0x140, 0x360)`, `D0 = get_D_mem(old_balances, amp)` (`getDMem_exact_400`: the memory grows
from `0x400` to `0x520`), the restore, `D0` at `0x340`, and the loop of line 538:
`new_balances[k] = old_balances[k] - amounts[k]` (checked) at `0x2e0 … 0x320`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

def rliIdx1 : List Nat := [35, 60, 87, 109, 130, 152, 174, 194, 212, 226, 240, 255, 270, 285, 300,
  315]

def rliIdx2 : List Nat := [330, 345, 360, 375, 390, 405, 419, 433, 447, 461, 475, 491, 505, 519,
  535, 548]

theorem rli_sv1_first :
    t_31b7_c0 = svIt 0x03 0x60 0x31 0xd9 (lpBr 16 rliIdx1 0x31 0xb7 t_31d9_c315 0) := rfl

theorem rli_sv1_chain : ∀ n, n < 16 → cert.prog[rliIdx1.getD n 0]? =
    some (svIt 0x03 0x60 0x31 0xd9 (lpBr 16 rliIdx1 0x31 0xb7 t_31d9_c315 (n + 1))) := by
  decide +kernel

theorem rli_rs1_first :
    t_3226_c315 = rsIt 0x03 0x60 0x32 0x49 (lpBr 16 rliIdx2 0x32 0x26 t_3249_c548 0) := rfl

theorem rli_rs1_chain : ∀ n, n < 16 → cert.prog[rliIdx2.getD n 0]? =
    some (rsIt 0x03 0x60 0x32 0x49 (lpBr 16 rliIdx2 0x32 0x26 t_3249_c548 (n + 1))) := by
  decide +kernel

theorem rli_prog_29 : cert.prog[29]? = some t_07b7_c29 := t_07b7_c29_prog

theorem rli_prog_561 : cert.prog[561]? = some t_325d_c561 := by decide +kernel

theorem rli_prog_572 : cert.prog[572]? = some t_325d_c572 := by decide +kernel

/-- **`D0`'s memory, exact**, up to bytes: the save of `[0x140, 0x360)` (counter at `0x360`),
`get_D_mem`'s arguments at `0x380 … 0x3e0`, `get_D_mem`'s memory (`getDMemNext`), `D0` parked
at `0x440`, the restore counter, the restore, `D0` at `0x340`, and the loop of line 538: the
counter at `0x460` and `new_balances` at `0x2e0 … 0x320`, then the next save counter at
`0x4a0`. -/
def rliD0Mem (sevm : Sevm) (M : Mem) (b0 b1 b2 Aw : B256) (x : V3) (v : Nat) : Mem :=
  let M5 := ((((saveMem M 0x360 (0x140 + 32 * 0) (16 + 1)).write 0x380 b0.toBytes).write 0x3a0
    b1.toBytes).write 0x3c0 b2.toBytes).write 0x3e0 Aw.toBytes
  let M7 := ((getDMemNext M5 (Nat.toB256 (0x3214 + 6)) b0 b1 b2 Aw x v).write 0x440
    (Nat.toB256 v).toBytes).write 0x360 (Bytes.toB256 [3, 64]).toBytes
  (((((((((restoreMem 0x360 M7 (0x140 + 32 * 16) (exSaved (memWord M) 0x140 (16 + 1))).write
    0x340 (Nat.toB256 v).toBytes).write 0x460 (Bytes.toB256 [0]).toBytes).write 0x2e0
    (b0 - Sevm.dataWord sevm (Bytes.toB256 [32] * Bytes.toB256 [0] + Bytes.toB256 [4])).toBytes).write
    0x460 (Bytes.toB256 [1] + Bytes.toB256 [0]).toBytes).write 0x300
    (b1 - Sevm.dataWord sevm (Bytes.toB256 [32] * (Bytes.toB256 [1] + Bytes.toB256 [0]) +
      Bytes.toB256 [4])).toBytes).write 0x460
    (Bytes.toB256 [1] + (Bytes.toB256 [1] + Bytes.toB256 [0])).toBytes).write 0x320
    (b2 - Sevm.dataWord sevm (Bytes.toB256 [32] * (Bytes.toB256 [1] + (Bytes.toB256 [1] +
      Bytes.toB256 [0])) + Bytes.toB256 [4])).toBytes).write 0x460
    (Bytes.toB256 [1] + (Bytes.toB256 [1] + (Bytes.toB256 [1] + Bytes.toB256 [0]))).toBytes).write
    0x4a0
    (Bytes.toB256 [1, 64]).toBytes

/-- **`D0` and `new_balances`, forward, exact** (core of `rx_rli_d0`). -/
theorem rx_rli_d0E {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R v : Nat} {Q : Outcome → Prop} {x : V3} {T F AF Aw b0 b1 b2 : B256}
    (hX : xpChk ⟨b0.toNat, b1.toNat, b2.toNat⟩ = some x)
    (hres : getDChk x.get Aw.toNat 1 = some v)
    (hu0 : ¬ b0 < rliAmt sevm 0) (hu1 : ¬ b1 < rliAmt sevm 1) (hu2 : ¬ b2 < rliAmt sevm 2)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x380)
    (hctr : WordAt img 0x360 (Nat.toB256 0x140)) (hT : WordAt img 0x140 T)
    (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw)
    (hb0 : WordAt img 0x280 b0) (hb1 : WordAt img 0x2a0 b1) (hb2 : WordAt img 0x2c0 b2)
    (hc0 : WordAt img 0x2e0 b0) (hc1 : WordAt img 0x300 b1) (hc2 : WordAt img 0x320 b2)
    (hG : costGetDMem x Aw.toNat + 5000 + R ≤ G) (hroom : S.length + 90 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x520 → WordAt img' 0x140 T → WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x280 b0 → WordAt img' 0x2a0 b1 →
      WordAt img' 0x2c0 b2 → WordAt img' 0x2e0 (b0 - rliAmt sevm 0) →
      WordAt img' 0x300 (b1 - rliAmt sevm 1) → WordAt img' 0x320 (b2 - rliAmt sevm 2) →
      WordAt img' 0x340 (Nat.toB256 v) → WordAt img' 0x4a0 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      G = g + (3117 + costGetDMem x Aw.toNat) →
      Mem.EqExcept M' (rliD0Mem sevm M b0 b1 b2 Aw x v) (fun _ => False) →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_32c1_c572 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_31b7_c0 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 1822 + costGetDMem x Aw.toNat + 28 + 19 + 120 +
      (67 * 16 + 56) := ⟨G - costGetDMem x Aw.toNat - 3117, by omega⟩
  have hR0 := hR
  rw [rli_sv1_first]
  refine rx_svFromM (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x360) (sz := 0x380)
    (by decide) rfl (by decide) (by decide) rli_sv1_chain 16 (n := 0) rfl hR hW hsz hctr
    (fun m _ _ => wordAt_self _ _) (by omega) ?_
  clear hR hW hsz
  intro M1 img1 hMsv hR hW hsz hk1 hct1
  -- the arguments of `get_D_mem`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x280) (v := b0) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hb0 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x380) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq1; intro M hMq1 hR hW hsz; rw [show memExtSize 0x380 0x380 32 = 0x3a0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2a0) (v := b1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hb1 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x3a0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq2; intro M hMq2 hR hW hsz; rw [show memExtSize 0x3a0 0x3a0 32 = 0x3c0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mloadW (o := 0x2c0) (v := b2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hb2 (.inl (by decide)))) (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x3c0) (c := 6) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq3; intro M hMq3 hR hW hsz; rw [show memExtSize 0x3c0 0x3c0 32 = 0x3e0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x220) (v := Aw) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH (hk1 _ _ hAw (.inl (by decide)))) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x3e0) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq4; intro M hMq4 hR hW hsz; rw [show memExtSize 0x3e0 0x3e0 32 = 0x400 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3e0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3c0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x3a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x380) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  obtain ⟨M2, hrun, ⟨-, hW2, hsz2⟩, hEq2⟩ := getDMem_exact_400L (G := g1 + 1822) (ρ := Nat.toB256 (0x3214 + 6))
    (S := exSaved (fun o => Bytes.toB256 (img.sliceD o 32 0)) (0x140 + 32 * 0) (16 + 1) ++ S)
    (M := M) hX hres hW hsz (by simp only [List.length_append, exSaved_length]; omega)
  refine rxe_pcCall rli_prog_29 (by decide)
    (by simp only [List.length_cons, List.length_append, exSaved_length]; omega) hrun ?_
  clear hR hW hsz hrun
  have hR := Mem.reads_data M2
  have hW := hW2
  have hsz := hsz2
  clear hW2 hsz2
  -- `D0` parked, the restore counter
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x440) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq5; intro M hMq5 hR hW hsz; rw [show memExtSize 0x520 0x440 32 = 0x520 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x360) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq6; intro M hMq6 hR hW hsz; rw [show memExtSize 0x520 0x360 32 = 0x520 by decide] at hsz
  rw [rli_rs1_first]
  refine rx_rsFromM (fun o => Bytes.toB256 (img.sliceD o 32 0)) (C := 0x360) (sz := 0x520)
    (by decide) rfl (by decide) (by decide) rli_rs1_chain 16 (n := 0) rfl hR hW hsz
    (by wauto) (by hrs) ?_
  intro M3 img3 hMrs hR3 hW3 hsz3 hm3 hk3
  have hD3 : WordAt img3 0x440 (Nat.toB256 v) := hk3 _ _ (by wauto) (.inr (.inr (by decide)))
  have rT := cw_restored (hm3 0 (by omega)) hT
  have rF := cw_restored (hm3 5 (by omega)) hF
  have rAF := cw_restored (hm3 6 (by omega)) hAF
  have rAw := cw_restored (hm3 7 (by omega)) hAw
  have rb0 := cw_restored (hm3 10 (by omega)) hb0
  have rb1 := cw_restored (hm3 11 (by omega)) hb1
  have rb2 := cw_restored (hm3 12 (by omega)) hb2
  have rc0 := cw_restored (hm3 13 (by omega)) hc0
  have rc1 := cw_restored (hm3 14 (by omega)) hc1
  have rc2 := cw_restored (hm3 15 (by omega)) hc2
  clear hR hW hsz hk3
  have hR := hR3; have hW := hW3; have hsz := hsz3
  clear hR3 hW3 hsz3
  -- `new_balances`
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x440) (v := Nat.toB256 v) hR hsz rfl ⟨by decide, by decide⟩ (by wautoH hD3) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x340) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq7; intro M hMq7 hR hW hsz; rw [show memExtSize 0x520 0x340 32 = 0x520 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq8; intro M hMq8 hR hW hsz; rw [show memExtSize 0x520 0x460 32 = 0x520 by decide] at hsz
  xr (rx_add (by hrs) ·)
  -- tree t_325d_c548
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_3271_c548
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x2e0) (v := b0) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH rc0) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_328a_c548
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hu0) ·)
  -- tree t_329c_c548
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x2e0) (c := 3) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq9; intro M hMq9 hR hW hsz; rw [show memExtSize 0x520 0x2e0 32 = 0x520 by decide] at hsz
  xr (rx_pop ·)
  -- tree t_32a7_c548
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq10; intro M hMq10 hR hW hsz; rw [show memExtSize 0x520 0x460 32 = 0x520 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branchTo_succ (by xbr) (g := t_325d_c561) rli_prog_561 ·)
  -- tree t_325d_c561
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_3271_c561
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x300) (v := b1) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH rc1) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_328a_c561
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hu1) ·)
  -- tree t_329c_c561
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x300) (c := 3) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq11; intro M hMq11 hR hW hsz; rw [show memExtSize 0x520 0x300 32 = 0x520 by decide] at hsz
  xr (rx_pop ·)
  -- tree t_32a7_c561
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq12; intro M hMq12 hR hW hsz; rw [show memExtSize 0x520 0x460 32 = 0x520 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branchTo_succ (by xbr) (g := t_325d_c572) rli_prog_572 ·)
  -- tree t_325d_c572
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_3271_c572
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mloadW (o := 0x320) (v := b2) hR hsz (cw_off (by decide) (by decide)) ⟨by decide, by decide⟩ (by wautoH rc2) (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (by xbr) ·)
  -- tree t_328a_c572
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_mul rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_lt rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_succ (ex_geGuard hu2) ·)
  -- tree t_329c_c572
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_sub (by hrs) ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_swap1 ·)
  xr (rx_pop ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x320) (c := 3) hR hW hsz (cw_off (by decide) (by decide)) (by decide) ?_; clear hR hW hsz; rename' M => Mq13; intro M hMq13 hR hW hsz; rw [show memExtSize 0x520 0x320 32 = 0x520 by decide] at hsz
  xr (rx_pop ·)
  -- tree t_32a7_c572
  xr (rx_dest ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x460) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x460) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq14; intro M hMq14 hR hW hsz; rw [show memExtSize 0x520 0x460 32 = 0x520 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_eq rfl (by hrs) ·)
  xr (rx_iszero rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_branch_zero' (by xbr0) ·)
  -- tree t_32b7_c572
  xr (rx_dest ·)
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x4a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; rename' M => Mq15; intro M hMq15 hR hW hsz; rw [show memExtSize 0x520 0x4a0 32 = 0x520 by decide] at hsz
  refine k M _ g1 hR hW hsz (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto)
    (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by wauto) (by omega) (by omega)
    (by omega) ?_
  rw [slice_memWord_fun hR0] at hMrs
  clear hR hW hsz k
  rw [hMq15, hMq14, hMq13, hMq12, hMq11, hMq10, hMq9, hMq8, hMq7, hMrs, hMq6, hMq5]
  rw [hMq4, hMq3, hMq2, hMq1, hMsv] at hEq2
  unfold rliD0Mem
  refine eqB_write (eqB_write (eqB_write (eqB_write (eqB_write (eqB_write (eqB_write (eqB_write
    (eqB_write ?_ _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _
  exact ((eqB_write (eqB_write hEq2 _ _) _ _).restoreMem 0x360 _).mono fun _ hi => hi.1
/-- **`D0` and `new_balances`, forward.** -/
theorem rx_rli_d0 {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {img : Bytes} {G R v : Nat} {Q : Outcome → Prop} {x : V3} {T F AF Aw b0 b1 b2 : B256}
    (hX : xpChk ⟨b0.toNat, b1.toNat, b2.toNat⟩ = some x)
    (hres : getDChk x.get Aw.toNat 1 = some v)
    (hu0 : ¬ b0 < rliAmt sevm 0) (hu1 : ¬ b1 < rliAmt sevm 1) (hu2 : ¬ b2 < rliAmt sevm 2)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x380)
    (hctr : WordAt img 0x360 (Nat.toB256 0x140)) (hT : WordAt img 0x140 T)
    (hF : WordAt img 0x1e0 F) (hAF : WordAt img 0x200 AF) (hAw : WordAt img 0x220 Aw)
    (hb0 : WordAt img 0x280 b0) (hb1 : WordAt img 0x2a0 b1) (hb2 : WordAt img 0x2c0 b2)
    (hc0 : WordAt img 0x2e0 b0) (hc1 : WordAt img 0x300 b1) (hc2 : WordAt img 0x320 b2)
    (hG : costGetDMem x Aw.toNat + 5000 + R ≤ G) (hroom : S.length + 90 < 1024)
    (k : ∀ (M' : Mem) (img' : Bytes) (g : Nat), Mem.Reads M' img' → Mem.Wf M' →
      M'.size = 0x520 → WordAt img' 0x140 T → WordAt img' 0x1e0 F → WordAt img' 0x200 AF →
      WordAt img' 0x220 Aw → WordAt img' 0x280 b0 → WordAt img' 0x2a0 b1 →
      WordAt img' 0x2c0 b2 → WordAt img' 0x2e0 (b0 - rliAmt sevm 0) →
      WordAt img' 0x300 (b1 - rliAmt sevm 1) → WordAt img' 0x320 (b2 - rliAmt sevm 2) →
      WordAt img' 0x340 (Nat.toB256 v) → WordAt img' 0x4a0 (Nat.toB256 0x140) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b S M' g) t_32c1_c572 Q) :
    SFunc.RunEx cert.prog sevm (St b S M G) t_31b7_c0 Q :=
  rx_rli_d0E hX hres hu0 hu1 hu2 hR hW hsz hctr hT hF hAF hAw hb0 hb1 hb2 hc0 hc1 hc2 hG hroom
    fun M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 _ _ =>
      k M' img' g h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17

end Blanc.Lift.Curve3Pool
