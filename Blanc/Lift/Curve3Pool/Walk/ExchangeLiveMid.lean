import Blanc.Lift.Curve3Pool.Walk.ExchangeLivePre

/-!
# `exchange`, forward: `_xp_mem`, the frame restore, `dx`, `input_coin`, up to the fee test

`rx_ex_mid` is `xa_ex_xp`'s forward twin: the call of `_xp_mem(old_balances)` run by
`xpMem_exact`, `xp` parked at `0x320`, the nine frame words restored, `xp` copied to `0x200`,
`dx_w_fee = dx` at `0x380`, `input_coin = coins[i]` at `0x3a0`, then the `i == FEE_INDEX` test.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The index guard `i < 3` passes. -/
theorem ex_lt3_ne {x : B256} (h : x.toNat < 3) : B256.ltCheck x (Bytes.toB256 [3]) ≠ 0 := by
  rw [← toB256_toNat x]
  obtain h' | h' | h' : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 := by omega
  all_goals rw [h']; decide

theorem ex_prog_34 : cert.prog[34]? = some t_03a1_c34 := by decide +kernel

/-- The words `exchange` stores between `_xp_mem` and the fee test, in order: `xp` parked at
`0x320 … 0x360`, the nine frame words restored to `0x240 … 0x140`, `xp` copied to
`0x200 … 0x240`, `dx` at `0x380`, the key scratch at `0xc0`, `coins[i]` at `0x3a0`. -/
def exMidWords (x0 x1 x2 z0 z1 z2 B0 B1 B2 dx c : B256) : List (Nat × B256) :=
  [(0x320, x0), (0x340, x1), (0x360, x2), (0x240, z2), (0x220, z1), (0x200, z0), (0x1e0, B2),
    (0x1c0, B1), (0x1a0, B0), (0x180, exR1), (0x160, exR1), (0x140, exR0), (0x200, x0),
    (0x220, x1), (0x240, x2), (0x380, dx), (0xc0, Bytes.toB256 [0]), (0x3a0, c)]

/-- The restored frame words cover `_xp_mem`'s scratch window. -/
theorem exMid_cover (x0 x1 x2 z0 z1 z2 B0 B1 B2 dx c : B256) :
    ∀ i, ¬ Mem.OffWindows xpMemWin i →
      ∃ o ∈ (exMidWords x0 x1 x2 z0 z1 z2 B0 B1 B2 dx c).map Prod.fst, o ≤ i ∧ i < o + 32 := by
  intro i hi
  have h1 : 0x140 ≤ i ∧ i < 0x260 := by
    by_contra hc
    exact hi fun w hw => by
      simp only [xpMemWin, List.mem_cons, List.not_mem_nil, or_false] at hw
      subst hw; omega
  refine ⟨0x140 + 32 * ((i - 0x140) / 32), ?_, by omega, by omega⟩
  have hq : (i - 0x140) / 32 < 9 := by omega
  simp only [exMidWords, List.map_cons, List.map_nil]
  generalize (i - 0x140) / 32 = q at hq
  obtain h | h | h | h | h | h | h | h | h : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 ∨
    q = 6 ∨ q = 7 ∨ q = 8 := by omega
  all_goals (subst h; decide)

/-- **`exchange` from `_xp_mem` to the fee test, forward, exactly**: `rx_ex_mid`, the
continuation also receiving the exact charge (`1589` plus the `coins[i]` load), the literal base,
and the literal memory `exMidWords` over the **pre-call** memory: the callee's scratch
`[0x140, 0x260)` is overwritten by the nine restored words, and the store at `0x320`
materialises the array, so its physical representation is gone. -/
theorem rx_ex_mid_core {sevm : Sevm} {b0 b : Devm} {σ : Stor} {g R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B0 B1 B2 z0 z1 z2 : B256} {xp : V3}
    (hfork : CoveredFork sevm.benvStat.fork) (hB : ExBase sevm b0 b σ) (hWc : WClosed sevm W)
    (hWb : W b) (hi : (exI sevm).toNat < 3)
    (hX : xpChk ⟨B0.toNat, B1.toNat, B2.toNat⟩ = some xp)
    (_hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2e0)
    (hG : 3689 + R ≤ g)
    (k : ∀ (b2 : Devm) (M2 : Mem) (img2 : Bytes) (g2 : Nat) (x0 x1 x2 : B256),
      xp = ⟨x0.toNat, x1.toNat, x2.toNat⟩ → ExBase sevm b0 b2 σ → W b2 →
      Mem.Reads M2 img2 → Mem.Wf M2 → M2.size = 0x3c0 →
      ExFrame img2 (exW3 B0 B1 B2) (exW3 x0 x1 x2) (exDx sevm) (σ.get (coinsBase + exI sevm)) →
      R ≤ g2 → g2 + 1500 ≤ g →
      g = g2 + 1589 + sloadCost sevm b (coinsBase + exI sevm) →
      b2 = afterSload sevm b (coinsBase + exI sevm) →
      M2 = Mem.writeWords M (exMidWords x0 x1 x2 z0 z1 z2 B0 B1 B2 (exDx sevm)
        (σ.get (coinsBase + exI sevm))) →
      SFunc.RunEx cert.prog sevm (St b2 [Bytes.toB256 [0x25, 0x17],
        B256.eqCheck (B256.eqCheck (exI sevm) (Bytes.toB256 [2])) 0] M2 g2)
        (.branchTo t_24d8_c0 11) Q) :
    SFunc.RunEx cert.prog sevm (St b [B0, B1, B2, z2, z1, z0, B2, B1, B0, exR1, exR1, exR0,
      Bytes.toB256 [2, 0]] M g) (pcCallTree 0x2452 0x03 0xa1 34 t_2458_c0) Q := by
  obtain ⟨g1, rfl⟩ : ∃ g', g = g' + 1290 + 19 := ⟨g - 1309, by omega⟩
  obtain ⟨x0, x1, x2, ⟨M', hrun, hko, hW', hsz'⟩, hxp⟩ := xpMem_exact (sevm := sevm) (b := b)
    (S := [z2, z1, z0, B2, B1, B0, exR1, exR1, exR0, Bytes.toB256 [2, 0]]) (G := g1)
    (ret := Nat.toB256 (0x2452 + 6)) hX hW hsz (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; omega)
  refine rxe_pcCall ex_prog_34 (by decide) (by simp only [List.length_cons, List.length_nil]; omega) hrun ?_
  have hWM := hW
  have hszM := hsz
  clear _hR hW hsz hrun img
  have hR := Mem.reads_data M'
  have hWM' := hW'
  have hszM' := hsz'
  have hW := hW'
  have hsz := hsz'
  clear hW' hsz'
  obtain ⟨h1, rfl⟩ : ∃ g, g1 = g + 253 := ⟨g1 - 253, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x320) (c := 12) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x2e0 0x320 32 = 0x340 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x340) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x340 0x340 32 = 0x360 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x360) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x360 0x360 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x240) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x240 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x220) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x220 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x200) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x200 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1e0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x1e0 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1c0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x1c0 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x1a0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x1a0 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x180) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x180 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x160) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x160 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x140) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x140 32 = 0x380 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rxm_mload (o := 0x320) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x200) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x200 32 = 0x380 by decide] at hsz
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mload (o := 0x340) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x220) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x220 32 = 0x380 by decide] at hsz
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  xr (rxm_mload (o := 0x360) hR hsz rfl (by decide) (by hr) ·); try wsimp
  xr (rx_dup rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_add (by hr) ·)
  refine rxe_mstoreL (o := 0x240) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x240 32 = 0x380 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x380) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x380 0x380 32 = 0x3a0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_dup rfl (by hr) ·)
  xr (rx_lt rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_branch_succ (ex_lt3_ne hi) ·)
  -- tree t_24bc_c0
  xr (rx_dest ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0xc0) (c := 3) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x3a0 0xc0 32 = 0x3a0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rxm_keccak (o := 0xc0) (z := 0x20) (c := 36) hR hsz (by decide) (by decide) ⟨by decide, by decide⟩ (by hr) (by decide) ·)
  rw [keccak_zero]
  xr (rx_add (by hr) ·)
  refine rxe_sloadVX hfork (by hr) (by omega) ?_; intro h2 b2 v2 hb2 hv2 hh21 hh22 hx_h2
  obtain ⟨h3, rfl⟩ : ∃ g, h2 = g + 27 := ⟨h2 - 27, by omega⟩
  xr (rx_push rfl (by hr) ·)
  refine rxe_mstoreL (o := 0x3a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x3a0 0x3a0 32 = 0x3c0 by decide] at hsz
  xr (rx_push rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  xr (rx_calldataload (by hr) ·)
  xr (rx_eq rfl (by hr) ·)
  xr (rx_iszero rfl (by hr) ·)
  xr (rx_push rfl (by hr) ·)
  have hF : ExFrame (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt (Bytes.writeAt
      (Bytes.writeAt M'.data.toList 800 x0.toBytes) 832 x1.toBytes) 864 x2.toBytes) 576 z2.toBytes)
      544 z1.toBytes) 512 z0.toBytes) 480 B2.toBytes) 448 B1.toBytes) 416 B0.toBytes)
      384 exR1.toBytes) 352 exR1.toBytes) 320 exR0.toBytes) 512 x0.toBytes) 544 x1.toBytes)
      576 x2.toBytes) 896 (Sevm.dataWord sevm (Bytes.toB256 [68])).toBytes)
      192 (Bytes.toB256 [0]).toBytes) 928 v2.toBytes)
      (exW3 B0 B1 B2) (exW3 x0 x1 x2) (exDx sevm) (σ.get (coinsBase + exI sevm)) := by
    have hC : σ.get (coinsBase + exI sevm) = v2 := by rw [hv2, getStorVal_eq, hB.stor]
    rw [hC]
    refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, by wauto, by wauto⟩ <;>
      obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    all_goals wauto
  obtain ⟨img2, hR2, hI⟩ := Mem.Reads.forget hR
  rw [← hI] at hF
  have hB2 : ExBase sevm b0 b2 σ := by rw [hb2]; exact hB.sload _
  have hW2 : W b2 := by rw [hb2]; exact hWc.sload _ _ hWb
  have hC : v2 = σ.get (coinsBase + exI sevm) := by rw [hv2, getStorVal_eq, hB.stor]
  refine k b2 _ img2 h3 x0 x1 x2 hxp hB2 hW2 hR2 hW (by rw [hsz]) hF (by omega) (by omega)
    (by have e : sloadCost sevm b (coinsBase + exI sevm) =
      sloadCost sevm b (coinsBase + Sevm.dataWord sevm (Bytes.toB256 [4])) := rfl
        omega) hb2 ?_
  rw [← hC, ← ((hko.eqExcept (by rw [hszM', hszM]) hWM hWM').symm).writeWords_eq _
    (exMid_cover _ _ _ _ _ _ _ _ _ _ _) (Mem.full_writeWords_of_grow (by rw [hszM']; decide) _)
    (Mem.full_writeWords_of_grow (by rw [hszM]; decide) _)]
  simp only [Mem.writeWords, exMidWords, List.foldl]

/-- **`exchange` from `_xp_mem` to the fee test, forward.** -/
theorem rx_ex_mid {sevm : Sevm} {b0 b : Devm} {σ : Stor} {g R : Nat} {Q : Outcome → Prop}
    {M : Mem} {img : Bytes} {W : Devm → Prop} {B0 B1 B2 z0 z1 z2 : B256} {xp : V3}
    (hfork : CoveredFork sevm.benvStat.fork) (hB : ExBase sevm b0 b σ) (hWc : WClosed sevm W)
    (hWb : W b) (hi : (exI sevm).toNat < 3)
    (hX : xpChk ⟨B0.toNat, B1.toNat, B2.toNat⟩ = some xp)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x2e0)
    (hG : 3689 + R ≤ g)
    (k : ∀ (b2 : Devm) (M2 : Mem) (img2 : Bytes) (g2 : Nat) (x0 x1 x2 : B256),
      xp = ⟨x0.toNat, x1.toNat, x2.toNat⟩ → ExBase sevm b0 b2 σ → W b2 →
      Mem.Reads M2 img2 → Mem.Wf M2 → M2.size = 0x3c0 →
      ExFrame img2 (exW3 B0 B1 B2) (exW3 x0 x1 x2) (exDx sevm) (σ.get (coinsBase + exI sevm)) →
      R ≤ g2 → g2 + 1500 ≤ g →
      SFunc.RunEx cert.prog sevm (St b2 [Bytes.toB256 [0x25, 0x17],
        B256.eqCheck (B256.eqCheck (exI sevm) (Bytes.toB256 [2])) 0] M2 g2)
        (.branchTo t_24d8_c0 11) Q) :
    SFunc.RunEx cert.prog sevm (St b [B0, B1, B2, z2, z1, z0, B2, B1, B0, exR1, exR1, exR0,
      Bytes.toB256 [2, 0]] M g) (pcCallTree 0x2452 0x03 0xa1 34 t_2458_c0) Q :=
  rx_ex_mid_core hfork hB hWc hWb hi hX hR hW hsz hG
    fun b2 M2 img2 g2 x0 x1 x2 h1 h2 h3 h4 h5 h6 h7 h8 h9 _ _ _ =>
      k b2 M2 img2 g2 x0 x1 x2 h1 h2 h3 h4 h5 h6 h7 h8 h9

end Blanc.Lift.Curve3Pool
