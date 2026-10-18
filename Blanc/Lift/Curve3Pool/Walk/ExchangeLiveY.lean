import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveRestore
import Blanc.Lift.Curve3Pool.Callee.GetYExact

/-!
# `exchange`, forward: `get_y` between the frame save and restore

`rx_ex_y`: `get_y`'s arguments staged at `0x800 … 0x8a0` and pushed, the call run by
`getY_exact` at its exact gas `costGetY`, `y` parked at `0x900`, and the frame restore
(`rx_ex_restFrom`), up to the `dy` arithmetic (`t_27fc_c1174`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- Across `_A`'s storage loads. -/
theorem ExLive.aBaseE {sevm : Sevm} {W : Devm → Prop} {b : Devm} {σ : Stor}
    (h : ExLive sevm W b σ) : ExLive sevm W (aBase sevm b) σ := by
  refine ⟨fun x => by rw [aBase_getStor]; exact h.stor x, IdReady_aBase h.id, h.wc, ?_⟩
  unfold aBase; split
  · exact h.wc.sload _ _ (h.wc.sload _ _ (h.wc.sload _ _ (h.wc.sload _ _ h.w)))
  · exact h.wc.sload _ _ (h.wc.sload _ _ h.w)

theorem ex_prog_252 : cert.prog[252]? = some t_18a4_c252 := by decide +kernel

/-- **`get_y` and the frame restore, forward** (`t_2776_c751` → `t_27fc_c1174`). -/
theorem rx_ex_y {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {G R amp v : Nat}
    {Q : Outcome → Prop} {M : Mem} {img : Bytes} {W : Devm → Prop} {B X : Nat → B256}
    {D C xw : B256} {w : Nat → B256}
    (hfork : CoveredFork sevm.benvStat.fork) (hL : ExLive sevm W b σ) (ha : Abstracts σ s)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hi : (exI sevm).toNat < 3) (hj : (exJ sevm).toNat < 3)
    (hres : getYChk amp ⟨(exI sevm).toNat, hi⟩ ⟨(exJ sevm).toNat, hj⟩ xw.toNat
      (V3.mk (X 0).toNat (X 1).toNat (X 2).toNat).get = some v)
    (hR : Mem.Reads M img) (hW : Mem.Wf M) (hsz : M.size = 0x800) (hF : ExFrame img B X D C)
    (hx : WordAt img 0x7a0 xw)
    (hG : costGetY sevm b amp (exI sevm).toNat (exJ sevm).toNat xw.toNat (X 0).toNat (X 1).toNat
      (X 2).toNat + 3906 + R ≤ G)
    (k : ∀ (b' : Devm) (M' : Mem) (img' : Bytes) (g : Nat), ExLive sevm W b' σ →
      Mem.Reads M' img' → Mem.Wf M' → M'.size = 0x920 →
      (∀ m, m ≤ 52 → WordAt img' (0x140 + 32 * m) (w (0x140 + 32 * m))) →
      WordAt img' 0x900 (Nat.toB256 v) → R ≤ g → g ≤ G →
      SFunc.RunEx cert.prog sevm (St b' [] M' g) t_27fc_c1174 Q) :
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 53) M G) t_2776_c751 Q := by
  obtain ⟨g1, rfl⟩ : ∃ g, G = g + 3699 + 26 + costGetY sevm b amp (exI sevm).toNat
      (exJ sevm).toNat xw.toNat (X 0).toNat (X 1).toNat (X 2).toNat + 19 + 162 :=
    ⟨G - 3906 - costGetY sevm b amp (exI sevm).toNat (exJ sevm).toNat xw.toNat (X 0).toNat
      (X 1).toNat (X 2).toNat, by omega⟩
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x800) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x800 0x800 32 = 0x820 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x820) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x820 0x820 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x7a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [hx.read]
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x840) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x840 0x840 32 = 0x860 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x200) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [(hF.xp 0 (by decide)).read]
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstore (o := 0x860) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x860 0x860 32 = 0x880 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x220) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [(hF.xp 1 (by decide)).read]
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x880) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x880 0x880 32 = 0x8a0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x240) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [(hF.xp 2 (by decide)).read]
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstore (o := 0x8a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz M; intro M hR hW hsz; rw [show memExtSize 0x8a0 0x8a0 32 = 0x8c0 by decide] at hsz
  xr (rx_pop ·)
  xr (rx_pop ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x8a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x880) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x860) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x840) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x820) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x800) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  have ha' : Abstracts (b.getStor sevm.currentTarget) s :=
    ha.of_lock fun x _ => hL.stor x
  obtain ⟨M', hrun, -, hW', hsz'⟩ := getY_exact (G := g1 + 3699 + 26)
    (ρ := Nat.toB256 (0x27c7 + 6)) (S := exSaved w 0x140 53) hfork ha' hA hi hj hres hW hsz
    (by decide) (by decide) (by hrs)
  refine rxe_pcCall ex_prog_252 (by decide) (by hrs) hrun ?_
  clear hR hW hsz hrun
  have hR := Mem.reads_data M'
  have hW := hW'
  have hsz := hsz'
  clear hW' hsz'
  xr (rx_dest ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x900) (c := 13) hR hW hsz rfl (by decide) ?_
  clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0x8c0 0x900 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstore (o := 0x7e0) (c := 3) hR hW hsz rfl (by decide) ?_
  clear hR hW hsz; intro M hR hW hsz; rw [show memExtSize 0x920 0x7e0 32 = 0x920 by decide] at hsz
  rw [ex_rest_first, show exSaved w 0x140 53 = exSaved w 0x140 (52 + 1) ++ [] from
    (List.append_nil _).symm]
  refine rx_ex_restFrom w 52 (n := 0) rfl hR hW hsz
    (WordAt.write_eq rfl (by decide)) (by simp only [List.length_nil]; omega) ?_
  intro M'' img'' hR'' hW'' hsz'' hm'' hk''
  exact k _ M'' img'' g1 hL.aBaseE hR'' hW'' hsz'' hm''
    (hk'' _ _ ((WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega))
      (.inr (.inr (by omega)))) (by omega) (by omega)

end Blanc.Lift.Curve3Pool
