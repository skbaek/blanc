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

/-- `get_y`'s arguments staged at `0x800 … 0x8a0` over the saved frame's memory. -/
def exYArgs (M : Mem) (sevm : Sevm) (xw x0 x1 x2 : B256) : Mem :=
  M.write 0x800 (exI sevm).toBytes |>.write 0x820 (exJ sevm).toBytes |>.write 0x840 xw.toBytes
    |>.write 0x860 x0.toBytes |>.write 0x880 x1.toBytes |>.write 0x8a0 x2.toBytes

/-- The literal memory after `get_y` and the restore: the arguments, `get_y`'s result at its scratch
word `0` and at `0x900`, the counter, and the 53 saved words restored. -/
def exYMem (M : Mem) (sevm : Sevm) (xw x0 x1 x2 : B256) (v : Nat) (w : Nat → B256) : Mem :=
  restoreMem 0x7e0 ((((exYArgs M sevm xw x0 x1 x2).write 0 (Nat.toB256 v).toBytes).write 0x900
    (Nat.toB256 v).toBytes).write 0x7e0 (Bytes.toB256 [7, 0xc0]).toBytes) (0x140 + 32 * 52)
    (exSaved w 0x140 (52 + 1))

/-- A word store past the logical size materialises the array. -/
theorem ex_full_write_word {μ : Mem} {o : Nat} (v : B256) (h : μ.size < o + 32) :
    Mem.Full (μ.write o v.toBytes) :=
  Mem.full_write_of_grow (fun e => by
    have := B256.length_toBytes v; rw [e] at this; exact absurd this (by decide))
    (by rw [B256.length_toBytes]; exact h)

/-- A callee that keeps off `get_y`'s windows and leaves `y` at word `0` agrees, off its frame
scratch `[0x140, 0x4c0)`, with the caller's memory and `y` written at `0`. -/
theorem exY_glue {A M' : Mem} {y : B256} (hk : Mem.KeepsOff A M' gyWin) (hsz : M'.size = A.size)
    (hA : Mem.Wf A) (hM' : Mem.Wf M') (hw : memWord M' 0 = y) (h32 : 32 ≤ A.size) :
    Mem.EqExcept (A.write 0 y.toBytes) M' (fun i => 0x140 ≤ i ∧ i < 0x4c0) := by
  refine ⟨by rw [Mem.size_write_word_of_add_le h32, hsz], hA.write _ _, hM', fun i hi => ?_⟩
  by_cases h0 : i < 32
  · have e := Mem.getD_eq_of_memWord_eq (o := 0) (j := i)
      (((Mem.memWord_write_word A 0 y).1).trans hw.symm) h0
    simpa only [Nat.zero_add] using e
  · rw [Mem.write_getD hA, ite_eq_right (by rw [B256.length_toBytes]; omega)]
    refine (hk.2 i ?_).symm
    intro w hw'
    simp only [gyWin, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl <;> simp only <;> omega

/-- The restored words and the counter cover `get_y`'s frame scratch. -/
theorem exY_cover (w : Nat → B256) (y c : B256) :
    ∀ i, ¬ ((((0x140 ≤ i ∧ i < 0x4c0) ∧ ¬ (0x900 ≤ i ∧ i < 0x900 + y.toBytes.length)) ∧
      ¬ (0x7e0 ≤ i ∧ i < 0x7e0 + c.toBytes.length)) ∧
      (exSaved w 0x140 (52 + 1) ≠ [] → ¬ (0x7e0 ≤ i ∧ i < 0x7e0 + 32)) ∧
      ∀ j, j < (exSaved w 0x140 (52 + 1)).length →
        ¬ (0x140 + 32 * 52 - 32 * j ≤ i ∧ i < 0x140 + 32 * 52 - 32 * j + 32)) := by
  rintro i ⟨⟨⟨hi, -⟩, -⟩, -, hj⟩
  refine hj (52 - (i - 0x140) / 32) (by rw [exSaved_length]; omega) ⟨by omega, by omega⟩

/-- **`get_y` and the frame restore, forward, exactly**: `rx_ex_y`, the continuation also
receiving the exact charge (`3906` plus the checked model's `costGetY`), the base `aBase`, and
the literal memory `exYMem` — `get_y`'s scratch is fully rewritten by the restore and its result
word `0` is retained, so no callee memory witness survives. -/
theorem rx_ex_y_core {sevm : Sevm} {b : Devm} {σ : Stor} {s : State} {G R amp v : Nat}
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
      G = g + 3906 + costGetY sevm b amp (exI sevm).toNat (exJ sevm).toNat xw.toNat (X 0).toNat
        (X 1).toNat (X 2).toNat → b' = aBase sevm b → M' = exYMem M sevm xw (X 0) (X 1) (X 2) v w →
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
  refine rxe_mstoreL (o := 0x800) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x800 0x800 32 = 0x820 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_calldataload (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x820) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x820 0x820 32 = 0x840 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rxm_mload (o := 0x7a0) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [hx.read]
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x840) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x840 0x840 32 = 0x860 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_dup rfl (by hrs) ·)
  xr (rxm_mload (o := 0x200) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [(hF.xp 0 (by decide)).read]
  xr (rx_dup rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x860) (c := 7) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x860 0x860 32 = 0x880 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x220) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [(hF.xp 1 (by decide)).read]
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x880) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x880 0x880 32 = 0x8a0 by decide] at hsz
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  xr (rxm_mload (o := 0x240) hR hsz rfl (by decide) (by hrs) ·); try wsimp
  rw [(hF.xp 2 (by decide)).read]
  xr (rx_dup rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  xr (rx_add (by hrs) ·)
  refine rxe_mstoreL (o := 0x8a0) (c := 6) hR hW hsz rfl (by decide) ?_; clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x8a0 0x8a0 32 = 0x8c0 by decide] at hsz
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
  have hWY := hW
  have hszY := hsz
  obtain ⟨M', hrun, ⟨hkY, hW', hsz'⟩, hw0⟩ := getY_exact_rich (G := g1 + 3699 + 26)
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
  have hWM' := hW
  have hszM' := hsz
  refine rxe_mstoreL (o := 0x900) (c := 13) hR hW hsz rfl (by decide) ?_
  clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x8c0 0x900 32 = 0x920 by decide] at hsz
  xr (rx_push rfl (by hrs) ·)
  xr (rx_push rfl (by hrs) ·)
  refine rxe_mstoreL (o := 0x7e0) (c := 3) hR hW hsz rfl (by decide) ?_
  clear hR hW hsz; intro hR hW hsz; rw [show memExtSize 0x920 0x7e0 32 = 0x920 by decide] at hsz
  rw [ex_rest_first, show exSaved w 0x140 53 = exSaved w 0x140 (52 + 1) ++ [] from
    (List.append_nil _).symm]
  refine rx_ex_restFrom_core w 52 (n := 0) rfl hR hW hsz
    (WordAt.write_eq rfl (by decide)) (by simp only [List.length_nil]; omega) ?_
  intro M'' img'' hR'' hW'' hsz'' hm'' hk'' hM''
  refine k _ M'' img'' g1 hL.aBaseE hR'' hW'' hsz'' hm''
    (hk'' _ _ ((WordAt.write_self _ _ _).write_other (by simp only [B256.length_toBytes]; omega))
      (.inr (.inr (by omega)))) (by omega) (by omega) (by omega) rfl ?_
  rw [hM'']
  have hg := exY_glue hkY (by rw [hszM', hszY]) hWY hWM' hw0 (by rw [hszY]; decide)
  have hgs := hg.1.trans hszM'
  refine ((((hg.write 0x900 (Nat.toB256 v).toBytes).write 0x7e0 _).restoreMem 0x7e0
    (p := 0x140 + 32 * 52) (exSaved w 0x140 (52 + 1))).eq (exY_cover _ _ _) ?_ ?_).symm
  · exact Mem.Full.restoreMem _ _ ((ex_full_write_word _ (by rw [hgs]; decide)).write _ _)
  · exact Mem.Full.restoreMem _ _ ((ex_full_write_word _ (by rw [hszM']; decide)).write _ _)

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
    SFunc.RunEx cert.prog sevm (St b (exSaved w 0x140 53) M G) t_2776_c751 Q :=
  rx_ex_y_core hfork hL ha hA hi hj hres hR hW hsz hF hx hG
    fun b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8 _ _ _ => k b' M' img' g h1 h2 h3 h4 h5 h6 h7 h8

end Blanc.Lift.Curve3Pool
