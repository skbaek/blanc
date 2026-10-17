import Blanc.Lift.Curve3Pool.Callee.Xp
import Blanc.Lift.Curve3Pool.Callee.GetD

/-!
# `get_D_mem` (entry 29, pc `0x7b7`): the callee contract

`get_D_mem(_balances, amp)` is `return self.get_D(self._xp_mem(_balances), amp)`.  The bytes:

* the prologue writes the return slot (`0x1c0`), the balances (`0x140 … 0x180`) and `amp`
  (`0x1a0`);
* the outer call saves the frame `[0x140, 0x420)` (23 words, `0x7d3`, `KitCheck.lean`);
* the inner call saves `[0x140, 0x300)` (14 words, `0x800`), copies the balances to
  `0x320 … 0x360`, calls `_xp_mem` (entry 34, `xpMem_spec`), stores its words at
  `0x3c0 … 0x400` and restores `[0x140, 0x300)` (`0x86b`);
* the arguments of `get_D` go to `0x440 … 0x4a0`, `get_D` (entry 417, `getD_spec`) returns `D`,
  stored at `0x500`, and `[0x140, 0x420)` is restored (`0x8d8`);
* the exit returns `D` through scratch word `0` and the restored return slot.

`getDMem_spec`: every run returns `D` over the caller's stack with `getDMem b amp = some D`, the
world unchanged, and memory kept off `[0, 0x20)` and `[0x140, 0x520)`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-! ## The inner call's frame chains and the call of `_xp_mem` -/

/-- Counter `0x300`, bound `0x300`, exit tag `0x822`, head tag `0x800`. -/
def saveTpl_0800 : FrameLoopTpl := ⟨0x03, 0x00, 0x03, 0x00, 0x08, 0x22, 0x08, 0x00⟩

def saveKs_0800 : List Nat := [429, 443, 457, 471, 485, 501, 515, 529, 545, 558, 571, 582, 593]

theorem saveTpl_0800_c : saveTpl_0800.c = 0x300 := by decide

theorem t_0800_c415_eq : t_0800_c415 = saveTpl_0800.saveTree t_0822_c593 saveKs_0800 := by
  decide +kernel

theorem saveChain_0800 : FrameSaveChain prog saveTpl_0800 t_0822_c593 saveKs_0800 := by
  unfold FrameSaveChain
  decide +kernel

/-- Counter `0x300`, bound `lo = 0x140`, exit tag `0x88e`, head tag `0x86b`. -/
def restoreTpl_086b : FrameLoopTpl := ⟨0x03, 0x00, 0x01, 0x40, 0x08, 0x8e, 0x08, 0x6b⟩

def restoreKs_086b : List Nat := [603, 613, 623, 633, 643, 653, 663, 673, 682, 691, 700, 709, 718]

theorem restoreTpl_086b_c : restoreTpl_086b.c = 0x300 := by decide

theorem t_086b_c593_eq : t_086b_c593 = restoreTpl_086b.restoreTree t_088e_c718 restoreKs_086b := by
  decide +kernel

theorem restoreChain_086b : FrameRestoreChain prog restoreTpl_086b t_088e_c718 restoreKs_086b := by
  unfold FrameRestoreChain
  decide +kernel

theorem prog_34 : prog[34]? = some t_03a1_c34 := by decide +kernel

theorem t_07b7_c29_prog : prog[29]? = some t_07b7_c29 := by decide +kernel

/-- `get_D_mem`'s windows: scratch word `0` and `[0x140, 0x520)`. -/
abbrev gdmWin : List (Nat × Nat) := [(0, 0x20), (0x140, 0x520)]

/-- A word of a restored frame, read back. -/
theorem Words.of_frameSlots {M W : Mem} {lo n : Nat} (h : Words M (frameSlots W lo n)) {j : Nat}
    (hj : j < n) {v : B256} (hv : memWord W (lo + 32 * j) = v) : Words M [(lo + 32 * j, v)] := by
  refine Words.cons.mpr ⟨?_, Words.nil M⟩
  have hm : (lo + 32 * j, memWord W (lo + 32 * j)) ∈ frameSlots W lo n := by
    simp only [frameSlots, List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩
  rw [← hv]
  exact h _ _ hm

section Chains

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

theorem ric_save_0800 (hsz : M.size % 32 = 0) (hcs : 0x320 ≤ M.size)
    (hctr : memWord M 0x300 = Nat.toB256 0x140)
    (run : SFunc.RunCut prog sevm [] (St b S M G) t_0800_c415 r) :
    ∃ G', SFunc.RunCut prog sevm [] (St b ((frameWords M 0x140 14).reverse ++ S)
      (saveMem M 0x300 0x140 14) G') t_0822_c593 r := by
  rw [t_0800_c415_eq] at run
  have h := ric_frameSave_chain saveChain_0800 (fun _ _ h => by cases h) hsz
    (by rw [saveTpl_0800_c]; omega) (by rw [saveTpl_0800_c]; exact hctr)
    (by rw [saveTpl_0800_c]; decide) run
  rw [saveTpl_0800_c] at h
  exact h

theorem ric_restore_086b {ts : List B256} (hts : ts.length = 14) (hsz : M.size % 32 = 0)
    (hcs : 0x320 ≤ M.size) (hctr : memWord M 0x300 = Nat.toB256 0x2e0)
    (run : SFunc.RunCut prog sevm [] (St b (ts ++ S) M G) t_086b_c593 r) :
    ∃ G', SFunc.RunCut prog sevm [] (St b S (restoreMem 0x300 M 0x2e0 ts) G') t_088e_c718 r := by
  rw [t_086b_c593_eq] at run
  have h := ric_frameRestore_chain (lo := 0x140) restoreChain_086b (fun _ _ h => by cases h)
    (by rw [hts]; rfl) hsz (by rw [restoreTpl_086b_c]; omega) (by decide)
    (by rw [restoreTpl_086b_c]; decide) (by rw [restoreTpl_086b_c]; exact hctr) run
  rw [restoreTpl_086b_c] at h
  exact h

theorem ric_restore_08d8' {ts : List B256} (hts : ts.length = 23) (hsz : M.size % 32 = 0)
    (hcs : 0x440 ≤ M.size) (hctr : memWord M 0x420 = Nat.toB256 0x400)
    (run : SFunc.RunCut prog sevm [] (St b (ts ++ S) M G) t_08d8_c718 r) :
    ∃ G', SFunc.RunCut prog sevm [] (St b S (restoreMem 0x420 M 0x400 ts) G') t_08fb_c918 r := by
  rw [t_08d8_c718_eq] at run
  have h := ric_frameRestore_chain (lo := 0x140) restoreChain_08d8 (fun _ _ h => by cases h)
    (by rw [hts]; rfl) hsz (by rw [restoreTpl_08d8_c]; omega) (by decide)
    (by rw [restoreTpl_08d8_c]; decide) (by rw [restoreTpl_08d8_c]; exact hctr) run
  rw [restoreTpl_08d8_c] at h
  exact h

end Chains

-- SEGMENT: getDMem_spec
theorem getDMem_spec {sevm : Sevm} {b : Devm} {ρ b0 b1 b2 amp : B256} {S : List B256} {M : Mem}
    {G : Nat} {o : Outcome} (hwf : Mem.Wf M) (hsz : M.size % 32 = 0)
    (run : SFunc.Run prog sevm (St b (ρ :: b0 :: b1 :: b2 :: amp :: S) M G) t_07b7_c29 o) :
    ∃ d, o = .returned d ∧ ∃ v M' G', d = St b (v :: S) M' G' ∧
      getDMem ⟨b0.toNat, b1.toNat, b2.toNat⟩ amp.toNat = some v.toNat ∧
      Mem.KeepsOff M M' gdmWin ∧ Words M' [(0, v)] ∧ Mem.Wf M' ∧ M'.size % 32 = 0 := by
  have hc := run.cut
  clear run
  have hT := MemTrack.init hwf gdmWin
  unfold t_07b7_c29 at hc
  have hd := ric_dest hc
  clear hc
  obtain ⟨_, run⟩ := hd
  imstoreO 0x1c0; imstoreO 0x140; imstoreO 0x160; imstoreO 0x180; imstoreO 0x1a0
  istep; imstoreO 0x420
  rename_i M1 G1
  -- the outer call's frame save, `[0x140, 0x420)`
  have hρ1 := hT.words.memWord (o := 0x1c0) (v := ρ) (by wmem)
  have hc1 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hcs1 := hT.mem_size (o := 0x420) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hal1 := hT.aligned hsz
  have hT1 := (hT.sub (L' := [(0x1a0, amp), (0x180, b2), (0x160, b1), (0x140, b0)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])).saveMem'
    (c := 0x420) (lo := 0x140) rfl rfl 23
  clear hT
  obtain ⟨_, run⟩ := ric_save_07d3 (by decide) hal1 (by omega) (hc1.trans (by decide)) run
  have hctr1 := saveMem_ctr (n := 23) (hc1.trans (by decide : Bytes.toB256 [1, 64] = Nat.toB256 0x140))
  have hT := hT1.withWords (Words.cons.mpr ⟨⟨by rw [saveMem_size (by omega)]; omega, hctr1⟩,
    hT1.words⟩)
  clear hT1
  -- the inner call: its frame save `[0x140, 0x300)`
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  istep; istep; imstoreO 0x300
  rename_i M3 G3
  have hamp3 := hT.words.memWord (o := 0x1a0) (v := amp) (by wmem)
  have hc2 := hT.words.memWord (o := 0x300) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hcs2 := hT.mem_size (o := 0x300) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hal2 := hT.aligned hsz
  have hT2 := (hT.sub (L' := [(0x420, Nat.toB256 (0x140 + 32 * 23)), (0x180, b2), (0x160, b1),
      (0x140, b0)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])).saveMem'
    (c := 0x300) (lo := 0x140) rfl rfl 14
  clear hT
  obtain ⟨_, run⟩ := ric_save_0800 hal2 (by omega) (hc2.trans (by decide)) run
  have hT := hT2
  clear hT2
  -- copy the balances to `0x320 … 0x360`, call `_xp_mem`
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  istep; istep; istep; imload' 0x140; istep; imstoreO' 0x320
  istep; istep; istep; imload' 0x160; istep; istep; istep; imstoreO' 0x340
  istep; istep; istep; imload' 0x180; istep; istep; istep; imstoreO' 0x360
  istep; istep; imload 0x360; imload 0x340; imload 0x320
  -- `_xp_mem`
  obtain ⟨_, D5, hcall, run⟩ := ric_pcCall xpMem_neverHalts prog_34 (by decide) run
  obtain ⟨d5, hd5, x0, x1, x2, M5, G5, hD5, hxp, hk5, hwf5, hal5⟩ := xpMem_spec hT.wf hcall
  cases hd5
  subst hD5
  have hW5 : Words M5 [(0x420, Nat.toB256 (0x140 + 32 * 23))] := by
    have hw0 := hT.words.sub (L' := [(0x420, Nat.toB256 (0x140 + 32 * 23))]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]; wmem)
    refine Words.keepsOff hw0 hk5 ?_
    intro o w h j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro w' hw'
    simp only [xpMemWin, List.mem_cons, List.not_mem_nil, or_false] at hw'
    subst hw'
    omega
  have hT5 : MemTrack M M5 gdmWin [(0x420, Nat.toB256 (0x140 + 32 * 23))] :=
    ⟨hT.keeps.trans (hk5.widen (by decide)), hW5, hwf5, fun h => hal5 (hT.aligned h)⟩
  clear hT
  have hT := hT5
  clear hT5
  -- store its words, restore `[0x140, 0x300)`
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  imstoreO 0x3c0; imstoreO 0x3e0; imstoreO 0x400; istep; imstoreO 0x300
  rename_i M6 G6
  have hc6 := hT.words.memWord (o := 0x300) (v := Bytes.toB256 [2, 0xe0]) (by wmem)
  have hcs6 := hT.mem_size (o := 0x420) (v := Nat.toB256 (0x140 + 32 * 23)) (by wmem)
  obtain ⟨_, run⟩ := ric_restore_086b (by simp only [List.length_reverse, length_frameWords])
    (hT.aligned hsz) (by omega) (hc6.trans (by decide)) run
  have hfr2 := restoreMem_frameWords (c := 0x300) (lo := 0x140) (n := 14) (M := M6) (W := M3)
    (by omega) (by decide)
  have hamp7 := Words.of_frameSlots hfr2 (j := 3) (by decide) hamp3
  have hoth7 := Words.restoreMem' (c := 0x300) (p := 0x2e0)
    (ws := (frameWords M3 0x140 14).reverse)
    (hT.words.sub (L' := [(0x3c0, x0), (0x3e0, x1), (0x400, x2),
      (0x420, Nat.toB256 (0x140 + 32 * 23))]) (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])) (by decide)
    (by simp only [List.length_reverse, length_frameWords]; rfl)
  have hT7 := (MemTrack.restoreMem (c := 0x300) rfl (frameWords M3 0x140 14).reverse hT
    (p := 0x2e0) (fun k hk => by
      simp only [List.length_reverse, length_frameWords] at hk
      have h14 : ∀ k, k < 14 → coversWord gdmWin (0x2e0 - 32 * k) = true := by decide
      exact h14 k hk)).withWords (Words.append.mpr ⟨hamp7, hoth7⟩)
  clear hT
  have hT := hT7
  clear hT7
  -- the arguments of `get_D` to `0x440 … 0x4a0`, call it
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  istep; istep; imload' 0x3c0; istep; imstoreO' 0x440
  istep; istep; istep; imload' 0x3e0; istep; istep; istep; imstoreO' 0x460
  istep; istep; istep; imload' 0x400; istep; istep; istep; imstoreO' 0x480
  istep; istep; imload 0x1a0; imstoreO 0x4a0
  imload 0x4a0; imload 0x480; imload 0x460; imload 0x440
  obtain ⟨_, D8, hcallD, run⟩ := ric_call_getD_08c6 run
  have hcs8 := hT.mem_size (o := 0x4a0) (v := amp) (by wmem)
  obtain ⟨d8, hd8, v, M9, G9, hD9, hgd, hsize9, hw9, hk9⟩ :=
    getD_spec (hT.aligned hsz) (by omega) hcallD
  cases hd8
  subst hD9
  have hW9 : Words M9 [(0x420, Nat.toB256 (0x140 + 32 * 23))] := by
    have hw0 := hT.words.sub (L' := [(0x420, Nat.toB256 (0x140 + 32 * 23))]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]; wmem)
    refine Words.keepsOff hw0 (hk9 hT.wf).1 ?_
    intro o w h j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro w' hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl <;> omega
  have hT9 : MemTrack M M9 gdmWin [(0x420, Nat.toB256 (0x140 + 32 * 23))] :=
    ⟨hT.keeps.trans ((hk9 hT.wf).1.widen (by decide)), hW9, (hk9 hT.wf).2,
      fun h => by rw [hsize9]; exact hT.aligned h⟩
  clear hT
  have hT := hT9
  clear hT9
  -- store `D`, restore `[0x140, 0x420)`
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  imstoreO 0x500; istep; imstoreO 0x420
  rename_i M10 G10
  have hc10 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [4, 0]) (by wmem)
  have hcs10 := hT.mem_size (o := 0x420) (v := Bytes.toB256 [4, 0]) (by wmem)
  obtain ⟨_, run⟩ := ric_restore_08d8' (by simp only [List.length_reverse, length_frameWords])
    (hT.aligned hsz) (by omega) (hc10.trans (by decide)) run
  have hfr1 := restoreMem_frameWords (c := 0x420) (lo := 0x140) (n := 23) (M := M10) (W := M1)
    (by omega) (by decide)
  have hρ11 := Words.of_frameSlots hfr1 (j := 4) (by decide) hρ1
  have hv11 := Words.restoreMem' (c := 0x420) (p := 0x400)
    (ws := (frameWords M1 0x140 23).reverse)
    (hT.words.sub (L' := [(0x500, v)]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]; wmem)) (by decide)
    (by simp only [List.length_reverse, length_frameWords]; rfl)
  have hT11 := (MemTrack.restoreMem (c := 0x420) rfl (frameWords M1 0x140 23).reverse hT
    (p := 0x400) (fun k hk => by
      simp only [List.length_reverse, length_frameWords] at hk
      have h23 : ∀ k, k < 23 → coversWord gdmWin (0x400 - 32 * k) = true := by decide
      exact h23 k hk)).withWords (Words.append.mpr ⟨hρ11, hv11⟩)
  clear hT
  have hT := hT11
  clear hT11
  -- the exit: `return D`
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  imload 0x500; imstoreO 0x0; imload 0x0; imload 0x1c0
  obtain ⟨G', hr⟩ := ric_ret run
  cases hr
  have hW0 : Words _ [(0, v)] := hT.words.sub (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [hx]; wmem)
  refine ⟨_, rfl, v, _, G', rfl, ?_, hT.keeps, hW0, hT.wf, hT.aligned hsz⟩
  unfold getDMem
  rw [hxp, Option.bind_eq_bind, Option.bind_some]
  exact hgd

end Blanc.Lift.Curve3Pool
