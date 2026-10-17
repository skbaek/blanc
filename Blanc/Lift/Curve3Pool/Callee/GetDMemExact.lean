import Blanc.Lift.Curve3Pool.Callee.GetDMem
import Blanc.Lift.Curve3Pool.Callee.GetDExact

/-!
# `get_D_mem`, forward: exact gas

The forward twin of `getDMem_spec`: from the checked model's success (`xpChk` and `getDChk`), the
entry tree runs to its return with exact gas `costGetDMem`, over a memory already covering
`[0, 0x520)`.  The constant `6676` is the prologue, the two frame saves (`1530`, `927`), the
`_xp_mem` call (`1290` with its call idiom), the two frame restores (`969`, `1599`) and the glue;
the rest is `get_D`'s `costGetD`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- Stack-room side goals over frame words. -/
macro "gdmlen" : tactic => `(tactic| (first | omega | (simp only [List.length_cons, List.length_append, List.length_reverse, length_frameWords]; omega)))

/-- The exact gas of `get_D_mem` at `xp = x`. -/
def costGetDMem (x : V3) (amp : Nat) : Nat := 6676 + costGetD x.v0 x.v1 x.v2 amp

section FwdChains

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

theorem rxc_save_07d3 (hsz : M.size % 32 = 0) (hcs : 0x440 ≤ M.size)
    (hctr : memWord M 0x420 = Nat.toB256 0x140) (hroom : S.length + 27 < 1024)
    (kk : SFunc.RunExactCut prog sevm [] (St b ((frameWords M 0x140 23).reverse ++ S)
      (saveMem M 0x420 0x140 23) G) t_07f5_c415 r) :
    SFunc.RunExactCut prog sevm [] (St b S M (G + 1530)) t_07d3_c29 r := by
  rw [t_07d3_c29_eq]
  have h := rxc_frameSave_chain (lo := 0x140) saveChain_07d3 (fun _ _ h => by cases h) hsz
    (by rw [saveTpl_07d3_c]; omega) (by rw [saveTpl_07d3_c]; exact hctr)
    (by rw [saveTpl_07d3_c, saveKs_07d3_length]) (by decide)
    (by rw [saveKs_07d3_length]; omega) kk
  rw [saveKs_07d3_length] at h
  exact h

theorem rxc_save_0800 (hsz : M.size % 32 = 0) (hcs : 0x320 ≤ M.size)
    (hctr : memWord M 0x300 = Nat.toB256 0x140) (hroom : S.length + 18 < 1024)
    (kk : SFunc.RunExactCut prog sevm [] (St b ((frameWords M 0x140 14).reverse ++ S)
      (saveMem M 0x300 0x140 14) G) t_0822_c593 r) :
    SFunc.RunExactCut prog sevm [] (St b S M (G + 927)) t_0800_c415 r := by
  rw [t_0800_c415_eq]
  have h := rxc_frameSave_chain (lo := 0x140) saveChain_0800 (fun _ _ h => by cases h) hsz
    (by rw [saveTpl_0800_c]; omega) (by rw [saveTpl_0800_c]; exact hctr) (by decide)
    (by decide) (by have : saveKs_0800.length = 13 := rfl; omega) kk
  rw [show saveKs_0800.length = 13 from rfl] at h
  exact h

theorem rxc_restore_086b {ts : List B256} (hts : ts.length = 14) (hsz : M.size % 32 = 0)
    (hcs : 0x320 ≤ M.size) (hctr : memWord M 0x300 = Nat.toB256 0x2e0)
    (hroom : S.length + 18 < 1024)
    (kk : SFunc.RunExactCut prog sevm [] (St b S (restoreMem 0x300 M 0x2e0 ts) G) t_088e_c718 r) :
    SFunc.RunExactCut prog sevm [] (St b (ts ++ S) M (G + 969)) t_086b_c593 r := by
  rw [t_086b_c593_eq]
  have h := rxc_frameRestore_chain (lo := 0x140) restoreChain_086b (fun _ _ h => by cases h)
    (by rw [hts]; rfl) hsz (by rw [restoreTpl_086b_c]; omega) (by decide) (by decide)
    (by rw [restoreTpl_086b_c]; decide) (by rw [restoreTpl_086b_c]; exact hctr)
    (by have : restoreKs_086b.length = 13 := rfl; omega) kk
  rw [show restoreKs_086b.length = 13 from rfl] at h
  exact h

theorem rxc_restore_08d8 {ts : List B256} (hts : ts.length = 23) (hsz : M.size % 32 = 0)
    (hcs : 0x440 ≤ M.size) (hctr : memWord M 0x420 = Nat.toB256 0x400)
    (hroom : S.length + 27 < 1024)
    (kk : SFunc.RunExactCut prog sevm [] (St b S (restoreMem 0x420 M 0x400 ts) G) t_08fb_c918 r) :
    SFunc.RunExactCut prog sevm [] (St b (ts ++ S) M (G + 1599)) t_08d8_c718 r := by
  rw [t_08d8_c718_eq]
  have h := rxc_frameRestore_chain (lo := 0x140) restoreChain_08d8 (fun _ _ h => by cases h)
    (by rw [hts]; rfl) hsz (by rw [restoreTpl_08d8_c]; omega) (by decide) (by decide)
    (by rw [restoreTpl_08d8_c]; decide) (by rw [restoreTpl_08d8_c]; exact hctr)
    (by rw [restoreKs_08d8_length]; omega) kk
  rw [restoreKs_08d8_length] at h
  exact h

end FwdChains

-- SEGMENT: getDMem_exact
theorem getDMem_exact {sevm : Sevm} {b : Devm} {ρ b0 b1 b2 amp : B256} {S : List B256} {M : Mem}
    {G n v : Nat} {x : V3} (hX : xpChk ⟨b0.toNat, b1.toNat, b2.toNat⟩ = some x)
    (hres : getDChk x.get amp.toNat 1 = some v) (hwf : Mem.Wf M) (hS : M.size = n)
    (hn : n % 32 = 0) (htop : 0x520 ≤ n) (hroom : S.length + 64 < 1024) :
    ∃ M', SFunc.RunExact prog sevm (St b (ρ :: b0 :: b1 :: b2 :: amp :: S) M
        (G + costGetDMem x amp.toNat)) t_07b7_c29 (.returned (St b (Nat.toB256 v :: S) M' G)) ∧
      (Mem.KeepsOff M M' gdmWin ∧ Mem.Wf M' ∧ M'.size = n) := by
  have hT := MemTrack.init hwf gdmWin
  rw [show G + costGetDMem x amp.toNat = G + costGetD x.v0 x.v1 x.v2 amp.toNat + 6676 from by
    unfold costGetDMem; omega]
  simp only [SFunc.runExact_iff_runExactCut_nil]
  -- prologue
  xstep; xmstore 0x1c0; xmstore 0x140; xmstore 0x160; xmstore 0x180; xmstore 0x1a0
  xstep; xmstore 0x420
  xname M1
  -- the outer frame save, `[0x140, 0x420)`
  have hρ1 := hT.words.memWord (o := 0x1c0) (v := ρ) (by wmem)
  have hc1 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hT1 := (hT.sub (L' := [(0x1a0, amp), (0x180, b2), (0x160, b1), (0x140, b0)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])).saveMem'
    (c := 0x420) (lo := 0x140) rfl rfl 23
  have hS1 : (saveMem M1 0x420 0x140 23).size = n := by
    rw [saveMem_size (by omega)]; exact hS
  have hctr1 := saveMem_ctr (n := 23)
    (hc1.trans (by decide : Bytes.toB256 [1, 64] = Nat.toB256 0x140))
  refine xlift (fun _ k => rxc_save_07d3 (by rw [hS]; exact hn) (by omega)
    (hc1.trans (by decide)) (by omega) k) ?_
  clear hT hS
  have hT := hT1.withWords (Words.cons.mpr ⟨⟨by omega, hctr1⟩, hT1.words⟩)
  have hS := hS1
  clear hT1 hS1
  generalize hF1 : (frameWords M1 0x140 23).reverse ++ S = S1
  have hS1l : S1.length = S.length + 23 := by
    rw [← hF1, List.length_append, List.length_reverse, length_frameWords]; omega
  -- the inner frame save, `[0x140, 0x300)`
  xstep; xstep; xstep; xmstore 0x300
  xname M3
  have hamp3 := hT.words.memWord (o := 0x1a0) (v := amp) (by wmem)
  have hc2 := hT.words.memWord (o := 0x300) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hT2 := (hT.sub (L' := [(0x420, Nat.toB256 (0x140 + 32 * 23)), (0x180, b2), (0x160, b1),
      (0x140, b0)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])).saveMem'
    (c := 0x300) (lo := 0x140) rfl rfl 14
  have hS2 : (saveMem M3 0x300 0x140 14).size = n := by
    rw [saveMem_size (by omega)]; exact hS
  refine xlift (fun _ k => rxc_save_0800 (by rw [hS]; exact hn) (by omega)
    (hc2.trans (by decide)) (by gdmlen) k) ?_
  clear hT hS
  have hT := hT2
  have hS := hS2
  clear hT2 hS2
  generalize hF2 : (frameWords M3 0x140 14).reverse ++ Bytes.toB256 [4, 64] :: S1 = S2
  have hS2l : S2.length = S.length + 38 := by
    rw [← hF2, List.length_append, List.length_reverse, length_frameWords, List.length_cons]
    omega
  -- copy the balances to `0x320 … 0x360`, call `_xp_mem`
  xstep; xstep; xstep; xstep; xmload' 0x140; xstep; xmstore' 0x320
  xstep; xstep; xstep; xmload' 0x160; xstep; xstep; xstep; xmstore' 0x340
  xstep; xstep; xstep; xmload' 0x180; xstep; xstep; xstep; xmstore' 0x360
  xstep; xstep; xmload 0x360; xmload 0x340; xmload 0x320
  xname M4
  obtain ⟨x0, x1, x2, ⟨M5, hcall, hk5, hwf5, hS5⟩, hx⟩ := xpMem_exact
    (sevm := sevm) (b := b) (ret := Nat.toB256 (0x851 + 6)) (G := G + costGetD x.v0 x.v1 x.v2 amp.toNat + 2768)
    (S := S2)
    hX hT.wf hS hn (by omega)
    (by gdmlen)
  subst hx
  refine xlift (fun _ k => rxc_pcCall prog_34 (by decide)
    (by gdmlen) hcall k) ?_
  have hT5 : MemTrack M M5 gdmWin [] :=
    ⟨hT.keeps.trans (hk5.widen (by decide)), Words.nil _, hwf5, fun _ => by rw [hS5]; exact hn⟩
  clear hT hS
  have hT := hT5
  have hS := hS5
  clear hT5 hS5
  -- store its words, restore `[0x140, 0x300)`
  xstep; xmstore 0x3c0; xmstore 0x3e0; xmstore 0x400; xstep; xmstore 0x300
  xname M6
  have hc6 := hT.words.memWord (o := 0x300) (v := Bytes.toB256 [2, 0xe0]) (by wmem)
  subst hF2
  refine xlift (fun _ k => rxc_restore_086b (by simp only [List.length_reverse, length_frameWords])
    (by rw [hS]; exact hn) (by omega) (hc6.trans (by decide))
    (by gdmlen) k) ?_
  have hfr2 := restoreMem_frameWords (c := 0x300) (lo := 0x140) (n := 14) (M := M6) (W := M3)
    (by omega) (by decide)
  have hamp7 := Words.of_frameSlots hfr2 (j := 3) (by decide) hamp3
  have hoth7 := Words.restoreMem' (c := 0x300) (p := 0x2e0)
    (ws := (frameWords M3 0x140 14).reverse)
    (hT.words.sub (L' := [(0x3c0, x0), (0x3e0, x1), (0x400, x2)]) (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl <;> simp only [true_or, or_true])) (by decide)
    (by simp only [List.length_reverse, length_frameWords]; rfl)
  have hT7 := (MemTrack.restoreMem (c := 0x300) rfl (frameWords M3 0x140 14).reverse hT
    (p := 0x2e0) (fun k hk => by
      simp only [List.length_reverse, length_frameWords] at hk
      have h14 : ∀ k, k < 14 → coversWord gdmWin (0x2e0 - 32 * k) = true := by decide
      exact h14 k hk)).withWords (Words.append.mpr ⟨hamp7, hoth7⟩)
  have hS7 : (restoreMem 0x300 M6 0x2e0 (frameWords M3 0x140 14).reverse).size = n := by
    rw [restoreMem_size _ (by omega) (by omega)]; exact hS
  clear hT hS
  have hT := hT7
  have hS := hS7
  clear hT7 hS7
  -- the arguments of `get_D` to `0x440 … 0x4a0`, call it
  xstep; xstep; xstep; xmload' 0x3c0; xstep; xmstore' 0x440
  xstep; xstep; xstep; xmload' 0x3e0; xstep; xstep; xstep; xmstore' 0x460
  xstep; xstep; xstep; xmload' 0x400; xstep; xstep; xstep; xmstore' 0x480
  xstep; xstep; xmload 0x1a0; xmstore 0x4a0
  xmload 0x4a0; xmload 0x480; xmload 0x460; xmload 0x440
  xname M8
  obtain ⟨M9, hso, hgD⟩ := getD_exact (sevm := sevm) (b := b) (ρ := Nat.toB256 (0x8c6 + 6)) (G := G + 1648)
    (S := S1) (by rw [hS]; exact hn) (by omega)
    (by gdmlen) hres
  rw [show G + 1648 + costGetD x0.toNat x1.toNat x2.toNat amp.toNat =
    G + costGetD x0.toNat x1.toNat x2.toNat amp.toNat + 1648 from by omega] at hgD
  refine xlift (fun _ k => rxc_pcCall prog_417 (by decide)
    (by gdmlen) hgD k) ?_
  have hT9 : MemTrack M M9 gdmWin [] :=
    ⟨hT.keeps.trans ((hso.keepsOff hT.wf).widen (by decide)), Words.nil _, hso.wf hT.wf,
      fun _ => by rw [hso.size, hS]; exact hn⟩
  have hS9 : M9.size = n := by rw [hso.size, hS]
  clear hT hS
  have hT := hT9
  have hS := hS9
  clear hT9 hS9
  -- store `D`, restore `[0x140, 0x420)`
  xstep; xmstore 0x500; xstep; xmstore 0x420
  xname M10
  have hc10 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [4, 0]) (by wmem)
  subst hF1
  refine xlift (fun _ k => rxc_restore_08d8 (by simp only [List.length_reverse, length_frameWords])
    (by rw [hS]; exact hn) (by omega) (hc10.trans (by decide)) (by omega) k) ?_
  have hfr1 := restoreMem_frameWords (c := 0x420) (lo := 0x140) (n := 23) (M := M10) (W := M1)
    (by omega) (by decide)
  have hρ11 := Words.of_frameSlots hfr1 (j := 4) (by decide) hρ1
  have hv11 := Words.restoreMem' (c := 0x420) (p := 0x400)
    (ws := (frameWords M1 0x140 23).reverse)
    (hT.words.sub (L' := [(0x500, Nat.toB256 v)]) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]; wmem)) (by decide)
    (by simp only [List.length_reverse, length_frameWords]; rfl)
  have hT11 := (MemTrack.restoreMem (c := 0x420) rfl (frameWords M1 0x140 23).reverse hT
    (p := 0x400) (fun k hk => by
      simp only [List.length_reverse, length_frameWords] at hk
      have h23 : ∀ k, k < 23 → coversWord gdmWin (0x400 - 32 * k) = true := by decide
      exact h23 k hk)).withWords (Words.append.mpr ⟨hρ11, hv11⟩)
  have hS11 : (restoreMem 0x420 M10 0x400 (frameWords M1 0x140 23).reverse).size = n := by
    rw [restoreMem_size _ (by omega) (by omega)]; exact hS
  clear hT hS
  have hT := hT11
  have hS := hS11
  clear hT11 hS11
  -- the exit: `return D`
  xstep; xmload 0x500; xmstore 0x0; xmload 0x0; xmload 0x1c0
  xret

end Blanc.Lift.Curve3Pool
