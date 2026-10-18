import Blanc.Lift.Curve3Pool.Callee.GetDMemExact
import Blanc.Lift.Curve3Pool.Callee.AGrow

/-!
# `get_D_mem` over a memory of `0x400`

`getDMem_exact` runs `get_D_mem` over a memory already covering `[0, 0x520)`.
`remove_liquidity_imbalance` calls it first with the memory at `0x400`: the callee's counter
store at `0x420`, `get_D`'s arguments at `0x440 … 0x4a0` and `D` at `0x500` grow it to `0x520`,
`28` gas more in all. `getDMem_exact_400` is that run.

`rxc_mstoreT_growTo` is the tracked `MSTORE` at an aligned offset at or past the end.
-/

namespace Blanc.Lift

open Jaune

/-- A word store at an aligned offset at or past an aligned end grows the memory to the word's
end. -/
theorem Mem.size_write_word_past {N : Mem} {w : B256} {o : Nat} (h : N.size % 32 = 0)
    (ho : N.size ≤ o) (ho32 : o % 32 = 0) : (N.write o w.toBytes).size = o + 32 := by
  have hc : ceil32 (o + 32) = o + 32 := by
    unfold ceil32; rw [show (o + 32) % 32 = 0 by omega]
  rcases hb : w.toBytes with _ | ⟨b, bs⟩
  · exact absurd (hb ▸ B256.length_toBytes w) (by simp only [List.length_nil,
      OfNat.zero_ne_ofNat, not_false_eq_true])
  · have hlen : (b :: bs).length = 32 := hb ▸ B256.length_toBytes w
    simp only [Mem.write, hlen]
    split_ifs with h1
    all_goals dsimp only
    all_goals first | omega | exact hc

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M M₀ : Mem}
  {G n : Nat} {f : SFunc} {W : List (Nat × Nat)} {L : List (Nat × B256)}

/-- A tracked `MSTORE` at an aligned offset at or past the end of an aligned memory. -/
theorem rxc_mstoreT_growTo {i v : B256} {o c : Nat} {R : Mem → Seg} {Q : Mem → Prop}
    (hT : MemTrack M₀ M W L) (hS : M.size = n)
    (hc : 3 + (calculateMemoryGasCost (o + 32) - calculateMemoryGasCost n) = c)
    (hn : n % 32 = 0) (hi : i.toNat = o) (ho : n ≤ o) (ho32 : o % 32 = 0)
    (hW : coversWord W o = true)
    (k : MemTrack M₀ (M.write o v.toBytes) W ((o, v) :: wordsOff o L) →
      (M.write o v.toBytes).size = o + 32 →
      ∃ M', SFunc.RunExactCut fs sevm C (St b S (M.write o v.toBytes) G) f (R M') ∧ Q M') :
    ∃ M', SFunc.RunExactCut fs sevm C
      (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore) f) (R M') ∧ Q M' := by
  subst hi hc
  have hsz : (M.write i.toNat v.toBytes).size = i.toNat + 32 :=
    Mem.size_write_word_past (by rw [hS]; exact hn) (by rw [hS]; exact ho) ho32
  obtain ⟨M', run, hq⟩ := k (hT.writeO v hW) hsz
  refine ⟨M', rxc_mstore ?_ rfl run, hq⟩
  rw [St.extCost_eq hS, show memExtSize n i.toNat 32 = i.toNat + 32 from by
    unfold memExtSize ceilDiv; simp only [Nat.max_def]; split_ifs <;> first | contradiction | omega]
  rfl

end Fwd

end Blanc.Lift

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift
open Blanc.StableSwapNewton

set_option hygiene false in
/-- `MSTORE` growing the tracked memory to the word at `o`, at cost `c`; renews `hT`, `hS`. -/
macro "xmstoreG' " o:term "," c:term : tactic => `(tactic|
  (refine rxc_mstoreT_growTo (o := $o) (c := $c) hT hS (by decide) hn rfl (by decide) (by decide)
     (by decide) ?_
   intro hT hS
   simp only [wordsOff, List.filter_cons, List.filter_nil, Nat.reduceAdd, Nat.reduceLeDiff,
     decide_true, decide_false, Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false,
     ite_true, ite_false, Bool.false_eq_true, ↓reduceIte] at hT))

-- SEGMENT: getDMem_exact_400
theorem getDMem_exact_400 {sevm : Sevm} {b : Devm} {ρ b0 b1 b2 amp : B256} {S : List B256} {M : Mem}
    {G v : Nat} {x : V3} (hX : xpChk ⟨b0.toNat, b1.toNat, b2.toNat⟩ = some x)
    (hres : getDChk x.get amp.toNat 1 = some v) (hwf : Mem.Wf M) (hS : M.size = 0x400)
    (hroom : S.length + 64 < 1024) :
    ∃ M', SFunc.RunExact prog sevm (St b (ρ :: b0 :: b1 :: b2 :: amp :: S) M
        (G + costGetDMem x amp.toNat + 28)) t_07b7_c29 (.returned (St b (Nat.toB256 v :: S) M' G)) ∧
      (Mem.KeepsOff M M' gdmWin ∧ Mem.Wf M' ∧ M'.size = 0x520) := by
  have hT := MemTrack.init hwf gdmWin
  have hn : (0x400 : Nat) % 32 = 0 := by decide
  rw [show G + costGetDMem x amp.toNat + 28 = G + costGetD x.v0 x.v1 x.v2 amp.toNat + 6704 from by
    unfold costGetDMem; omega]
  simp only [SFunc.runExact_iff_runExactCut_nil]
  -- prologue
  xstep; xmstore 0x1c0; xmstore 0x140; xmstore 0x160; xmstore 0x180; xmstore 0x1a0
  xstep; xstep; xmstoreG' 0x420, 9
  clear hn; have hn : (0x440 : Nat) % 32 = 0 := by decide
  xname M1
  -- the outer frame save, `[0x140, 0x420)`
  have hρ1 := hT.words.memWord (o := 0x1c0) (v := ρ) (by wmem)
  have hc1 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hT1 := (hT.sub (L' := [(0x1a0, amp), (0x180, b2), (0x160, b1), (0x140, b0)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])).saveMem'
    (c := 0x420) (lo := 0x140) rfl rfl 23
  have hS1 : (saveMem M1 0x420 0x140 23).size = 0x440 := by
    rw [saveMem_size (by omega)]; exact hS
  have hctr1 := saveMem_ctr (n := 23)
    (hc1.trans (by decide : Bytes.toB256 [1, 64] = Nat.toB256 0x140))
  refine xlift (fun _ k => rxc_save_07d3 (by rw [hS]) (by omega)
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
  have hS2 : (saveMem M3 0x300 0x140 14).size = 0x440 := by
    rw [saveMem_size (by omega)]; exact hS
  refine xlift (fun _ k => rxc_save_0800 (by rw [hS]) (by omega)
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
    (sevm := sevm) (b := b) (ret := Nat.toB256 (0x851 + 6)) (G := G + costGetD x.v0 x.v1 x.v2 amp.toNat + 2790)
    (S := S2)
    hX hT.wf hS hn (by omega)
    (by gdmlen)
  subst hx
  refine xlift (fun _ k => rxc_pcCall prog_34 (by decide)
    (by gdmlen) hcall k) ?_
  have hT5 : MemTrack M M5 gdmWin [] :=
    ⟨hT.keeps.trans (hk5.widen (by decide)), Words.nil _, hwf5, fun _ => by rw [hS5]⟩
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
    (by rw [hS]) (by omega) (hc6.trans (by decide))
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
  have hS7 : (restoreMem 0x300 M6 0x2e0 (frameWords M3 0x140 14).reverse).size = 0x440 := by
    rw [restoreMem_size _ (by omega) (by omega)]; exact hS
  clear hT hS
  have hT := hT7
  have hS := hS7
  clear hT7 hS7
  -- the arguments of `get_D` to `0x440 … 0x4a0`, call it
  xstep; xstep; xstep; xmload' 0x3c0; xstep; xmstoreG' 0x440, 6
  clear hn; have hn : (0x440 + 32 : Nat) % 32 = 0 := by decide
  xstep; xstep; xstep; xmload' 0x3e0; xstep; xstep; xstep; xmstoreG' 0x460, 6
  clear hn; have hn : (0x460 + 32 : Nat) % 32 = 0 := by decide
  xstep; xstep; xstep; xmload' 0x400; xstep; xstep; xstep; xmstoreG' 0x480, 6
  clear hn; have hn : (0x480 + 32 : Nat) % 32 = 0 := by decide
  xstep; xstep; xmload 0x1a0; xstep; xmstoreG' 0x4a0, 6
  clear hn; have hn : (0x4a0 + 32 : Nat) % 32 = 0 := by decide
  xmload 0x4a0; xmload 0x480; xmload 0x460; xmload 0x440
  xname M8
  obtain ⟨M9, hso, hgD⟩ := getD_exact (sevm := sevm) (b := b) (ρ := Nat.toB256 (0x8c6 + 6)) (G := G + 1658)
    (S := S1) (by rw [hS]) (by omega)
    (by gdmlen) hres
  rw [show G + 1658 + costGetD x0.toNat x1.toNat x2.toNat amp.toNat =
    G + costGetD x0.toNat x1.toNat x2.toNat amp.toNat + 1658 from by omega] at hgD
  refine xlift (fun _ k => rxc_pcCall prog_417 (by decide)
    (by gdmlen) hgD k) ?_
  have hT9 : MemTrack M M9 gdmWin [] :=
    ⟨hT.keeps.trans ((hso.keepsOff hT.wf).widen (by decide)), Words.nil _, hso.wf hT.wf,
      fun _ => by rw [hso.size, hS]⟩
  have hS9 : M9.size = 0x4a0 + 32 := by rw [hso.size, hS]
  clear hT hS
  have hT := hT9
  have hS := hS9
  clear hT9 hS9
  -- store `D`, restore `[0x140, 0x420)`
  xstep; xstep; xmstoreG' 0x500, 13
  clear hn; have hn : (0x500 + 32 : Nat) % 32 = 0 := by decide
  xstep; xmstore 0x420
  xname M10
  have hc10 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [4, 0]) (by wmem)
  subst hF1
  refine xlift (fun _ k => rxc_restore_08d8 (by simp only [List.length_reverse, length_frameWords])
    (by rw [hS]) (by omega) (hc10.trans (by decide)) (by omega) k) ?_
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
  have hS11 : (restoreMem 0x420 M10 0x400 (frameWords M1 0x140 23).reverse).size = 0x500 + 32 := by
    rw [restoreMem_size _ (by omega) (by omega)]; exact hS
  clear hT hS
  have hT := hT11
  have hS := hS11
  clear hT11 hS11
  -- the exit: `return D`
  xstep; xmload 0x500; xmstore 0x0; xmload 0x0; xmload 0x1c0
  xret


end Blanc.Lift.Curve3Pool
