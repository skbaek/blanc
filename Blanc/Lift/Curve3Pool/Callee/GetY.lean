import Blanc.Lift.Curve3Pool.Callee.GetYCoins
import Blanc.Lift.Curve3Pool.Callee.A
import Blanc.Lift.Curve3Pool.Callee.GetD

/-!
# `get_y` (entry 252, pc `0x18a4`): the callee contract

`get_y(i, j, x, xp_)` (lines 354–397).  The bytes:

* the prologue writes the return slot (`0x200`) and the arguments `i`, `j`, `x`, `xp_`
  (`0x140 … 0x1e0`) and asserts `i ≠ j`, `0 ≤ j < 3`, `0 ≤ i < 3`;
* `amp = self._A()`: the eight words `0x140 … 0x220` pushed, `_A` called (entry 27, `a_spec`),
  `amp` parked at `0x260`, the words popped back, `amp` stored at `0x220`;
* `D = self.get_D(xp_, amp)`: the frame `[0x140, 0x2a0)` saved (11 words, `0x1971`), `xp_` and
  `amp` copied to `0x2c0 … 0x320`, `get_D` called (entry 417, `getD_spec`), `D` parked at
  `0x380`, the frame restored (`0x19e0`);
* `c = D`, `S_ = 0`, `Ann = amp * N_COINS`, `_x = 0`, then the coin loop and the Newton `y`
  loop of `GetYCoins.lean`/`GetYLoop.lean`.

`getY_spec`: every run returns `y` over the caller's stack with `0 ≤ i, j < 3`,
`aChk s t = some amp` (`_A`'s value) and `getYChk amp i j x xp_ = some y`, the world moved only
by `_A`'s storage reads (`aBase`), and memory kept off `[0, 0x20)` and `[0x140, 0x4c0)`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-! ## The frame chains around the call of `get_D` -/

/-- Counter `0x2a0`, bound `0x2a0`, exit tag `0x1993`, head tag `0x1971`. -/
def saveTpl_1971 : FrameLoopTpl := ⟨0x02, 0xa0, 0x02, 0xa0, 0x19, 0x93, 0x19, 0x71⟩

def saveKs_1971 : List Nat := [267, 282, 297, 312, 327, 342, 357, 372, 387, 402]

theorem saveTpl_1971_c : saveTpl_1971.c = 0x2a0 := by decide

theorem t_1971_c252_eq : t_1971_c252 = saveTpl_1971.saveTree t_1993_c402 saveKs_1971 := by
  decide +kernel

theorem saveChain_1971 : FrameSaveChain prog saveTpl_1971 t_1993_c402 saveKs_1971 := by
  unfold FrameSaveChain
  decide +kernel

/-- Counter `0x2a0`, bound `lo = 0x140`, exit tag `0x1a03`, head tag `0x19e0`. -/
def restoreTpl_19e0 : FrameLoopTpl := ⟨0x02, 0xa0, 0x01, 0x40, 0x1a, 0x03, 0x19, 0xe0⟩

def restoreKs_19e0 : List Nat := [418, 432, 446, 460, 474, 490, 504, 518, 534, 547]

theorem restoreTpl_19e0_c : restoreTpl_19e0.c = 0x2a0 := by decide

theorem t_19e0_c402_eq : t_19e0_c402 = restoreTpl_19e0.restoreTree t_1a03_c547 restoreKs_19e0 := by
  decide +kernel

theorem restoreChain_19e0 : FrameRestoreChain prog restoreTpl_19e0 t_1a03_c547 restoreKs_19e0 := by
  unfold FrameRestoreChain
  decide +kernel

section Chains

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

theorem ric_save_1971 (hsz : M.size % 32 = 0) (hcs : 0x2c0 ≤ M.size)
    (hctr : memWord M 0x2a0 = Nat.toB256 0x140)
    (run : SFunc.RunCut prog sevm [] (St b S M G) t_1971_c252 r) :
    ∃ G', SFunc.RunCut prog sevm [] (St b ((frameWords M 0x140 11).reverse ++ S)
      (saveMem M 0x2a0 0x140 11) G') t_1993_c402 r := by
  rw [t_1971_c252_eq] at run
  have h := ric_frameSave_chain saveChain_1971 (fun _ _ h => by cases h) hsz
    (by rw [saveTpl_1971_c]; omega) (by rw [saveTpl_1971_c]; exact hctr)
    (by rw [saveTpl_1971_c]; decide) run
  rw [saveTpl_1971_c] at h
  exact h

theorem ric_restore_19e0 {ts : List B256} (hts : ts.length = 11) (hsz : M.size % 32 = 0)
    (hcs : 0x2c0 ≤ M.size) (hctr : memWord M 0x2a0 = Nat.toB256 0x280)
    (run : SFunc.RunCut prog sevm [] (St b (ts ++ S) M G) t_19e0_c402 r) :
    ∃ G', SFunc.RunCut prog sevm [] (St b S (restoreMem 0x2a0 M 0x280 ts) G') t_1a03_c547 r := by
  rw [t_19e0_c402_eq] at run
  have h := ric_frameRestore_chain (lo := 0x140) restoreChain_19e0 (fun _ _ h => by cases h)
    (by rw [hts]; rfl) hsz (by rw [restoreTpl_19e0_c]; omega) (by decide)
    (by rw [restoreTpl_19e0_c]; decide) (by rw [restoreTpl_19e0_c]; exact hctr) run
  rw [restoreTpl_19e0_c] at h
  exact h

end Chains

/-! ## The bytes' evaluation order is the model's -/

/-- `get_y` after `D` and `Ann`, on naturals in the bytes' evaluation order. -/
def gyRes (i j x x0 x1 x2 D ann : Nat) : Option Nat :=
  (gyCoinStep i j 0 x x0 D (D, 0)).bind fun cs =>
    (gyCoinStep i j 1 x x1 D cs).bind fun cs =>
      (gyCoinStep i j 2 x x2 D cs).bind fun cs => ydPostRes cs.1 cs.2 D ann

theorem gyRes_core {i j x x0 x1 x2 D ann y : Nat} (hi : i < 3) (hj : j < 3) (hij : i ≠ j)
    (h : gyRes i j x x0 x1 x2 D ann = some y) :
    ((cOfChk (withAt (V3.mk x0 x1 x2).get ⟨i, hi⟩ x (others ⟨j, hj⟩).1)
        (withAt (V3.mk x0 x1 x2).get ⟨i, hi⟩ x (others ⟨j, hj⟩).2) D ann).bind fun c =>
      (bOfChk (withAt (V3.mk x0 x1 x2).get ⟨i, hi⟩ x (others ⟨j, hj⟩).1)
        (withAt (V3.mk x0 x1 x2).get ⟨i, hi⟩ x (others ⟨j, hj⟩).2) D ann).bind fun b =>
        loopYChk c b D 1 255 D) = some y := by
  unfold gyRes at h
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  all_goals first
    | exact absurd rfl hij
    | (simp only [gyCoinStep, Nat.reduceEqDiff, ↓reduceIte, Option.bind_some] at h
       simp only [Option.bind_eq_some_iff] at h
       obtain ⟨⟨c1, s1⟩, h1, ⟨c2, s2⟩, h2, hp⟩ := h
       exact ydRes_core h1 h2 hp)

theorem gyRes_getYChk {amp i j x x0 x1 x2 D ann y : Nat} (hi : i < 3) (hj : j < 3) (hij : i ≠ j)
    (hD : getDChk (V3.mk x0 x1 x2).get amp 1 = some D) (hann : chkMul amp 3 = some ann)
    (h : gyRes i j x x0 x1 x2 D ann = some y) :
    getYChk amp ⟨i, hi⟩ ⟨j, hj⟩ x (V3.mk x0 x1 x2).get = some y := by
  unfold getYChk
  rw [if_neg (fun he => hij (Fin.mk.inj_iff.mp he))]
  simp only [hD, hann, Option.bind_eq_bind, Option.bind_some]
  exact gyRes_core hi hj hij h

/-! ## The callee contract -/

theorem t_18a4_c252_prog : prog[252]? = some t_18a4_c252 := by decide +kernel

/-- `i < 3` from the two range asserts. -/
theorem lt_three_of_asserts {i : B256}
    (h1 : B256.eqCheck (B256.sltCheck i (Bytes.toB256 [0x00])) 0 ≠ 0)
    (h2 : B256.sltCheck i (Bytes.toB256 [0x03]) ≠ 0) : i.toNat < 3 := by
  refine B256.toNat_lt_three_of_slt ?_ ?_
  · intro hs
    apply h1
    have h0 : Bytes.toB256 [0x00] = 0 := by decide
    rw [h0]
    unfold B256.sltCheck; rw [ite_eq_left hs]; decide
  · by_contra hs
    apply h2
    unfold B256.sltCheck; rw [ite_eq_right hs]

-- SEGMENT: getY_spec
/-- **`get_y`'s callee contract.**  Any outcome of the entry tree from the call's state is a
return: `0 ≤ i, j < 3`, `_A`'s value `amp` (`aChk`), the result `v` over the caller's stack with
`getYChk amp i j x xp_ = some v`, the world moved only by `_A`'s storage reads (`aBase`), and
memory kept off `get_y`'s windows `[0, 0x20)` and `[0x140, 0x4c0)`, well formed, word-aligned,
with `v` at scratch word `0`. -/
theorem getY_spec {sevm : Sevm} {b : Devm} {ρ i j x x0 x1 x2 : B256} {S : List B256} {M : Mem}
    {G : Nat} {s : State} {o : Outcome} (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s) (hwf : Mem.Wf M) (hsz : M.size % 32 = 0)
    (run : SFunc.Run prog sevm (St b (ρ :: i :: j :: x :: x0 :: x1 :: x2 :: S) M G)
      t_18a4_c252 o) :
    ∃ d, o = .returned d ∧ ∃ v M' G', d = St (aBase sevm b) (v :: S) M' G' ∧
      ∃ amp, aChk s sevm.benvStat.time.toNat = some amp ∧
      ∃ (hi : i.toNat < 3) (hj : j.toNat < 3),
        getYChk amp ⟨i.toNat, hi⟩ ⟨j.toNat, hj⟩ x.toNat (V3.mk x0.toNat x1.toNat x2.toNat).get =
          some v.toNat ∧
      Mem.KeepsOff M M' gyWin ∧ Words M' [(0, v)] ∧ Mem.Wf M' ∧ M'.size % 32 = 0 := by
  have hc := run.cut
  clear run
  have hT := MemTrack.init hwf gyWin
  unfold t_18a4_c252 at hc
  have hd := ric_dest hc
  clear hc
  obtain ⟨_, run⟩ := hd
  -- the arguments
  imstoreO 0x200; imstoreO 0x140; imstoreO 0x160; imstoreO 0x180; imstoreO 0x1a0
  imstoreO 0x1c0; imstoreO 0x1e0
  -- `assert i != j`, `0 <= j < 3`, `0 <= i < 3`
  imload 0x160; imload 0x140; istep; istep
  iassert hij
  istep; imload 0x160; isltV; istep; istep
  iassert hj1
  istep; imload 0x160; isltV; istep
  iassert hj2
  istep; imload 0x140; isltV; istep; istep
  iassert hi1
  istep; imload 0x140; isltV; istep
  iassert hi2
  have hi3 := lt_three_of_asserts hi1 hi2
  have hj3 := lt_three_of_asserts hj1 hj2
  have hne : i ≠ j := by
    intro he
    rw [he, (B256.xor_eq_zero_iff _ _).mpr rfl] at hij
    exact hij rfl
  clear hij hi1 hi2 hj1 hj2
  -- `amp = self._A()`, around the eight words `0x140 … 0x220`
  imload 0x140; imload 0x160; imload 0x180; imload 0x1a0; imload 0x1c0; imload 0x1e0
  imload 0x200; imloadU 0x220
  rename_i w7
  obtain ⟨_, DA, hcallA, run⟩ := ric_pcCall a_neverHalts prog_27 (by decide) run
  obtain ⟨dA, hdA, amp, MA, GA, hDA, hamp, hkA, hwfA, halA⟩ := a_spec hfork ha hT.wf hcallA
  cases hdA
  subst hDA
  have hTA : MemTrack M MA gyWin [] :=
    ⟨hT.keeps.trans (hkA.widen (by decide)), Words.nil _, hwfA, fun h => halA (hT.aligned h)⟩
  clear hT
  have hT := hTA
  clear hTA
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  imstoreO 0x260; imstoreO 0x220; imstoreO 0x200; imstoreO 0x1e0; imstoreO 0x1c0; imstoreO 0x1a0
  imstoreO 0x180; imstoreO 0x160; imstoreO 0x140
  imload 0x260; imstoreO 0x220
  istep; imstoreO 0x2a0
  rename_i M1 G1
  -- the frame save, `[0x140, 0x2a0)`
  have hc1 := hT.words.memWord (o := 0x2a0) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hcs1 := hT.mem_size (o := 0x2a0) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hal1 := hT.aligned hsz
  have hi1 := hT.words.memWord (o := 0x140) (v := i) (by wmem)
  have hj1 := hT.words.memWord (o := 0x160) (v := j) (by wmem)
  have hx1 := hT.words.memWord (o := 0x180) (v := x) (by wmem)
  have hx01 := hT.words.memWord (o := 0x1a0) (v := x0) (by wmem)
  have hx11 := hT.words.memWord (o := 0x1c0) (v := x1) (by wmem)
  have hx21 := hT.words.memWord (o := 0x1e0) (v := x2) (by wmem)
  have hρ1 := hT.words.memWord (o := 0x200) (v := ρ) (by wmem)
  have hamp1 := hT.words.memWord (o := 0x220) (v := amp) (by wmem)
  have hT1 := (hT.sub (L' := [(0x220, amp), (0x1e0, x2), (0x1c0, x1), (0x1a0, x0)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])).saveMem'
    (c := 0x2a0) (lo := 0x140) rfl rfl 11
  clear hT
  obtain ⟨_, run⟩ := ric_save_1971 hal1 (by omega) (hc1.trans (by decide)) run
  have hctr1 := saveMem_ctr (n := 11)
    (hc1.trans (by decide : Bytes.toB256 [1, 64] = Nat.toB256 0x140))
  have hT := hT1.withWords (Words.cons.mpr ⟨⟨by rw [saveMem_size (by omega)]; omega, hctr1⟩,
    hT1.words⟩)
  clear hT1
  -- `xp_` and `amp` to `0x2c0 … 0x320`, call `get_D`
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  istep; istep; istep; imload' 0x1a0; istep; imstoreO' 0x2c0
  istep; istep; istep; imload' 0x1c0; istep; istep; istep; imstoreO' 0x2e0
  istep; istep; istep; imload' 0x1e0; istep; istep; istep; imstoreO' 0x300
  istep; istep; imload 0x220; imstoreO 0x320
  imload 0x320; imload 0x300; imload 0x2e0; imload 0x2c0
  obtain ⟨_, D8, hcallD, run⟩ := ric_pcCall getD_neverHalts prog_417 (by decide) run
  have hcs8 := hT.mem_size (o := 0x320) (v := amp) (by wmem)
  obtain ⟨d8, hd8, D, M9, G9, hD9, hgd, hsize9, hw9, hk9⟩ :=
    getD_spec (hT.aligned hsz) (by omega) hcallD
  cases hd8
  subst hD9
  have hT9 : MemTrack M M9 gyWin [] :=
    ⟨hT.keeps.trans ((hk9 hT.wf).1.widen (by decide)), Words.nil _, (hk9 hT.wf).2,
      fun h => by rw [hsize9]; exact hT.aligned h⟩
  have hcs9 : 0x2c0 ≤ M9.size := by omega
  clear hT
  have hT := hT9
  clear hT9
  -- park `D` at `0x380`, restore `[0x140, 0x2a0)`
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  imstoreO 0x380; istep; imstoreO 0x2a0
  rename_i M10 G10
  have hc10 := hT.words.memWord (o := 0x2a0) (v := Bytes.toB256 [2, 0x80]) (by wmem)
  have hcs10 := hT.mem_size (o := 0x2a0) (v := Bytes.toB256 [2, 0x80]) (by wmem)
  obtain ⟨_, run⟩ := ric_restore_19e0 (by simp only [List.length_reverse, length_frameWords])
    (hT.aligned hsz) (by omega) (hc10.trans (by decide)) run
  have hfr := restoreMem_frameWords (c := 0x2a0) (lo := 0x140) (n := 11) (M := M10) (W := M1)
    (by omega) (by decide)
  have hw11 := Words.append.mpr ⟨Words.of_frameSlots hfr (j := 0) (by decide) hi1,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 1) (by decide) hj1,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 2) (by decide) hx1,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 3) (by decide) hx01,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 4) (by decide) hx11,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 5) (by decide) hx21,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 6) (by decide) hρ1,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 7) (by decide) hamp1,
      Words.restoreMem' (c := 0x2a0) (p := 0x280) (ws := (frameWords M1 0x140 11).reverse)
        (hT.words.sub (L' := [(0x380, D)]) (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; wmem)) (by decide)
        (by simp only [List.length_reverse, length_frameWords]; rfl)⟩⟩⟩⟩⟩⟩⟩⟩
  have hT11 := (MemTrack.restoreMem (c := 0x2a0) rfl (frameWords M1 0x140 11).reverse hT
    (p := 0x280) (fun k hk => by
      simp only [List.length_reverse, length_frameWords] at hk
      have h11 : ∀ k, k < 11 → coversWord gyWin (0x280 - 32 * k) = true := by decide
      exact h11 k hk)).withWords hw11
  clear hT hw11
  have hT := hT11
  clear hT11
  -- `c = D`, `S_ = 0`, `Ann = amp * N_COINS`, `_x = 0`, the coin-loop counter
  rw [t_1a03_c547_eq] at run
  unfold gyMid at run
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  imload 0x380; imstoreO 0x280; imload 0x280; imstoreO 0x3a0; istep; imstoreO 0x3c0
  imload 0x220; istep
  obtain ⟨hm, _, run⟩ := ric_vyMulT vyRevertT_noOk run
  imstoreO 0x3e0; istep; imstoreO 0x400
  istep; istep; istep; istep; istep; imstoreO' 0x420
  rename_i Mc G11
  istep
  rename_i G12
  rw [toB256_three, toB256_0x420] at run
  have hi12 := hT.words.memWord (o := 0x140) (v := i) (by wmem)
  have hj12 := hT.words.memWord (o := 0x160) (v := j) (by wmem)
  have hx12 := hT.words.memWord (o := 0x180) (v := x) (by wmem)
  have hx012 := hT.words.memWord (o := 0x1a0) (v := x0) (by wmem)
  have hx112 := hT.words.memWord (o := 0x1c0) (v := x1) (by wmem)
  have hx212 := hT.words.memWord (o := 0x1e0) (v := x2) (by wmem)
  have hρ12 := hT.words.memWord (o := 0x200) (v := ρ) (by wmem)
  have hamp12 := hT.words.memWord (o := 0x220) (v := amp) (by wmem)
  have hD12 := hT.words.memWord (o := 0x280) (v := D) (by wmem)
  have hc12 := hT.words.memWord (o := 0x3a0) (v := D) (by wmem)
  have hs12 := hT.words.memWord (o := 0x3c0) (v := Bytes.toB256 [0x00]) (by wmem)
  have hann12 := hT.words.memWord (o := 0x3e0) (v := amp * Bytes.toB256 [0x03]) (by wmem)
  have hxv12 := hT.words.memWord (o := 0x400) (v := Bytes.toB256 [0x00]) (by wmem)
  have hcc12 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [0x00]) (by wmem)
  have hcs12 := hT.mem_size (o := 0x420) (v := Bytes.toB256 [0x00]) (by wmem)
  have hF := WordFrame.init (M0 := Mc) (lo := 0x140) (n := 24) (hT.aligned hsz) (by omega)
  rw [show frameWords Mc 0x140 24 = [memWord Mc 0x140, memWord Mc 0x160, memWord Mc 0x180,
    memWord Mc 0x1a0, memWord Mc 0x1c0, memWord Mc 0x1e0, memWord Mc 0x200, memWord Mc 0x220,
    memWord Mc 0x240, memWord Mc 0x260, memWord Mc 0x280, memWord Mc 0x2a0, memWord Mc 0x2c0,
    memWord Mc 0x2e0, memWord Mc 0x300, memWord Mc 0x320, memWord Mc 0x340, memWord Mc 0x360,
    memWord Mc 0x380, memWord Mc 0x3a0, memWord Mc 0x3c0, memWord Mc 0x3e0, memWord Mc 0x400,
    memWord Mc 0x420] from rfl, hi12, hj12, hx12, hx012, hx112, hx212, hρ12, hamp12, hD12, hc12,
    hs12, hann12, hxv12, hcc12, toB256_zero] at hF
  have hst := gyStage0 (M0 := Mc) hT.wf hF run
  obtain ⟨y, hres, hy, Mf, Gf, hr, hkf, hwff, hwf0, half⟩ := hst
  have ho : o = .returned (St (aBase sevm b) (Nat.toB256 y :: S) Mf Gf) := by injection hr
  subst ho
  have hann : chkMul amp.toNat 3 = some (amp * Bytes.toB256 [0x03]).toNat := by
    have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
    rw [e3]; exact chkMul_toNat_of_nofm hm
  refine ⟨_, rfl, Nat.toB256 y, Mf, Gf, rfl, amp.toNat, hamp, hi3, hj3, ?_,
    hT.keeps.trans hkf, hwf0, hwff, half⟩
  rw [B256.toNat_toB256_of_lt hy]
  refine gyRes_getYChk hi3 hj3 (fun h => hne (by apply B256.toNat_inj; exact h)) hgd hann ?_
  unfold gyRes
  rw [show (Nat.toB256 0).toNat = 0 by decide] at hres
  exact hres

/-! ## Kernel facts for the frame-walk bridge (`xa_callee`) -/

/-- `get_y`'s entry closure, with `_A`'s and `get_D`'s. -/
def gyEntries : List Nat :=
  [9, 27, 44, 70, 71, 72, 95, 115, 116, 117, 136, 137, 138, 158, 159, 160, 180, 181, 182, 200,
    201, 252, 267, 282, 297, 312, 327, 342, 357, 372, 387, 402, 417, 418, 431, 432, 445, 446,
    459, 460, 473, 474, 487, 488, 489, 490, 503, 504, 517, 518, 531, 532, 533, 534, 547, 559,
    560]

theorem gy_execFreeSet : ExecFreeSet cert.prog gyEntries = true := by decide +kernel

theorem gy_free : t_18a4_c252.execFreeIn gyEntries = true := by decide +kernel

theorem gy_neverHalts : calleeNeverHalts prog 252 128 = true := by decide +kernel

end Blanc.Lift.Curve3Pool
