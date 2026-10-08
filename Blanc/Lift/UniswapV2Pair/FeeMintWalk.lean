import Blanc.Lift.UniswapV2Pair.FeeMintCall
import Blanc.Lift.UniswapV2Pair.FeeMintArithmetic
import Blanc.Lift.UniswapV2Pair.SqrtWalk
import Blanc.Lift.UniswapV2Pair.LPMintCore
import Blanc.Lift.PackedWord

/-! Actual fee68 branches after the genuine factory observation. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Actual final cleanup preserves feeOn and every caller suffix word. -/
theorem feeReturn25_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_2870_c25 r) :
    ∃ gas, r = .done (.returned (St b (f :: R) M gas)) := by
  unfold t_2870_c25 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := ρ :: r1 :: r0 :: f :: R) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_swap (S' := r0 :: r1 :: ρ :: f :: R) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  exact ric_ret run

/-- Literal final cleanup costs23 and preserves the full world and memory. -/
theorem feeReturn25_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 23)) t_2870_c25
      (.returned (St b (f :: R) M G)) := by
  unfold t_2870_c25
  apply rx_dest
  apply rx_pop
  apply rx_pop
  apply rx_swap (S' := ρ :: r1 :: r0 :: f :: R) rfl
  apply rx_swap (S' := r0 :: r1 :: ρ :: f :: R) rfl
  apply rx_pop
  apply rx_pop
  exact rx_ret

/-- Zero kLast and the two-root paths share the real jump24 to cleanup25. -/
theorem feeReturn24_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} {r : Seg} (h25 : 25 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_285f_c24 r) :
    ∃ gas, r = .done (.returned (St b (f :: R) M gas)) := by
  unfold t_285f_c24 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, run⟩ := ric_jump (g := t_2870_c25) h25 rfl run
  exact feeReturn25_inv run

/-- Exact zero-kLast cleanup charge includes the literal jump,35gas. -/
theorem feeReturn24_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} (room : R.length ≤ 1017) :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 35)) t_285f_c24
      (.returned (St b (f :: R) M G)) := by
  unfold t_285f_c24
  apply rx_dest
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  exact rx_jump rfl feeReturn25_exact

/-- The real root cleanup drops both roots before the shared return. -/
theorem feeReturn23_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {a z K w f r1 r0 ρ : B256} {r : Seg} (h25 : 25 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_285c_c23 r) :
    ∃ gas, r = .done (.returned (St b (f :: R) M gas)) := by
  unfold t_285c_c23 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  exact feeReturn24_inv h25 run

/-- Exact two-root cleanup is40gas. -/
theorem feeReturn23_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {a z K w f r1 r0 ρ : B256} (room : R.length ≤ 1017) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 40)) t_285c_c23
      (.returned (St b (f :: R) M G)) := by
  unfold t_285c_c23
  apply rx_dest
  apply rx_pop
  apply rx_pop
  exact feeReturn24_exact room

/-- The zero-liquidity and actual LP-mint continuations drop L,D,N in order. -/
theorem feeReturn2858_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {L D N z a K w f r1 r0 ρ : B256} {r : Seg} (h25 : 25 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (L :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_2858_c68 r) :
    ∃ gas, r = .done (.returned (St b (f :: R) M gas)) := by
  unfold t_2858_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  exact feeReturn23_inv h25 run

/-- Exact three-word plus root cleanup is47gas. -/
theorem feeReturn2858_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {L D N z a K w f r1 r0 ρ : B256} (room : R.length ≤ 1017) :
    SFunc.RunExact cert.prog sevm
      (St b (L :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 47)) t_2858_c68
      (.returned (St b (f :: R) M G)) := by
  unfold t_2858_c68
  apply rx_dest
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact feeReturn23_exact room

/-- The decoded flag tests only the reply word's low160 address. -/
def feeOnWord (w : B256) : B256 := B256.eqCheck (B256.eqCheck w.toAdr.toB256 0) 0

def feeKLastWord (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget 11

def feeKLastWorld (sevm : Sevm) (b : Devm) : Devm := afterSload sevm b 11

def feeDecodedTree (w : B256) : SFunc :=
  if w.toAdr.toB256 = 0 then t_2864_c68 else t_27ab_c68

/-- The real decoder reads kLast from the actual call post and keeps the full reply word. -/
theorem feeDecoder_inv {P : Sevm → Devm → Ninst → Devm → Prop} {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {len w r1 r0 ρ : B256} {r : Seg}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (word : Bytes.toB256 (M.read 128 32).1 = w)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (len :: 128 :: 0 :: 0 :: r1 :: r0 :: ρ :: R) M G) t_2781_c68 r) :
    ∃ gas, SFunc.RunCutP P cert.prog sevm C
      (St (feeKLastWorld sevm b)
        (feeKLastWord sevm b :: w :: feeOnWord w :: r1 :: r0 :: ρ :: R) M gas)
      (feeDecodedTree w) r := by
  unfold t_2781_c68 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨d, hs, run⟩ := ric_nextP run
  obtain ⟨_, eq⟩ := ri_mload (project hs)
  rw [show (128 : B256).toNat = 128 from rfl, word,
    mem.read_self (by omega : 128 + 32 ≤ 192)] at eq
  subst d
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project hs)
  rw [show Bytes.toB256 [0x0b] = (11 : B256) from by decide] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_sload fork (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup (w := w) rfl (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_and (project hs)
  rw [B256.and_comm w, ff20_and_word] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (project hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (project hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (project hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_pop (project hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_swap rfl (project hs)
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (project hs)
  by_cases addressZero : w.toAdr.toB256 = 0
  · simp only [B256.eqCheck, ite_eq_left addressZero] at run
    rcases ric_branchP run with ⟨hz, _, _⟩ | ⟨_, gas, tail⟩
    · exact (by decide : (1 : B256) ≠ 0) hz |>.elim
    · exact ⟨gas, by simpa only [feeDecodedTree, ite_eq_left addressZero,
        feeKLastWorld, feeKLastWord, feeOnWord, B256.eqCheck, ite_eq_left addressZero] using tail⟩
  · simp only [B256.eqCheck, ite_eq_right addressZero] at run
    rcases ric_branchP run with ⟨_, gas, tail⟩ | ⟨hz, _, _⟩
    · exact ⟨gas, by simpa only [feeDecodedTree, ite_eq_right addressZero,
        feeKLastWorld, feeKLastWord, feeOnWord, B256.eqCheck, ite_eq_right addressZero] using tail⟩
    · exact (hz rfl).elim

/-- Decoder exact gas is56 plus its selected kLast SLOAD; no blanket static guard. -/
theorem feeDecoder_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load : Nat} {len w r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (room : R.length ≤ 1015) (charge : load = sloadCost sevm b 11)
    (word : Bytes.toB256 (M.read 128 32).1 = w)
    (body : SFunc.RunExact cert.prog sevm
      (St (feeKLastWorld sevm b)
        (feeKLastWord sevm b :: w :: feeOnWord w :: r1 :: r0 :: ρ :: R) M G)
      (feeDecodedTree w) o) :
    SFunc.RunExact cert.prog sevm
      (St b (len :: 128 :: 0 :: 0 :: r1 :: r0 :: ρ :: R) M (G + load + 56))
      t_2781_c68 o := by
  unfold t_2781_c68
  apply rx_dest
  apply rx_pop
  apply rx_mload (i := 128) (c := 3)
    (by rw [St.extCost_eq mem.size, show (128 : B256).toNat = 128 from rfl, memExtSize_of_le mem.n32 (by decide : 128 + 32 ≤ 192), Nat.sub_self]; rfl) word
    (mem.read_self (by omega : 128 + 32 ≤ 192)) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 11) (by decide) (by simp only [List.length_cons]; omega)
  rw [show G + load + 47 = (G + 47) + load from by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := w) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := w.toAdr.toB256) (by rw [B256.and_comm w, ff20_and_word])
    (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (S' := 0 :: B256.eqCheck w.toAdr.toB256 0 :: feeKLastWord sevm b ::
    w :: 0 :: feeOnWord w :: r1 :: r0 :: ρ :: R) rfl
  apply rx_pop
  apply rx_swap (S' := w :: feeKLastWord sevm b :: B256.eqCheck w.toAdr.toB256 0 ::
    0 :: feeOnWord w :: r1 :: r0 :: ρ :: R) rfl
  apply rx_swap (S' := 0 :: feeKLastWord sevm b :: B256.eqCheck w.toAdr.toB256 0 ::
    w :: feeOnWord w :: r1 :: r0 :: ρ :: R) rfl
  apply rx_pop
  apply rx_swap (S' := B256.eqCheck w.toAdr.toB256 0 :: feeKLastWord sevm b ::
    w :: feeOnWord w :: r1 :: r0 :: ρ :: R) rfl
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  by_cases addressZero : w.toAdr.toB256 = 0
  · have zeroFlag : B256.eqCheck w.toAdr.toB256 0 = 1 := ite_eq_left addressZero
    rw [zeroFlag]
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    simpa only [feeDecodedTree, ite_eq_left addressZero, feeKLastWorld] using body
  · have zeroFlag : B256.eqCheck w.toAdr.toB256 0 = 0 := ite_eq_right addressZero
    rw [zeroFlag]
    apply rx_branch_zero
    simpa only [feeDecodedTree, ite_eq_right addressZero, feeKLastWorld] using body

/-- Fee-off only writes when the actual cached kLast is nonzero. -/
def feeOffWorld (sevm : Sevm) (b : Devm) (K : B256) : Devm :=
  if K = 0 then b else afterSstore sevm b 11 0

def feeOffCharge (sevm : Sevm) (b : Devm) (K : B256) : Nat :=
  if K = 0 then 43 else 49 + sstoreCost sevm b 11 0

/-- Both fee-off paths, including the real conditional slot11 clear and its static guard. -/
theorem feeOff_inv {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_2864_c68 o) :
    (K ≠ 0 → sevm.isStatic = false) ∧
      ∃ gas, o = .returned (St (feeOffWorld sevm b K) (f :: R) M gas) := by
  have h := run.cut
  unfold t_2864_c68 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := K) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  by_cases zeroK : K = 0
  · simp only [B256.eqCheck, ite_eq_left zeroK] at h
    rcases ric_branchTo (g := t_2870_c25) (by decide : 25 ∉ []) rfl h with
      ⟨bad, _, _⟩ | ⟨_, _, tail⟩
    · exact (by decide : (1 : B256) ≠ 0) bad |>.elim
    · obtain ⟨gas, eq⟩ := feeReturn25_inv tail
      exact ⟨fun hn => (hn zeroK).elim, gas,
        by simpa only [feeOffWorld, ite_eq_left zeroK] using Seg.done.inj eq⟩
  · simp only [B256.eqCheck, ite_eq_right zeroK] at h
    rcases ric_branchTo (g := t_2870_c25) (by decide : 25 ∉ []) rfl h with
      ⟨_, _, tail⟩ | ⟨bad, _, _⟩
    · unfold t_286b_c68 at tail
      obtain ⟨_, hs, tail⟩ := ric_next tail; obtain ⟨_, rfl⟩ := ri_push hs
      obtain ⟨_, hs, tail⟩ := ric_next tail; obtain ⟨_, rfl⟩ := ri_push hs
      rw [show Bytes.toB256 [0x0b] = (11 : B256) from by decide,
        show Bytes.toB256 [0x00] = (0 : B256) from by decide] at tail
      obtain ⟨_, hs, tail⟩ := ric_next tail
      have nonstatic := ri_sstore_nonstatic fork hs
      obtain ⟨_, rfl⟩ := ri_sstore fork hs
      obtain ⟨gas, eq⟩ := feeReturn25_inv tail
      exact ⟨fun _ => nonstatic, gas,
        by simpa only [feeOffWorld, ite_eq_right zeroK] using Seg.done.inj eq⟩
    · exact (bad rfl).elim

/-- Exact fee-off cost distinguishes the no-store path and genuine selected clear charge. -/
theorem feeOff_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (room : R.length ≤ 1016)
    (nonstatic : K ≠ 0 → sevm.isStatic = false)
    (sentry : K ≠ 0 → gCallStipend < G + sstoreCost sevm b 11 0 + 23) :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + feeOffCharge sevm b K))
      t_2864_c68 (.returned (St (feeOffWorld sevm b K) (f :: R) M G)) := by
  unfold t_2864_c68
  by_cases zeroK : K = 0
  · simp only [feeOffCharge, feeOffWorld, ite_eq_left zeroK]
    apply rx_dest
    apply rx_dup (w := K) rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (ite_eq_left zeroK) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_succ (g := t_2870_c25) (by decide : (1 : B256) ≠ 0) rfl
    exact feeReturn25_exact
  · simp only [feeOffCharge, feeOffWorld, ite_eq_right zeroK]
    rw [show G + (49 + sstoreCost sevm b 11 0) = (G + sstoreCost sevm b 11 0) + 49 from by omega]
    apply rx_dest
    apply rx_dup (w := K) rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 0) (ite_eq_right zeroK) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    unfold t_286b_c68
    apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
    apply rx_push (w := 11) (by decide) (by simp only [List.length_cons]; omega)
    rw [show (G + sstoreCost sevm b 11 0) + 23 =
      (G + 23) + sstoreCost sevm b 11 0 from by omega]
    apply rx_sstoreC fork rfl (by have := sentry zeroK; omega) (nonstatic zeroK)
    exact feeReturn25_exact

/-- A real fee-on run with zero kLast has no square-root call or store. -/
theorem feeOnZero_inv {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {w f r1 r0 ρ : B256} {o : Outcome}
    (run : SFunc.Run cert.prog sevm
      (St b (0 :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27ab_c68 o) :
    ∃ gas, o = .returned (St b (f :: R) M gas) := by
  have h := run.cut
  unfold t_27ab_c68 at h
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := 0) rfl hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hs
  simp only [show B256.eqCheck 0 0 = (1 : B256) from by decide] at h
  rcases ric_branchTo (g := t_285f_c24) (by decide : 24 ∉ []) rfl h with
    ⟨bad, _, _⟩ | ⟨_, _, tail⟩
  · exact (by decide : (1 : B256) ≠ 0) bad |>.elim
  · obtain ⟨gas, eq⟩ := feeReturn24_inv (by decide : 25 ∉ []) tail
    exact ⟨gas, Seg.done.inj eq⟩

/-- The fee-on zero-kLast arm costs54gas and also admits static execution. -/
theorem feeOnZero_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {w f r1 r0 ρ : B256} (room : R.length ≤ 1016) :
    SFunc.RunExact cert.prog sevm
      (St b (0 :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 54))
      t_27ab_c68 (.returned (St b (f :: R) M G)) := by
  unfold t_27ab_c68
  apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_branchTo_succ (g := t_285f_c24) (by decide : (1 : B256) ≠ 0) rfl
  exact feeReturn24_exact (by omega)

/-- The actual root comparison selects growth or the literal two-root cleanup. -/
theorem feeRootCompare_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {z a K w f r1 r0 ρ : B256} {r : Seg}
    (h23 : 23 ∉ C) (h25 : 25 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (z :: 0 :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27e5_c68 r) :
    (¬z < a ∧ ∃ gas, r = .done (.returned (St b (f :: R) M gas))) ∨
    (z < a ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas) t_27f0_c68 r) := by
  unfold t_27e5_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := z) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := a) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_gt hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  by_cases growth : z < a
  · simp only [B256.gtCheck, ite_eq_left growth,
      show B256.eqCheck 1 0 = (0 : B256) from by decide] at run
    rcases ric_branchTo (g := t_285c_c23) h23 rfl run with ⟨_, gas, tail⟩ | ⟨bad, _, _⟩
    · exact .inr ⟨growth, gas, tail⟩
    · exact (bad rfl).elim
  · simp only [B256.gtCheck, ite_eq_right growth,
      show B256.eqCheck 0 0 = (1 : B256) from by decide] at run
    rcases ric_branchTo (g := t_285c_c23) h23 rfl run with ⟨bad, _, _⟩ | ⟨_, _, tail⟩
    · exact (by decide : (1 : B256) ≠ 0) bad |>.elim
    · exact .inl ⟨growth, feeReturn23_inv h25 tail⟩

/-- Exact root-comparison prefix costs31, with its actual selected continuation. -/
theorem feeRootCompare_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {z a K w f r1 r0 ρ : B256} {o : Outcome}
    (room : R.length ≤ 1014)
    (body : SFunc.RunExact cert.prog sevm
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      (if z < a then t_27f0_c68 else t_285c_c23) o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: 0 :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 31))
      t_27e5_c68 o := by
  unfold t_27e5_c68
  apply rx_dest
  apply rx_swap (S' := 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) rfl
  apply rx_pop
  apply rx_dup (w := z) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := a) rfl (by simp only [List.length_cons]; omega)
  by_cases growth : z < a
  · apply rx_gt (v := 1) (ite_eq_left growth) (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    simpa only [ite_eq_left growth] using body
  · apply rx_gt (v := 0) (ite_eq_right growth) (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
    apply rx_push rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_succ (g := t_285c_c23) (by decide : (1 : B256) ≠ 0) rfl
    simpa only [ite_eq_right growth] using body

/-- Actual no-growth arm returns without stores/logs,71gas including cleanup. -/
theorem feeNoGrowth_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {z a K w f r1 r0 ρ : B256}
    (growth : ¬z < a) (room : R.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: 0 :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 71))
      t_27e5_c68 (.returned (St b (f :: R) M G)) := by
  apply feeRootCompare_exact room
  simp only [ite_eq_right growth]
  exact feeReturn23_exact (by omega)

/-- Second actual sqrt69 call uses kLast, distinct from the reserve-product input. -/
theorem feeRootKLast_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {a K w f r1 r0 ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (a :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27d8_c68 r) :
    ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((Nat.sqrt K.toNat).toB256 :: 0 :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_27e5_c68 r := by
  unfold t_27d8_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := K) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, branch⟩ := ric_call (g := t_2878_c69) rfl run
  rcases branch with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨_, eq⟩ := sqrt_of_run callee
    cases eq
    exact ⟨_, tail⟩
  · obtain ⟨_, eq⟩ := sqrt_of_run callee
    cases eq

/-- Second sqrt69 caller costs26 plus the exact sqrt charge. -/
theorem feeRootKLast_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {a K w f r1 r0 ρ : B256} {o : Outcome}
    (room : R.length ≤ 1006)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((Nat.sqrt K.toNat).toB256 :: 0 :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_27e5_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (a :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + sqrtCharge K.toNat + 26))
      t_27d8_c68 o := by
  unfold t_27d8_c68
  apply rx_dest
  apply rx_swap (S' := 0 :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) rfl
  apply rx_pop
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := K) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_callRet (g := t_2878_c69) rfl (sqrt_exact (by simp only [List.length_cons]; omega))
  exact body

/-- The context-specific0x1257 continuation calls the first sqrt on the actual product. -/
theorem feeRootK_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {product K w f r1 r0 ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (product :: 0x27d8 :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_1257_c68 r) :
    ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((Nat.sqrt product.toNat).toB256 :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_27d8_c68 r := by
  unfold t_1257_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, branch⟩ := ric_call (g := t_2878_c69) rfl run
  rcases branch with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨_, eq⟩ := sqrt_of_run callee
    cases eq
    exact ⟨_, tail⟩
  · obtain ⟨_, eq⟩ := sqrt_of_run callee
    cases eq

/-- Actual first sqrt caller costs12 plus its separately floored product-root charge. -/
theorem feeRootK_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {product K w f r1 r0 ρ : B256} {o : Outcome}
    (room : R.length ≤ 1007)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((Nat.sqrt product.toNat).toB256 :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_27d8_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (product :: 0x27d8 :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + sqrtCharge product.toNat + 12)) t_1257_c68 o := by
  unfold t_1257_c68
  apply rx_dest
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_2878_c69) rfl
    (sqrt_exact (by simp only [List.length_cons]; omega)) body

/-- The ordinary branch cut is derived from the same D factory continuation;
the loaded word is proved by physical reply memory, never an incoming word assumption. -/
theorem feeFactoryDecoded_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {C : List Nat} {M : Mem} {G : Nat} {r1 r0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm C
      (St b (r1 :: r0 :: ρ :: R) M G) t_26ec_c68 seg) :
    ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0 ∧
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (decodeGas branchGas : Nat),
      StepIn D sevm
        (St (feeFactoryCallWorld sevm b)
          (gw :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
            132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeRequestMemory M) callGas) (.exec .staticcall) d ∧
      StaticCallPost (feeFactoryCallWorld sevm b) d
        (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) 128 4 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2^256 ∧
      StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
        (ExternalOperation.encode .feeTo) out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St d (out.length.toB256 :: 128 :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeReplyMemory M out) decodeGas) t_2781_c68 seg ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm C
        (St (feeKLastWorld sevm d)
          (feeKLastWord sevm d :: Bytes.toB256 (out.take 32) ::
            feeOnWord (Bytes.toB256 (out.take 32)) :: r1 :: r0 :: ρ :: R)
          (feeReplyMemory M out) branchGas)
        (feeDecodedTree (Bytes.toB256 (out.take 32))) seg := by
  obtain ⟨code, gw, callGas, d, out, decodeGas, step, post, width, bound, answer, continuation⟩ :=
    feeFactoryObservation_inv fork mem run
  obtain ⟨branchGas, branch⟩ := feeDecoder_inv (fun h => StepIn.toRun h) fork
    (feeReplyMemory_ptr out (feeRequestMemory_ptr mem))
    (feeReplyMemory_word mem.wf out width)
    continuation
  exact ⟨code, gw, callGas, d, out, decodeGas, branchGas,
    step, post, width, bound, answer, continuation, branch⟩

/-- The literal fee reserve mask has the source's112-bit width. -/
def feeReserveWord (word : B256) : B256 :=
  word &&& Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]

theorem feeReserveWord_eq {word : B256} (bound : word.toNat < 2 ^ 112) :
    feeReserveWord word = word := by
  unfold feeReserveWord
  rw [show Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] =
    (2 ^ 112 - 1 : Nat).toB256 from by decide]
  exact PackedWord.lowMask_eq_self_of_lt (by decide : 112 ≤ 256) bound

/-- Cached bounded reserves justify the real checked product; not the fee numerator. -/
theorem feeReserveProduct_noWrap {r0 r1 : B256}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) : B256.Nofm r0 r1 := by
  unfold B256.Nofm
  have product := Nat.mul_lt_mul_of_lt_of_lt bound0 bound1
  have width : (2 : Nat) ^ 112 * 2 ^ 112 < 2 ^ 256 := by decide
  exact lt_trans product width

/-- The actual reserve-product mul58 returns into the context-specific1257 continuation. -/
theorem feeReserveProduct_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} {r : Seg}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27b1_c68 r) :
    ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((r0 * r1) :: 0x27d8 :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_1257_c68 r := by
  unfold t_27b1_c68 at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := r0) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  rw [show Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] &&& r0 =
    r0 from by rw [B256.and_comm]; exact feeReserveWord_eq bound0] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := r1) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  rw [show r1 &&& Bytes.toB256
    [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] =
    r1 from feeReserveWord_eq bound1] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, branch⟩ := ric_call (g := t_21e8_c58) rfl run
  rcases branch with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq
    exact ⟨_, tail⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq

/-- Exact reserve staging47 plus checked multiplication uses genuine bounded cached words. -/
theorem feeReserveProduct_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} {o : Outcome}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (room : R.length ≤ 1007)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((r0 * r1) :: 0x27d8 :: 0 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_1257_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + mul58Charge r1 + 47))
      t_27b1_c68 o := by
  unfold t_27b1_c68
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x27d8) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x1257) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := r0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := r0) (by rw [B256.and_comm]; exact feeReserveWord_eq bound0)
    (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_dup (w := r1) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := r1) (feeReserveWord_eq bound1) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x21e8) (by decide) (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_21e8_c58) rfl
    (mul58_exact (feeReserveProduct_noWrap bound0 bound1) (by simp only [List.length_cons]; omega)) body

/-- Nonzero kLast takes the actual reserve-product arm, with no initial storage write. -/
theorem feeOnNonzero_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} {r : Seg}
    (nonzero : K ≠ 0) (h24 : 24 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27ab_c68 r) :
    ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M gas) t_27b1_c68 r := by
  unfold t_27ab_c68 at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := K) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  simp only [B256.eqCheck, ite_eq_right nonzero] at run
  rcases ric_branchTo (g := t_285f_c24) h24 rfl run with ⟨_, gas, tail⟩ | ⟨bad, _, _⟩
  · exact ⟨gas, tail⟩
  · exact (bad rfl).elim

/-- Actual nonzero-kLast prefix costs19 before the checked reserve-product arm. -/
theorem feeOnNonzero_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {K w f r1 r0 ρ : B256} {o : Outcome}
    (nonzero : K ≠ 0) (room : R.length ≤ 1016)
    (body : SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27b1_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 19)) t_27ab_c68 o := by
  unfold t_27ab_c68
  apply rx_dup (w := K) rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 0) (ite_eq_right nonzero) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  exact rx_branchTo_zero body

/-- Final liquidity result preserves the real LP post only when liquidity is positive. -/
def feeLiquidityPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (w f N D : B256) (G : Nat) : Devm :=
  if N / D = 0 then St b (f :: R) M G
  else lpMintPost sevm b (f :: R) M w (N / D) G

def feeLiquidityTree (N D : B256) : SFunc :=
  if N / D = 0 then t_2858_c68 else t_284f_c68

/-- Actual floor DIV and liquidity branch derive genuine LP guards only on its positive arm. -/
theorem feeLiquidity_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {N D z a K w f r1 r0 ρ : B256} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M) (h25 : 25 ∉ C)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (N :: D :: 0 :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2845_c68 r) :
    (N / D ≠ 0 → lpMintAccepts sevm b w (N / D)) ∧
      ∃ gas, r = .done (.returned (feeLiquidityPost sevm b R M w f N D gas)) := by
  unfold t_2845_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_div hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_iszero hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  by_cases zeroL : N / D = 0
  · simp only [B256.eqCheck, ite_eq_left zeroL] at run
    rcases ric_branch run with ⟨bad, _, _⟩ | ⟨_, _, tail⟩
    · exact (by decide : (1 : B256) ≠ 0) bad |>.elim
    · obtain ⟨gas, eq⟩ := feeReturn2858_inv h25 tail
      exact ⟨fun hn => (hn zeroL).elim, gas,
        by simpa only [feeLiquidityPost, ite_eq_left zeroL] using eq⟩
  · simp only [B256.eqCheck, ite_eq_right zeroL] at run
    rcases ric_branch run with ⟨_, _, tail⟩ | ⟨bad, _, _⟩
    · obtain ⟨_, _, _, guards, continuation⟩ :=
        lpMint_fee_caller_inv (fun h => h) fork mem tail
      dsimp only [lpMintPost, lpMintSupplyPost, lpMintCreditPost] at continuation
      obtain ⟨gas, eq⟩ := feeReturn2858_inv h25 continuation
      exact ⟨fun _ => guards, gas, by
        simpa only [feeLiquidityPost, ite_eq_right zeroL,
          lpMintPost, lpMintSupplyPost, lpMintCreditPost] using eq⟩
    · exact (bad rfl).elim

/-- Literal floor-DIV/liquidity selection prefix costs30gas. -/
theorem feeLiquidity_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {N D z a K w f r1 r0 ρ : B256} {o : Outcome}
    (room : R.length ≤ 1011)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((N / D) :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      (feeLiquidityTree N D) o) :
    SFunc.RunExact cert.prog sevm
      (St b (N :: D :: 0 :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + 30)) t_2845_c68 o := by
  unfold t_2845_c68
  apply rx_dest
  apply rx_div rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (S' := 0 :: N / D :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) rfl
  apply rx_pop
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  by_cases zeroL : N / D = 0
  · have flag : B256.eqCheck (N / D) 0 = 1 := ite_eq_left zeroL
    rw [flag]
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    simpa only [feeLiquidityTree, ite_eq_left zeroL] using body
  · have flag : B256.eqCheck (N / D) 0 = 0 := ite_eq_right zeroL
    rw [flag]
    apply rx_branch_zero
    simpa only [feeLiquidityTree, ite_eq_right zeroL] using body

/-- Growth with zero floor liquidity takes the actual no-store/log continuation,77gas. -/
theorem feeZeroLiquidity_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {N D z a K w f r1 r0 ρ : B256}
    (zeroL : N / D = 0) (room : R.length ≤ 1011) :
    SFunc.RunExact cert.prog sevm
      (St b (N :: D :: 0 :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + 77)) t_2845_c68 (.returned (St b (f :: R) M G)) := by
  apply feeLiquidity_exact room
  simp only [feeLiquidityTree, ite_eq_left zeroL]
  exact feeReturn2858_exact (by omega)

/-- The positive-liquidity literal caller consumes a genuine mint62 run and its cleanup.
Its20gas prefix is independent of the separately selected mint62 storage charges. -/
theorem feePositiveLiquidityCaller_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G mintGas : Nat} {L D N z a K w f r1 r0 ρ : B256}
    (room : R.length ≤ 1003)
    (mint : SFunc.RunExact cert.prog sevm
      (St b (L :: w :: 0x2858 :: L :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M mintGas)
      t_28ca_c62 (.returned (lpMintPost sevm b
        (L :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M w L (G + 47)))) :
    SFunc.RunExact cert.prog sevm
      (St b (L :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M (mintGas + 20))
      t_284f_c68 (.returned (lpMintPost sevm b (f :: R) M w L G)) := by
  unfold t_284f_c68
  apply rx_push (w := 0x2858) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := w) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := L) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_callRet (g := t_28ca_c62) rfl mint
  dsimp only [lpMintPost, lpMintSupplyPost, lpMintCreditPost]
  exact feeReturn2858_exact (by omega)

/-- The literal denominator guard excludes INVALID and reaches the true division operands. -/
theorem feeDenominatorGuard_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {D N z a K w f r1 r0 ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (D :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2838_c68 r) :
    D ≠ 0 ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b (N :: D :: 0 :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_2845_c68 r := by
  unfold t_2838_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := D) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := N) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := D) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  rcases ric_branch run with ⟨_, _, failed⟩ | ⟨nonzero, gas, tail⟩
  · exact (failed.false_of_noOk (by decide : t_2844_c68.noOk = true)).elim
  · exact ⟨nonzero, gas, tail⟩

/-- Actual denominator guard costs31; its nonzero premise is discharged by the preceding producer. -/
theorem feeDenominatorGuard_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {D N z a K w f r1 r0 ρ : B256} {o : Outcome}
    (nonzero : D ≠ 0) (room : R.length ≤ 1009)
    (body : SFunc.RunExact cert.prog sevm
      (St b (N :: D :: 0 :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2845_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (D :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + 31)) t_2838_c68 o := by
  unfold t_2838_c68
  apply rx_dest
  apply rx_swap (S' := 0 :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) rfl
  apply rx_pop
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := D) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := N) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := D) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  exact rx_branch_succ nonzero body

/-- Checked denominator add72 derives actual no-wrap and retains the true sum order. -/
theorem feeDenominatorAdd_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {fiveA N z a K w f r1 r0 ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (fiveA :: z :: 0x2838 :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_282c_c68 r) :
    fiveA.toNat + z.toNat < 2 ^ 256 ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((fiveA + z) :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_2838_c68 r := by
  unfold t_282c_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, branch⟩ := ric_call (g := t_2abc_c72) rfl run
  rcases branch with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨nowrap, _, eq⟩ := add72_inv callee
    cases eq
    exact ⟨nowrap, _, tail⟩
  · obtain ⟨_, _, eq⟩ := add72_inv callee
    cases eq

/-- Actual denominator add caller21 plus checked add54 costs75gas. -/
theorem feeDenominatorAdd_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {fiveA N z a K w f r1 r0 ρ : B256} {o : Outcome}
    (nowrap : fiveA.toNat + z.toNat < 2 ^ 256) (room : R.length ≤ 1008)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((fiveA + z) :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2838_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (fiveA :: z :: 0x2838 :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + 75)) t_282c_c68 o := by
  unfold t_282c_c68
  apply rx_dest
  apply rx_swap (S' := z :: fiveA :: 0x2838 :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) rfl
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x2abc) (by decide) (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_2abc_c72) rfl
    (add72_exact nowrap (by simp only [List.length_cons]; omega)) body

/-- The actual factor-five mul58 derives its guard, independently of numerator no-wrap. -/
theorem feeDenominatorMul_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {N z a K w f r1 r0 ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (N :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2813_c68 r) :
    B256.Nofm a 5 ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((a * 5) :: z :: 0x2838 :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_282c_c68 r := by
  unfold t_2813_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := z) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := a) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  rw [show Bytes.toB256 [5] = (5 : B256) from by decide] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, branch⟩ := ric_call (g := t_21e8_c58) rfl run
  rcases branch with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨nowrap, _, eq⟩ := mul58_inv callee
    cases eq
    exact ⟨nowrap, _, tail⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq

/-- Actual factor-five caller41 plus checked nonzero multiplier108 costs149gas. -/
theorem feeDenominatorMul_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {N z a K w f r1 r0 ρ : B256} {o : Outcome}
    (nowrap : B256.Nofm a 5) (room : R.length ≤ 1003)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((a * 5) :: z :: 0x2838 :: 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_282c_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (N :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + 149)) t_2813_c68 o := by
  have factorCharge : mul58Charge (5 : B256) = 108 := by decide
  unfold t_2813_c68
  apply rx_dest
  apply rx_swap (S' := 0 :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) rfl
  apply rx_pop
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := z) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := a) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 5) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x21e8) (by decide) (by simp only [List.length_cons]; omega)
  rw [show G + 116 = (G + mul58Charge (5 : B256)) + 8 from by rw [factorCharge]]
  exact rx_callRet (g := t_21e8_c58) rfl
    (mul58_exact nowrap (by simp only [List.length_cons]; omega)) body

/-- Numerator mul58 derives its independent overflow guard after the actual supply read. -/
theorem feeNumerator_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {Δ z a K w f r1 r0 ρ : B256} {r : Seg}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut cert.prog sevm C
      (St b (Δ :: 0x2813 :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2804_c68 r) :
    B256.Nofm (b.getStorVal sevm.currentTarget 0) Δ ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St (afterSload sevm b 0)
        ((b.getStorVal sevm.currentTarget 0 * Δ) :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_2813_c68 r := by
  unfold t_2804_c68 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  rw [show Bytes.toB256 [0] = (0 : B256) from rfl] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sload fork hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  dsimp only [List.set] at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, branch⟩ := ric_call (g := t_21e8_c58) rfl run
  rcases branch with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨nowrap, _, eq⟩ := mul58_inv callee
    cases eq
    exact ⟨nowrap, _, tail⟩
  · obtain ⟨_, _, eq⟩ := mul58_inv callee
    cases eq

/-- Numerator caller24, selected supply load and the actual multiplier charge. -/
theorem feeNumerator_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G load : Nat} {Δ z a K w f r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (charge : load = sloadCost sevm b 0)
    (nowrap : B256.Nofm (b.getStorVal sevm.currentTarget 0) Δ) (room : R.length ≤ 1006)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 0)
        ((b.getStorVal sevm.currentTarget 0 * Δ) :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2813_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (Δ :: 0x2813 :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + mul58Charge Δ + load + 24)) t_2804_c68 o := by
  unfold t_2804_c68
  apply rx_dest
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  rw [show G + mul58Charge Δ + load + 20 = (G + mul58Charge Δ + 20) + load from by omega]
  apply rx_sload_selC fork charge (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x21e8) (by decide) (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_21e8_c58) rfl
    (mul58_exact nowrap (by simp only [List.length_cons]; omega)) body

/-- Actual root subtraction derives cover before the independent numerator multiplication. -/
theorem feeGrowthSub_inv {sevm : Sevm} {b : Devm} {R : List B256} {C : List Nat}
    {M : Mem} {G : Nat} {z a K w f r1 r0 ρ : B256} {r : Seg}
    (run : SFunc.RunCut cert.prog sevm C
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27f0_c68 r) :
    z ≤ a ∧ ∃ gas, SFunc.RunCut cert.prog sevm C
      (St b ((a - z) :: 0x2813 :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M gas)
      t_2804_c68 r := by
  unfold t_27f0_c68 at run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := a) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup (w := z) rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, branch⟩ := ric_call (g := t_226e_c59) rfl run
  rcases branch with ⟨d, callee, tail⟩ | ⟨d, callee, _⟩
  · obtain ⟨cover, _, eq⟩ := sub59_inv callee
    cases eq
    exact ⟨cover, _, tail⟩
  · obtain ⟨_, _, eq⟩ := sub59_inv callee
    cases eq

/-- Growth subtraction caller32 plus checked sub59 cost54, before the supply load. -/
theorem feeGrowthSub_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {z a K w f r1 r0 ρ : B256} {o : Outcome}
    (cover : z ≤ a) (room : R.length ≤ 1008)
    (body : SFunc.RunExact cert.prog sevm
      (St b ((a - z) :: 0x2813 :: 0 :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_2804_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M (G + 86)) t_27f0_c68 o := by
  unfold t_27f0_c68
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := a) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := z) rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_push rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := 0x226e) (by decide) (by simp only [List.length_cons]; omega)
  exact rx_callRet (g := t_226e_c59) rfl
    (sub59_exact cover (by simp only [List.length_cons]; omega)) body

def feeNumeratorWord (sevm : Sevm) (b : Devm) (z a : B256) : B256 :=
  b.getStorVal sevm.currentTarget 0 * (a - z)

def feeDenominatorWord (z a : B256) : B256 := a * 5 + z

/-- These guards are obtained from the actual three checked callees and division guard. -/
def feeGrowthAccepts (sevm : Sevm) (b : Devm) (w z a : B256) : Prop :=
  B256.Nofm (b.getStorVal sevm.currentTarget 0) (a - z) ∧
  B256.Nofm a 5 ∧ (a * 5).toNat + z.toNat < 2 ^ 256 ∧
  feeDenominatorWord z a ≠ 0 ∧
  (feeNumeratorWord sevm b z a / feeDenominatorWord z a ≠ 0 →
    lpMintAccepts sevm (afterSload sevm b 0) w
      (feeNumeratorWord sevm b z a / feeDenominatorWord z a))

def feeGrowthPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (w f z a : B256) (G : Nat) : Devm :=
  feeLiquidityPost sevm (afterSload sevm b 0) R M w f
    (feeNumeratorWord sevm b z a) (feeDenominatorWord z a) G

/-- Complete actual growth suffix derives arithmetic/conditional LP acceptance and full poststate. -/
theorem feeGrowth_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {z a K w f r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27f0_c68 o) :
    z ≤ a ∧ feeGrowthAccepts sevm b w z a ∧
      ∃ gas, o = .returned (feeGrowthPost sevm b R M w f z a gas) := by
  obtain ⟨cover, _, sub⟩ := feeGrowthSub_inv run.cut
  obtain ⟨numerator, _, mul⟩ := feeNumerator_inv fork sub
  obtain ⟨factor, _, add⟩ := feeDenominatorMul_inv mul
  obtain ⟨denominator, _, guard⟩ := feeDenominatorAdd_inv add
  obtain ⟨nonzero, _, divide⟩ := feeDenominatorGuard_inv guard
  obtain ⟨mint, gas, result⟩ := feeLiquidity_inv fork mem (by decide : 25 ∉ []) divide
  exact ⟨cover, ⟨numerator, factor, denominator, nonzero, mint⟩,
    gas, Seg.done.inj result⟩

/-- All checked growth staging costs365 plus actual numerator/load charges before division. -/
theorem feeGrowthPrefix_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G load : Nat} {z a K w f r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (charge : load = sloadCost sevm b 0)
    (cover : z ≤ a)
    (numerator : B256.Nofm (b.getStorVal sevm.currentTarget 0) (a - z))
    (factor : B256.Nofm a 5) (denominator : (a * 5).toNat + z.toNat < 2 ^ 256)
    (nonzero : feeDenominatorWord z a ≠ 0) (room : R.length ≤ 1003)
    (body : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 0)
        (feeNumeratorWord sevm b z a :: feeDenominatorWord z a :: 0 ::
          feeDenominatorWord z a :: feeNumeratorWord sevm b z a ::
          z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_2845_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + mul58Charge (a - z) + load + 365)) t_27f0_c68 o := by
  rw [show G + mul58Charge (a - z) + load + 365 =
    (G + 255 + mul58Charge (a - z) + load + 24) + 86 from by omega]
  apply feeGrowthSub_exact cover (by omega)
  apply feeNumerator_exact fork charge numerator (by omega)
  apply feeDenominatorMul_exact factor room
  apply feeDenominatorAdd_exact denominator (by omega)
  apply feeDenominatorGuard_exact nonzero (by omega)
  exact body

def feeReserveRoot (r0 r1 : B256) : B256 := (Nat.sqrt (r0 * r1).toNat).toB256

def feeLastRoot (K : B256) : B256 := (Nat.sqrt K.toNat).toB256

def feeOnAccepts (sevm : Sevm) (b : Devm) (K w r0 r1 : B256) : Prop :=
  K ≠ 0 → feeLastRoot K < feeReserveRoot r0 r1 →
    feeGrowthAccepts sevm b w (feeLastRoot K) (feeReserveRoot r0 r1)

def feeOnPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (K w f r0 r1 : B256) (G : Nat) : Devm :=
  if K = 0 then St b (f :: R) M G
  else if feeLastRoot K < feeReserveRoot r0 r1 then
    feeGrowthPost sevm b R M w f (feeLastRoot K) (feeReserveRoot r0 r1) G
  else St b (f :: R) M G

/-- Actual nonzero-kLast route consumes both distinct roots and the complete growth suffix. -/
theorem feeOnNonzeroFull_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {K w f r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) (nonzero : K ≠ 0)
    (run : SFunc.Run cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27ab_c68 o) :
    feeOnAccepts sevm b K w r0 r1 ∧
      ∃ gas, o = .returned (feeOnPost sevm b R M K w f r0 r1 gas) := by
  obtain ⟨_, product⟩ := feeOnNonzero_inv nonzero (by decide : 24 ∉ []) run.cut
  obtain ⟨_, root⟩ := feeReserveProduct_inv bound0 bound1 product
  obtain ⟨_, last⟩ := feeRootK_inv root
  obtain ⟨_, compare⟩ := feeRootKLast_inv last
  rcases feeRootCompare_inv (by decide : 23 ∉ []) (by decide : 25 ∉ []) compare with
    ⟨noGrowth, gas, result⟩ | ⟨growth, _, tail⟩
  · exact ⟨fun _ h => (noGrowth h).elim, gas, by
      simpa only [feeOnPost, ite_eq_right nonzero,
        ite_eq_right (show ¬ feeLastRoot K < feeReserveRoot r0 r1 from noGrowth)] using Seg.done.inj result⟩
  · obtain ⟨_, accepts, gas, result⟩ := feeGrowth_inv fork mem tail.uncut
    exact ⟨fun _ _ => accepts, gas, by
      rw [feeOnPost, ite_eq_right nonzero,
        ite_eq_left (show feeLastRoot K < feeReserveRoot r0 r1 from growth)]
      simpa only [feeLastRoot, feeReserveRoot] using result⟩

/-- All fee-on arms derive their guards and actual complete poststate, including kLast-zero. -/
theorem feeOnFull_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {K w f r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.Run cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R) M G) t_27ab_c68 o) :
    feeOnAccepts sevm b K w r0 r1 ∧
      ∃ gas, o = .returned (feeOnPost sevm b R M K w f r0 r1 gas) := by
  by_cases zeroK : K = 0
  · subst K
    obtain ⟨gas, result⟩ := feeOnZero_inv run
    exact ⟨fun hn => (hn rfl).elim, gas, by
      rw [feeOnPost, ite_eq_left (show (0 : B256) = 0 from rfl)]
      exact result⟩
  · exact feeOnNonzeroFull_inv fork mem bound0 bound1 zeroK run

def feeBranchAccepts (sevm : Sevm) (b : Devm) (K w r0 r1 : B256) : Prop :=
  if w.toAdr.toB256 = 0 then K ≠ 0 → sevm.isStatic = false
  else feeOnAccepts sevm b K w r0 r1

def feeBranchPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (K w r0 r1 : B256) (G : Nat) : Devm :=
  if w.toAdr.toB256 = 0 then St (feeOffWorld sevm b K) (feeOnWord w :: R) M G
  else feeOnPost sevm b R M K w (feeOnWord w) r0 r1 G

/-- All actual fee branches retain the caller locals and the allocated pointer, including LP scratch writes. -/
theorem pairFeePost_machine {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {K w r0 r1 : B256} {G : Nat} (mem : PtrMem 128 192 M) :
    (feeBranchPost sevm b R M K w r0 r1 G).stack = feeOnWord w :: R ∧
    PtrMem 128 192 (feeBranchPost sevm b R M K w r0 r1 G).memory := by
  unfold feeBranchPost
  split
  · exact ⟨rfl, mem⟩
  · unfold feeOnPost
    split
    · exact ⟨rfl, mem⟩
    · split
      · unfold feeGrowthPost feeLiquidityPost
        split
        · exact ⟨rfl, mem⟩
        · exact ⟨rfl, lpMintMemory_ptr (lpMintScratch_ptr mem w) w _⟩
      · exact ⟨rfl, mem⟩

/-- All six decoded fee arms derive conditional guards and the full raw return state. -/
theorem feeBranch_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {K w r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.Run cert.prog sevm
      (St b (K :: w :: feeOnWord w :: r1 :: r0 :: ρ :: R) M G) (feeDecodedTree w) o) :
    feeBranchAccepts sevm b K w r0 r1 ∧
      ∃ gas, o = .returned (feeBranchPost sevm b R M K w r0 r1 gas) := by
  by_cases zeroAddress : w.toAdr.toB256 = 0
  · rw [feeDecodedTree, ite_eq_left zeroAddress] at run
    obtain ⟨guard, gas, result⟩ := feeOff_inv fork run
    exact ⟨by simpa only [feeBranchAccepts, ite_eq_left zeroAddress] using guard,
      gas, by simpa only [feeBranchPost, ite_eq_left zeroAddress] using result⟩
  · rw [feeDecodedTree, ite_eq_right zeroAddress] at run
    obtain ⟨guard, gas, result⟩ := feeOnFull_inv fork mem bound0 bound1 run
    exact ⟨by simpa only [feeBranchAccepts, ite_eq_right zeroAddress] using guard,
      gas, by simpa only [feeBranchPost, ite_eq_right zeroAddress] using result⟩

/-- Actual fee68 success derives all branch guards from its same-D factory observation.
The arbitrary complete reply, primitive post and both original continuations are retained. -/
theorem fee68_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {r1 r0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (run : SFunc.RunP (StepIn D) cert.prog sevm
      (St b (r1 :: r0 :: ρ :: R) M G) t_26ec_c68 o) :
    ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0 ∧
    ∃ (gw : B256) (callGas : Nat) (d : Devm) (out : Bytes) (decodeGas branchGas gas : Nat),
      StepIn D sevm
        (St (feeFactoryCallWorld sevm b)
          (gw :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
            132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeRequestMemory M) callGas) (.exec .staticcall) d ∧
      StaticCallPost (feeFactoryCallWorld sevm b) d
        (132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) 128 4 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2^256 ∧
      StaticAnswered sevm (feeFactoryCallWorld sevm b) (feeFactoryWord sevm b).toAdr
        (ExternalOperation.encode .feeTo) out ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St d (out.length.toB256 :: 128 :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
          (feeReplyMemory M out) decodeGas) t_2781_c68 (.done o) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St (feeKLastWorld sevm d)
          (feeKLastWord sevm d :: Bytes.toB256 (out.take 32) ::
            feeOnWord (Bytes.toB256 (out.take 32)) :: r1 :: r0 :: ρ :: R)
          (feeReplyMemory M out) branchGas)
        (feeDecodedTree (Bytes.toB256 (out.take 32))) (.done o) ∧
      feeBranchAccepts sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
        (Bytes.toB256 (out.take 32)) r0 r1 ∧
      o = .returned (feeBranchPost sevm (feeKLastWorld sevm d) R (feeReplyMemory M out)
        (feeKLastWord sevm d) (Bytes.toB256 (out.take 32)) r0 r1 gas) := by
  obtain ⟨code, gw, callGas, d, out, decodeGas, branchGas,
    step, post, width, bound, answer, decoder, branch⟩ :=
    feeFactoryDecoded_inv fork mem (SFunc.runP_iff_runCutP_nil.mp run)
  have quiet := (SFunc.runP_iff_runCutP_nil.mpr branch).mono (fun h => StepIn.toRun h)
  obtain ⟨guards, gas, result⟩ := feeBranch_inv fork
    (feeReplyMemory_ptr out (feeRequestMemory_ptr mem)) bound0 bound1 quiet
  exact ⟨code, gw, callGas, d, out, decodeGas, branchGas, gas,
    step, post, width, bound, answer, decoder, branch, guards, result⟩

/-- Positive fee liquidity constructs the actual LP62 run from its four selected charges.
No callee outcome is assumed, and the recipient charge follows the supply store. -/
theorem feePositiveLiquidity_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G sourceCost supplyCost loadCost creditCost : Nat} {N D z a K w f r1 r0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (positive : N / D ≠ 0) (accepts : lpMintAccepts sevm b w (N / D))
    (sourceEq : sourceCost = sloadCost sevm b 0)
    (supplyEq : supplyCost = sstoreCost sevm (afterSload sevm b 0) 0
      (lpMintSupplyWord sevm b + N / D))
    (loadEq : loadCost = sloadCost sevm
      (lpMintSupplyBase sevm (afterSload sevm b 0) (lpMintSupplyWord sevm b + N / D))
      (transferBalanceSlot w.toAdr))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm b 0)
        (lpMintSupplyWord sevm b + N / D)) (transferBalanceSlot w.toAdr))
      (transferBalanceSlot w.toAdr)
      (lpMintRecipientWord sevm (afterSload sevm b 0) w (lpMintSupplyWord sevm b + N / D) + N / D))
    (supplySentry : gCallStipend < G + supplyCost + loadCost + creditCost + 2124)
    (creditSentry : gCallStipend < G + creditCost + 1875) (room : R.length ≤ 1003) :
    SFunc.RunExact cert.prog sevm
      (St b (N :: D :: 0 :: D :: N :: z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + sourceCost + supplyCost + loadCost + creditCost + 2268)) t_2845_c68
      (.returned (feeLiquidityPost sevm b R M w f N D G)) := by
  rw [feeLiquidityPost, ite_eq_right positive]
  rw [show G + sourceCost + supplyCost + loadCost + creditCost + 2268 =
    ((G + 47) + sourceCost + supplyCost + loadCost + creditCost + 2171 + 20) + 30 from by omega]
  apply feeLiquidity_exact (by omega)
  rw [feeLiquidityTree, ite_eq_right positive]
  apply feePositiveLiquidityCaller_exact room
  exact lpMint62_exact fork mem sourceEq supplyEq loadEq creditEq
    (by omega) (by omega) accepts.2.1 accepts.1 accepts.2.2
    (by simp only [List.length_cons]; omega)

/-- The complete zero-liquidity growth arm costs442 fixed gas plus its actual supply load
and numerator multiplier, and performs no store or log. -/
theorem feeGrowthZero_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G load : Nat} {z a K w f r1 r0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (charge : load = sloadCost sevm b 0)
    (cover : z ≤ a) (accepts : feeGrowthAccepts sevm b w z a)
    (zeroL : feeNumeratorWord sevm b z a / feeDenominatorWord z a = 0)
    (room : R.length ≤ 1003) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + mul58Charge (a - z) + load + 442)) t_27f0_c68
      (.returned (feeGrowthPost sevm b R M w f z a G)) := by
  rw [show G + mul58Charge (a - z) + load + 442 =
    (G + 77) + mul58Charge (a - z) + load + 365 from by omega]
  apply feeGrowthPrefix_exact fork charge cover accepts.1 accepts.2.1 accepts.2.2.1 accepts.2.2.2.1 room
  rw [feeGrowthPost, feeLiquidityPost, ite_eq_left zeroL]
  exact feeZeroLiquidity_exact zeroL (by omega)

/-- Positive growth constructs every checked call, the real second supply load and both LP stores. -/
theorem feeGrowthPositive_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G load sourceCost supplyCost loadCost creditCost : Nat} {z a K w f r1 r0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (charge : load = sloadCost sevm b 0) (cover : z ≤ a)
    (accepts : feeGrowthAccepts sevm b w z a)
    (positive : feeNumeratorWord sevm b z a / feeDenominatorWord z a ≠ 0)
    (sourceEq : sourceCost = sloadCost sevm (afterSload sevm b 0) 0)
    (supplyEq : supplyCost = sstoreCost sevm (afterSload sevm (afterSload sevm b 0) 0) 0
      (lpMintSupplyWord sevm (afterSload sevm b 0) + feeNumeratorWord sevm b z a / feeDenominatorWord z a))
    (loadEq : loadCost = sloadCost sevm
      (lpMintSupplyBase sevm (afterSload sevm (afterSload sevm b 0) 0)
        (lpMintSupplyWord sevm (afterSload sevm b 0) + feeNumeratorWord sevm b z a / feeDenominatorWord z a))
      (transferBalanceSlot w.toAdr))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm (afterSload sevm b 0) 0)
        (lpMintSupplyWord sevm (afterSload sevm b 0) + feeNumeratorWord sevm b z a / feeDenominatorWord z a))
        (transferBalanceSlot w.toAdr)) (transferBalanceSlot w.toAdr)
      (lpMintRecipientWord sevm (afterSload sevm (afterSload sevm b 0) 0) w
        (lpMintSupplyWord sevm (afterSload sevm b 0) + feeNumeratorWord sevm b z a / feeDenominatorWord z a) +
        feeNumeratorWord sevm b z a / feeDenominatorWord z a))
    (supplySentry : gCallStipend < G + supplyCost + loadCost + creditCost + 2124)
    (creditSentry : gCallStipend < G + creditCost + 1875) (room : R.length ≤ 1003) :
    SFunc.RunExact cert.prog sevm
      (St b (z :: a :: K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + sourceCost + supplyCost + loadCost + creditCost + mul58Charge (a - z) + load + 2633))
      t_27f0_c68 (.returned (feeGrowthPost sevm b R M w f z a G)) := by
  rw [show G + sourceCost + supplyCost + loadCost + creditCost + mul58Charge (a - z) + load + 2633 =
    (G + sourceCost + supplyCost + loadCost + creditCost + 2268) + mul58Charge (a - z) + load + 365 from by omega]
  apply feeGrowthPrefix_exact fork charge cover accepts.1 accepts.2.1 accepts.2.2.1 accepts.2.2.2.1 room
  exact feePositiveLiquidity_exact fork mem positive (accepts.2.2.2.2 positive)
    sourceEq supplyEq loadEq creditEq supplySentry creditSentry room

/-- Both exact roots and the no-growth cleanup are constructed for the actual nonzero-kLast arm. -/
theorem feeOnNoGrowth_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {K w f r1 r0 ρ : B256}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (nonzero : K ≠ 0) (noGrowth : ¬ feeLastRoot K < feeReserveRoot r0 r1)
    (room : R.length ≤ 1006) :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 + 175))
      t_27ab_c68 (.returned (feeOnPost sevm b R M K w f r0 r1 G)) := by
  rw [feeOnPost, ite_eq_right nonzero, ite_eq_right noGrowth]
  rw [show G + sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 + 175 =
    (((G + 71) + sqrtCharge K.toNat + 26) + sqrtCharge (r0 * r1).toNat + 12) + mul58Charge r1 + 47 + 19 from by omega]
  apply feeOnNonzero_exact nonzero (by omega)
  apply feeReserveProduct_exact bound0 bound1 (by omega)
  apply feeRootK_exact (by omega)
  apply feeRootKLast_exact room
  exact feeNoGrowth_exact noGrowth (by omega)

/-- All actual root prefixes for growth cost135 plus their separately selected sqrt/mul charges. -/
theorem feeOnGrowthPrefix_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {K w f r1 r0 ρ : B256} {o : Outcome}
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112)
    (nonzero : K ≠ 0) (growth : feeLastRoot K < feeReserveRoot r0 r1)
    (room : R.length ≤ 1006)
    (body : SFunc.RunExact cert.prog sevm
      (St b (feeLastRoot K :: feeReserveRoot r0 r1 :: K :: w :: f :: r1 :: r0 :: ρ :: R) M G)
      t_27f0_c68 o) :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: f :: r1 :: r0 :: ρ :: R)
        M (G + sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 + 135))
      t_27ab_c68 o := by
  rw [show G + sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 + 135 =
    (((G + 31) + sqrtCharge K.toNat + 26) + sqrtCharge (r0 * r1).toNat + 12) + mul58Charge r1 + 47 + 19 from by omega]
  apply feeOnNonzero_exact nonzero (by omega)
  apply feeReserveProduct_exact bound0 bound1 (by omega)
  apply feeRootK_exact (by omega)
  apply feeRootKLast_exact room
  apply feeRootCompare_exact (by omega)
  dsimp only [feeLastRoot, feeReserveRoot] at growth body
  rw [ite_eq_left growth]
  exact body

def feeGrowthLiquidity (sevm : Sevm) (b : Devm) (z a : B256) : B256 :=
  feeNumeratorWord sevm b z a / feeDenominatorWord z a

def feeGrowthCharge (sevm : Sevm) (b : Devm) (z a : B256)
    (sourceCost supplyCost loadCost creditCost : Nat) : Nat :=
  mul58Charge (a - z) + sloadCost sevm b 0 +
    if feeGrowthLiquidity sevm b z a = 0 then 442
    else sourceCost + supplyCost + loadCost + creditCost + 2633

def feeOnCharge (sevm : Sevm) (b : Devm) (K r0 r1 : B256)
    (sourceCost supplyCost loadCost creditCost : Nat) : Nat :=
  if K = 0 then 54 else
    sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 +
      if feeLastRoot K < feeReserveRoot r0 r1 then
        feeGrowthCharge sevm b (feeLastRoot K) (feeReserveRoot r0 r1)
          sourceCost supplyCost loadCost creditCost + 135
      else 175

def feeBranchCharge (sevm : Sevm) (b : Devm) (K w r0 r1 : B256)
    (sourceCost supplyCost loadCost creditCost : Nat) : Nat :=
  if w.toAdr.toB256 = 0 then feeOffCharge sevm b K
  else feeOnCharge sevm b K r0 r1 sourceCost supplyCost loadCost creditCost

/-- Exact fee forward obligations describe genuine selected charges and only actual store sentries.
The four LP costs are annotations of total cost functions even on arms that do not mint. -/
structure FeeBranchForward (sevm : Sevm) (b : Devm) (K w r0 r1 : B256)
    (G sourceCost supplyCost loadCost creditCost : Nat) : Prop where
  accepts : feeBranchAccepts sevm b K w r0 r1
  clearSentry : w.toAdr.toB256 = 0 → K ≠ 0 →
    gCallStipend < G + sstoreCost sevm b 11 0 + 23
  sourceEq : sourceCost = sloadCost sevm (afterSload sevm b 0) 0
  supplyEq : supplyCost = sstoreCost sevm (afterSload sevm (afterSload sevm b 0) 0) 0
    (lpMintSupplyWord sevm (afterSload sevm b 0) +
      feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1))
  loadEq : loadCost = sloadCost sevm
    (lpMintSupplyBase sevm (afterSload sevm (afterSload sevm b 0) 0)
      (lpMintSupplyWord sevm (afterSload sevm b 0) +
        feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)))
    (transferBalanceSlot w.toAdr)
  creditEq : creditCost = sstoreCost sevm
    (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm (afterSload sevm b 0) 0)
      (lpMintSupplyWord sevm (afterSload sevm b 0) +
        feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)))
      (transferBalanceSlot w.toAdr)) (transferBalanceSlot w.toAdr)
    (lpMintRecipientWord sevm (afterSload sevm (afterSload sevm b 0) 0) w
      (lpMintSupplyWord sevm (afterSload sevm b 0) +
        feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1)) +
      feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1))
  supplySentry : w.toAdr.toB256 ≠ 0 → K ≠ 0 → feeLastRoot K < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1) ≠ 0 →
    gCallStipend < G + supplyCost + loadCost + creditCost + 2124
  creditSentry : w.toAdr.toB256 ≠ 0 → K ≠ 0 → feeLastRoot K < feeReserveRoot r0 r1 →
    feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1) ≠ 0 →
    gCallStipend < G + creditCost + 1875

/-- Complete exact forward for all six literal branches constructs every callee and its actual post. -/
theorem feeBranch_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G sourceCost supplyCost loadCost creditCost : Nat} {K w r1 r0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) (room : R.length ≤ 1003)
    (forward : FeeBranchForward sevm b K w r0 r1 G sourceCost supplyCost loadCost creditCost) :
    SFunc.RunExact cert.prog sevm
      (St b (K :: w :: feeOnWord w :: r1 :: r0 :: ρ :: R)
        M (G + feeBranchCharge sevm b K w r0 r1 sourceCost supplyCost loadCost creditCost))
      (feeDecodedTree w) (.returned (feeBranchPost sevm b R M K w r0 r1 G)) := by
  by_cases zeroAddress : w.toAdr.toB256 = 0
  · rw [feeDecodedTree, feeBranchCharge, feeBranchPost,
      ite_eq_left zeroAddress, ite_eq_left zeroAddress, ite_eq_left zeroAddress]
    apply feeOff_exact fork (by omega)
    · simpa only [feeBranchAccepts, ite_eq_left zeroAddress] using forward.accepts
    · exact forward.clearSentry zeroAddress
  · rw [feeDecodedTree, feeBranchCharge, feeBranchPost,
      ite_eq_right zeroAddress, ite_eq_right zeroAddress, ite_eq_right zeroAddress]
    by_cases zeroK : K = 0
    · rw [feeOnCharge, feeOnPost, ite_eq_left zeroK, ite_eq_left zeroK]
      subst K
      exact feeOnZero_exact (by omega)
    · by_cases growth : feeLastRoot K < feeReserveRoot r0 r1
      · have accepts : feeGrowthAccepts sevm b w (feeLastRoot K) (feeReserveRoot r0 r1) :=
          (show feeOnAccepts sevm b K w r0 r1 from by
            simpa only [feeBranchAccepts, ite_eq_right zeroAddress] using forward.accepts) zeroK growth
        rw [feeOnCharge, feeOnPost, ite_eq_right zeroK, ite_eq_right zeroK,
          ite_eq_left growth, ite_eq_left growth]
        rw [show G + (sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 +
            (feeGrowthCharge sevm b (feeLastRoot K) (feeReserveRoot r0 r1)
              sourceCost supplyCost loadCost creditCost + 135)) =
          (G + feeGrowthCharge sevm b (feeLastRoot K) (feeReserveRoot r0 r1)
            sourceCost supplyCost loadCost creditCost) +
            sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 + 135 from by omega]
        apply feeOnGrowthPrefix_exact bound0 bound1 zeroK growth (by omega)
        by_cases zeroL : feeGrowthLiquidity sevm b (feeLastRoot K) (feeReserveRoot r0 r1) = 0
        · rw [feeGrowthCharge, ite_eq_left zeroL]
          rw [show G + (mul58Charge (feeReserveRoot r0 r1 - feeLastRoot K) + sloadCost sevm b 0 + 442) =
            G + mul58Charge (feeReserveRoot r0 r1 - feeLastRoot K) + sloadCost sevm b 0 + 442 from by omega]
          exact feeGrowthZero_exact fork rfl (le_of_lt growth) accepts zeroL room
        · rw [feeGrowthCharge, ite_eq_right zeroL]
          rw [show G + (mul58Charge (feeReserveRoot r0 r1 - feeLastRoot K) + sloadCost sevm b 0 +
              (sourceCost + supplyCost + loadCost + creditCost + 2633)) =
            G + sourceCost + supplyCost + loadCost + creditCost +
              mul58Charge (feeReserveRoot r0 r1 - feeLastRoot K) + sloadCost sevm b 0 + 2633 from by omega]
          exact feeGrowthPositive_exact fork mem rfl (le_of_lt growth) accepts zeroL
            forward.sourceEq forward.supplyEq forward.loadEq forward.creditEq
            (forward.supplySentry zeroAddress zeroK growth zeroL)
            (forward.creditSentry zeroAddress zeroK growth zeroL) room
      · rw [feeOnCharge, ite_eq_right zeroK, ite_eq_right growth]
        rw [show G + (sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 + 175) =
          G + sqrtCharge K.toNat + sqrtCharge (r0 * r1).toNat + mul58Charge r1 + 175 from by omega]
        exact feeOnNoGrowth_exact bound0 bound1 zeroK growth (by omega)

/-- Full actual fee68 exact forward consumes a genuine factory STATICCALL and constructs
all six decoded arms. Its physical reply word comes from the complete actual returndata. -/
theorem fee68_exact {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem}
    {G callGas sourceCost supplyCost loadCost creditCost : Nat} {r1 r0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) (room : R.length ≤ 1003)
    (code : ((feeFactoryLoadWorld sevm b).getCode (feeFactoryWord sevm b).toAdr).size.toB256 ≠ 0)
    (call : Ninst.RunCompiled sevm
      (St (feeFactoryCallWorld sevm b)
        (callGas.toB256 :: feeFactoryWord sevm b :: 128 :: 4 :: 128 :: 32 ::
          132 :: 0x017e7e58 :: feeFactoryWord sevm b :: 0 :: 0 :: r1 :: r0 :: ρ :: R)
        (feeRequestMemory M) callGas) (.exec .staticcall) d)
    (success : d.stack = 1 :: 132 :: 0x017e7e58 :: feeFactoryWord sevm b ::
      0 :: 0 :: r1 :: r0 :: ρ :: R)
    (width : 32 ≤ d.returnData.length)
    (returnedGas : d.gasLeft = G +
      feeBranchCharge sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 sourceCost supplyCost loadCost creditCost +
      sloadCost sevm d 11 + 120)
    (forward : FeeBranchForward sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 G sourceCost supplyCost loadCost creditCost) :
    SFunc.RunExact cert.prog sevm
      (St b (r1 :: r0 :: ρ :: R) M (callGas + sloadCost sevm b 5 +
        temporalAccountAccessCost (feeFactoryLoadWorld sevm b) (feeFactoryWord sevm b).toAdr + 142))
      t_26ec_c68 (.returned (feeBranchPost sevm (feeKLastWorld sevm d) R
        (feeReplyMemory M d.returnData) (feeKLastWord sevm d)
        (Bytes.toB256 (d.returnData.take 32)) r0 r1 G)) := by
  apply feeFactoryObservation_exact (decodeGas := G +
    feeBranchCharge sevm (feeKLastWorld sevm d) (feeKLastWord sevm d)
      (Bytes.toB256 (d.returnData.take 32)) r0 r1 sourceCost supplyCost loadCost creditCost +
    sloadCost sevm d 11 + 56) fork mem (by omega) code call success (by omega) width
  apply feeDecoder_exact fork (feeReplyMemory_ptr d.returnData (feeRequestMemory_ptr mem))
    (by omega) rfl (feeReplyMemory_word mem.wf d.returnData width)
  exact feeBranch_exact fork (feeReplyMemory_ptr d.returnData (feeRequestMemory_ptr mem))
    bound0 bound1 room forward

end Blanc.Lift.UniswapV2Pair
