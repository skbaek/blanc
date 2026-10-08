import Blanc.Lift.UniswapV2Pair.PairTransferPreparation
import Blanc.Lift.UniswapV2Pair.PairTransferInitialize
import Blanc.Lift.UniswapV2Pair.BurnPricingWalk
import Blanc.Lift.ByteWindowMemory
import Blanc.Lift.ReturnDataBound
import Jaune.MemoryAccounting

/-! Literal57 transfer call and its full optional-return decoder. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The actual helper57 cleanup returns after discarding its five local words. -/
private theorem safeTransfer_return_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {a x y z w ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (a :: x :: y :: z :: w :: ρ :: R) M G) t_21e1_c17 r) :
    ∃ residual, r = .done (.returned (St b R M residual)) := by
  have h := run
  unfold t_21e1_c17 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  cases h with
  | ret d pop =>
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    exact ⟨_, congrArg (fun d => Seg.done (.returned d)) eq⟩

/-- Exact helper57 cleanup costs19gas and retains the full returned world and memory. -/
private theorem safeTransfer_return_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {a x y z w ρ : B256} :
    SFunc.RunExact cert.prog sevm (St b (a :: x :: y :: z :: w :: ρ :: R) M (G + 19))
      t_21e1_c17 (.returned (St b R M G)) := by
  unfold t_21e1_c17
  apply rx_dest
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact rx_ret

/-- The final transfer guard accepts every nonzero word and excludes its actual revert arm. -/
private theorem safeTransfer_check_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {flag a x y z w ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (flag :: a :: x :: y :: z :: w :: ρ :: R) M G) t_2176_c17 r) :
    flag ≠ 0 ∧ ∃ residual, r = .done (.returned (St b R M residual)) := by
  have h := run
  unfold t_2176_c17 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x21, 0xe1] = (0x21e1 : B256) from rfl] at eq
  subst d
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨positive, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_217b_c17.noOk = true)).elim
  · exact ⟨positive, safeTransfer_return_inv project body⟩

/-- Exact helper57 final guard and cleanup cost33gas for any nonzero boolean word. -/
private theorem safeTransfer_check_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {flag a x y z w ρ : B256}
    (positive : flag ≠ 0) (room : R.length ≤ 1016) :
    SFunc.RunExact cert.prog sevm (St b (flag :: a :: x :: y :: z :: w :: ρ :: R) M (G + 33))
      t_2176_c17 (.returned (St b R M G)) := by
  unfold t_2176_c17
  apply rx_dest
  apply rx_push (w := 0x21e1) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ positive
  exact safeTransfer_return_exact

/-- The nonempty-reply path checks the actual loaded word, with its selected memory expansion. -/
private theorem safeTransfer_head_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {discard ptr a x y z w ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (discard :: ptr :: a :: x :: y :: z :: w :: ρ :: R) M G) t_2173_c16 r) :
    Bytes.toB256 (M.read ptr.toNat 32).1 ≠ 0 ∧ ∃ residual,
      r = .done (.returned (St b R (M.read ptr.toNat 32).2 residual)) := by
  have h := run
  unfold t_2173_c16 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_mload (project hd)
  subst d
  exact safeTransfer_check_inv project h

/-- Exact nonempty-reply word check keeps the actual expansion cost and expanded memory. -/
private theorem safeTransfer_head_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {discard ptr a x y z w ρ : B256}
    (positive : Bytes.toB256 (M.read ptr.toNat 32).1 ≠ 0) (room : R.length ≤ 1016) :
    let c := gVerylow + (St b [] M 0).extCost [⟨ptr.toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b (discard :: ptr :: a :: x :: y :: z :: w :: ρ :: R) M (G + 33 + c + 3))
      t_2173_c16 (.returned (St b R (M.read ptr.toNat 32).2 G)) := by
  unfold t_2173_c16
  apply rx_dest
  apply rx_pop
  apply rx_mload_ext (i := ptr) (v := Bytes.toB256 (M.read ptr.toNat 32).1)
    (c := gVerylow + (St b [] M 0).extCost [⟨ptr.toNat, 32⟩]) rfl rfl rfl
    (by simp only [List.length_cons]; omega)
  exact safeTransfer_check_exact positive room

/-- The actual nonempty decoder derives its minimum width and checks the selected reply word. -/
private theorem safeTransfer_decodeWords_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {discard ptr success value toWord tokenWord ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (discard :: ptr :: success :: value :: toWord :: tokenWord :: ρ :: R) M G)
      t_215e_c16 r) :
    let M1 := (M.read ptr.toNat 32).2
    32 ≤ (Bytes.toB256 (M.read ptr.toNat 32).1).toNat ∧
      Bytes.toB256 (M1.read (32 + ptr).toNat 32).1 ≠ 0 ∧ ∃ residual,
      r = .done (.returned (St b R (M1.read (32 + ptr).toNat 32).2 residual)) := by
  have h := run
  unfold t_215e_c16 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup (w := Bytes.toB256 (M.read ptr.toNat 32).1) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  rcases ric_branchP h with ⟨_, _, failed⟩ | ⟨positive, _, body⟩
  · exact (failed.false_of_noOk (by decide : t_216f_c16.noOk = true)).elim
  · have width := toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero positive)
    exact ⟨width, safeTransfer_head_inv project body⟩

/-- Exact nonempty decoder retains both selected memory expansions and the modular data pointer. -/
private theorem safeTransfer_decodeWords_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {discard ptr success value toWord tokenWord ρ : B256}
    (width : 32 ≤ (Bytes.toB256 (M.read ptr.toNat 32).1).toNat)
    (positive : Bytes.toB256 ((M.read ptr.toNat 32).2.read (32 + ptr).toNat 32).1 ≠ 0)
    (room : R.length ≤ 1014) :
    let M1 := (M.read ptr.toNat 32).2
    let cL := gVerylow + (St b [] M 0).extCost [⟨ptr.toNat, 32⟩]
    let cH := gVerylow + (St b [] M1 0).extCost [⟨(32 + ptr).toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b (discard :: ptr :: success :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + 78 + cL + cH)) t_215e_c16
      (.returned (St b R (M1.read (32 + ptr).toNat 32).2 G)) := by
  dsimp only
  let cL := gVerylow + (St b [] M 0).extCost [⟨ptr.toNat, 32⟩]
  let cH := gVerylow + (St b [] (M.read ptr.toNat 32).2 0).extCost [⟨(32 + ptr).toNat, 32⟩]
  have enough : ¬ Bytes.toB256 (M.read ptr.toNat 32).1 < (32 : B256) := by
    rw [B256.lt_iff_toNat_lt_toNat]
    change ¬ (Bytes.toB256 (M.read ptr.toNat 32).1).toNat < 32
    omega
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (discard :: ptr :: success :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + 33 + cH + 3 + 10 + 3 + 3 + 3 + 3 + 3 + cL + 3 + 3 + 3 + 3 + 3 + 2))
      t_215e_c16 (.returned (St b R ((M.read ptr.toNat 32).2.read (32 + ptr).toNat 32).2 G)) by
    have gas : G + 33 + cH + 3 + 10 + 3 + 3 + 3 + 3 + 3 + cL + 3 + 3 + 3 + 3 + 3 + 2 =
      G + 78 + cL + cH := by omega
    rw [gas] at h
    exact h
  unfold t_215e_c16
  apply rx_pop
  apply rx_dup (w := ptr) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := ptr) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_mload_ext (i := ptr) (v := Bytes.toB256 (M.read ptr.toNat 32).1)
    (c := cL) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := Bytes.toB256 (M.read ptr.toNat 32).1) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_lt (v := 0) (by simp only [B256.ltCheck, ite_eq_right enough])
    (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2173) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  exact safeTransfer_head_exact positive (by omega)

/-- The optional-return branch preserves the empty arm and the actual two later reads. -/
private theorem safeTransfer_optional_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {discard ptr success value toWord tokenWord ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 17 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (discard :: ptr :: success :: value :: toWord :: tokenWord :: ρ :: R) M G)
      t_2155_c16 r) :
    let len := Bytes.toB256 (M.read ptr.toNat 32).1
    let M1 := (M.read ptr.toNat 32).2
    (len = 0 ∧ ∃ residual, r = .done (.returned (St b R M1 residual))) ∨
    (len ≠ 0 ∧ 32 ≤ (Bytes.toB256 (M1.read ptr.toNat 32).1).toNat ∧
      Bytes.toB256 ((M1.read ptr.toNat 32).2.read (32 + ptr).toNat 32).1 ≠ 0 ∧
      ∃ residual, r = .done (.returned
        (St b R ((M1.read ptr.toNat 32).2.read (32 + ptr).toNat 32).2 residual))) := by
  have h := run
  unfold t_2155_c16 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  by_cases empty : Bytes.toB256 (M.read ptr.toNat 32).1 = 0
  · rw [empty, show B256.eqCheck 0 0 = (1 : B256) from by decide] at h
    cases h with
    | toZero d pop tail =>
      obtain ⟨_, bad, _⟩ := St.of_pop2 pop
      exact ((by decide : (1 : B256) ≠ 0) bad).elim
    | toSuccCut d w nonzero cut pop => exact (notCut cut).elim
    | toSucc d w nonzero nc lookup pop tail =>
      change some t_2176_c17 = _ at lookup
      cases lookup
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      exact Or.inl ⟨empty, (safeTransfer_check_inv project tail).2⟩
  · have flag : B256.eqCheck (Bytes.toB256 (M.read ptr.toNat 32).1) 0 = 0 := ite_eq_right empty
    rw [flag] at h
    cases h with
    | toSuccCut d w nonzero cut pop => exact (notCut cut).elim
    | toSucc d w nonzero nc lookup pop tail =>
      obtain ⟨_, rfl, _⟩ := St.of_pop2 pop
      exact (nonzero rfl).elim
    | toZero d pop tail =>
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      exact Or.inr ⟨empty, safeTransfer_decodeWords_inv project tail⟩

/-- Exact optional-return decoder selects the actual empty or nonempty memory/gas arm. -/
private theorem safeTransfer_optional_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {discard ptr success value toWord tokenWord ρ : B256}
    (accepted : Bytes.toB256 (M.read ptr.toNat 32).1 = 0 ∨
      (32 ≤ (Bytes.toB256 ((M.read ptr.toNat 32).2.read ptr.toNat 32).1).toNat ∧
       Bytes.toB256 (((M.read ptr.toNat 32).2.read ptr.toNat 32).2.read (32 + ptr).toNat 32).1 ≠ 0))
    (room : R.length ≤ 1014) :
    let len := Bytes.toB256 (M.read ptr.toNat 32).1
    let M1 := (M.read ptr.toNat 32).2
    let M2 := (M1.read ptr.toNat 32).2
    let c1 := gVerylow + (St b [] M 0).extCost [⟨ptr.toNat, 32⟩]
    let c2 := gVerylow + (St b [] M1 0).extCost [⟨ptr.toNat, 32⟩]
    let cH := gVerylow + (St b [] M2 0).extCost [⟨(32 + ptr).toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b (discard :: ptr :: success :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + 24 + c1 + if len = 0 then 33 else 78 + c2 + cH)) t_2155_c16
      (.returned (St b R (if len = 0 then M1 else (M2.read (32 + ptr).toNat 32).2) G)) := by
  dsimp only
  let c1 := gVerylow + (St b [] M 0).extCost [⟨ptr.toNat, 32⟩]
  let c2 := gVerylow + (St b [] (M.read ptr.toNat 32).2 0).extCost [⟨ptr.toNat, 32⟩]
  let cH := gVerylow + (St b [] ((M.read ptr.toNat 32).2.read ptr.toNat 32).2 0).extCost
    [⟨(32 + ptr).toNat, 32⟩]
  by_cases empty : Bytes.toB256 (M.read ptr.toNat 32).1 = 0
  · simp only [ite_eq_left empty]
    suffices h : SFunc.RunExact cert.prog sevm
        (St b (discard :: ptr :: success :: value :: toWord :: tokenWord :: ρ :: R)
          M (G + 33 + 10 + 3 + 3 + 3 + c1 + 3 + 2)) t_2155_c16
        (.returned (St b R (M.read ptr.toNat 32).2 G)) by
      have gas : G + 33 + 10 + 3 + 3 + 3 + c1 + 3 + 2 = G + 24 + c1 + 33 := by omega
      rw [gas] at h
      exact h
    unfold t_2155_c16
    apply rx_pop
    apply rx_dup (w := ptr) rfl (by simp only [List.length_cons]; omega)
    apply rx_mload_ext (i := ptr) (v := Bytes.toB256 (M.read ptr.toNat 32).1)
      (c := c1) rfl rfl rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 1) (by simp only [B256.eqCheck, ite_eq_left empty])
      (by simp only [List.length_cons]; omega)
    apply rx_dup (w := 1) rfl (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x2176) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_succ (by decide : (1 : B256) ≠ 0) (by rfl)
    exact safeTransfer_check_exact (by decide : (1 : B256) ≠ 0) (by omega)
  · simp only [ite_eq_right empty]
    obtain ⟨width, positive⟩ := accepted.resolve_left empty
    suffices h : SFunc.RunExact cert.prog sevm
        (St b (discard :: ptr :: success :: value :: toWord :: tokenWord :: ρ :: R)
          M (G + 78 + c2 + cH + 10 + 3 + 3 + 3 + c1 + 3 + 2)) t_2155_c16
        (.returned (St b R (((M.read ptr.toNat 32).2.read ptr.toNat 32).2.read (32 + ptr).toNat 32).2 G)) by
      have gas : G + 78 + c2 + cH + 10 + 3 + 3 + 3 + c1 + 3 + 2 =
        G + 24 + c1 + (78 + c2 + cH) := by omega
      rw [gas] at h
      exact h
    unfold t_2155_c16
    apply rx_pop
    apply rx_dup (w := ptr) rfl (by simp only [List.length_cons]; omega)
    apply rx_mload_ext (i := ptr) (v := Bytes.toB256 (M.read ptr.toNat 32).1)
      (c := c1) rfl rfl rfl (by simp only [List.length_cons]; omega)
    apply rx_iszero (v := 0) (by simp only [B256.eqCheck, ite_eq_right empty])
      (by simp only [List.length_cons]; omega)
    apply rx_dup (w := 0) rfl (by simp only [List.length_cons]; omega)
    apply rx_push (w := 0x2176) rfl (by simp only [List.length_cons]; omega)
    apply rx_branchTo_zero
    exact safeTransfer_decodeWords_exact width positive room

/-- Actual CALL cleanup derives success before entering the optional-return decoder. -/
theorem safeTransfer_success_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {x ptr success y z value toWord tokenWord ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 17 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (x :: ptr :: success :: y :: z :: value :: toWord :: tokenWord :: ρ :: R) M G)
      t_2148_c16 r) :
    success ≠ 0 ∧
    (let len := Bytes.toB256 (M.read ptr.toNat 32).1
     let M1 := (M.read ptr.toNat 32).2
     (len = 0 ∧ ∃ residual, r = .done (.returned (St b R M1 residual))) ∨
     (len ≠ 0 ∧ 32 ≤ (Bytes.toB256 (M1.read ptr.toNat 32).1).toNat ∧
       Bytes.toB256 ((M1.read ptr.toNat 32).2.read (32 + ptr).toNat 32).1 ≠ 0 ∧
       ∃ residual, r = .done (.returned
         (St b R ((M1.read ptr.toNat 32).2.read (32 + ptr).toNat 32).2 residual)))) := by
  have h := run
  unfold t_2148_c16 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := success) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := success) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_iszero (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  by_cases failed : success = 0
  · rw [failed, show B256.eqCheck 0 0 = (1 : B256) from by decide] at h
    cases h with
    | toZero d pop tail =>
      obtain ⟨_, bad, _⟩ := St.of_pop2 pop
      exact ((by decide : (1 : B256) ≠ 0) bad).elim
    | toSuccCut d w nonzero cut pop => exact (notCut cut).elim
    | toSucc d w nonzero nc lookup pop tail =>
      change some t_2176_c17 = _ at lookup
      cases lookup
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      exact ((safeTransfer_check_inv project tail).1 rfl).elim
  · have flag : B256.eqCheck success 0 = 0 := ite_eq_right failed
    rw [flag] at h
    cases h with
    | toSuccCut d w nonzero cut pop => exact (notCut cut).elim
    | toSucc d w nonzero nc lookup pop tail =>
      obtain ⟨_, rfl, _⟩ := St.of_pop2 pop
      exact (nonzero rfl).elim
    | toZero d pop tail =>
      obtain ⟨_, _, eq⟩ := St.of_pop2 pop
      rw [eq] at tail
      exact ⟨failed, safeTransfer_optional_inv project notCut tail⟩

/-- Exact CALL cleanup consumes success and builds the full selected optional-return arm. -/
private theorem safeTransfer_success_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {x ptr success y z value toWord tokenWord ρ : B256}
    (nonzero : success ≠ 0)
    (accepted : Bytes.toB256 (M.read ptr.toNat 32).1 = 0 ∨
      (32 ≤ (Bytes.toB256 ((M.read ptr.toNat 32).2.read ptr.toNat 32).1).toNat ∧
       Bytes.toB256 (((M.read ptr.toNat 32).2.read ptr.toNat 32).2.read (32 + ptr).toNat 32).1 ≠ 0))
    (room : R.length ≤ 1014) :
    let len := Bytes.toB256 (M.read ptr.toNat 32).1
    let M1 := (M.read ptr.toNat 32).2
    let M2 := (M1.read ptr.toNat 32).2
    let c1 := gVerylow + (St b [] M 0).extCost [⟨ptr.toNat, 32⟩]
    let c2 := gVerylow + (St b [] M1 0).extCost [⟨ptr.toNat, 32⟩]
    let cH := gVerylow + (St b [] M2 0).extCost [⟨(32 + ptr).toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b (x :: ptr :: success :: y :: z :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + 24 + c1 + (if len = 0 then 33 else 78 + c2 + cH) + 35)) t_2148_c16
      (.returned (St b R (if len = 0 then M1 else (M2.read (32 + ptr).toNat 32).2) G)) := by
  dsimp only
  unfold t_2148_c16
  apply rx_dest
  apply rx_pop
  apply rx_swap2
  apply rx_pop
  apply rx_swap2
  apply rx_pop
  apply rx_dup (w := success) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := success) rfl (by simp only [List.length_cons]; omega)
  apply rx_iszero (v := 0) (by simp only [B256.eqCheck, ite_eq_right nonzero])
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2176) rfl (by simp only [List.length_cons]; omega)
  apply rx_branchTo_zero
  exact safeTransfer_optional_exact accepted room

/-- Full returndata allocation transports the original primitive relation into the real cleanup. -/
private theorem safeTransfer_allocate_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {x oldPtr success y z value toWord tokenWord ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 16 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (x :: oldPtr :: success :: y :: z :: value :: toWord :: tokenWord :: ρ :: R) M G)
      t_2122_c57 r) :
    let ptr := Bytes.toB256 (M.read 64 32).1
    let len := b.returnData.length.toB256
    let M1 := (M.read 64 32).2
    let M2 := M1.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
    let M3 := M2.write ptr.toNat len.toBytes
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b (x :: ptr :: success :: y :: z :: value :: toWord :: tokenWord :: ρ :: R)
        (M3.write (ptr + 32).toNat (b.returnData.sliceD 0 len.toNat 0)) residual) t_2148_c16 r := by
  let ptr := Bytes.toB256 (M.read 64 32).1
  have h := run
  unfold t_2122_c57 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_not (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := ptr) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, _, rfl⟩ := ri_returndatacopy (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  cases h with
  | jumpCut d cut pop => exact (notCut cut).elim
  | jump d nc lookup pop tail =>
    change some t_2148_c16 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at tail
    exact ⟨_, tail⟩

/-- Exact full-reply allocation keeps the literal modular pointer and four selected memory charges. -/
private theorem safeTransfer_allocate_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome} {x oldPtr success y z value toWord tokenWord ρ : B256}
    (room : R.length ≤ 1011)
    (continuation :
      let ptr := Bytes.toB256 (M.read 64 32).1
      let len := b.returnData.length.toB256
      let M2 := (M.read 64 32).2.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
      let M3 := M2.write ptr.toNat len.toBytes
      SFunc.RunExact cert.prog sevm
        (St b (x :: ptr :: success :: y :: z :: value :: toWord :: tokenWord :: ρ :: R)
          (M3.write (ptr + 32).toNat (b.returnData.sliceD 0 len.toNat 0)) G) t_2148_c16 o) :
    let ptr := Bytes.toB256 (M.read 64 32).1
    let len := b.returnData.length.toB256
    let M1 := (M.read 64 32).2
    let M2 := M1.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
    let M3 := M2.write ptr.toNat len.toBytes
    let cRead := gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]
    let cStore := gVerylow + (St b [] M1 0).extCost [⟨64, 32⟩]
    let cLen := gVerylow + (St b [] M2 0).extCost [⟨ptr.toNat, 32⟩]
    let cCopy := gVerylow + gReturnDataCopy * ceilDiv len.toNat 32 +
      (St b [] M3 0).extCost [⟨(ptr + 32).toNat, len.toNat⟩]
    SFunc.RunExact cert.prog sevm
      (St b (x :: oldPtr :: success :: y :: z :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + 64 + cRead + cStore + cLen + cCopy)) t_2122_c57 o := by
  dsimp only at continuation ⊢
  let ptr := Bytes.toB256 (M.read 64 32).1
  let len := b.returnData.length.toB256
  let M1 := (M.read 64 32).2
  let M2 := M1.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
  let M3 := M2.write ptr.toNat len.toBytes
  let cRead := gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]
  let cStore := gVerylow + (St b [] M1 0).extCost [⟨64, 32⟩]
  let cLen := gVerylow + (St b [] M2 0).extCost [⟨ptr.toNat, 32⟩]
  let cCopy := gVerylow + gReturnDataCopy * ceilDiv len.toNat 32 +
    (St b [] M3 0).extCost [⟨(ptr + 32).toNat, len.toNat⟩]
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (x :: oldPtr :: success :: y :: z :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + 8 + 3 + cCopy + 3 + 3 + 3 + 3 + 2 + cLen + 3 + 2 + cStore + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 2 + 3 + cRead + 3))
      t_2122_c57 o by
    have gas : G + 8 + 3 + cCopy + 3 + 3 + 3 + 3 + 2 + cLen + 3 + 2 + cStore + 3 + 3 + 3 + 3 + 3 + 2 + 3 + 3 + 3 + 2 + 3 + cRead + 3 =
      G + 64 + cRead + cStore + cLen + cCopy := by omega
    rw [gas] at h
    exact h
  unfold t_2122_c57
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (i := 64) (v := ptr) (c := cRead) rfl rfl rfl
    (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_pop
  apply rx_push (w := 31) rfl (by simp only [List.length_cons]; omega)
  apply rx_not rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 63) rfl (by simp only [List.length_cons]; omega)
  apply rx_returndatasize (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := ptr) rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := 64) (c := cStore) rfl rfl
  apply rx_returndatasize (by simp only [List.length_cons]; omega)
  apply rx_dup (w := ptr) rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := ptr) (c := cLen) rfl rfl
  apply rx_returndatasize (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := ptr) rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  refine .next (Ninst.runCompiled_returndatacopy_of (c := cCopy) rfl rfl ?_ rfl rfl) ?_
  · simp only [show (0 : B256).toNat = 0 from rfl, Nat.zero_add, St.returnData]
    change len.toNat ≤ b.returnData.length
    rw [show len = b.returnData.length.toB256 from rfl, B256.toNat_toB256]
    exact Nat.mod_le _ _
  · apply rx_push (w := 0x2148) rfl (by simp only [List.length_cons]; omega)
    exact rx_jump rfl continuation

/-- One literal remaining-length copy pass keeps unaligned offsets and actual read expansion. -/
private theorem safeTransfer_copyBody_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {src dst len : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 71 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (src :: dst :: len :: R) M G) t_20ad_c57 r) :
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b ((32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
        ((M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes)
        residual) t_20a4_c57 r := by
  have h := run
  unfold t_20ad_c57 at h
  change SFunc.RunCutP P cert.prog sevm C _
    (pairTransferCopyLine.foldr SFunc.next (.jump 71)) r at h
  obtain ⟨middle, line, tail⟩ := h.split_nexts (fun step => project step) pairTransferCopyLine
  obtain ⟨residual, equal⟩ := pair_transfer_copy_line_inv line
  rw [equal] at tail
  cases tail with
  | jumpCut d cut pop => exact (notCut cut).elim
  | jump d nc lookup pop tail =>
    change some t_20a4_c57 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at tail
    exact ⟨_, tail⟩

/-- The real copy guard enters another pass when the remaining word is at least32. -/
private theorem safeTransfer_copyPass_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {src dst len : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 71 ∉ C) (enough : ¬ len < (32 : B256))
    (run : SFunc.RunCutP P cert.prog sevm C (St b (src :: dst :: len :: R) M G) t_20a4_c57 r) :
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b ((32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
        ((M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes)
        residual) t_20a4_c57 r := by
  have h := run
  unfold t_20a4_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := len) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [32] = (32 : B256) from rfl, B256.ltCheck,
    ite_eq_right enough] at h
  rcases ric_branchP h with ⟨_, _, body⟩ | ⟨nonzero, _, _⟩
  · exact safeTransfer_copyBody_inv project notCut body
  · exact (nonzero rfl).elim

/-- Exact literal copy body keeps the unaligned source/destination and selected expansions. -/
private theorem safeTransfer_copyBody_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome} {src dst len : B256}
    (room : R.length ≤ 1018)
    (continuation : SFunc.RunExact cert.prog sevm
      (St b ((32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
        ((M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes)
        G) t_20a4_c57 o) :
    let cRead := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
    let cStore := gVerylow + (St b [] (M.read src.toNat 32).2 0).extCost [⟨dst.toNat, 32⟩]
    SFunc.RunExact cert.prog sevm (St b (src :: dst :: len :: R) M (G + 50 + cRead + cStore))
      t_20ad_c57 o := by
  dsimp only
  let cRead := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
  let cStore := gVerylow + (St b [] (M.read src.toNat 32).2 0).extCost [⟨dst.toNat, 32⟩]
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (src :: dst :: len :: R)
        M (G + 8 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + cStore + 3 + cRead + 3))
      t_20ad_c57 o by
    have gas : G + 8 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + cStore + 3 + cRead + 3 =
      G + 50 + cRead + cStore := by omega
    rw [gas] at h
    exact h
  unfold t_20ad_c57
  apply rx_dup (w := src) rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (i := src) (v := Bytes.toB256 (M.read src.toNat 32).1)
    (c := cRead) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := dst) rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := dst) (c := cStore) rfl rfl
  apply rx_push (w := ~~~(31 : B256)) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap3
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_dup (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x20a4) rfl (by simp only [List.length_cons]; omega)
  exact rx_jump rfl continuation

/-- Exact remaining-length pass includes its actual23gas guard and50gas copy body. -/
private theorem safeTransfer_copyPass_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome} {src dst len : B256}
    (room : R.length ≤ 1018) (enough : ¬ len < (32 : B256))
    (continuation : SFunc.RunExact cert.prog sevm
      (St b ((32 + src) :: (32 + dst) :: (len + ~~~(31 : B256)) :: R)
        ((M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes)
        G) t_20a4_c57 o) :
    let cRead := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
    let cStore := gVerylow + (St b [] (M.read src.toNat 32).2 0).extCost [⟨dst.toNat, 32⟩]
    SFunc.RunExact cert.prog sevm (St b (src :: dst :: len :: R) M (G + 73 + cRead + cStore))
      t_20a4_c57 o := by
  dsimp only
  let cRead := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
  let cStore := gVerylow + (St b [] (M.read src.toNat 32).2 0).extCost [⟨dst.toNat, 32⟩]
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (src :: dst :: len :: R) M (G + 50 + cRead + cStore + 10 + 3 + 3 + 3 + 3 + 1))
      t_20a4_c57 o by
    have gas : G + 50 + cRead + cStore + 10 + 3 + 3 + 3 + 3 + 1 =
      G + 73 + cRead + cStore := by omega
    rw [gas] at h
    exact h
  unfold t_20a4_c57
  apply rx_dest
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := len) rfl (by simp only [List.length_cons]; omega)
  apply rx_lt (v := 0) (by simp only [B256.ltCheck, ite_eq_right enough])
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x20e1) rfl (by simp only [List.length_cons]; omega)
  apply rx_branch_zero
  exact safeTransfer_copyBody_exact room continuation


/-- The final copy guard preserves the actual remaining partial word and memory. -/
private theorem safeTransfer_copyExit_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {src dst len : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (short : len < (32 : B256))
    (run : SFunc.RunCutP P cert.prog sevm C (St b (src :: dst :: len :: R) M G) t_20a4_c57 r) :
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b (src :: dst :: len :: R) M residual) t_20e1_c57 r := by
  have h := run
  unfold t_20a4_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := len) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_lt (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [32] = (32 : B256) from rfl, B256.ltCheck,
    ite_eq_left short] at h
  rcases ric_branchP h with ⟨zero, _, _⟩ | ⟨_, _, body⟩
  · exact ((by decide : (1 : B256) ≠ 0) zero).elim
  · exact ⟨_, body⟩

/-- The final copy guard has its actual23gas charge. -/
private theorem safeTransfer_copyExit_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome} {src dst len : B256}
    (room : R.length ≤ 1018) (short : len < (32 : B256))
    (continuation : SFunc.RunExact cert.prog sevm
      (St b (src :: dst :: len :: R) M G) t_20e1_c57 o) :
    SFunc.RunExact cert.prog sevm (St b (src :: dst :: len :: R) M (G + 23))
      t_20a4_c57 o := by
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (src :: dst :: len :: R) M (G + 10 + 3 + 3 + 3 + 3 + 1)) t_20a4_c57 o by
    have gas : G + 10 + 3 + 3 + 3 + 3 + 1 = G + 23 := by omega
    rw [gas] at h
    exact h
  unfold t_20a4_c57
  apply rx_dest
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := len) rfl (by simp only [List.length_cons]; omega)
  apply rx_lt (v := 1) (by simp only [B256.ltCheck, ite_eq_left short])
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x20e1) rfl (by simp only [List.length_cons]; omega)
  exact rx_branch_succ (by decide : (1 : B256) ≠ 0) continuation

/-- The68byte payload performs exactly two literal passes before its four-byte tail. -/
private theorem safeTransfer_copy68_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {src dst : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 71 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (src :: dst :: 68 :: R) M G) t_20a4_c57 r) :
    let M1 := (M.read src.toNat 32).2.write dst.toNat
      (Bytes.toB256 (M.read src.toNat 32).1).toBytes
    let M2 := (M1.read (32 + src).toNat 32).2.write (32 + dst).toNat
      (Bytes.toB256 (M1.read (32 + src).toNat 32).1).toBytes
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b ((32 + (32 + src)) :: (32 + (32 + dst)) :: 4 :: R) M2 residual) t_20e1_c57 r := by
  dsimp only
  obtain ⟨g1, h1⟩ := safeTransfer_copyPass_inv project notCut
    (by decide : ¬ (68 : B256) < 32) run
  rw [show (68 : B256) + ~~~31 = 36 from rfl] at h1
  obtain ⟨g2, h2⟩ := safeTransfer_copyPass_inv project notCut
    (by decide : ¬ (36 : B256) < 32) h1
  rw [show (36 : B256) + ~~~31 = 4 from rfl] at h2
  exact safeTransfer_copyExit_inv project (by decide : (4 : B256) < 32) h2

/-- Exact68byte copy retains all four sequential read/store expansion charges. -/
private theorem safeTransfer_copy68_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome} {src dst : B256}
    (room : R.length ≤ 1018) :
    let M1 := (M.read src.toNat 32).2.write dst.toNat
      (Bytes.toB256 (M.read src.toNat 32).1).toBytes
    let M2 := (M1.read (32 + src).toNat 32).2.write (32 + dst).toNat
      (Bytes.toB256 (M1.read (32 + src).toNat 32).1).toBytes
    let cR0 := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
    let cS0 := gVerylow + (St b [] (M.read src.toNat 32).2 0).extCost [⟨dst.toNat, 32⟩]
    let cR1 := gVerylow + (St b [] M1 0).extCost [⟨(32 + src).toNat, 32⟩]
    let cS1 := gVerylow + (St b [] (M1.read (32 + src).toNat 32).2 0).extCost [⟨(32 + dst).toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b ((32 + (32 + src)) :: (32 + (32 + dst)) :: 4 :: R) M2 G) t_20e1_c57 o →
    SFunc.RunExact cert.prog sevm
      (St b (src :: dst :: 68 :: R) M (G + 169 + cR0 + cS0 + cR1 + cS1)) t_20a4_c57 o := by
  dsimp only
  intro continuation
  have exit := safeTransfer_copyExit_exact room (by decide : (4 : B256) < 32) continuation
  rw [← show (36 : B256) + ~~~31 = 4 from rfl] at exit
  have second := safeTransfer_copyPass_exact room (by decide : ¬ (36 : B256) < 32) exit
  rw [← show (68 : B256) + ~~~31 = 36 from rfl] at second
  have first := safeTransfer_copyPass_exact room (by decide : ¬ (68 : B256) < 32) second
  let M1 := (M.read src.toNat 32).2.write dst.toNat (Bytes.toB256 (M.read src.toNat 32).1).toBytes
  let cR0 := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
  let cS0 := gVerylow + (St b [] (M.read src.toNat 32).2 0).extCost [⟨dst.toNat, 32⟩]
  let cR1 := gVerylow + (St b [] M1 0).extCost [⟨(32 + src).toNat, 32⟩]
  let cS1 := gVerylow + (St b [] (M1.read (32 + src).toNat 32).2 0).extCost [⟨(32 + dst).toNat, 32⟩]
  change SFunc.RunExact cert.prog sevm
    (St b (src :: dst :: 68 :: R) M (G + 23 + 73 + cR1 + cS1 + 73 + cR0 + cS0))
    t_20a4_c57 o at first
  have gas : G + 23 + 73 + cR1 + cS1 + 73 + cR0 + cS0 =
    G + 169 + cR0 + cS0 + cR1 + cS1 := by omega
  rw [gas] at first
  exact first


/-- The literal post-CALL tree retains full returndata before choosing allocation or empty data. -/
def safeTransfer_afterCall : SFunc :=
  .next (.reg (.swap 1)) (.next (.reg .pop) (.next (.reg .pop)
    (.next (.reg .returndatasize) (.next (.reg (.dup 0)) (.next (.push [0] (by decide))
      (.next (.reg (.dup 1)) (.next (.reg .eq) (.next (.push [0x21, 0x43] (by decide))
        (.branch t_2122_c57 t_2143_c57)))))))))

/-- Actual four-byte merge and CALL preparation derive all seven operands in the same P run. -/
private theorem safeTransfer_partialCall_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {src dst a x y z w token : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (src :: dst :: 4 :: a :: x :: y :: z :: w :: token :: R) M G) t_20e1_c57 r) :
    let mask := B256.bexp 256 (32 - 4) - 1
    let M1 := (M.read src.toNat 32).2
    let M2 := (M1.read dst.toNat 32).2
    let M3 := M2.write dst.toNat
      (((Bytes.toB256 (M.read src.toNat 32).1) &&& ~~~mask) |||
        ((Bytes.toB256 (M1.read dst.toNat 32).1) &&& mask)).toBytes
    let q := Bytes.toB256 (M3.read 64 32).1
    let M4 := (M3.read 64 32).2
    ∃ forwarded callGas d,
      P sevm (St b (forwarded :: token :: 0 :: q :: ((a + y) - q) :: q :: 0 ::
        (a + y) :: token :: R) M4 callGas) (.exec .call) d ∧
      SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r := by
  dsimp only
  have h := run
  unfold t_20e1_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  change SFunc.RunCutP P cert.prog sevm C _
    (pairTransferPartialLine.foldr SFunc.next
      (.next (.reg .gas) (.next (.exec .call) safeTransfer_afterCall))) r at h
  obtain ⟨middle, line, tail⟩ := h.split_nexts (fun step => project step) pairTransferPartialLine
  obtain ⟨residual, equal⟩ := pair_transfer_partial_line_inv line
  rw [equal] at tail
  obtain ⟨d, hd, tail⟩ := ric_nextP tail
  obtain ⟨forwarded, callGas, rfl⟩ := ri_gas (project hd)
  obtain ⟨d, hd, tail⟩ := ric_nextP tail
  exact ⟨forwarded, callGas, d, hd, tail⟩

/-- The actual post-CALL branch derives the empty sentinel or full physical allocation. -/
theorem safeTransfer_afterCall_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {success endWord token y z value toWord tokenWord ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (notCut : 16 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (success :: endWord :: token :: y :: z :: value :: toWord :: tokenWord :: ρ :: R) M G)
      safeTransfer_afterCall r) :
    let len := b.returnData.length.toB256
    let ptr := Bytes.toB256 (M.read 64 32).1
    let M2 := (M.read 64 32).2.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
    let M3 := M2.write ptr.toNat len.toBytes
    let allocated := M3.write (ptr + 32).toNat (b.returnData.sliceD 0 len.toNat 0)
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b (len :: (if len = 0 then 96 else ptr) :: success :: y :: z :: value ::
          toWord :: tokenWord :: ρ :: R) (if len = 0 then M else allocated) residual) t_2148_c16 r := by
  dsimp only
  have h := run
  unfold safeTransfer_afterCall at h
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_returndatasize (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_eq (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl] at h
  by_cases empty : b.returnData.length.toB256 = 0
  · rw [empty, show B256.eqCheck 0 0 = (1 : B256) from rfl] at h
    rcases ric_branchP h with ⟨zero, _, _⟩ | ⟨_, _, body⟩
    · exact ((by decide : (1 : B256) ≠ 0) zero).elim
    · unfold t_2143_c57 at body
      obtain ⟨_, body⟩ := ric_destP body
      obtain ⟨d, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_push (project hd)
      obtain ⟨d, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
      obtain ⟨d, hd, body⟩ := ric_nextP body; obtain ⟨_, rfl⟩ := ri_pop (project hd)
      simp only [empty, ite_true]
      exact ⟨_, body⟩
  · have flag : B256.eqCheck b.returnData.length.toB256 0 = 0 := ite_eq_right empty
    rw [flag] at h
    rcases ric_branchP h with ⟨_, _, body⟩ | ⟨nonzero, _, _⟩
    · simp only [empty, ite_false]
      exact safeTransfer_allocate_inv project notCut body
    · exact (nonzero rfl).elim

/-- Exact post-CALL branching consumes the same allocation implementation and selected costs. -/
private theorem safeTransfer_afterCall_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome}
    {success endWord token y z value toWord tokenWord ρ : B256}
    (room : R.length ≤ 1011) :
    let len := b.returnData.length.toB256
    let ptr := Bytes.toB256 (M.read 64 32).1
    let M1 := (M.read 64 32).2
    let M2 := M1.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
    let M3 := M2.write ptr.toNat len.toBytes
    let allocated := M3.write (ptr + 32).toNat (b.returnData.sliceD 0 len.toNat 0)
    let cRead := gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]
    let cStore := gVerylow + (St b [] M1 0).extCost [⟨64, 32⟩]
    let cLen := gVerylow + (St b [] M2 0).extCost [⟨ptr.toNat, 32⟩]
    let cCopy := gVerylow + gReturnDataCopy * ceilDiv len.toNat 32 +
      (St b [] M3 0).extCost [⟨(ptr + 32).toNat, len.toNat⟩]
    SFunc.RunExact cert.prog sevm
      (St b (len :: (if len = 0 then 96 else ptr) :: success :: y :: z :: value ::
          toWord :: tokenWord :: ρ :: R) (if len = 0 then M else allocated) G) t_2148_c16 o →
    SFunc.RunExact cert.prog sevm
      (St b (success :: endWord :: token :: y :: z :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + 34 + (if len = 0 then 9 else 64 + cRead + cStore + cLen + cCopy)))
      safeTransfer_afterCall o := by
  dsimp only
  intro continuation
  let len := b.returnData.length.toB256
  let ptr := Bytes.toB256 (M.read 64 32).1
  let M1 := (M.read 64 32).2
  let M2 := M1.write 64 (ptr + ((len + 63) &&& ~~~(31 : B256))).toBytes
  let M3 := M2.write ptr.toNat len.toBytes
  let cRead := gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]
  let cStore := gVerylow + (St b [] M1 0).extCost [⟨64, 32⟩]
  let cLen := gVerylow + (St b [] M2 0).extCost [⟨ptr.toNat, 32⟩]
  let cCopy := gVerylow + gReturnDataCopy * ceilDiv len.toNat 32 +
    (St b [] M3 0).extCost [⟨(ptr + 32).toNat, len.toNat⟩]
  let charge := if len = 0 then 9 else 64 + cRead + cStore + cLen + cCopy
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (success :: endWord :: token :: y :: z :: value :: toWord :: tokenWord :: ρ :: R)
        M (G + charge + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 2 + 3)) safeTransfer_afterCall o by
    have gas : G + charge + 10 + 3 + 3 + 3 + 3 + 3 + 2 + 2 + 2 + 3 = G + 34 + charge := by omega
    rw [gas] at h
    exact h
  unfold safeTransfer_afterCall
  apply rx_swap2
  apply rx_pop
  apply rx_pop
  apply rx_returndatasize (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_eq rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x2143) rfl (by simp only [List.length_cons]; omega)
  by_cases empty : b.returnData.length.toB256 = 0
  · simp only [charge, len, empty, B256.eqCheck, ite_true] at continuation ⊢
    apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
    unfold t_2143_c57
    apply rx_dest
    apply rx_push (w := 96) rfl (by simp only [List.length_cons]; omega)
    apply rx_swap2
    apply rx_pop
    exact continuation
  · have flag : B256.eqCheck b.returnData.length.toB256 0 = 0 := ite_eq_right empty
    simp only [charge, len, empty, ite_false, flag]
    apply rx_branch_zero
    have gas : G + (64 + cRead + cStore + cLen + cCopy) =
      G + 64 + cRead + cStore + cLen + cCopy := by omega
    rw [gas]
    apply safeTransfer_allocate_exact room
    simpa only [empty, ite_false] using continuation


/-- The real CALL plus its successful helper continuation derives the entered flag,
full width and physical parent-memory image without forbidding child effects. -/
theorem safeTransfer_call_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b d : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {forwarded token ptr inputSize endWord y z value toWord tokenWord ρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (notAlloc : 16 ∉ C) (notGuard : 17 ∉ C)
    (callStep : P sevm
      (St b (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: endWord :: token ::
        y :: z :: value :: toWord :: tokenWord :: ρ :: R) M G) (.exec .call) d)
    (continuation : SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r) :
    d.stack = 1 :: endWord :: token :: y :: z :: value :: toWord :: tokenWord :: ρ :: R ∧
    d.memory = (M.extends [(ptr.toNat, inputSize.toNat), (ptr.toNat, 0)]).write
      ptr.toNat (d.returnData.take 0) ∧
    d.output = b.output ∧ d.returnData.length < 2^256 := by
  let rest := endWord :: token :: y :: z :: value :: toWord :: tokenWord :: ρ :: R
  have actual := project callStep
  have matched : AbstractStackSafety.Matches
      ((none :: none :: none :: none :: none :: none :: none :: rest.map some) : AbstractStackSafety.Pattern)
      (St b (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) M G).stack :=
    ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl,
      Or.inl rfl, matches_some_map rest⟩
  have transferred : AbstractStackSafety.Matches (none :: rest.map some) d.stack :=
    ninstTransfer_run fork matched rfl actual
  obtain ⟨flag, stack⟩ : ∃ flag, d.stack = flag :: rest := by
    cases eq : d.stack with
    | nil => rw [eq] at transferred; exact transferred.elim
    | cons flag tail =>
      rw [eq] at transferred
      refine ⟨flag, ?_⟩
      rw [matches_some_map_eq transferred.2]
  have image : d = St d (flag :: rest) d.memory d.gasLeft := St.self stack rfl
  have suffix : SFunc.RunCutP P cert.prog sevm C
      (St d (flag :: rest) d.memory d.gasLeft) safeTransfer_afterCall r := by
    rw [← image]
    exact continuation
  obtain ⟨_, decoded⟩ := safeTransfer_afterCall_inv project notAlloc suffix
  have nonzero := (safeTransfer_success_inv project notGuard decoded).1
  have operands : (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) <<+
      (St b (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) M G).stack := by
    simpa only [List.append_nil, St.stack] using
      (pref_append (forwarded :: token :: 0 :: ptr :: inputSize :: ptr :: 0 :: rest) [])
  rcases of_run_call_val_with_depth_frame operands actual fork with failed | entered
  · rw [stack] at failed
    have zero : flag = 0 := (pref_head_unique failed.1 (pref_append [flag] rest)).symm
    exact (nonzero zero).elim
  · obtain ⟨parent, child, xl, dp, na, code, avail, pc, step, depth, parentStack,
      parentState, parentMemory, parentLogs, parentOutput, delegation, filled, process,
      clean, resume, childState, returned, memory, resultStack⟩ := entered
    have tail : parent.stack = rest := by
      simp only [St.stack, List.cons.injEq] at parentStack
      exact parentStack.2.2.2.2.2.2.2.symm
    refine ⟨by rw [resultStack, tail], ?_, ?_, ReturnDataBound.call_returnData_length_lt actual fork⟩
    · rw [memory, parentMemory, returned]
      rfl
    · exact (Resume.call_output resume).trans parentOutput


/-- Exact four-byte merge and CALL preparation use the actual post-GAS word and four
selected memory charges; the primitive CALL continuation is internal to helper57. -/
private theorem safeTransfer_partialCall_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome} {src dst a x y z w token : B256}
    (room : R.length ≤ 1010) :
    let mask := B256.bexp 256 (32 - 4) - 1
    let M1 := (M.read src.toNat 32).2
    let M2 := (M1.read dst.toNat 32).2
    let M3 := M2.write dst.toNat
      (((Bytes.toB256 (M.read src.toNat 32).1) &&& ~~~mask) |||
        ((Bytes.toB256 (M1.read dst.toNat 32).1) &&& mask)).toBytes
    let q := Bytes.toB256 (M3.read 64 32).1
    let M4 := (M3.read 64 32).2
    let cSrc := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
    let cDst := gVerylow + (St b [] M1 0).extCost [⟨dst.toNat, 32⟩]
    let cStore := gVerylow + (St b [] M2 0).extCost [⟨dst.toNat, 32⟩]
    let cFree := gVerylow + (St b [] M3 0).extCost [⟨64, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b (G.toB256 :: token :: 0 :: q :: ((a + y) - q) :: q :: 0 ::
        (a + y) :: token :: R) M4 G) (.next (.exec .call) safeTransfer_afterCall) o →
    SFunc.RunExact cert.prog sevm
      (St b (src :: dst :: 4 :: a :: x :: y :: z :: w :: token :: R)
        M (G + 165 + cSrc + cDst + cStore + cFree)) t_20e1_c57 o := by
  dsimp only
  intro continuation
  let mask := B256.bexp 256 (32 - 4) - 1
  let M1 := (M.read src.toNat 32).2
  let M2 := (M1.read dst.toNat 32).2
  let M3 := M2.write dst.toNat
    (((Bytes.toB256 (M.read src.toNat 32).1) &&& ~~~mask) |||
      ((Bytes.toB256 (M1.read dst.toNat 32).1) &&& mask)).toBytes
  let cSrc := gVerylow + (St b [] M 0).extCost [⟨src.toNat, 32⟩]
  let cDst := gVerylow + (St b [] M1 0).extCost [⟨dst.toNat, 32⟩]
  let cStore := gVerylow + (St b [] M2 0).extCost [⟨dst.toNat, 32⟩]
  let cFree := gVerylow + (St b [] M3 0).extCost [⟨64, 32⟩]
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (src :: dst :: 4 :: a :: x :: y :: z :: w :: token :: R)
        M (G + 2 + 3 + 3 + 3 + 3 + 3 + 3 + cFree + 3 + 3 + 2 + 2 + 3 + 3 + 2 + 3 + 2 + 2 + 2 + 2 + 2 + 2 + cStore + 3 + 3 + 3 + 3 + 3 + cDst + 3 + 3 + 3 + cSrc + 3 + 3 + 3 + 3 + 60 + 3 + 3 + 3 + 3 + 3 + 1)) t_20e1_c57 o by
    have gas : G + 2 + 3 + 3 + 3 + 3 + 3 + 3 + cFree + 3 + 3 + 2 + 2 + 3 + 3 + 2 + 3 + 2 + 2 + 2 + 2 + 2 + 2 + cStore + 3 + 3 + 3 + 3 + 3 + cDst + 3 + 3 + 3 + cSrc + 3 + 3 + 3 + 3 + 60 + 3 + 3 + 3 + 3 + 3 + 1 =
      G + 165 + cSrc + cDst + cStore + cFree := by omega
    rw [gas] at h
    exact h
  unfold t_20e1_c57
  apply rx_dest
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_push (w := 256) rfl (by simp only [List.length_cons]; omega)
  apply rx_exp' (c := 60) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_not rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (i := src) (v := Bytes.toB256 (M.read src.toNat 32).1) (c := cSrc) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (i := dst) (v := Bytes.toB256 (M1.read dst.toNat 32).1) (c := cDst) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_or rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (i := dst) (c := cStore) rfl rfl
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_swap1
  apply rx_pop
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_pop
  apply rx_pop
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (i := 64) (v := Bytes.toB256 (M3.read 64 32).1) (c := cFree) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_gas (by simp only [List.length_cons]; omega)
  exact continuation

/-- Literal initializer preserves every selected read and ordered write before the unaligned copy. -/
private theorem safeTransfer_initialize_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
    let M1 := (M.read (64 : B256).toNat 32).2
    let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
    let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
    let M4 := M3.write ((32 + p1) : B256).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
    let M5 := (M4.read (64 : B256).toNat 32).2
    let M6 := M5.write ((p2 + 36) : B256).toNat ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
    let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
    let M8 := (M7.read (64 : B256).toNat 32).2
    let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
    let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
    let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
    let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
    let M12 := M11.write ((p3 + 32) : B256).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 ||| (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
    let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
    let M13 := (M12.read (64 : B256).toNat 32).2
    let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
    let M14 := (M13.read (p3 : B256).toNat 32).2
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b ((p3 + 32) :: p5 :: p6 :: p6 :: (p3 + 32) :: p5 :: p5 :: p3 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) M14 residual) t_20a4_c57 r := by
  have h := run
  unfold t_1fdb_c57 at h
  obtain ⟨_, h⟩ := ric_destP h
  change SFunc.RunCutP P cert.prog sevm C _
    (pairTransferInitializeLine.foldr SFunc.next t_20a4_c57) r at h
  obtain ⟨middle, line, tail⟩ := h.split_nexts (fun step => project step) pairTransferInitializeLine
  obtain ⟨residual, equal⟩ := pair_transfer_initialize_line_inv line
  rw [equal] at tail
  exact ⟨residual, tail⟩

/-- Exact initializer constructs the actual selected payload stages and all fourteen memory charges. -/
private theorem safeTransfer_initialize_exact {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {o : Outcome} {amount toWord tokenWord rho : B256}
    (room : R.length ≤ 1008) :
    let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
    let M1 := (M.read (64 : B256).toNat 32).2
    let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
    let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
    let M4 := M3.write ((32 + p1) : B256).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
    let M5 := (M4.read (64 : B256).toNat 32).2
    let M6 := M5.write ((p2 + 36) : B256).toNat ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
    let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
    let M8 := (M7.read (64 : B256).toNat 32).2
    let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
    let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
    let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
    let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
    let M12 := M11.write ((p3 + 32) : B256).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 ||| (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
    let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
    let M13 := (M12.read (64 : B256).toNat 32).2
    let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
    let M14 := (M13.read (p3 : B256).toNat 32).2
    let c1 := gVerylow + (St b [] M 0).extCost [⟨(64 : B256).toNat, 32⟩]
    let c2 := gVerylow + (St b [] M1 0).extCost [⟨(64 : B256).toNat, 32⟩]
    let c3 := gVerylow + (St b [] M2 0).extCost [⟨(p1 : B256).toNat, 32⟩]
    let c4 := gVerylow + (St b [] M3 0).extCost [⟨((32 + p1) : B256).toNat, 32⟩]
    let c5 := gVerylow + (St b [] M4 0).extCost [⟨(64 : B256).toNat, 32⟩]
    let c6 := gVerylow + (St b [] M5 0).extCost [⟨((p2 + 36) : B256).toNat, 32⟩]
    let c7 := gVerylow + (St b [] M6 0).extCost [⟨((p2 + 68) : B256).toNat, 32⟩]
    let c8 := gVerylow + (St b [] M7 0).extCost [⟨(64 : B256).toNat, 32⟩]
    let c9 := gVerylow + (St b [] M8 0).extCost [⟨(p3 : B256).toNat, 32⟩]
    let c10 := gVerylow + (St b [] M9 0).extCost [⟨(64 : B256).toNat, 32⟩]
    let c11 := gVerylow + (St b [] M10 0).extCost [⟨((p3 + 32) : B256).toNat, 32⟩]
    let c12 := gVerylow + (St b [] M11 0).extCost [⟨((p3 + 32) : B256).toNat, 32⟩]
    let c13 := gVerylow + (St b [] M12 0).extCost [⟨(64 : B256).toNat, 32⟩]
    let c14 := gVerylow + (St b [] M13 0).extCost [⟨(p3 : B256).toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b ((p3 + 32) :: p5 :: p6 :: p6 :: (p3 + 32) :: p5 :: p5 :: p3 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) M14 G) t_20a4_c57 o →
    SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M (G + 199 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14)) t_1fdb_c57 o := by
  dsimp only
  intro continuation
  let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
  let M1 := (M.read (64 : B256).toNat 32).2
  let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
  let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
  let M4 := M3.write ((32 + p1) : B256).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
  let M5 := (M4.read (64 : B256).toNat 32).2
  let M6 := M5.write ((p2 + 36) : B256).toNat ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
  let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
  let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
  let M8 := (M7.read (64 : B256).toNat 32).2
  let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
  let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
  let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
  let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
  let M12 := M11.write ((p3 + 32) : B256).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 ||| (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
  let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
  let M13 := (M12.read (64 : B256).toNat 32).2
  let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
  let M14 := (M13.read (p3 : B256).toNat 32).2
  let c1 := gVerylow + (St b [] M 0).extCost [⟨(64 : B256).toNat, 32⟩]
  let c2 := gVerylow + (St b [] M1 0).extCost [⟨(64 : B256).toNat, 32⟩]
  let c3 := gVerylow + (St b [] M2 0).extCost [⟨(p1 : B256).toNat, 32⟩]
  let c4 := gVerylow + (St b [] M3 0).extCost [⟨((32 + p1) : B256).toNat, 32⟩]
  let c5 := gVerylow + (St b [] M4 0).extCost [⟨(64 : B256).toNat, 32⟩]
  let c6 := gVerylow + (St b [] M5 0).extCost [⟨((p2 + 36) : B256).toNat, 32⟩]
  let c7 := gVerylow + (St b [] M6 0).extCost [⟨((p2 + 68) : B256).toNat, 32⟩]
  let c8 := gVerylow + (St b [] M7 0).extCost [⟨(64 : B256).toNat, 32⟩]
  let c9 := gVerylow + (St b [] M8 0).extCost [⟨(p3 : B256).toNat, 32⟩]
  let c10 := gVerylow + (St b [] M9 0).extCost [⟨(64 : B256).toNat, 32⟩]
  let c11 := gVerylow + (St b [] M10 0).extCost [⟨((p3 + 32) : B256).toNat, 32⟩]
  let c12 := gVerylow + (St b [] M11 0).extCost [⟨((p3 + 32) : B256).toNat, 32⟩]
  let c13 := gVerylow + (St b [] M12 0).extCost [⟨(64 : B256).toNat, 32⟩]
  let c14 := gVerylow + (St b [] M13 0).extCost [⟨(p3 : B256).toNat, 32⟩]
  change SFunc.RunExact cert.prog sevm
    (St b ((p3 + 32) :: p5 :: p6 :: p6 :: (p3 + 32) :: p5 :: p5 :: p3 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) M14 G) t_20a4_c57 o at continuation
  suffices h : SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M (G + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + c14 + 3 + c13 + 3 + c12 + 3 + 3 + 3 + 3 + 3 + c11 + 3 + 3 + 3 + 3 + c10 + 3 + 3 + 3 + 3 + 3 + c9 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + c8 + 3 + c7 + 3 + 3 + 3 + 3 + 3 + 3 + c6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + c5 + 3 + c4 + 3 + 3 + 3 + 3 + 3 + c3 + 3 + 3 + c2 + 3 + 3 + 3 + 3 + c1 + 3 + 3 + 1)) t_1fdb_c57 o by
    have gas : G + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + c14 + 3 + c13 + 3 + c12 + 3 + 3 + 3 + 3 + 3 + c11 + 3 + 3 + 3 + 3 + c10 + 3 + 3 + 3 + 3 + 3 + c9 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + c8 + 3 + c7 + 3 + 3 + 3 + 3 + 3 + 3 + c6 + 3 + 3 + 3 + 3 + 3 + 3 + 3 + c5 + 3 + c4 + 3 + 3 + 3 + 3 + 3 + c3 + 3 + 3 + c2 + 3 + 3 + 3 + 3 + c1 + 3 + 3 + 1 =
      G + 199 + c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + c12 + c13 + c14 := by omega
    rw [gas] at h
    exact h
  unfold t_1fdb_c57
  apply rx_dest
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (c := c1) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (c := c2) rfl rfl
  apply rx_push (w := 25) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (c := c3) rfl rfl
  apply rx_push (w := 0x7472616e7366657228616464726573732c75696e743235362900000000000000) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (c := c4) rfl rfl
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (c := c5) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0xffffffffffffffffffffffffffffffffffffffff) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 36) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (c := c6) rfl rfl
  apply rx_push (w := 68) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_mstore (c := c7) rfl rfl
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (c := c8) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_sub (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap2
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (c := c9) rfl rfl
  apply rx_push (w := 100) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap3
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (c := c10) rfl rfl
  apply rx_swap2
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add' rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (c := c11) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0xa9059cbb00000000000000000000000000000000000000000000000000000000) rfl (by simp only [List.length_cons]; omega)
  apply rx_or rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mstore (c := c12) rfl rfl
  apply rx_swap3
  apply rx_mload_ext (c := c13) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_mload_ext (c := c14) rfl rfl rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (S' := ((p3 + 32) :: p6 :: p5 :: p3 :: 0xffffffffffffffffffffffffffffffffffffffff :: 0 :: amount :: toWord :: tokenWord :: rho :: R)) rfl
  apply rx_push (w := 96) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap (S' := (0xffffffffffffffffffffffffffffffffffffffff :: (p3 + 32) :: p6 :: p5 :: p3 :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)) rfl
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_swap4
  apply rx_swap3
  apply rx_swap2
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_swap1
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  exact continuation

/-- Actual first-transfer payload memory; no concrete memory image is evaluated. -/
def safeTransfer_payload128Memory (M : Mem) (amount toWord : B256) : Mem :=
  let N1 := M.write 64 (192 : B256).toBytes
  let N2 := N1.write 128 (25 : B256).toBytes
  let N3 := N2.write 160 (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write 228 ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
  let N5 := N4.write 260 amount.toBytes
  let N6 := N5.write 192 (68 : B256).toBytes
  let N7 := N6.write 64 (292 : B256).toBytes
  let N8 := N7.write 224 ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) ||| ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read 224 32).1)).toBytes
  N8

/-- The actual first burn transfer enters with pointer128/allocated192; later pointers stay general. -/
private theorem safeTransfer_initialize128_image {M : Mem} {amount toWord : B256}
    (mem : PtrMem 128 192 M) :
    let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
    let M1 := (M.read (64 : B256).toNat 32).2
    let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
    let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
    let M4 := M3.write ((32 + p1) : B256).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
    let M5 := (M4.read (64 : B256).toNat 32).2
    let M6 := M5.write ((p2 + 36) : B256).toNat ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
    let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
    let M8 := (M7.read (64 : B256).toNat 32).2
    let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
    let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
    let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
    let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
    let M12 := M11.write ((p3 + 32) : B256).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 ||| (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
    let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
    let M13 := (M12.read (64 : B256).toNat 32).2
    let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
    let M14 := (M13.read (p3 : B256).toNat 32).2
    p1 = 128 ∧ p2 = 192 ∧ p3 = 192 ∧ p5 = 292 ∧ p6 = 68 ∧
      M14 = safeTransfer_payload128Memory M amount toWord ∧
      PtrMem 292 320 (safeTransfer_payload128Memory M amount toWord) := by
  let N1 := M.write 64 (192 : B256).toBytes
  let N2 := N1.write 128 (25 : B256).toBytes
  let N3 := N2.write 160 (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write 228 ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
  let N5 := N4.write 260 amount.toBytes
  let N6 := N5.write 192 (68 : B256).toBytes
  let N7 := N6.write 64 (292 : B256).toBytes
  let N8 := N7.write 224 ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) ||| ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read 224 32).1)).toBytes
  have h1 : PtrMem 192 192 N1 := mem.set
  have h2 : PtrMem 192 192 N2 := h1.write 128 25 (Or.inr (by decide))
  have h3 : PtrMem 192 192 N3 := h2.write 160 _ (Or.inr (by decide))
  have h4 : PtrMem 192 288 N4 := h3.write 228 _ (Or.inr (by decide))
  have h5 : PtrMem 192 320 N5 := h4.write 260 amount (Or.inr (by decide))
  have h6 : PtrMem 192 320 N6 := h5.write 192 68 (Or.inr (by decide))
  have h7 : PtrMem 292 320 N7 := h6.set
  have h8 : PtrMem 292 320 N8 := h7.write 224 _ (Or.inr (by decide))
  have length6 := Mem.memWord_write_word N5 192 (68 : B256)
  have length7 : memWord N7 192 = 68 := by
    rw [memWord_congr (μ := N6) (fun k hk =>
      (Mem.write_agree N6 64 (292 : B256).toBytes).2 (192 + k)
        (by rw [h6.size]; omega) (by right; rw [B256.length_toBytes]; omega))]
    exact length6.1
  have length8 : memWord N8 192 = 68 := by
    rw [memWord_congr (μ := N7) (fun k hk =>
      (Mem.write_agree N7 224 _).2 (192 + k)
        (by rw [h7.size]; omega) (by left; omega))]
    exact length7
  have read0 : Bytes.toB256 (M.read 64 32).1 = 128 := mem.word
  have read3 : Bytes.toB256 (N3.read 64 32).1 = 192 := h3.word
  have read5 : Bytes.toB256 (N5.read 64 32).1 = 192 := h5.word
  have read8 : Bytes.toB256 (N8.read 64 32).1 = 292 := h8.word
  dsimp only
  simp only [show (64 : B256).toNat = 64 from rfl]
  rw [read0, mem.read_self (by decide),
    show (64 : B256) + 128 = 192 from rfl,
    show (32 : B256) + 128 = 160 from rfl]
  change 128 = 128 ∧
    let p2 := Bytes.toB256 (N3.read 64 32).1
    let M5 := (N3.read 64 32).2
    let M6 := M5.write (p2 + 36).toNat ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
    let M7 := M6.write (p2 + 68).toNat amount.toBytes
    let p3 := Bytes.toB256 (M7.read 64 32).1
    let M8 := (M7.read 64 32).2
    let M9 := M8.write p3.toNat (68 + (p2 - p3)).toBytes
    let M10 := M9.write 64 (p2 + 100).toBytes
    let p4 := Bytes.toB256 (M10.read (p3 + 32).toNat 32).1
    let M11 := (M10.read (p3 + 32).toNat 32).2
    let M12 := M11.write (p3 + 32).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) ||| ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& p4)).toBytes
    let p5 := Bytes.toB256 (M12.read 64 32).1
    let M13 := (M12.read 64 32).2
    let p6 := Bytes.toB256 (M13.read p3.toNat 32).1
    let M14 := (M13.read p3.toNat 32).2
    p2 = 192 ∧ p3 = 192 ∧ p5 = 292 ∧ p6 = 68 ∧ M14 = N8 ∧ PtrMem 292 320 N8
  dsimp only
  rw [read3, h3.read_self (by decide),
    show (192 : B256) + 36 = 228 from rfl,
    show (192 : B256) + 68 = 260 from rfl]
  change 128 = 128 ∧ 192 = 192 ∧
    let p3 := Bytes.toB256 (N5.read 64 32).1
    let M8 := (N5.read 64 32).2
    let M9 := M8.write p3.toNat (68 + ((192 : B256) - p3)).toBytes
    let M10 := M9.write 64 (292 : B256).toBytes
    let p4 := Bytes.toB256 (M10.read (p3 + 32).toNat 32).1
    let M11 := (M10.read (p3 + 32).toNat 32).2
    let M12 := M11.write (p3 + 32).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) ||| ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& p4)).toBytes
    let p5 := Bytes.toB256 (M12.read 64 32).1
    let M13 := (M12.read 64 32).2
    let p6 := Bytes.toB256 (M13.read p3.toNat 32).1
    let M14 := (M13.read p3.toNat 32).2
    p3 = 192 ∧ p5 = 292 ∧ p6 = 68 ∧ M14 = N8 ∧ PtrMem 292 320 N8
  dsimp only
  rw [read5, h5.read_self (by decide),
    show (68 : B256) + (192 - 192) = 68 from rfl,
    show (192 : B256) + 32 = 224 from rfl]
  change 128 = 128 ∧ 192 = 192 ∧ 192 = 192 ∧
    let M12 := (N7.read 224 32).2.write 224 ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) ||| ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read 224 32).1)).toBytes
    let p5 := Bytes.toB256 (M12.read 64 32).1
    let M13 := (M12.read 64 32).2
    let p6 := Bytes.toB256 (M13.read 192 32).1
    let M14 := (M13.read 192 32).2
    p5 = 292 ∧ p6 = 68 ∧ M14 = N8 ∧ PtrMem 292 320 N8
  dsimp only
  rw [h7.read_self (by decide)]
  change 128 = 128 ∧ 192 = 192 ∧ 192 = 192 ∧
    Bytes.toB256 (N8.read 64 32).1 = 292 ∧
    Bytes.toB256 ((N8.read 64 32).2.read 192 32).1 = 68 ∧
    ((N8.read 64 32).2.read 192 32).2 = N8 ∧ PtrMem 292 320 N8
  change Bytes.toB256 (N8.read 192 32).1 = 68 at length8
  rw [read8, h8.read_self (by decide), length8, h8.read_self (by decide)]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, h8⟩

/-- First-burn initializer normalization consumes the single arbitrary-pointer inverse. -/
private theorem safeTransfer_initialize128_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b (224 :: 292 :: 68 :: 68 :: 224 :: 292 :: 292 :: 192 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_payload128Memory M amount toWord) residual) t_20a4_c57 r := by
  let p1 := Bytes.toB256 (M.read (64 : B256).toNat 32).1
  let M1 := (M.read (64 : B256).toNat 32).2
  let M2 := M1.write (64 : B256).toNat ((64 + p1) : B256).toBytes
  let M3 := M2.write (p1 : B256).toNat (25 : B256).toBytes
  let M4 := M3.write ((32 + p1) : B256).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let p2 := Bytes.toB256 (M4.read (64 : B256).toNat 32).1
  let M5 := (M4.read (64 : B256).toNat 32).2
  let M6 := M5.write ((p2 + 36) : B256).toNat ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
  let M7 := M6.write ((p2 + 68) : B256).toNat (amount : B256).toBytes
  let p3 := Bytes.toB256 (M7.read (64 : B256).toNat 32).1
  let M8 := (M7.read (64 : B256).toNat 32).2
  let M9 := M8.write (p3 : B256).toNat ((68 + (p2 - p3)) : B256).toBytes
  let M10 := M9.write (64 : B256).toNat ((p2 + 100) : B256).toBytes
  let p4 := Bytes.toB256 (M10.read ((p3 + 32) : B256).toNat 32).1
  let M11 := (M10.read ((p3 + 32) : B256).toNat 32).2
  let M12 := M11.write ((p3 + 32) : B256).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 ||| (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff &&& p4)) : B256).toBytes
  let p5 := Bytes.toB256 (M12.read (64 : B256).toNat 32).1
  let M13 := (M12.read (64 : B256).toNat 32).2
  let p6 := Bytes.toB256 (M13.read (p3 : B256).toNat 32).1
  let M14 := (M13.read (p3 : B256).toNat 32).2
  have h := safeTransfer_initialize_inv project run
  have image := safeTransfer_initialize128_image (amount := amount) (toWord := toWord) mem
  change ∃ residual, SFunc.RunCutP P cert.prog sevm C
    (St b ((p3 + 32) :: p5 :: p6 :: p6 :: (p3 + 32) :: p5 :: p5 :: p3 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) M14 residual) t_20a4_c57 r at h
  change p1 = 128 ∧ p2 = 192 ∧ p3 = 192 ∧ p5 = 292 ∧ p6 = 68 ∧
    M14 = safeTransfer_payload128Memory M amount toWord ∧
    PtrMem 292 320 (safeTransfer_payload128Memory M amount toWord) at image
  obtain ⟨_, _, eq3, eq5, eq6, eqM, _⟩ := image
  rw [eq3, eq5, eq6, eqM] at h
  exact h

/-- Actual first transfer's ordered two-word and four-byte payload copy. -/
def safeTransfer_call128Memory (M : Mem) (amount toWord : B256) : Mem :=
  let N0 := safeTransfer_payload128Memory M amount toWord
  let N1 := N0.write 292 (Bytes.toB256 (N0.read 224 32).1).toBytes
  let N2 := N1.write 324 (Bytes.toB256 (N1.read 256 32).1).toBytes
  let mask := B256.bexp 256 (32 - 4) - 1
  (N2.read 356 32).2.write 356
    (((Bytes.toB256 (N2.read 288 32).1) &&& ~~~mask) |||
      ((Bytes.toB256 (N2.read 356 32).1) &&& mask)).toBytes

/-- First actual helper57 composes initializer/copy/merge and derives all seven CALL operands.
The child world and full reply remain opaque. -/
private theorem safeTransfer_firstCall_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (mem : PtrMem 128 192 M) (notCopyCut : 71 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    ∃ forwarded callGas d,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_call128Memory M amount toWord) callGas) (.exec .call) d ∧
      SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r ∧
      PtrMem 292 416 (safeTransfer_call128Memory M amount toWord) := by
  let N0 := safeTransfer_payload128Memory M amount toWord
  let N1 := N0.write 292 (Bytes.toB256 (N0.read 224 32).1).toBytes
  let N2 := N1.write 324 (Bytes.toB256 (N1.read 256 32).1).toBytes
  let mask := B256.bexp 256 (32 - 4) - 1
  let N3 := (N2.read 356 32).2.write 356
    (((Bytes.toB256 (N2.read 288 32).1) &&& ~~~mask) |||
      ((Bytes.toB256 (N2.read 356 32).1) &&& mask)).toBytes
  have h0 : PtrMem 292 320 N0 := (safeTransfer_initialize128_image mem).2.2.2.2.2.2
  have h1 : PtrMem 292 352 N1 := h0.write 292 _ (Or.inr (by decide))
  have h2 : PtrMem 292 384 N2 := h1.write 324 _ (Or.inr (by decide))
  have hDest : PtrMem 292 416 (N2.read 356 32).2 := by
    refine ⟨?_, by decide, h2.wf.extend 356 32, ?_⟩
    · change memExtSize N2.size 356 32 = 416
      rw [h2.size]
      rfl
    · generalize N2 = V at h2 ⊢
      exact MemMatches.of_data_eq (μ := V) (μ' := (V.read 356 32).2) rfl
        (memExtSize_ge V.size 356 32) h2.map
  have h3 : PtrMem 292 416 N3 := hDest.write 356 _ (Or.inr (by decide))
  obtain ⟨gInit, initialized⟩ := safeTransfer_initialize128_inv project mem run
  obtain ⟨gCopy, copied⟩ := safeTransfer_copy68_inv project notCopyCut initialized
  rw [show ((safeTransfer_payload128Memory M amount toWord).read (224 : B256).toNat 32).2 = N0 from h0.read_self (by decide)] at copied
  change SFunc.RunCutP P cert.prog sevm C
    (St b (288 :: 356 :: 4 :: 68 :: 224 :: 292 :: 292 :: 192 ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
      ((N1.read 256 32).2.write 324 (Bytes.toB256 (N1.read 256 32).1).toBytes) gCopy)
    t_20e1_c57 r at copied
  rw [h1.read_self (by decide)] at copied
  change SFunc.RunCutP P cert.prog sevm C
    (St b (288 :: 356 :: 4 :: 68 :: 224 :: 292 :: 292 :: 192 ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) N2 gCopy)
    t_20e1_c57 r at copied
  have call := safeTransfer_partialCall_inv project copied
  dsimp only at call
  simp only [show (288 : B256).toNat = 288 from rfl,
    show (356 : B256).toNat = 356 from rfl] at call
  rw [h2.read_self (by decide : 288 + 32 ≤ 384)] at call
  change ∃ forwarded callGas d,
    P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: Bytes.toB256 (N3.read 64 32).1 ::
      ((68 + 292) - Bytes.toB256 (N3.read 64 32).1) ::
      Bytes.toB256 (N3.read 64 32).1 :: 0 :: 360 ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
      (N3.read 64 32).2 callGas) (.exec .call) d ∧
    SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r at call
  rw [show Bytes.toB256 (N3.read 64 32).1 = 292 from h3.word,
    h3.read_self (by decide)] at call
  obtain ⟨forwarded, callGas, d, step, tail⟩ := call
  exact ⟨forwarded, callGas, d, step, tail, h3⟩

/-- The first actual helper call derives successful settlement while preserving opaque child effects. -/
private theorem safeTransfer_firstCall_post_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (notCopyCut : 71 ∉ C) (notAlloc : 16 ∉ C) (notGuard : 17 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    ∃ forwarded callGas d,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_call128Memory M amount toWord) callGas) (.exec .call) d ∧
      SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r ∧
      d.stack = 1 :: 360 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
      d.memory = safeTransfer_call128Memory M amount toWord ∧
      d.output = b.output ∧ d.returnData.length < 2^256 ∧ PtrMem 292 416 d.memory := by
  obtain ⟨forwarded, callGas, d, step, tail, preMem⟩ :=
    safeTransfer_firstCall_inv project mem notCopyCut run
  have settled := safeTransfer_call_inv project fork notAlloc notGuard step tail
  have extension : (safeTransfer_call128Memory M amount toWord).extends
      [(292, 68), (292, 0)] = safeTransfer_call128Memory M amount toWord := by
    generalize safeTransfer_call128Memory M amount toWord = V at preMem ⊢
    change (⟨V.data, memExtsSize V.size [(292, 68), (292, 0)]⟩ : Mem) = V
    have size : memExtsSize V.size [(292, 68), (292, 0)] = V.size := by
      rw [preMem.size]
      rfl
    rw [size]
  have memory : d.memory = safeTransfer_call128Memory M amount toWord := by
    rw [settled.2.1]
    change (safeTransfer_call128Memory M amount toWord).extends [(292, 68), (292, 0)] =
      safeTransfer_call128Memory M amount toWord
    exact extension
  refine ⟨forwarded, callGas, d, step, tail, settled.1, memory,
    settled.2.2.1, settled.2.2.2, ?_⟩
  rw [memory]
  exact preMem

/-- Actual nonempty first-reply allocation keeps the modular free-pointer expression. -/
def safeTransfer_reply292Memory (M : Mem) (reply : Bytes) : Mem :=
  let len := reply.length.toB256
  ((M.write 64 (292 + ((len + 63) &&& ~~~31)).toBytes).write 292 len.toBytes).write 324 reply

/-- The first transfer leaves this literal free-pointer word for the second helper. -/
def burnFirstTransferPointer (reply : Bytes) : B256 :=
  if reply = [] then 292 else 292 + ((reply.length.toB256 + 63) &&& ~~~31)

/-- The producer's reply bound makes the actual modular allocation a natural
allocation, with room for every fixed offset of the second transfer. -/
theorem burnFirstTransferPointer_layout {reply : Bytes}
    (width : reply.length < 2 ^ 160) :
    (burnFirstTransferPointer reply).toNat =
      (if reply = [] then 292 else 292 + 32 * ((reply.length + 63) / 32)) ∧
    292 ≤ (burnFirstTransferPointer reply).toNat ∧
    (reply ≠ [] → 324 + reply.length ≤ (burnFirstTransferPointer reply).toNat) ∧
    (burnFirstTransferPointer reply).toNat + 260 < 2 ^ 256 := by
  have margin : 2 ^ 160 + 615 < (2 ^ 256 : Nat) := by decide
  have lenWidth : reply.length < 2 ^ 256 := by omega
  have sumWidth : reply.length + 63 < 2 ^ 256 := by omega
  have sumNat : (reply.length.toB256 + (63 : B256)).toNat = reply.length + 63 := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt lenWidth,
      show (63 : B256).toNat = 63 from rfl, Nat.lo_eq_of_lt sumWidth]
  have maskNat : ((reply.length.toB256 + (63 : B256)) &&& ~~~31).toNat =
      32 * ((reply.length + 63) / 32) := by
    rw [B256.toNat_and, sumNat,
      show (~~~ (31 : B256)).toNat = 2 ^ 256 - 32 from rfl,
      Nat.and_mask32 sumWidth]
  have division := Nat.mod_add_div (reply.length + 63) 32
  have remainder : (reply.length + 63) % 32 < 32 := Nat.mod_lt _ (by decide)
  have roundedWidth : 292 + 32 * ((reply.length + 63) / 32) < 2 ^ 256 := by omega
  have pointerNat : (292 + ((reply.length.toB256 + (63 : B256)) &&& ~~~31)).toNat =
      292 + 32 * ((reply.length + 63) / 32) := by
    rw [B256.toNat_add, show (292 : B256).toNat = 292 from rfl,
      maskNat, Nat.lo_eq_of_lt roundedWidth]
  by_cases empty : reply = []
  · simp only [burnFirstTransferPointer, empty, ite_true,
      show (292 : B256).toNat = 292 from rfl]
    exact ⟨True.intro, by omega, fun nonempty => False.elim (nonempty rfl), by decide⟩
  · simp only [burnFirstTransferPointer, ite_eq_right empty, pointerNat]
    exact ⟨True.intro, by omega, fun _ => by omega, by omega⟩

/-- The second transfer starts its reply array after its own 164-byte staging
area and advances only for its independently observed nonempty reply. -/
def burnSecondTransferPointer (firstReply secondReply : Bytes) : B256 :=
  let start := burnFirstTransferPointer firstReply + 164
  if secondReply = [] then start else start + ((secondReply.length.toB256 + 63) &&& ~~~31)

/-- Both independent reply allocations and the following fixed ABI area fit
without word wrap; a nonempty second reply ends below the actual new pointer. -/
theorem burnSecondTransferPointer_layout {firstReply secondReply : Bytes}
    (firstWidth : firstReply.length < 2 ^ 160)
    (secondWidth : secondReply.length < 2 ^ 160) :
    (burnSecondTransferPointer firstReply secondReply).toNat =
      (burnFirstTransferPointer firstReply).toNat + 164 +
        (if secondReply = [] then 0 else 32 * ((secondReply.length + 63) / 32)) ∧
    (burnFirstTransferPointer firstReply).toNat + 164 ≤
      (burnSecondTransferPointer firstReply secondReply).toNat ∧
    (secondReply ≠ [] →
      (burnFirstTransferPointer firstReply).toNat + 196 + secondReply.length ≤
        (burnSecondTransferPointer firstReply secondReply).toNat) ∧
    (burnSecondTransferPointer firstReply secondReply).toNat + 64 < 2 ^ 256 := by
  have firstLayout := burnFirstTransferPointer_layout firstWidth
  have firstDivision := Nat.mod_add_div (firstReply.length + 63) 32
  have firstBound : (burnFirstTransferPointer firstReply).toNat ≤ firstReply.length + 355 := by
    rw [firstLayout.1]
    split <;> omega
  have margin : 2 * 2 ^ 160 + 646 < (2 ^ 256 : Nat) := by decide
  have startWidth : (burnFirstTransferPointer firstReply).toNat + 164 < 2 ^ 256 := by omega
  have startNat : (burnFirstTransferPointer firstReply + 164).toNat =
      (burnFirstTransferPointer firstReply).toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl,
      Nat.lo_eq_of_lt startWidth]
  have lenWidth : secondReply.length < 2 ^ 256 := by omega
  have sumWidth : secondReply.length + 63 < 2 ^ 256 := by omega
  have sumNat : (secondReply.length.toB256 + (63 : B256)).toNat = secondReply.length + 63 := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt lenWidth,
      show (63 : B256).toNat = 63 from rfl, Nat.lo_eq_of_lt sumWidth]
  have maskNat : ((secondReply.length.toB256 + (63 : B256)) &&& ~~~31).toNat =
      32 * ((secondReply.length + 63) / 32) := by
    rw [B256.toNat_and, sumNat,
      show (~~~ (31 : B256)).toNat = 2 ^ 256 - 32 from rfl,
      Nat.and_mask32 sumWidth]
  have division := Nat.mod_add_div (secondReply.length + 63) 32
  have remainder : (secondReply.length + 63) % 32 < 32 := Nat.mod_lt _ (by decide)
  have roundedWidth : (burnFirstTransferPointer firstReply).toNat + 164 +
      32 * ((secondReply.length + 63) / 32) < 2 ^ 256 := by omega
  have pointerNat :
      (burnFirstTransferPointer firstReply + 164 +
        ((secondReply.length.toB256 + 63) &&& ~~~31)).toNat =
      (burnFirstTransferPointer firstReply).toNat + 164 +
        32 * ((secondReply.length + 63) / 32) := by
    rw [B256.toNat_add, startNat, maskNat, Nat.lo_eq_of_lt roundedWidth]
  by_cases empty : secondReply = []
  · simp only [burnSecondTransferPointer, empty, ite_true, startNat, Nat.add_zero]
    exact ⟨True.intro, by omega, fun nonempty => False.elim (nonempty rfl), by omega⟩
  · simp only [burnSecondTransferPointer, ite_eq_right empty, pointerNat]
    exact ⟨True.intro, by omega, fun _ => by omega, by omega⟩

/-- The first reply's physical bytes and word image use full arbitrary returndata. -/
private theorem safeTransfer_reply292_image {M : Mem} {reply : Bytes}
    (mem : PtrMem 292 416 M) :
    let len := reply.length.toB256
    let allocated := safeTransfer_reply292Memory M reply
    PtrMem (292 + ((len + 63) &&& ~~~31)) (memExtSize 416 324 reply.length) allocated ∧
      memWord allocated 292 = len ∧
      (32 ≤ reply.length → (allocated.read 324 32).1 = reply.sliceD 0 32 0) := by
  exact Blanc.Lift.bytesArrayMemory_image mem (by decide) (by decide) (by decide)

/-- The first helper's actual returned memory supplies the second helper's
pointer carrier, untouched empty-array sentinel, and allocation separation. -/
theorem burnFirstTransfer_memoryLayout {M : Mem} {reply : Bytes}
    (mem : PtrMem 292 416 M) (sentinel : memWord M 96 = 0)
    (width : reply.length < 2 ^ 160) :
    let post := if reply = [] then M else safeTransfer_reply292Memory M reply
    PtrMem (burnFirstTransferPointer reply)
      (if reply = [] then 416 else memExtSize 416 324 reply.length) post ∧
    memWord post 96 = 0 ∧
    292 ≤ (burnFirstTransferPointer reply).toNat ∧
    (reply ≠ [] → 324 + reply.length ≤ (burnFirstTransferPointer reply).toNat) ∧
    (burnFirstTransferPointer reply).toNat + 260 < 2 ^ 256 := by
  have layout := burnFirstTransferPointer_layout width
  by_cases empty : reply = []
  · simp only [empty, ite_true, burnFirstTransferPointer]
    exact ⟨mem, sentinel, by decide,
      fun nonempty => False.elim (nonempty rfl), by decide⟩
  · simp only [ite_eq_right empty, burnFirstTransferPointer]
    let len := reply.length.toB256
    let q := 292 + ((len + 63) &&& ~~~31)
    let N1 := M.write 64 q.toBytes
    let N2 := N1.write 292 len.toBytes
    have h1 : PtrMem q 416 N1 := mem.set
    have h2 : PtrMem q 416 N2 := h1.write 292 len (Or.inr (by decide))
    have sentinel1 : memWord N1 96 = 0 := by
      rw [memWord_congr (μ := M) (fun k hk =>
        (Mem.write_agree M 64 q.toBytes).2 (96 + k)
          (by rw [mem.size]; omega)
          (by rw [B256.length_toBytes]; right; omega))]
      exact sentinel
    have sentinel2 : memWord N2 96 = 0 := by
      rw [memWord_congr (μ := N1) (fun k hk =>
        (Mem.write_agree N1 292 len.toBytes).2 (96 + k)
          (by rw [h1.size]; omega) (by left; omega))]
      exact sentinel1
    have sentinel3 : memWord (safeTransfer_reply292Memory M reply) 96 = 0 := by
      change memWord (N2.write 324 reply) 96 = 0
      rw [memWord_congr (μ := N2) (fun k hk =>
        (Mem.write_agree N2 324 reply).2 (96 + k)
          (by rw [h2.size]; omega) (by left; omega))]
      exact sentinel2
    have carrier := (safeTransfer_reply292_image mem (reply := reply)).1
    simp only [burnFirstTransferPointer, ite_eq_right empty] at layout
    exact ⟨carrier, sentinel3, layout.2.1, layout.2.2.1, layout.2.2.2⟩

/-- The first actual callback-to-decoder composition retains the full reply and SAME P child step. -/
private theorem safeTransfer_firstReply_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (notCopyCut : 71 ∉ C) (notAlloc : 16 ∉ C) (notGuard : 17 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    ∃ forwarded callGas d decoderGas,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_call128Memory M amount toWord) callGas) (.exec .call) d ∧
      d.stack = 1 :: 360 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
      d.memory = safeTransfer_call128Memory M amount toWord ∧
      d.output = b.output ∧ d.returnData.length < 2^256 ∧ PtrMem 292 416 d.memory ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (d.returnData.length.toB256 ::
          (if d.returnData.length.toB256 = 0 then 96 else 292) ::
          1 :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
          (if d.returnData.length.toB256 = 0 then d.memory else
            safeTransfer_reply292Memory d.memory d.returnData) decoderGas) t_2148_c16 r := by
  obtain ⟨forwarded, callGas, d, step, tail, stack, memory, output, width, postMem⟩ :=
    safeTransfer_firstCall_post_inv project fork mem notCopyCut notAlloc notGuard run
  have image : d = St d (1 :: 360 ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) d.memory d.gasLeft :=
    St.self stack rfl
  have normalized : SFunc.RunCutP P cert.prog sevm C
      (St d (1 :: 360 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) d.memory d.gasLeft)
      safeTransfer_afterCall r := by
    rw [← image]
    exact tail
  obtain ⟨decoderGas, decoded⟩ := safeTransfer_afterCall_inv project notAlloc normalized
  rw [show Bytes.toB256 (d.memory.read 64 32).1 = 292 from postMem.word,
    postMem.read_self (by decide)] at decoded
  have copied : d.returnData.sliceD 0 d.returnData.length.toB256.toNat 0 = d.returnData := by
    rw [B256.toNat_toB256_of_lt width]
    exact Bytes.sliceD_zero_length rfl
  rw [copied] at decoded
  exact ⟨forwarded, callGas, d, decoderGas, step, stack, memory, output, width, postMem, decoded⟩

/-- Full first helper57 inverse derives its optional-return acceptance and raw returned world.
Its whole-run input discharges internal cuts; arbitrary child storage/log effects are retained. -/
private theorem safeTransfer_firstReturned_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunP P cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 (.returned out)) :
    ∃ forwarded callGas d residual,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_call128Memory M amount toWord) callGas) (.exec .call) d ∧
      d.stack = 1 :: 360 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
      d.memory = safeTransfer_call128Memory M amount toWord ∧ d.output = b.output ∧
      d.returnData.length < 2^256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      out = St d R (if d.returnData = [] then d.memory else
        safeTransfer_reply292Memory d.memory d.returnData) residual := by
  obtain ⟨forwarded, callGas, d, decoderGas, step, stack, memory, output, width, postMem, decoded⟩ :=
    safeTransfer_firstReply_inv project fork mem (by decide : 71 ∉ [])
      (by decide : 16 ∉ []) (by decide : 17 ∉ [])
      ((SFunc.runP_iff_runCutP_nil (P := P)).mp run)
  by_cases empty : d.returnData = []
  · rw [empty, show Nat.toB256 (List.length ([] : Bytes)) = (0 : B256) from rfl,
      ite_eq_left rfl, ite_eq_left rfl] at decoded
    have accepted := (safeTransfer_success_inv project (by decide : 17 ∉ []) decoded).2
    rcases accepted with ⟨_, residual, returned⟩ | ⟨_, _, _, residual, returned⟩
    · simp only [show (96 : B256).toNat = 96 from rfl] at returned
      rw [postMem.read_self (by decide : 96 + 32 ≤ 416)] at returned
      have outEq : out = St d R d.memory residual := Seg.done.inj returned |> Outcome.returned.inj
      refine ⟨forwarded, callGas, d, residual, step, stack, memory, output, width, Or.inl empty, ?_⟩
      rw [ite_eq_left empty]
      exact outEq
    · simp only [show (96 : B256).toNat = 96 from rfl,
        show ((32 : B256) + 96).toNat = 128 from rfl] at returned
      rw [postMem.read_self (by decide : 96 + 32 ≤ 416),
        postMem.read_self (by decide : 96 + 32 ≤ 416),
        postMem.read_self (by decide : 128 + 32 ≤ 416)] at returned
      have outEq : out = St d R d.memory residual := Seg.done.inj returned |> Outcome.returned.inj
      refine ⟨forwarded, callGas, d, residual, step, stack, memory, output, width, Or.inl empty, ?_⟩
      rw [ite_eq_left empty]
      exact outEq
  · have positive : 0 < d.returnData.length := List.length_pos_iff.mpr empty
    have lenNat : d.returnData.length.toB256.toNat = d.returnData.length :=
      B256.toNat_toB256_of_lt width
    have lenNonzero : d.returnData.length.toB256 ≠ 0 := by
      intro zero
      rw [zero] at lenNat
      change 0 = d.returnData.length at lenNat
      omega
    rw [ite_eq_right lenNonzero, ite_eq_right lenNonzero] at decoded
    let A := safeTransfer_reply292Memory d.memory d.returnData
    have images := safeTransfer_reply292_image (reply := d.returnData) postMem
    have carrier : PtrMem (292 + ((d.returnData.length.toB256 + 63) &&& ~~~31))
        (memExtSize 416 324 d.returnData.length) A := images.1
    have room : 416 ≤ memExtSize 416 324 d.returnData.length := memExtSize_ge _ _ _
    have lengthWord : Bytes.toB256 (A.read 292 32).1 = d.returnData.length.toB256 := images.2.1
    have accepted := (safeTransfer_success_inv project (by decide : 17 ∉ []) decoded).2
    change (Bytes.toB256 (A.read 292 32).1 = 0 ∧
        ∃ residual, Seg.done (.returned out) = .done (.returned (St d R (A.read 292 32).2 residual))) ∨
      (Bytes.toB256 (A.read 292 32).1 ≠ 0 ∧
        32 ≤ (Bytes.toB256 ((A.read 292 32).2.read 292 32).1).toNat ∧
        Bytes.toB256 (((A.read 292 32).2.read 292 32).2.read 324 32).1 ≠ 0 ∧
        ∃ residual, Seg.done (.returned out) = .done (.returned
          (St d R (((A.read 292 32).2.read 292 32).2.read 324 32).2 residual))) at accepted
    rw [carrier.read_self (by omega), carrier.read_self (by omega),
      lengthWord, lenNat] at accepted
    rcases accepted with ⟨zero, _⟩ | ⟨_, enough, head, residual, returned⟩
    · exact (lenNonzero zero).elim
    · rw [images.2.2 enough] at head
      rw [carrier.read_self (by omega)] at returned
      have outEq : out = St d R A residual := Seg.done.inj returned |> Outcome.returned.inj
      refine ⟨forwarded, callGas, d, residual, step, stack, memory, output, width,
        Or.inr ⟨enough, head⟩, ?_⟩
      rw [ite_eq_right empty]
      exact outEq


/-- The actual first helper's overlapping copy exposes precisely its 68-byte source window. -/
private theorem safeTransfer_copy128_image {M : Mem} {amount toWord : B256} :
    ((safeTransfer_call128Memory M amount toWord).read 292 68).1 =
      ((safeTransfer_payload128Memory M amount toWord).read 224 68).1 := by
  change ((Blanc.Lift.copy68Memory (safeTransfer_payload128Memory M amount toWord) 224 292).read 292 68).1 =
    ((safeTransfer_payload128Memory M amount toWord).read 224 68).1
  exact Blanc.Lift.copy68Memory_read (by decide)


/-- The actual first initializer emits canonical transfer calldata for arbitrary well-formed memory. -/
private theorem safeTransfer_payload128_data {M : Mem} {amount toWord : B256}
    (wf : Mem.Wf M) :
    ((safeTransfer_payload128Memory M amount toWord).read 224 68).1 =
      abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes := by
  let recipient := (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord
  let N1 := M.write 64 (192 : B256).toBytes
  let N2 := N1.write 128 (25 : B256).toBytes
  let N3 := N2.write 160 (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write 228 recipient.toBytes
  let N5 := N4.write 260 amount.toBytes
  let N6 := N5.write 192 (68 : B256).toBytes
  let N7 := N6.write 64 (292 : B256).toBytes
  have wf3 : Mem.Wf N3 := ((wf.write 64 _).write 128 _).write 160 _
  have wf5 : Mem.Wf N5 := (wf3.write 228 _).write 260 _
  have wf6 : Mem.Wf N6 := wf5.write 192 _
  have wf7 : Mem.Wf N7 := wf6.write 64 _
  have r5 := Mem.reads_data N5
  have r6 := r5.write wf5 192 (68 : B256).toBytes
  have r7 := r6.write wf6 64 (292 : B256).toBytes
  have pair7 : (N7.read 228 64).1 = recipient.toBytes ++ amount.toBytes := by
    rw [r7.read, Bytes.sliceD_writeAt_after _ _ 228 64 64 (by rw [B256.length_toBytes]; decide),
      Bytes.sliceD_writeAt_after _ _ 228 64 192 (by rw [B256.length_toBytes]; decide), ← r5.read 228 64]
    exact Mem.read_two_word_writes_at_raw N3 228 recipient amount
  change ((N7.write 224
    ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
      ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read 224 32).1)).toBytes).read 224 68).1 =
    abiSelectorBytes 0xa9059cbb ++ recipient.toBytes ++ amount.toBytes
  let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
  let selectorWord := (0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256)
  let loaded := Bytes.toB256 (N7.read 224 32).1
  let merged := selectorWord ||| (mask &&& loaded)
  have mergeEq : merged = (selectorWord &&& ~~~mask) ||| (loaded &&& mask) := by
    rw [show selectorWord &&& ~~~mask = selectorWord from rfl]
    exact congrArg (fun x => selectorWord ||| x) (B256.and_comm mask loaded)
  change (((N7.write 224 merged.toBytes).read 224 68).1) =
    abiSelectorBytes 0xa9059cbb ++ recipient.toBytes ++ amount.toBytes
  rw [mergeEq, Blanc.Lift.mergeFourMemory_read68 selectorWord wf7,
    show selectorWord.toBytes.take 4 = abiSelectorBytes 0xa9059cbb from by decide,
    pair7, List.append_assoc]

/-- The actual CALL reads the canonical 68-byte transfer payload produced by the first burn caller. -/
private theorem safeTransfer_call128_data {M : Mem} {amount toWord : B256}
    (wf : Mem.Wf M) :
    ((safeTransfer_call128Memory M amount toWord).read 292 68).1 =
      abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes := by
  rw [safeTransfer_copy128_image]
  exact safeTransfer_payload128_data wf

/-- Every first-call payload/copy write misses the caller's actual empty-array word96. -/
theorem safeTransfer_call128_sentinel {M : Mem} {amount toWord : B256}
    (mem : PtrMem 128 192 M) (sentinel : memWord M 96 = 0) :
    memWord (safeTransfer_call128Memory M amount toWord) 96 = 0 := by
  have original : MemMatches 0 [(96, .const 0)] M := by
    intro o v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    cases hv
    exact ⟨by rw [mem.size]; decide, sentinel⟩
  let N1 := M.write 64 (192 : B256).toBytes
  let N2 := N1.write 128 (25 : B256).toBytes
  let N3 := N2.write 160 (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write 228 ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
  let N5 := N4.write 260 amount.toBytes
  let N6 := N5.write 192 (68 : B256).toBytes
  let N7 := N6.write 64 (292 : B256).toBytes
  let N8 := N7.write 224 ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
    ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read 224 32).1)).toBytes
  have a1 : MemMatches 0 [(96, .const 0)] N1 := by
    have h := original.write 64 (192 : B256).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have a2 : MemMatches 0 [(96, .const 0)] N2 := by
    have h := a1.write 128 (25 : B256).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have a3 : MemMatches 0 [(96, .const 0)] N3 := by
    have h := a2.write 160 (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have a4 : MemMatches 0 [(96, .const 0)] N4 := by
    have h := a3.write 228 ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have a5 : MemMatches 0 [(96, .const 0)] N5 := by
    have h := a4.write 260 amount.toBytes
    rw [B256.length_toBytes] at h
    exact h
  have a6 : MemMatches 0 [(96, .const 0)] N6 := by
    have h := a5.write 192 (68 : B256).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have a7 : MemMatches 0 [(96, .const 0)] N7 := by
    have h := a6.write 64 (292 : B256).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have a8 : MemMatches 0 [(96, .const 0)] (safeTransfer_payload128Memory M amount toWord) := by
    have h := a7.write 224 ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
      ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read 224 32).1)).toBytes
    rw [B256.length_toBytes] at h
    exact h
  unfold safeTransfer_call128Memory
  generalize safeTransfer_payload128Memory M amount toWord = V at a8 ⊢
  let C1 := V.write 292 (Bytes.toB256 (V.read 224 32).1).toBytes
  let C2 := C1.write 324 (Bytes.toB256 (C1.read 256 32).1).toBytes
  have b1 : MemMatches 0 [(96, .const 0)] C1 := by
    have h := a8.write 292 (Bytes.toB256 (V.read 224 32).1).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have b2 : MemMatches 0 [(96, .const 0)] C2 := by
    have h := b1.write 324 (Bytes.toB256 (C1.read 256 32).1).toBytes
    rw [B256.length_toBytes] at h
    exact h
  have extended : MemMatches 0 [(96, .const 0)] (C2.read 356 32).2 :=
    MemMatches.of_data_eq (μ := C2) (μ' := (C2.read 356 32).2) rfl
      (by change C2.size ≤ memExtSize C2.size 356 32; exact memExtSize_ge _ _ _) b2
  have b3 := extended.write 356
    (((Bytes.toB256 (C2.read 288 32).1) &&& ~~~(B256.bexp 256 (32 - 4) - 1)) |||
      ((Bytes.toB256 (C2.read 356 32).1) &&& (B256.bexp 256 (32 - 4) - 1))).toBytes
  rw [B256.length_toBytes] at b3
  exact (b3 96 (.const 0) (List.mem_cons_self)).2

/-- The actual returned first helper exposes canonical calldata at its SAME P primitive CALL,
full optional-return acceptance and the raw child world. No child storage/log effect is erased. -/
theorem safeTransfer_first_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {amount toWord tokenWord rho : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunP P cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 (.returned out)) :
    ∃ forwarded callGas d residual,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_call128Memory M amount toWord) callGas) (.exec .call) d ∧
      d.stack = 1 :: 360 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
      ((safeTransfer_call128Memory M amount toWord).read 292 68).1 =
        abiSelectorBytes 0xa9059cbb ++
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes ∧
      d.memory = safeTransfer_call128Memory M amount toWord ∧ d.output = b.output ∧
      d.returnData.length < 2^256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      out = St d R (if d.returnData = [] then d.memory else
        safeTransfer_reply292Memory d.memory d.returnData) residual := by
  obtain ⟨forwarded, callGas, d, residual, step, stack, memory, output, width, accepted, returned⟩ :=
    safeTransfer_firstReturned_inv project fork mem run
  exact ⟨forwarded, callGas, d, residual, step, stack, safeTransfer_call128_data mem.wf,
    memory, output, width, accepted, returned⟩

/-- The literal first burn caller derives a returned helper; its halted alternative is impossible. -/
private theorem burnFirstTransfer_call_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_168d_c13 r) :
    ∃ helperGas out,
      SFunc.RunP P cert.prog sevm
        (St b (amount0 :: toWord :: token0 :: 0x1698 ::
          burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M helperGas)
        t_1fdb_c57 (.returned out) ∧
      SFunc.RunCutP P cert.prog sevm C out t_1698_c13 r := by
  have h := run
  unfold t_168d_c13 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0x98] = (0x1698 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup (w := token0) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup (w := toWord) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup (w := amount0) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x1f, 0xdb] = (0x1fdb : B256) from rfl] at eq
  subst d
  cases h with
  | callHalt d lookup pop callee =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    exact False.elim (callee.not_halted_entry (S := [16,17,57,71])
      (by decide) (by decide : 57 ∈ [16,17,57,71]) (by rfl : cert.prog[57]? = some t_1fdb_c57) rfl)
  | callRet d lookup pop callee continuation =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    exact ⟨_, _, (St.of_pop1 pop).2 ▸ callee, continuation⟩

/-- The named first burn caller consumes the complete returned-helper observation and
retains the original cached locals, child effects, full reply and literal second-transfer tail. -/
theorem burnFirstTransfer_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_168d_c13 r) :
    ∃ helperGas forwarded callGas d residual,
      SFunc.RunP P cert.prog sevm
        (St b (amount0 :: toWord :: token0 :: 0x1698 ::
          burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M helperGas)
        t_1fdb_c57 (.returned (St d
          (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
          (if d.returnData = [] then d.memory else safeTransfer_reply292Memory d.memory d.returnData) residual)) ∧
      P sevm (St b (forwarded :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
        (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) :: 96 :: 0 :: amount0 :: toWord :: token0 :: 0x1698 ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (safeTransfer_call128Memory M amount0 toWord) callGas) (.exec .call) d ∧
      d.stack = 1 :: 360 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount0 :: toWord :: token0 :: 0x1698 ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R ∧
      ((safeTransfer_call128Memory M amount0 toWord).read 292 68).1 =
        abiSelectorBytes 0xa9059cbb ++
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount0.toBytes ∧
      d.memory = safeTransfer_call128Memory M amount0 toWord ∧ d.output = b.output ∧
      d.returnData.length < 2^256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
          (if d.returnData = [] then d.memory else safeTransfer_reply292Memory d.memory d.returnData) residual)
        t_1698_c13 r := by
  obtain ⟨helperGas, out, callee, continuation⟩ := burnFirstTransfer_call_inv project run
  obtain ⟨forwarded, callGas, d, residual, step, stack, calldata, memory, output, width, accepted, returned⟩ :=
    safeTransfer_first_inv project fork mem callee
  rw [returned] at callee continuation
  exact ⟨helperGas, forwarded, callGas, d, residual, callee, step, stack, calldata,
    memory, output, width, accepted, continuation⟩

/-- The helper's ordered payload writes at the moving pointer left by an
earlier transfer. Every offset remains the literal modular word expression. -/
def safeTransfer_dynamicPayloadMemory (M : Mem) (p amount toWord : B256) : Mem :=
  let N1 := M.write 64 (p + 64).toBytes
  let N2 := N1.write p.toNat (25 : B256).toBytes
  let N3 := N2.write (p + 32).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write (p + 100).toNat ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
  let N5 := N4.write (p + 132).toNat amount.toBytes
  let N6 := N5.write (p + 64).toNat (68 : B256).toBytes
  let N7 := N6.write 64 (p + 164).toBytes
  N7.write (p + 96).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
    ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1)).toBytes

/-- Canonical payload bytes at the pointer produced by an earlier transfer. -/
theorem safeTransfer_dynamicPayload_data {M : Mem} {p amount toWord : B256}
    (wf : Mem.Wf M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 164 < 2 ^ 256) :
    ((safeTransfer_dynamicPayloadMemory M p amount toWord).read (p + 96).toNat 68).1 =
      abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes := by
  have addNat (k : Nat) (hk : k ≤ 164) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have nat32 : (p + 32).toNat = p.toNat + 32 := by
    simpa only [show (32 : Nat).toB256 = (32 : B256) from rfl] using addNat 32 (by decide)
  have nat64 : (p + 64).toNat = p.toNat + 64 := by
    simpa only [show (64 : Nat).toB256 = (64 : B256) from rfl] using addNat 64 (by decide)
  have nat96 : (p + 96).toNat = p.toNat + 96 := by
    simpa only [show (96 : Nat).toB256 = (96 : B256) from rfl] using addNat 96 (by decide)
  have nat100 : (p + 100).toNat = p.toNat + 100 := by
    simpa only [show (100 : Nat).toB256 = (100 : B256) from rfl] using addNat 100 (by decide)
  have nat132 : (p + 132).toNat = p.toNat + 132 := by
    simpa only [show (132 : Nat).toB256 = (132 : B256) from rfl] using addNat 132 (by decide)
  let recipient := (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord
  let N1 := M.write 64 (p + 64).toBytes
  let N2 := N1.write p.toNat (25 : B256).toBytes
  let N3 := N2.write (p.toNat + 32) (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write (p.toNat + 100) recipient.toBytes
  let N5 := N4.write (p.toNat + 132) amount.toBytes
  let N6 := N5.write (p.toNat + 64) (68 : B256).toBytes
  let N7 := N6.write 64 (p + 164).toBytes
  have wf3 : Mem.Wf N3 := ((wf.write 64 _).write p.toNat _).write (p.toNat + 32) _
  have wf5 : Mem.Wf N5 := (wf3.write (p.toNat + 100) _).write (p.toNat + 132) _
  have wf6 : Mem.Wf N6 := wf5.write (p.toNat + 64) _
  have wf7 : Mem.Wf N7 := wf6.write 64 _
  have r5 := Mem.reads_data N5
  have r6 := r5.write wf5 (p.toNat + 64) (68 : B256).toBytes
  have r7 := r6.write wf6 64 (p + 164).toBytes
  have pair7 : (N7.read (p.toNat + 100) 64).1 = recipient.toBytes ++ amount.toBytes := by
    rw [r7.read,
      Bytes.sliceD_writeAt_after _ _ (p.toNat + 100) 64 64 (by rw [B256.length_toBytes]; omega),
      Bytes.sliceD_writeAt_after _ _ (p.toNat + 100) 64 (p.toNat + 64) (by rw [B256.length_toBytes]; omega),
      ← r5.read (p.toNat + 100) 64]
    exact Mem.read_two_word_writes_at_raw N3 (p.toNat + 100) recipient amount
  unfold safeTransfer_dynamicPayloadMemory
  rw [nat32, nat64, nat96, nat100, nat132]
  let mask := (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256)
  let selectorWord := (0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256)
  let loaded := Bytes.toB256 (N7.read (p.toNat + 96) 32).1
  let merged := selectorWord ||| (mask &&& loaded)
  have mergeEq : merged = (selectorWord &&& ~~~mask) ||| (loaded &&& mask) := by
    rw [show selectorWord &&& ~~~mask = selectorWord from rfl]
    exact congrArg (fun x => selectorWord ||| x) (B256.and_comm mask loaded)
  change (((N7.write (p.toNat + 96) merged.toBytes).read (p.toNat + 96) 68).1) =
    abiSelectorBytes 0xa9059cbb ++ recipient.toBytes ++ amount.toBytes
  rw [mergeEq, Blanc.Lift.mergeFourMemory_read68 selectorWord wf7,
    show selectorWord.toBytes.take 4 = abiSelectorBytes 0xa9059cbb from by decide,
    pair7, List.append_assoc]

/-- The second transfer's ordered copy starts at its current free-memory pointer. -/
def safeTransfer_dynamicCallMemory (M : Mem) (p amount toWord : B256) : Mem :=
  Blanc.Lift.copy68Memory (safeTransfer_dynamicPayloadMemory M p amount toWord)
    (p + 96).toNat (p + 164).toNat

/-- The moving CALL window contains the exact selector and both argument words. -/
theorem safeTransfer_dynamicCall_data {M : Mem} {p amount toWord : B256}
    (wf : Mem.Wf M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 164 < 2 ^ 256) :
    ((safeTransfer_dynamicCallMemory M p amount toWord).read (p + 164).toNat 68).1 =
      abiSelectorBytes 0xa9059cbb ++
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes := by
  have addNat (k : Nat) (hk : k ≤ 164) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have nat96 : (p + 96).toNat = p.toNat + 96 := by
    simpa only [show (96 : Nat).toB256 = (96 : B256) from rfl] using addNat 96 (by decide)
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    simpa only [show (164 : Nat).toB256 = (164 : B256) from rfl] using addNat 164 (by decide)
  unfold safeTransfer_dynamicCallMemory
  rw [Blanc.Lift.copy68Memory_read (by rw [nat96, nat164])]
  exact safeTransfer_dynamicPayload_data wf lower width

/-- The memory an actual `_safeTransfer` leaves at its return. (Moved down from
`SwapTransfer` so the dynamic forward theorem sits with the stage lemmas.) -/
def swapTransferMemory (M : Mem) (p amount toWord : B256) (reply : Bytes) : Mem :=
  if reply = [] then safeTransfer_dynamicCallMemory M p amount toWord
  else Blanc.Lift.bytesArrayMemory (safeTransfer_dynamicCallMemory M p amount toWord) (p + 164) reply

/-- The forward `_safeTransfer` contract, proved by `safeTransfer_dynamic_forward` at the charges
`safeTransferPreCharge`/`safeTransferPostCharge`: the `_safeTransfer` helper `t_1fdb_c57`, entered at free
pointer `p` over memory of size `n` (with the zero slot `0x60` clear), reaches
its actual token `CALL` after a pre-call charge `pre n p` with the canonical
stack and staged memory; given that `CALL`'s primitive result (success flag on
the caller's stack, an accepted optional-bool reply) and its residual gas
`G + post n p reply`, the helper returns exactly to its caller with the
transfer memory `swapTransferMemory` and gas `G`. -/
def SwapSafeTransferForward (pre : Nat → B256 → Nat) (post : Nat → B256 → Bytes → Nat) :
    Prop :=
  ∀ (sevm : Sevm) (b d : Devm) (L : List B256) (M : Mem) (n callGas G : Nat)
    (p amount toWord token rho : B256),
    CoveredFork sevm.benvStat.fork → PtrMem p n M → memWord M 96 = 0 →
    128 ≤ p.toNat → p.toNat + 260 < 2 ^ 256 → L.length ≤ 1000 →
    Ninst.RunCompiled sevm
      (St b (callGas.toB256 :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: token :: rho :: L)
        (safeTransfer_dynamicCallMemory M p amount toWord) callGas) (.exec .call) d →
    d.stack = 1 :: (68 + (p + 164)) :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: token :: rho :: L →
    (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
      Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) →
    d.gasLeft = G + post n p d.returnData →
    SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: token :: rho :: L) M (callGas + pre n p)) t_1fdb_c57
      (.returned (St d L (swapTransferMemory M p amount toWord d.returnData) G))

/-- The actual arbitrary-pointer initializer normalizes to the moving payload
image, with its real allocation and all copy operands. The pointer bounds
are intermediate obligations supplied by the first reply's producer. -/
theorem safeTransfer_initialize_dynamic_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 164 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    let N := safeTransfer_dynamicPayloadMemory M p amount toWord
    ∃ residual, SFunc.RunCutP P cert.prog sevm C
      (St b ((p + 96) :: (p + 164) :: 68 :: 68 :: (p + 96) :: (p + 164) ::
        (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) N residual) t_20a4_c57 r ∧
      PtrMem (p + 164) N.size N ∧ p.toNat + 164 ≤ N.size := by
  have addNat (k : Nat) (hk : k ≤ 164) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
      Nat.lo_eq_of_lt (by omega)]
  have nat32 : (p + 32).toNat = p.toNat + 32 := by
    simpa only [show (32 : Nat).toB256 = (32 : B256) from rfl] using addNat 32 (by decide)
  have nat64 : (p + 64).toNat = p.toNat + 64 := by
    simpa only [show (64 : Nat).toB256 = (64 : B256) from rfl] using addNat 64 (by decide)
  have nat96 : (p + 96).toNat = p.toNat + 96 := by
    simpa only [show (96 : Nat).toB256 = (96 : B256) from rfl] using addNat 96 (by decide)
  have nat100 : (p + 100).toNat = p.toNat + 100 := by
    simpa only [show (100 : Nat).toB256 = (100 : B256) from rfl] using addNat 100 (by decide)
  have nat132 : (p + 132).toNat = p.toNat + 132 := by
    simpa only [show (132 : Nat).toB256 = (132 : B256) from rfl] using addNat 132 (by decide)
  let N1 := M.write 64 (p + 64).toBytes
  let N2 := N1.write p.toNat (25 : B256).toBytes
  let N3 := N2.write (p + 32).toNat (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write (p + 100).toNat ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes
  let N5 := N4.write (p + 132).toNat amount.toBytes
  let N6 := N5.write (p + 64).toNat (68 : B256).toBytes
  let N7 := N6.write 64 (p + 164).toBytes
  let N8 := N7.write (p + 96).toNat ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
    ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1)).toBytes
  have h1 : PtrMem (p + 64) N1.size N1 := by
    have hc : PtrMem (p + 64) n N1 := mem.set
    rw [hc.size]; exact hc
  have h2 : PtrMem (p + 64) N2.size N2 := by
    have hc := h1.write p.toNat 25 (Or.inr (by omega))
    rw [hc.size]; exact hc
  have h3 : PtrMem (p + 64) N3.size N3 := by
    have hc := h2.write (p + 32).toNat
      (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256)
      (Or.inr (by rw [nat32]; omega))
    rw [hc.size]; exact hc
  have h4 : PtrMem (p + 64) N4.size N4 := by
    have hc := h3.write (p + 100).toNat
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord)
      (Or.inr (by rw [nat100]; omega))
    rw [hc.size]; exact hc
  have h5 : PtrMem (p + 64) N5.size N5 := by
    have hc := h4.write (p + 132).toNat amount (Or.inr (by rw [nat132]; omega))
    rw [hc.size]; exact hc
  have fit5 : p.toNat + 164 ≤ N5.size := by
    calc
      p.toNat + 164 = (p + 132).toNat + 32 := by rw [nat132]
      _ ≤ N5.size := (Mem.memWord_write_word N4 (p + 132).toNat amount).2
  have h6 : PtrMem (p + 64) N6.size N6 := by
    have hc := h5.write (p + 64).toNat 68 (Or.inr (by rw [nat64]; omega))
    rw [hc.size]; exact hc
  have fit6 : p.toNat + 164 ≤ N6.size :=
    le_trans fit5 (Mem.write_agree N5 (p + 64).toNat (68 : B256).toBytes).1
  have h7 : PtrMem (p + 164) N7.size N7 := by
    have hc : PtrMem (p + 164) N6.size N7 := h6.set
    rw [hc.size]; exact hc
  have fit7 : p.toNat + 164 ≤ N7.size :=
    le_trans fit6 (Mem.write_agree N6 64 (p + 164).toBytes).1
  have h8 : PtrMem (p + 164) N8.size N8 := by
    have hc := h7.write (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1))
      (Or.inr (by rw [nat96]; omega))
    rw [hc.size]; exact hc
  have fit8 : p.toNat + 164 ≤ N8.size :=
    le_trans fit7 (Mem.write_agree N7 (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1)).toBytes).1
  have length6 := (Mem.memWord_write_word N5 (p + 64).toNat 68).1
  have length7 : memWord N7 (p + 64).toNat = 68 := by
    rw [memWord_congr (μ := N6) (fun k hk =>
      (Mem.write_agree N6 64 (p + 164).toBytes).2 ((p + 64).toNat + k)
        (by rw [nat64]; omega) (by rw [nat64, B256.length_toBytes]; right; omega))]
    exact length6
  have length8 : memWord N8 (p + 64).toNat = 68 := by
    rw [memWord_congr (μ := N7) (fun k hk =>
      (Mem.write_agree N7 (p + 96).toNat
        ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
          ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1)).toBytes).2 ((p + 64).toNat + k)
        (by rw [nat64]; omega) (by rw [nat64, nat96]; left; omega))]
    exact length7
  have read0 : Bytes.toB256 (M.read 64 32).1 = p := mem.word
  have read3 : Bytes.toB256 (N3.read 64 32).1 = p + 64 := h3.word
  have read5 : Bytes.toB256 (N5.read 64 32).1 = p + 64 := h5.word
  have read8 : Bytes.toB256 (N8.read 64 32).1 = p + 164 := h8.word
  change Bytes.toB256 (N8.read (p + 64).toNat 32).1 = 68 at length8
  have combine36 : p + 64 + 36 = p + 100 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat100, show (36 : B256).toNat = 36 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have combine68 : p + 64 + 68 = p + 132 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat132, show (68 : B256).toNat = 68 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have combine100 : p + 64 + 100 = p + 164 := by
    have nat164 : (p + 164).toNat = p.toNat + 164 := by
      simpa only [show (164 : Nat).toB256 = (164 : B256) from rfl] using addNat 164 (by decide)
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat164, show (100 : B256).toNat = 100 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have combine32 : p + 64 + 32 = p + 96 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat96, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have h := safeTransfer_initialize_inv project run
  dsimp only at h
  simp only [show (64 : B256).toNat = 64 from rfl] at h
  rw [read0, mem.read_self mem.ge,
    show (64 : B256) + p = p + 64 from B256.add_comm,
    show (32 : B256) + p = p + 32 from B256.add_comm] at h
  rw [read3, h3.read_self h3.ge, combine36, combine68] at h
  rw [read5, h5.read_self h5.ge,
    show (68 : B256) + ((p + 64) - (p + 64)) = 68 from by rw [B256.sub_self, B256.add_zero],
    combine100, combine32] at h
  rw [h7.read_self (by rw [nat96]; omega)] at h
  rw [read8, h8.read_self h8.ge, length8,
    h8.read_self (by rw [nat64]; omega)] at h
  obtain ⟨residual, tail⟩ := h
  exact ⟨residual, tail, h8, fit8⟩

/-- The moving helper reaches its primitive CALL with the exact ordered copy
image and seven operands; its child world remains opaque. -/
theorem safeTransfer_dynamicCall_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (notCopyCut : 71 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    let N := safeTransfer_dynamicCallMemory M p amount toWord
    ∃ forwarded callGas d,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) N callGas) (.exec .call) d ∧
      SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r ∧
      PtrMem (p + 164) N.size N ∧ p.toNat + 260 ≤ N.size := by
  have addNat (k : Nat) (hk : k ≤ 260) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega), Nat.lo_eq_of_lt (by omega)]
  have nat96 : (p + 96).toNat = p.toNat + 96 := by
    simpa only [show (96 : Nat).toB256 = (96 : B256) from rfl] using addNat 96 (by decide)
  have nat128 : (p + 128).toNat = p.toNat + 128 := by
    simpa only [show (128 : Nat).toB256 = (128 : B256) from rfl] using addNat 128 (by decide)
  have nat160 : (p + 160).toNat = p.toNat + 160 := by
    simpa only [show (160 : Nat).toB256 = (160 : B256) from rfl] using addNat 160 (by decide)
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    simpa only [show (164 : Nat).toB256 = (164 : B256) from rfl] using addNat 164 (by decide)
  have nat196 : (p + 196).toNat = p.toNat + 196 := by
    simpa only [show (196 : Nat).toB256 = (196 : B256) from rfl] using addNat 196 (by decide)
  have nat228 : (p + 228).toNat = p.toNat + 228 := by
    simpa only [show (228 : Nat).toB256 = (228 : B256) from rfl] using addNat 228 (by decide)
  have advance96 : 32 + (p + 96) = p + 128 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat96, nat128, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have advance128 : 32 + (p + 128) = p + 160 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat128, nat160, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have advance164 : 32 + (p + 164) = p + 196 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat164, nat196, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  have advance196 : 32 + (p + 196) = p + 228 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat196, nat228, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  let N0 := safeTransfer_dynamicPayloadMemory M p amount toWord
  let N1 := N0.write (p + 164).toNat (Bytes.toB256 (N0.read (p + 96).toNat 32).1).toBytes
  let N2 := N1.write (p + 196).toNat (Bytes.toB256 (N1.read (p + 128).toNat 32).1).toBytes
  let mask := B256.bexp 256 (32 - 4) - 1
  let word := ((Bytes.toB256 (N2.read (p + 160).toNat 32).1) &&& ~~~mask) |||
    ((Bytes.toB256 (N2.read (p + 228).toNat 32).1) &&& mask)
  let N3 := (N2.read (p + 228).toNat 32).2.write (p + 228).toNat word.toBytes
  obtain ⟨gInit, initialized, h0, fit0⟩ :=
    safeTransfer_initialize_dynamic_inv project mem lower (by omega) run
  change PtrMem (p + 164) N0.size N0 at h0
  change p.toNat + 164 ≤ N0.size at fit0
  have h1 : PtrMem (p + 164) N1.size N1 := by
    have hc := h0.write (p + 164).toNat (Bytes.toB256 (N0.read (p + 96).toNat 32).1)
      (Or.inr (by rw [nat164]; omega))
    rw [hc.size]; exact hc
  have fit1 : p.toNat + 196 ≤ N1.size := by
    have bound : (p + 164).toNat + 32 ≤ N1.size := (Mem.memWord_write_word N0 (p + 164).toNat
      (Bytes.toB256 (N0.read (p + 96).toNat 32).1)).2
    rw [nat164] at bound
    exact bound
  have h2 : PtrMem (p + 164) N2.size N2 := by
    have hc := h1.write (p + 196).toNat (Bytes.toB256 (N1.read (p + 128).toNat 32).1)
      (Or.inr (by rw [nat196]; omega))
    rw [hc.size]; exact hc
  have fit2 : p.toNat + 228 ≤ N2.size := by
    have bound : (p + 196).toNat + 32 ≤ N2.size := (Mem.memWord_write_word N1 (p + 196).toNat
      (Bytes.toB256 (N1.read (p + 128).toNat 32).1)).2
    rw [nat196] at bound
    exact bound
  have h3 : PtrMem (p + 164) N3.size N3 := by
    have extended := h2.extend (p + 228).toNat 32
    have hc := extended.write (p + 228).toNat word (Or.inr (by rw [nat228]; omega))
    rw [hc.size]; exact hc
  have fit3 : p.toNat + 260 ≤ N3.size := by
    have bound : (p + 228).toNat + 32 ≤ N3.size := (Mem.memWord_write_word (N2.read (p + 228).toNat 32).2
      (p + 228).toNat word).2
    rw [nat228] at bound
    exact bound
  obtain ⟨gCopy, copied⟩ := safeTransfer_copy68_inv project notCopyCut initialized
  rw [h0.read_self (by rw [nat96]; omega), advance96, advance128,
    advance164, advance196] at copied
  change SFunc.RunCutP P cert.prog sevm C
    (St b ((p + 160) :: (p + 228) :: 4 :: 68 :: (p + 96) :: (p + 164) ::
      (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
      ((N1.read (p + 128).toNat 32).2.write (p + 196).toNat
        (Bytes.toB256 (N1.read (p + 128).toNat 32).1).toBytes) gCopy) t_20e1_c57 r at copied
  rw [h1.read_self (by rw [nat128]; omega)] at copied
  have call := safeTransfer_partialCall_inv project copied
  dsimp only at call
  rw [h2.read_self (by rw [nat160]; omega)] at call
  change ∃ forwarded callGas d,
    P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: Bytes.toB256 (N3.read 64 32).1 ::
      ((68 + (p + 164)) - Bytes.toB256 (N3.read 64 32).1) ::
      Bytes.toB256 (N3.read 64 32).1 :: 0 :: (68 + (p + 164)) ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
      (N3.read 64 32).2 callGas) (.exec .call) d ∧
    SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r at call
  rw [show Bytes.toB256 (N3.read 64 32).1 = p + 164 from h3.word,
    h3.read_self h3.ge] at call
  have inputSize : (68 + (p + 164)) - (p + 164) = 68 := by
    apply B256.toNat_inj
    rw [B256.toNat_sub, B256.toNat_add, nat164,
      show (68 : B256).toNat = 68 from rfl,
      @Nat.lo_eq_of_lt (68 + (p.toNat + 164)) 256 (by omega)]
    rw [show 2 ^ 256 + (68 + (p.toNat + 164)) - (p.toNat + 164) = 2 ^ 256 + 68 by omega,
      Nat.two_pow_add_lo, Nat.lo_eq_of_lt (by decide)]
  rw [inputSize] at call
  have image : N3 = safeTransfer_dynamicCallMemory M p amount toWord := by
    unfold safeTransfer_dynamicCallMemory Blanc.Lift.copy68Memory
    simp only [N3, word, mask, N2, N1, N0, nat96, nat164, nat128, nat160, nat196, nat228, Nat.add_assoc]
  rw [image] at h3 fit3 call
  obtain ⟨forwarded, callGas, d, step, tail⟩ := call
  exact ⟨forwarded, callGas, d, step, tail, h3, fit3⟩

/-- Successful continuation settles the moving CALL without changing its
prepaid parent memory or constraining the token child's world effects. -/
theorem safeTransfer_dynamicCall_post_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (notCopyCut : 71 ∉ C) (notAlloc : 16 ∉ C) (notGuard : 17 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    let N := safeTransfer_dynamicCallMemory M p amount toWord
    ∃ forwarded callGas d,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) N callGas) (.exec .call) d ∧
      SFunc.RunCutP P cert.prog sevm C d safeTransfer_afterCall r ∧
      d.stack = 1 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
      d.memory = N ∧ d.output = b.output ∧ d.returnData.length < 2 ^ 256 ∧
      PtrMem (p + 164) N.size d.memory ∧ p.toNat + 260 ≤ N.size := by
  obtain ⟨forwarded, callGas, d, step, tail, preMem, fit⟩ :=
    safeTransfer_dynamicCall_inv project mem lower width notCopyCut run
  let N := safeTransfer_dynamicCallMemory M p amount toWord
  change PtrMem (p + 164) N.size N at preMem
  change p.toNat + 260 ≤ N.size at fit
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have covered : memExtsSize N.size [((p + 164).toNat, 68), ((p + 164).toNat, 0)] = N.size := by
    simp only [memExtsSize]
    rw [memExtSize_of_le preMem.n32 (by rw [nat164]; omega),
      memExtSize_of_le preMem.n32 (by rw [nat164]; omega)]
  have settled := safeTransfer_call_inv project fork notAlloc notGuard step tail
  have memory : d.memory = N := by
    rw [settled.2.1]
    change (N.extends [((p + 164).toNat, 68), ((p + 164).toNat, 0)]).write
      (p + 164).toNat (d.returnData.take 0) = N
    rw [Mem.extends_covered covered]
    simp only [List.take_zero, Mem.write]
  refine ⟨forwarded, callGas, d, step, tail, settled.1, memory,
    settled.2.2.1, settled.2.2.2, ?_, fit⟩
  rw [memory]
  exact preMem

/-- The moving helper's decoder receives its own full physical CALL reply,
independently of the reply that produced its entry pointer. -/
theorem safeTransfer_dynamicReply_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (notCopyCut : 71 ∉ C) (notAlloc : 16 ∉ C) (notGuard : 17 ∉ C)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 r) :
    let N := safeTransfer_dynamicCallMemory M p amount toWord
    ∃ forwarded callGas d decoderGas,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) N callGas) (.exec .call) d ∧
      d.stack = 1 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
      d.memory = N ∧ d.output = b.output ∧ d.returnData.length < 2 ^ 256 ∧
      PtrMem (p + 164) N.size d.memory ∧ p.toNat + 260 ≤ N.size ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (d.returnData.length.toB256 ::
          (if d.returnData.length.toB256 = 0 then 96 else p + 164) ::
          1 :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
          (if d.returnData.length.toB256 = 0 then d.memory else
            ((d.memory.write 64
                (p + 164 + ((d.returnData.length.toB256 + 63) &&& ~~~31)).toBytes).write
              (p + 164).toNat d.returnData.length.toB256.toBytes).write
                (p + 164 + 32).toNat d.returnData) decoderGas) t_2148_c16 r := by
  obtain ⟨forwarded, callGas, d, step, tail, stack, memory, output, replyWidth, postMem, fit⟩ :=
    safeTransfer_dynamicCall_post_inv project fork mem lower width notCopyCut notAlloc notGuard run
  have image : d = St d (1 :: (68 + (p + 164)) ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) d.memory d.gasLeft :=
    St.self stack rfl
  have normalized : SFunc.RunCutP P cert.prog sevm C
      (St d (1 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) d.memory d.gasLeft)
      safeTransfer_afterCall r := by
    rw [← image]
    exact tail
  obtain ⟨decoderGas, decoded⟩ := safeTransfer_afterCall_inv project notAlloc normalized
  rw [show Bytes.toB256 (d.memory.read 64 32).1 = p + 164 from postMem.word,
    postMem.read_self postMem.ge] at decoded
  have copied : d.returnData.sliceD 0 d.returnData.length.toB256.toNat 0 = d.returnData := by
    rw [B256.toNat_toB256_of_lt replyWidth]
    exact Bytes.sliceD_zero_length rfl
  rw [copied] at decoded
  exact ⟨forwarded, callGas, d, decoderGas, step, stack, memory, output, replyWidth, postMem, fit, decoded⟩

/-- The already reached physical optional-bool decoder returns its own full
reply image. This inverse does not select or rerun an external call. -/
theorem safeTransfer_decodedReturned_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {d out : Devm} {R : List B256} {G : Nat}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (postMem : PtrMem (p + 164) n d.memory) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (fit : p.toNat + 260 ≤ n)
    (replyWidth : d.returnData.length < 2 ^ 256)
    (decoded : SFunc.RunCutP P cert.prog sevm []
      (St d (d.returnData.length.toB256 ::
        (if d.returnData.length.toB256 = 0 then 96 else p + 164) ::
        1 :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (if d.returnData.length.toB256 = 0 then d.memory else
          ((d.memory.write 64
              (p + 164 + ((d.returnData.length.toB256 + 63) &&& ~~~31)).toBytes).write
            (p + 164).toNat d.returnData.length.toB256.toBytes).write
              (p + 164 + 32).toNat d.returnData) G) t_2148_c16 (.done (.returned out))) :
    ∃ residual,
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      out = St d R (if d.returnData = [] then d.memory else
        Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData) residual := by
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl, Nat.lo_eq_of_lt (by omega)]
  by_cases empty : d.returnData = []
  · rw [empty, show Nat.toB256 (List.length ([] : Bytes)) = (0 : B256) from rfl,
      ite_eq_left rfl, ite_eq_left rfl] at decoded
    have accepted := (safeTransfer_success_inv project (by decide : 17 ∉ []) decoded).2
    rcases accepted with ⟨_, residual, returned⟩ | ⟨_, _, _, residual, returned⟩
    · simp only [show (96 : B256).toNat = 96 from rfl] at returned
      rw [postMem.read_self (by omega)] at returned
      have outEq : out = St d R d.memory residual := Seg.done.inj returned |> Outcome.returned.inj
      refine ⟨residual, Or.inl empty, ?_⟩
      rw [ite_eq_left empty]
      exact outEq
    · simp only [show (96 : B256).toNat = 96 from rfl,
        show ((32 : B256) + 96).toNat = 128 from rfl] at returned
      rw [postMem.read_self (by omega), postMem.read_self (by omega),
        postMem.read_self (by omega)] at returned
      have outEq : out = St d R d.memory residual := Seg.done.inj returned |> Outcome.returned.inj
      refine ⟨residual, Or.inl empty, ?_⟩
      rw [ite_eq_left empty]
      exact outEq
  · have positive : 0 < d.returnData.length := List.length_pos_iff.mpr empty
    have lenNat : d.returnData.length.toB256.toNat = d.returnData.length :=
      B256.toNat_toB256_of_lt replyWidth
    have lenNonzero : d.returnData.length.toB256 ≠ 0 := by
      intro zero
      rw [zero] at lenNat
      change 0 = d.returnData.length at lenNat
      omega
    rw [ite_eq_right lenNonzero, ite_eq_right lenNonzero] at decoded
    let A := Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData
    have images := Blanc.Lift.bytesArrayMemory_image (bytes := d.returnData) postMem
      (by rw [nat164]; omega) (by rw [nat164]; omega) (by rw [nat164]; omega)
    have carrier : PtrMem (p + 164 + ((d.returnData.length.toB256 + 63) &&& ~~~31))
        (memExtSize n
          (p + 164 + 32).toNat d.returnData.length) A := images.1
    have room : n ≤
        memExtSize n
          (p + 164 + 32).toNat d.returnData.length := memExtSize_ge _ _ _
    have lengthWord : Bytes.toB256 (A.read (p + 164).toNat 32).1 = d.returnData.length.toB256 := images.2.1
    have accepted := (safeTransfer_success_inv project (by decide : 17 ∉ []) decoded).2
    change (Bytes.toB256 (A.read (p + 164).toNat 32).1 = 0 ∧
        ∃ residual, Seg.done (.returned out) = .done (.returned
          (St d R (A.read (p + 164).toNat 32).2 residual))) ∨
      (Bytes.toB256 (A.read (p + 164).toNat 32).1 ≠ 0 ∧
        32 ≤ (Bytes.toB256 ((A.read (p + 164).toNat 32).2.read (p + 164).toNat 32).1).toNat ∧
        Bytes.toB256 (((A.read (p + 164).toNat 32).2.read (p + 164).toNat 32).2.read
          (32 + (p + 164)).toNat 32).1 ≠ 0 ∧
        ∃ residual, Seg.done (.returned out) = .done (.returned
          (St d R (((A.read (p + 164).toNat 32).2.read (p + 164).toNat 32).2.read
            (32 + (p + 164)).toNat 32).2 residual))) at accepted
    rw [carrier.read_self (by rw [nat164]; omega), carrier.read_self (by rw [nat164]; omega),
      lengthWord, lenNat] at accepted
    rcases accepted with ⟨zero, _⟩ | ⟨_, enough, head, residual, returned⟩
    · exact (lenNonzero zero).elim
    · rw [show (32 : B256) + (p + 164) = (p + 164) + 32 from B256.add_comm,
        images.2.2 enough] at head
      have copyRoom := Jaune.memExtSize_access_le
        n (p + 164 + 32).toNat
        d.returnData.length (by omega)
      rw [show (32 : B256) + (p + 164) = (p + 164) + 32 from B256.add_comm,
        carrier.read_self (by omega)] at returned
      have outEq : out = St d R A residual := Seg.done.inj returned |> Outcome.returned.inj
      refine ⟨residual, Or.inr ⟨enough, head⟩, ?_⟩
      rw [ite_eq_right empty]
      exact outEq

/-- A complete moving helper returns exactly its own full optional reply
allocation and derives the token's optional-bool acceptance from the bytecode. -/
theorem safeTransfer_dynamicReturned_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b out : Devm} {R : List B256} {M : Mem} {G : Nat}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunP P cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M G) t_1fdb_c57 (.returned out)) :
    ∃ forwarded callGas d residual,
      P sevm (St b (forwarded :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_dynamicCallMemory M p amount toWord) callGas) (.exec .call) d ∧
      d.stack = 1 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R ∧
      d.memory = safeTransfer_dynamicCallMemory M p amount toWord ∧ d.output = b.output ∧
      d.returnData.length < 2 ^ 256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      out = St d R (if d.returnData = [] then d.memory else
        Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData) residual := by
  obtain ⟨forwarded, callGas, d, decoderGas, step, stack, memory, output, replyWidth, postMem, fit, decoded⟩ :=
    safeTransfer_dynamicReply_inv project fork mem lower width (by decide : 71 ∉ [])
      (by decide : 16 ∉ []) (by decide : 17 ∉ [])
      ((SFunc.runP_iff_runCutP_nil (P := P)).mp run)
  obtain ⟨residual, accepted, returned⟩ := safeTransfer_decodedReturned_inv project
    postMem lower width fit replyWidth decoded
  exact ⟨forwarded, callGas, d, residual, step, stack, memory, output, replyWidth,
    accepted, returned⟩

/-- The literal second burn caller derives a returned helper; its halted alternative is impossible. -/
theorem burnSecondTransfer_call_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_1698_c13 r) :
    ∃ helperGas out,
      SFunc.RunP P cert.prog sevm
        (St b (amount1 :: toWord :: token1 :: 0x16a3 ::
          burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M helperGas)
        t_1fdb_c57 (.returned out) ∧
      SFunc.RunCutP P cert.prog sevm C out t_16a3_c13 r := by
  have h := run
  unfold t_1698_c13 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x16, 0xa3] = (0x16a3 : B256) from rfl] at eq
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup (w := token1) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup (w := toWord) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_dup (w := amount1) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_push (project hd)
  rw [show Bytes.toB256 [0x1f, 0xdb] = (0x1fdb : B256) from rfl] at eq
  subst d
  cases h with
  | callHalt d lookup pop callee =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    exact False.elim (callee.not_halted_entry (S := [16,17,57,71])
      (by decide) (by decide : 57 ∈ [16,17,57,71]) (by rfl : cert.prog[57]? = some t_1fdb_c57) rfl)
  | callRet d lookup pop callee continuation =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    exact ⟨_, _, (St.of_pop1 pop).2 ▸ callee, continuation⟩

/-- The actual second Burn caller consumes the moving helper's full return
proof and canonical calldata, retaining cached locals and its literal suffix. -/
theorem burnSecondTransfer_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {p : B256} {n : Nat}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_1698_c13 r) :
    ∃ helperGas forwarded callGas d residual,
      SFunc.RunP P cert.prog sevm
        (St b (amount1 :: toWord :: token1 :: 0x16a3 ::
          burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M helperGas)
        t_1fdb_c57 (.returned (St d
          (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
          (if d.returnData = [] then d.memory else
            Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData) residual)) ∧
      P sevm (St b (forwarded :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount1 :: toWord :: token1 :: 0x16a3 ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
        (safeTransfer_dynamicCallMemory M p amount1 toWord) callGas) (.exec .call) d ∧
      d.stack = 1 :: (68 + (p + 164)) ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount1 :: toWord :: token1 :: 0x16a3 ::
        burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R ∧
      ((safeTransfer_dynamicCallMemory M p amount1 toWord).read (p + 164).toNat 68).1 =
        abiSelectorBytes 0xa9059cbb ++
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount1.toBytes ∧
      d.memory = safeTransfer_dynamicCallMemory M p amount1 toWord ∧ d.output = b.output ∧
      d.returnData.length < 2 ^ 256 ∧
      (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
        Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0)) ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R)
          (if d.returnData = [] then d.memory else
            Blanc.Lift.bytesArrayMemory d.memory (p + 164) d.returnData) residual)
        t_16a3_c13 r := by
  obtain ⟨helperGas, out, callee, continuation⟩ := burnSecondTransfer_call_inv project run
  obtain ⟨forwarded, callGas, d, residual, step, stack, memory, output, replyWidth, accepted, returned⟩ :=
    safeTransfer_dynamicReturned_inv project fork mem lower width callee
  have calldata := safeTransfer_dynamicCall_data
    (amount := amount1) (toWord := toWord) mem.wf lower
    (by omega : p.toNat + 164 < 2 ^ 256)
  rw [returned] at callee continuation
  exact ⟨helperGas, forwarded, callGas, d, residual, callee, step, stack, calldata,
    memory, output, replyWidth, accepted, continuation⟩

/-- Both literal Burn transfers come from one retained source continuation.
Their actual 68-byte CALL operands bound the full replies independently; the
first allocation supplies the second pointer without a caller-potential premise. -/
theorem burnTransfers_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (sentinel : memWord M 96 = 0)
    (run : SFunc.RunCutP P cert.prog sevm C
      (St b (burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R) M G)
      t_168d_c13 r) :
    ∃ (forwarded0 : B256) (callGas0 : Nat) (d0 : Devm) (residual0 : Nat)
        (forwarded1 : B256) (callGas1 : Nat) (d1 : Devm) (residual1 : Nat),
      let locals := burnPricedLocals supply f L b1 b0 token1 token0 r1 r0 amount1 amount0 toWord extρ R
      let mid := if d0.returnData = [] then d0.memory else
        safeTransfer_reply292Memory d0.memory d0.returnData
      let p := burnFirstTransferPointer d0.returnData
      let N := safeTransfer_dynamicCallMemory mid p amount1 toWord
      P sevm (St b (forwarded0 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: 292 :: 68 :: 292 :: 0 :: 360 ::
        (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount0 :: toWord :: token0 :: 0x1698 :: locals)
        (safeTransfer_call128Memory M amount0 toWord) callGas0) (.exec .call) d0 ∧
      P sevm (St d0 (forwarded1 :: (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount1 :: toWord :: token1 :: 0x16a3 :: locals)
        N callGas1) (.exec .call) d1 ∧
      d0.stack = 1 :: 360 :: (token0 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount0 :: toWord :: token0 :: 0x1698 :: locals ∧
      d1.stack = 1 :: (68 + (p + 164)) ::
        (token1 &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount1 :: toWord :: token1 :: 0x16a3 :: locals ∧
      ((safeTransfer_call128Memory M amount0 toWord).read 292 68).1 =
        abiSelectorBytes 0xa9059cbb ++
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount0.toBytes ∧
      (N.read (p + 164).toNat 68).1 =
        abiSelectorBytes 0xa9059cbb ++
          ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount1.toBytes ∧
      d0.memory = safeTransfer_call128Memory M amount0 toWord ∧ d1.memory = N ∧
      d0.output = b.output ∧ d1.output = b.output ∧
      d0.returnData.length < 2 ^ 160 ∧ d1.returnData.length < 2 ^ 160 ∧
      (d0.returnData = [] ∨ (32 ≤ d0.returnData.length ∧
        Bytes.toB256 (d0.returnData.sliceD 0 32 0) ≠ 0)) ∧
      (d1.returnData = [] ∨ (32 ≤ d1.returnData.length ∧
        Bytes.toB256 (d1.returnData.sliceD 0 32 0) ≠ 0)) ∧
      PtrMem p (if d0.returnData = [] then 416 else memExtSize 416 324 d0.returnData.length) mid ∧
      memWord mid 96 = 0 ∧
      (burnSecondTransferPointer d0.returnData d1.returnData).toNat + 64 < 2 ^ 256 ∧
      PtrMem (burnSecondTransferPointer d0.returnData d1.returnData)
        (if d1.returnData = [] then N.size else
          memExtSize N.size (p + 164 + 32).toNat d1.returnData.length)
        (if d1.returnData = [] then d1.memory else
          Blanc.Lift.bytesArrayMemory d1.memory (p + 164) d1.returnData) ∧
      SFunc.RunCutP P cert.prog sevm C (St d0 locals mid residual0) t_1698_c13 r ∧
      SFunc.RunCutP P cert.prog sevm C
        (St d1 locals (if d1.returnData = [] then d1.memory else
          Blanc.Lift.bytesArrayMemory d1.memory (p + 164) d1.returnData) residual1)
        t_16a3_c13 r := by
  obtain ⟨helperGas0, forwarded0, callGas0, d0, residual0, callee0, call0, flag0,
      calldata0, memory0, output0, _, accepted0, continuation0⟩ :=
    burnFirstTransfer_caller_inv project fork mem run
  have width0 : d0.returnData.length < 2 ^ 160 :=
    Jaune.call_returnData_length_lt_two_pow_160_of_input_size (project call0) rfl
      fork.rules_stateGas_none (by decide : (68 : B256).toNat < 2 ^ 160)
  obtain ⟨_, _, _, _, _, callMem0⟩ := safeTransfer_firstCall_inv project mem
    (by decide : 71 ∉ []) ((SFunc.runP_iff_runCutP_nil (P := P)).mp callee0)
  have postMem0 : PtrMem 292 416 d0.memory := by
    rw [memory0]
    exact callMem0
  have postSentinel0 : memWord d0.memory 96 = 0 := by
    rw [memory0]
    exact safeTransfer_call128_sentinel mem sentinel
  have midLayout := burnFirstTransfer_memoryLayout postMem0 postSentinel0 width0
  let p := burnFirstTransferPointer d0.returnData
  let mid := if d0.returnData = [] then d0.memory else
    safeTransfer_reply292Memory d0.memory d0.returnData
  let N := safeTransfer_dynamicCallMemory mid p amount1 toWord
  have lower : 128 ≤ p.toNat := by
    have bound : 292 ≤ p.toNat := midLayout.2.2.1
    omega
  have room : p.toNat + 260 < 2 ^ 256 := midLayout.2.2.2.2
  obtain ⟨helperGas1, forwarded1, callGas1, d1, residual1, callee1, call1, flag1,
      calldata1, memory1, output1, _, accepted1, continuation1⟩ :=
    burnSecondTransfer_caller_inv project fork midLayout.1 lower room continuation0
  have width1 : d1.returnData.length < 2 ^ 160 :=
    Jaune.call_returnData_length_lt_two_pow_160_of_input_size (project call1) rfl
      fork.rules_stateGas_none (by decide : (68 : B256).toNat < 2 ^ 160)
  obtain ⟨_, _, _, _, _, callMem1, callFit1⟩ :=
    safeTransfer_dynamicCall_inv project midLayout.1 lower room (by decide : 71 ∉ [])
      ((SFunc.runP_iff_runCutP_nil (P := P)).mp callee1)
  have callFit : p.toNat + 260 ≤ N.size := callFit1
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have postMem1 : PtrMem (p + 164)
      N.size d1.memory := by
    rw [memory1]
    exact callMem1
  have finalMem : PtrMem (burnSecondTransferPointer d0.returnData d1.returnData)
      (if d1.returnData = [] then N.size else
        memExtSize N.size
          (p + 164 + 32).toNat d1.returnData.length)
      (if d1.returnData = [] then d1.memory else
        Blanc.Lift.bytesArrayMemory d1.memory (p + 164) d1.returnData) := by
    by_cases empty : d1.returnData = []
    · simpa only [burnSecondTransferPointer, empty, ite_true] using postMem1
    · have image := Blanc.Lift.bytesArrayMemory_image (bytes := d1.returnData) postMem1
        (by rw [nat164]; omega) (by rw [nat164]; omega) (by rw [nat164]; omega)
      simpa only [burnSecondTransferPointer, ite_eq_right empty] using image.1
  exact ⟨forwarded0, callGas0, d0, residual0, forwarded1, callGas1, d1, residual1,
    call0, call1, flag0, flag1, calldata0, calldata1, memory0, memory1, output0, output1.trans output0,
    width0, width1, accepted0, accepted1, midLayout.1, midLayout.2.1,
    (burnSecondTransferPointer_layout width0 width1).2.2.2, finalMem,
    continuation0, continuation1⟩

/-- Ordered staging size of the dynamic `_safeTransfer` pre-CALL segment: the
exact read/write access order of `safeTransfer_initialize_exact` (14 accesses),
`safeTransfer_copy68_exact` (4 accesses) and `safeTransfer_partialCall_exact`
(4 accesses), each folded through `memExtSize`. Offsets are relative to the
free pointer `p`; `64` is the free-pointer slot. -/
def safeTransferPreSize (n : Nat) (p : B256) : Nat :=
  let q := p.toNat
  List.foldl (fun s k => memExtSize s k 32) n
    [64, 64, q, q + 32, 64, q + 100, q + 132, 64, q + 64, 64, q + 96, q + 96,
      64, q + 64, q + 96, q + 164, q + 128, q + 196, q + 160, q + 228, q + 228, 64]

/-- Exact pre-CALL charge at pointer `p` over memory of size `n`: the 599
literal base opcodes plus the telescoped memory-expansion delta. -/
def safeTransferPreCharge (n : Nat) (p : B256) : Nat :=
  599 + (calculateMemoryGasCost (safeTransferPreSize n p) - calculateMemoryGasCost n)

/-- Ordered size after the dynamic `_safeTransfer` post-CALL allocation: the
free-pointer slot read, the free-pointer word store, the reply-length store at
`p + 164`, and the full reply copy at `p + 196`. -/
def safeTransferPostSize (n : Nat) (p : B256) (reply : Bytes) : Nat :=
  let s := safeTransferPreSize n p
  let q := p.toNat
  memExtSize (memExtSize (memExtSize s 64 32) (q + 164) 32) (q + 196) reply.length

/-- Exact post-CALL charge: 138 on the empty reply (no expansion past the
staged image); otherwise the 253 literal base plus the copy charge with its
memory-expansion delta. -/
def safeTransferPostCharge (n : Nat) (p : B256) (reply : Bytes) : Nat :=
  if reply = [] then 138
  else 253 + (gVerylow + gReturnDataCopy * ceilDiv reply.length 32 +
    (calculateMemoryGasCost (safeTransferPostSize n p reply) -
      calculateMemoryGasCost (safeTransferPreSize n p)))

/-- Word-level offset equations for the moving `_safeTransfer` staging area:
every payload/copy offset stays below `2 ^ 256` under the predicate's width,
so each B256 offset word reads back as the natural sum. -/
private theorem safeTransfer_stageOffset {p : B256}
    (width : p.toNat + 260 < 2 ^ 256) :
    (32 : B256) + p = p + 32 ∧ (64 : B256) + p = p + 64 ∧
      p + 64 + 36 = p + 100 ∧ p + 64 + 68 = p + 132 ∧ p + 64 + 100 = p + 164 ∧
      (p + 96).toNat = p.toNat + 96 ∧ (p + 164).toNat = p.toNat + 164 ∧
      (p + 228).toNat = p.toNat + 228 ∧
      (p + 32).toNat = p.toNat + 32 ∧ (p + 64).toNat = p.toNat + 64 ∧
      (p + 100).toNat = p.toNat + 100 ∧ (p + 132).toNat = p.toNat + 132 ∧
      (p + 196).toNat = p.toNat + 196 := by
  have addNat (k : Nat) (hk : k ≤ 260) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
      Nat.lo_eq_of_lt (by omega)]
  have nat96 : (p + 96).toNat = p.toNat + 96 := by
    simpa only [show (96 : Nat).toB256 = (96 : B256) from rfl] using addNat 96 (by decide)
  have nat164 : (p + 164).toNat = p.toNat + 164 := by
    simpa only [show (164 : Nat).toB256 = (164 : B256) from rfl] using addNat 164 (by decide)
  have nat228 : (p + 228).toNat = p.toNat + 228 := by
    simpa only [show (228 : Nat).toB256 = (228 : B256) from rfl] using addNat 228 (by decide)
  have nat100 : (p + 100).toNat = p.toNat + 100 := by
    simpa only [show (100 : Nat).toB256 = (100 : B256) from rfl] using addNat 100 (by decide)
  have nat132 : (p + 132).toNat = p.toNat + 132 := by
    simpa only [show (132 : Nat).toB256 = (132 : B256) from rfl] using addNat 132 (by decide)
  have nat64 : (p + 64).toNat = p.toNat + 64 := by
    simpa only [show (64 : Nat).toB256 = (64 : B256) from rfl] using addNat 64 (by decide)
  have nat32 : (p + 32).toNat = p.toNat + 32 := by
    simpa only [show (32 : Nat).toB256 = (32 : B256) from rfl] using addNat 32 (by decide)
  have nat196 : (p + 196).toNat = p.toNat + 196 := by
    simpa only [show (196 : Nat).toB256 = (196 : B256) from rfl] using addNat 196 (by decide)
  refine ⟨B256.add_comm, B256.add_comm, ?_, ?_, ?_, nat96, nat164, nat228,
    nat32, nat64, nat100, nat132, nat196⟩
  · apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat100,
      show (36 : B256).toNat = 36 from rfl, Nat.lo_eq_of_lt (by omega)]
  · apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat132,
      show (68 : B256).toNat = 68 from rfl, Nat.lo_eq_of_lt (by omega)]
  · apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat164,
      show (100 : B256).toNat = 100 from rfl, Nat.lo_eq_of_lt (by omega)]

/-- The moving helper's staged image already covers its CALL window: the final
merge write at `p + 228` reaches `p.toNat + 260`. -/
theorem safeTransfer_dynamicCall_fit {M : Mem} {p amount toWord : B256} {n : Nat}
    (_mem : PtrMem p n M) (_lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    p.toNat + 260 ≤ (safeTransfer_dynamicCallMemory M p amount toWord).size := by
  obtain ⟨c32, c64, e100, e132, e164, nat96, nat164, nat228,
    nat32, nat64, nat100, nat132, nat196⟩ := safeTransfer_stageOffset width
  have grow : ∀ (W : Mem) (w : B256), p.toNat + 260 ≤
      (((W.read ((p + 164).toNat + 64) 32).2.write ((p + 164).toNat + 64)
        w.toBytes).size) := by
    intro W w
    have hne : w.toBytes ≠ [] := by
      intro h
      have hl := B256.length_toBytes w
      rw [h, List.length_nil] at hl
      exact absurd hl (by decide)
    obtain ⟨A, _, hfit, _, _, _⟩ := Mem.write_base (W.read ((p + 164).toNat + 64) 32).2
      ((p + 164).toNat + 64) hne
    have hlen : w.toBytes.length = 32 := B256.length_toBytes w
    rw [nat164] at hfit
    omega
  unfold safeTransfer_dynamicCallMemory Blanc.Lift.copy68Memory
  dsimp only
  exact grow _ _

/-- Payload staging sizes for the moving `_safeTransfer` initializer: the eight
ordered writes of `safeTransfer_dynamicPayloadMemory`, each with its size,
alignment and absolute coverage. -/
private theorem safeTransfer_payloadSizes {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (_lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    let N1 := M.write 64 (p + 64).toBytes
    let N2 := N1.write p.toNat (25 : B256).toBytes
    let N3 := N2.write (p + 32).toNat
      (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let N4 := N3.write (p + 100).toNat
      ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let N5 := N4.write (p + 132).toNat amount.toBytes
    let N6 := N5.write (p + 64).toNat (68 : B256).toBytes
    let N7 := N6.write 64 (p + 164).toBytes
    let N8 := N7.write (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
          Bytes.toB256 (N7.read (p + 96).toNat 32).1)) : B256).toBytes
    N1.size = memExtSize n 64 32 ∧
    N2.size = memExtSize N1.size p.toNat 32 ∧
    N3.size = memExtSize N2.size (p + 32).toNat 32 ∧
    N4.size = memExtSize N3.size (p + 100).toNat 32 ∧
    N5.size = memExtSize N4.size (p + 132).toNat 32 ∧
    N6.size = memExtSize N5.size (p + 64).toNat 32 ∧
    N7.size = memExtSize N6.size 64 32 ∧
    N8.size = memExtSize N7.size (p + 96).toNat 32 ∧
    N1.size % 32 = 0 ∧ N2.size % 32 = 0 ∧ N3.size % 32 = 0 ∧
    N4.size % 32 = 0 ∧ N5.size % 32 = 0 ∧ N6.size % 32 = 0 ∧
    N7.size % 32 = 0 ∧ N8.size % 32 = 0 ∧
    64 + 32 ≤ N1.size ∧ p.toNat + 32 ≤ N2.size ∧
    (p + 32).toNat + 32 ≤ N3.size ∧ (p + 100).toNat + 32 ≤ N4.size ∧
    (p + 132).toNat + 32 ≤ N5.size ∧ (p + 64).toNat + 32 ≤ N6.size ∧
    64 + 32 ≤ N7.size ∧ (p + 96).toNat + 32 ≤ N8.size ∧
    (safeTransfer_dynamicPayloadMemory M p amount toWord).size =
      memExtSize (memExtSize (memExtSize (memExtSize
        (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
        (memExtSize (memExtSize (memExtSize (memExtSize n 64 32) 64 32)
        p.toNat 32) (p.toNat + 32) 32) 64 32) (p.toNat + 100) 32)
        (p.toNat + 132) 32) 64 32) (p.toNat + 64) 32) 64 32)
        (p.toNat + 96) 32) (p.toNat + 96) 32) 64 32) (p.toNat + 64) 32 ∧
    (safeTransfer_dynamicPayloadMemory M p amount toWord).size % 32 = 0 ∧
    p.toNat + 164 ≤
      (safeTransfer_dynamicPayloadMemory M p amount toWord).size := by
  let N1 := M.write 64 (p + 64).toBytes
  let N2 := N1.write p.toNat (25 : B256).toBytes
  let N3 := N2.write (p + 32).toNat
    (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write (p + 100).toNat
    ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
  let N5 := N4.write (p + 132).toNat amount.toBytes
  let N6 := N5.write (p + 64).toNat (68 : B256).toBytes
  let N7 := N6.write 64 (p + 164).toBytes
  let N8 := N7.write (p + 96).toNat
    ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
      ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
        Bytes.toB256 (N7.read (p + 96).toNat 32).1)) : B256).toBytes
  have z1 : N1.size = memExtSize n 64 32 :=
    Mem.size_write_of_size mem.size mem.n32 (B256.length_toBytes _)
  have a1 : N1.size % 32 = 0 := by
    rw [z1]; exact memExtSize_mod_32 mem.n32
  have c1 : 64 + 32 ≤ N1.size :=
    (Mem.memWord_write_word M 64 (p + 64)).2
  have z2 : N2.size = memExtSize N1.size p.toNat 32 :=
    Mem.size_write_of_size rfl a1 (B256.length_toBytes _)
  have a2 : N2.size % 32 = 0 := by
    rw [z2]; exact memExtSize_mod_32 a1
  have c2 : p.toNat + 32 ≤ N2.size :=
    (Mem.memWord_write_word _ _ _).2
  have z3 : N3.size = memExtSize N2.size (p + 32).toNat 32 :=
    Mem.size_write_of_size rfl a2 (B256.length_toBytes _)
  have a3 : N3.size % 32 = 0 := by
    rw [z3]; exact memExtSize_mod_32 a2
  have c3 : (p + 32).toNat + 32 ≤ N3.size :=
    (Mem.memWord_write_word _ _ _).2
  have z4 : N4.size = memExtSize N3.size (p + 100).toNat 32 :=
    Mem.size_write_of_size rfl a3 (B256.length_toBytes _)
  have a4 : N4.size % 32 = 0 := by
    rw [z4]; exact memExtSize_mod_32 a3
  have c4 : (p + 100).toNat + 32 ≤ N4.size :=
    (Mem.memWord_write_word _ _ _).2
  have z5 : N5.size = memExtSize N4.size (p + 132).toNat 32 :=
    Mem.size_write_of_size rfl a4 (B256.length_toBytes _)
  have a5 : N5.size % 32 = 0 := by
    rw [z5]; exact memExtSize_mod_32 a4
  have c5 : (p + 132).toNat + 32 ≤ N5.size :=
    (Mem.memWord_write_word _ _ _).2
  have z6 : N6.size = memExtSize N5.size (p + 64).toNat 32 :=
    Mem.size_write_of_size rfl a5 (B256.length_toBytes _)
  have a6 : N6.size % 32 = 0 := by
    rw [z6]; exact memExtSize_mod_32 a5
  have c6 : (p + 64).toNat + 32 ≤ N6.size :=
    (Mem.memWord_write_word _ _ _).2
  have z7 : N7.size = memExtSize N6.size 64 32 :=
    Mem.size_write_of_size rfl a6 (B256.length_toBytes _)
  have a7 : N7.size % 32 = 0 := by
    rw [z7]; exact memExtSize_mod_32 a6
  have c7 : 64 + 32 ≤ N7.size :=
    (Mem.memWord_write_word _ _ _).2
  have z8 : N8.size = memExtSize N7.size (p + 96).toNat 32 :=
    Mem.size_write_of_size rfl a7 (B256.length_toBytes _)
  have a8 : N8.size % 32 = 0 := by
    rw [z8]; exact memExtSize_mod_32 a7
  have c8 : (p + 96).toNat + 32 ≤ N8.size :=
    (Mem.memWord_write_word _ _ _).2
  obtain ⟨c32, c64, e100, e132, e164, nat96, nat164, nat228,
    nat32, nat64, nat100, nat132, nat196⟩ := safeTransfer_stageOffset width
  have g56 : N5.size ≤ N6.size := by
    rw [z6]; exact memExtSize_ge _ _ _
  have m7 : N7.size = N6.size := by
    rw [z7]; exact memExtSize_of_le a6 (by omega)
  have hfold14 : memExtSize (memExtSize (memExtSize (memExtSize
      (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
      (memExtSize (memExtSize (memExtSize (memExtSize n 64 32) 64 32)
      p.toNat 32) (p.toNat + 32) 32) 64 32) (p.toNat + 100) 32)
      (p.toNat + 132) 32) 64 32) (p.toNat + 64) 32) 64 32)
      (p.toNat + 96) 32) (p.toNat + 96) 32) 64 32) (p.toNat + 64) 32 = N8.size := by
    rw [←z1]
    rw [show memExtSize N1.size 64 32 = N1.size from
      memExtSize_of_le a1 (by omega)]
    rw [←z2]
    rw [←nat32, ←z3]
    rw [show memExtSize N3.size 64 32 = N3.size from
      memExtSize_of_le a3 (by omega)]
    rw [←nat100, ←z4]
    rw [←nat132, ←z5]
    rw [show memExtSize N5.size 64 32 = N5.size from
      memExtSize_of_le a5 (by omega)]
    rw [←nat64, ←z6]
    rw [show memExtSize N6.size 64 32 = N6.size from
      memExtSize_of_le a6 (by omega)]
    rw [show memExtSize N6.size (p.toNat + 96) 32 = N6.size from
      memExtSize_of_le a6 (by omega)]
    rw [←nat96, ←m7, ←z8]
    rw [show memExtSize N8.size 64 32 = N8.size from
      memExtSize_of_le a8 (by omega)]
    rw [show memExtSize N8.size (p + 64).toNat 32 = N8.size from
      memExtSize_of_le a8 (by omega)]
  have payEq : N8 =
      safeTransfer_dynamicPayloadMemory M p amount toWord := by
    unfold safeTransfer_dynamicPayloadMemory
    simp only [N8, N7, N6, N5, N4, N3, N2, N1]
  have payFold : (safeTransfer_dynamicPayloadMemory M p amount toWord).size =
      memExtSize (memExtSize (memExtSize (memExtSize
        (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
        (memExtSize (memExtSize (memExtSize (memExtSize n 64 32) 64 32)
        p.toNat 32) (p.toNat + 32) 32) 64 32) (p.toNat + 100) 32)
        (p.toNat + 132) 32) 64 32) (p.toNat + 64) 32) 64 32)
        (p.toNat + 96) 32) (p.toNat + 96) 32) 64 32) (p.toNat + 64) 32 := by
    rw [←payEq]; exact hfold14.symm
  have payMod : (safeTransfer_dynamicPayloadMemory M p amount toWord).size % 32 = 0 := by
    rw [←payEq]; exact a8
  have payBound : p.toNat + 164 ≤
      (safeTransfer_dynamicPayloadMemory M p amount toWord).size := by
    rw [←payEq]
    have g56 : N5.size ≤ N6.size := by
      rw [z6]; exact memExtSize_ge _ _ _
    have g67 : N6.size ≤ N7.size := by
      rw [z7]; exact memExtSize_ge _ _ _
    have g78 : N7.size ≤ N8.size := by
      rw [z8]; exact memExtSize_ge _ _ _
    omega
  exact ⟨z1, z2, z3, z4, z5, z6, z7, z8, a1, a2, a3, a4, a5, a6, a7, a8,
    c1, c2, c3, c4, c5, c6, c7, c8, payFold, payMod, payBound⟩

/-- Copy staging sizes for the moving `_safeTransfer` 68-byte copy and merge:
extending the payload fold to the full `safeTransferPreSize`. -/
theorem safeTransfer_copySizes {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    (safeTransfer_dynamicCallMemory M p amount toWord).size =
      safeTransferPreSize n p ∧
    (safeTransfer_dynamicCallMemory M p amount toWord).size % 32 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    payFold, payMod, payBound⟩ :=
    safeTransfer_payloadSizes (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨c32, c64, e100, e132, e164, nat96, nat164, nat228,
    nat32, nat64, nat100, nat132, nat196⟩ := safeTransfer_stageOffset width
  have o196 : (p + 164).toNat + 32 = p.toNat + 196 := by rw [nat164]
  have o228 : (p + 164).toNat + 64 = p.toNat + 228 := by rw [nat164]
  let P := safeTransfer_dynamicPayloadMemory M p amount toWord
  let C1 := P.write (p + 164).toNat
    (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
  let C2 := C1.write ((p + 164).toNat + 32)
    (Bytes.toB256 (C1.read ((p + 96).toNat + 32) 32).1).toBytes
  let mask := B256.bexp 256 (32 - 4) - 1
  let word := ((Bytes.toB256 (C2.read ((p + 96).toNat + 64) 32).1) &&& ~~~mask) |||
    ((Bytes.toB256 (C2.read ((p + 164).toNat + 64) 32).1) &&& mask)
  let W := (C2.read ((p + 164).toNat + 64) 32).2
  let C3 := W.write ((p + 164).toNat + 64) word.toBytes
  have nEq : C3 = safeTransfer_dynamicCallMemory M p amount toWord := by
    unfold safeTransfer_dynamicCallMemory Blanc.Lift.copy68Memory
    simp only [C3, W, word, mask, C2, C1, P]
  have d1 : C1.size = memExtSize P.size (p + 164).toNat 32 :=
    Mem.size_write_of_size rfl payMod (B256.length_toBytes _)
  have b1 : C1.size % 32 = 0 := by
    rw [d1]; exact memExtSize_mod_32 payMod
  have e1c : (p + 164).toNat + 32 ≤ C1.size :=
    (Mem.memWord_write_word _ _ _).2
  have d2 : C2.size = memExtSize C1.size ((p + 164).toNat + 32) 32 :=
    Mem.size_write_of_size rfl b1 (B256.length_toBytes _)
  have b2 : C2.size % 32 = 0 := by
    rw [d2]; exact memExtSize_mod_32 b1
  have e2c : ((p + 164).toNat + 32) + 32 ≤ C2.size :=
    (Mem.memWord_write_word _ _ _).2
  have dW : W.size = memExtSize C2.size ((p + 164).toNat + 64) 32 := rfl
  have bW : W.size % 32 = 0 := by
    rw [dW]; exact memExtSize_mod_32 b2
  have d3 : C3.size = memExtSize W.size ((p + 164).toNat + 64) 32 :=
    Mem.size_write_of_size rfl bW (B256.length_toBytes _)
  have b3 : C3.size % 32 = 0 := by
    rw [d3]; exact memExtSize_mod_32 bW
  have e3c : ((p + 164).toNat + 64) + 32 ≤ C3.size :=
    (Mem.memWord_write_word _ _ _).2
  have hPre : safeTransferPreSize n p =
      memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
        (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
        (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
        (memExtSize (memExtSize (memExtSize (memExtSize n 64 32) 64 32)
        p.toNat 32) (p.toNat + 32) 32) 64 32) (p.toNat + 100) 32)
        (p.toNat + 132) 32) 64 32) (p.toNat + 64) 32) 64 32)
        (p.toNat + 96) 32) (p.toNat + 96) 32) 64 32) (p.toNat + 64) 32)
        (p.toNat + 96) 32) (p.toNat + 164) 32) (p.toNat + 128) 32)
        (p.toNat + 196) 32) (p.toNat + 160) 32) (p.toNat + 228) 32)
        (p.toNat + 228) 32) 64 32 := rfl
  have hfold : memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
      (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
      (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize (memExtSize
      (memExtSize (memExtSize (memExtSize (memExtSize n 64 32) 64 32)
      p.toNat 32) (p.toNat + 32) 32) 64 32) (p.toNat + 100) 32)
      (p.toNat + 132) 32) 64 32) (p.toNat + 64) 32) 64 32)
      (p.toNat + 96) 32) (p.toNat + 96) 32) 64 32) (p.toNat + 64) 32)
      (p.toNat + 96) 32) (p.toNat + 164) 32) (p.toNat + 128) 32)
      (p.toNat + 196) 32) (p.toNat + 160) 32) (p.toNat + 228) 32)
      (p.toNat + 228) 32) 64 32 = C3.size := by
    rw [←payFold]
    have fit15 : p.toNat + 96 + 32 ≤ P.size := by
      have h1 : p.toNat + (96 + 32) ≤ p.toNat + 164 :=
        Nat.add_le_add_left (by decide) _
      have e : p.toNat + 96 + 32 = p.toNat + (96 + 32) := by ac_rfl
      rw [e]
      exact Nat.le_trans h1 payBound
    rw [show memExtSize P.size (p.toNat + 96) 32 = P.size from
      memExtSize_of_le payMod fit15]
    rw [←nat164, ←d1]
    have e1c' : p.toNat + 196 ≤ C1.size := by rw [←o196]; exact e1c
    have fit17 : p.toNat + 128 + 32 ≤ C1.size := by
      have h1 : p.toNat + (128 + 32) ≤ p.toNat + 196 :=
        Nat.add_le_add_left (by decide) _
      have e : p.toNat + 128 + 32 = p.toNat + (128 + 32) := by ac_rfl
      rw [e]
      exact Nat.le_trans h1 e1c'
    rw [show memExtSize C1.size (p.toNat + 128) 32 = C1.size from
      memExtSize_of_le b1 fit17]
    rw [←o196, ←d2]
    have e228' : ((p + 164).toNat + 32) + 32 = p.toNat + 228 := by rw [o196]
    have e2c' : p.toNat + 228 ≤ C2.size := by rw [←e228']; exact e2c
    have fit19 : p.toNat + 160 + 32 ≤ C2.size := by
      have h1 : p.toNat + (160 + 32) ≤ p.toNat + 228 :=
        Nat.add_le_add_left (by decide) _
      have e : p.toNat + 160 + 32 = p.toNat + (160 + 32) := by ac_rfl
      rw [e]
      exact Nat.le_trans h1 e2c'
    rw [show memExtSize C2.size (p.toNat + 160) 32 = C2.size from
      memExtSize_of_le b2 fit19]
    rw [←o228, ←dW]
    rw [←d3]
    have e260' : ((p + 164).toNat + 64) + 32 = p.toNat + 260 := by rw [o228]
    have e3c' : p.toNat + 260 ≤ C3.size := by rw [←e260']; exact e3c
    have fit22 : 64 + 32 ≤ C3.size :=
      Nat.le_trans (Nat.le_trans (by decide) lower)
        (Nat.le_trans (Nat.le_add_right (p.toNat) 260) e3c')
    rw [show memExtSize C3.size 64 32 = C3.size from
      memExtSize_of_le b3 fit22]
  have hsize : (safeTransfer_dynamicCallMemory M p amount toWord).size =
      safeTransferPreSize n p := by
    rw [hPre, hfold, nEq]
  have hmod : (safeTransfer_dynamicCallMemory M p amount toWord).size % 32 = 0 := by
    rw [←nEq]; exact b3
  exact ⟨hsize, hmod⟩

/-- A write outside the zero slot preserves the zero word. Placed locally
while proving the dynamic forward walk; hoist if a second consumer appears. -/
private theorem safeTransfer_zeroWord_write {μ : Mem} {off : Nat} {v : B256}
    (hwf : Mem.Wf μ) (miss : off + 32 ≤ 96 ∨ 128 ≤ off) :
    memWord (μ.write off v.toBytes) 96 = memWord μ 96 := by
  refine memWord_congr (fun j hj => ?_)
  rw [Mem.Reads.write hwf (Mem.reads_data μ) off v.toBytes (96 + j),
    Bytes.getD_writeAt]
  split
  · exfalso
    rw [B256.length_toBytes] at *
    omega
  · exact (Mem.reads_data μ (96 + j)).symm

/-- The moving helper's staged memory keeps the zero slot clear. -/
theorem safeTransfer_dynamicCall_sentinel {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (sentinel : memWord M 96 = 0) :
    memWord (safeTransfer_dynamicCallMemory M p amount toWord) 96 = 0 := by
  obtain ⟨c32, c64, e100, e132, e164, nat96, nat164, nat228,
    nat32, nat64, nat100, nat132, nat196⟩ := safeTransfer_stageOffset width
  let P := safeTransfer_dynamicPayloadMemory M p amount toWord
  let C1 := P.write (p + 164).toNat
    (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
  let C2 := C1.write ((p + 164).toNat + 32)
    (Bytes.toB256 (C1.read ((p + 96).toNat + 32) 32).1).toBytes
  let mask := B256.bexp 256 (32 - 4) - 1
  let word := ((Bytes.toB256 (C2.read ((p + 96).toNat + 64) 32).1) &&& ~~~mask) |||
    ((Bytes.toB256 (C2.read ((p + 164).toNat + 64) 32).1) &&& mask)
  let W := (C2.read ((p + 164).toNat + 64) 32).2
  let C3 := W.write ((p + 164).toNat + 64) word.toBytes
  have nEq : C3 = safeTransfer_dynamicCallMemory M p amount toWord := by
    unfold safeTransfer_dynamicCallMemory Blanc.Lift.copy68Memory
    simp only [C3, W, word, mask, C2, C1, P]
  let A1 := M.write 64 (p + 64).toBytes
  let A2 := A1.write p.toNat (25 : B256).toBytes
  let A3 := A2.write (p + 32).toNat
    (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let A4 := A3.write (p + 100).toNat
    ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
  let A5 := A4.write (p + 132).toNat amount.toBytes
  let A6 := A5.write (p + 64).toNat (68 : B256).toBytes
  let A7 := A6.write 64 (p + 164).toBytes
  have payEq : A7.write (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
          Bytes.toB256 (A7.read (p + 96).toNat 32).1)) : B256).toBytes = P := by
    simp only [P]
    unfold safeTransfer_dynamicPayloadMemory
    simp only [A7, A6, A5, A4, A3, A2, A1]
  have wA1 : Mem.Wf A1 := Mem.Wf.write mem.wf _ _
  have sA1 : memWord A1 96 = memWord M 96 :=
    safeTransfer_zeroWord_write mem.wf (Or.inl (by decide))
  have wA2 : Mem.Wf A2 := Mem.Wf.write wA1 _ _
  have sA2 : memWord A2 96 = memWord A1 96 :=
    safeTransfer_zeroWord_write wA1 (Or.inr lower)
  have wA3 : Mem.Wf A3 := Mem.Wf.write wA2 _ _
  have sA3 : memWord A3 96 = memWord A2 96 :=
    safeTransfer_zeroWord_write wA2
      (Or.inr (by rw [nat32]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  have wA4 : Mem.Wf A4 := Mem.Wf.write wA3 _ _
  have sA4 : memWord A4 96 = memWord A3 96 :=
    safeTransfer_zeroWord_write wA3
      (Or.inr (by rw [nat100]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  have wA5 : Mem.Wf A5 := Mem.Wf.write wA4 _ _
  have sA5 : memWord A5 96 = memWord A4 96 :=
    safeTransfer_zeroWord_write wA4
      (Or.inr (by rw [nat132]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  have wA6 : Mem.Wf A6 := Mem.Wf.write wA5 _ _
  have sA6 : memWord A6 96 = memWord A5 96 :=
    safeTransfer_zeroWord_write wA5
      (Or.inr (by rw [nat64]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  have wA7 : Mem.Wf A7 := Mem.Wf.write wA6 _ _
  have sA7 : memWord A7 96 = memWord A6 96 :=
    safeTransfer_zeroWord_write wA6 (Or.inl (by decide))
  have sA8 : memWord (A7.write (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
          Bytes.toB256 (A7.read (p + 96).toNat 32).1)) : B256).toBytes) 96 =
      memWord A7 96 :=
    safeTransfer_zeroWord_write wA7
      (Or.inr (by rw [nat96]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  have sP : memWord P 96 = memWord A7 96 := by
    rw [←payEq]; exact sA8
  have wP : Mem.Wf P := by
    rw [←payEq]
    exact Mem.Wf.write wA7 _ _
  have wC1 : Mem.Wf C1 := Mem.Wf.write wP _ _
  have sC1 : memWord C1 96 = memWord P 96 :=
    safeTransfer_zeroWord_write wP
      (Or.inr (by rw [nat164]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  have wC2 : Mem.Wf C2 := Mem.Wf.write wC1 _ _
  have sC2 : memWord C2 96 = memWord C1 96 :=
    safeTransfer_zeroWord_write wC1
      (Or.inr (by
        have h : (p + 164).toNat + 32 = p.toNat + 196 := by rw [nat164]
        rw [h]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  have rC2 := Mem.reads_data C2
  have rW : Mem.Reads W C2.data.toList := rC2.extend _ _
  have wW : Mem.Wf W := Mem.Wf.extend wC2 _ _
  have sW : memWord W 96 = memWord C2 96 := by
    show Bytes.toB256 (W.read 96 32).1 = Bytes.toB256 (C2.read 96 32).1
    rw [Mem.Reads.read rW, Mem.Reads.read rC2]
  have wC3 : Mem.Wf C3 := Mem.Wf.write wW _ _
  have sC3 : memWord C3 96 = memWord W 96 :=
    safeTransfer_zeroWord_write wW
      (Or.inr (by
        have h : (p + 164).toNat + 64 = p.toNat + 228 := by rw [nat164]
        rw [h]; exact Nat.le_trans lower (Nat.le_add_right _ _)))
  rw [←nEq, sC3, sW, sC2, sC1, sP, sA7, sA6, sA5, sA4, sA3, sA2, sA1]
  exact sentinel

/-- Pure pointer arithmetic for the moving `_safeTransfer` copy/merge/call
windows: advancing by a full word, and the CALL input-size identity. -/
theorem safeTransfer_stageAdvance {p : B256}
    (width : p.toNat + 260 < 2 ^ 256) :
    32 + (p + 96) = p + 128 ∧ 32 + (p + 128) = p + 160 ∧
      32 + (p + 164) = p + 196 ∧ 32 + (p + 196) = p + 228 ∧
      (68 + (p + 164)) - (p + 164) = 68 := by
  obtain ⟨c32, c64, e100, e132, e164, nat96, nat164, nat228,
    nat32, nat64, nat100, nat132, nat196⟩ := safeTransfer_stageOffset width
  have nat128 : (p + 128).toNat = p.toNat + 128 := by
    have addNat (k : Nat) (hk : k ≤ 260) : (p + k.toB256).toNat = p.toNat + k := by
      rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
        Nat.lo_eq_of_lt (by omega)]
    simpa only [show (128 : Nat).toB256 = (128 : B256) from rfl] using addNat 128 (by decide)
  have nat160 : (p + 160).toNat = p.toNat + 160 := by
    have addNat (k : Nat) (hk : k ≤ 260) : (p + k.toB256).toNat = p.toNat + k := by
      rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
        Nat.lo_eq_of_lt (by omega)]
    simpa only [show (160 : Nat).toB256 = (160 : B256) from rfl] using addNat 160 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply B256.toNat_inj
    rw [B256.toNat_add, nat96, nat128, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  · apply B256.toNat_inj
    rw [B256.toNat_add, nat128, nat160, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  · apply B256.toNat_inj
    rw [B256.toNat_add, nat164, nat196, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  · apply B256.toNat_inj
    rw [B256.toNat_add, nat196, nat228, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
    omega
  · apply B256.toNat_inj
    rw [B256.toNat_sub, B256.toNat_add, nat164,
      show (68 : B256).toNat = 68 from rfl,
      @Nat.lo_eq_of_lt (68 + (p.toNat + 164)) 256 (by omega)]
    rw [show 2 ^ 256 + (68 + (p.toNat + 164)) - (p.toNat + 164) = 2 ^ 256 + 68 by omega,
      Nat.two_pow_add_lo, Nat.lo_eq_of_lt (by decide)]

/-- Pure payload image for the moving `_safeTransfer` initializer: the pointer
words, free-pointer carrier reads, length word and B256 offset equations used
by both the inverse and the exact specialization. -/
theorem safeTransfer_dynamicPayload_facts {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    let N1 := M.write 64 (p + 64).toBytes
    let N2 := N1.write p.toNat (25 : B256).toBytes
    let N3 := N2.write (p + 32).toNat
      (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let N4 := N3.write (p + 100).toNat
      ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let N5 := N4.write (p + 132).toNat amount.toBytes
    let N6 := N5.write (p + 64).toNat (68 : B256).toBytes
    let N7 := N6.write 64 (p + 164).toBytes
    let N8 := N7.write (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
          Bytes.toB256 (N7.read (p + 96).toNat 32).1)) : B256).toBytes
    PtrMem (p + 64) N3.size N3 ∧ PtrMem (p + 64) N5.size N5 ∧
    PtrMem (p + 164) N7.size N7 ∧ PtrMem (p + 164) N8.size N8 ∧
    p.toNat + 164 ≤ N7.size ∧ p.toNat + 164 ≤ N8.size ∧
    Bytes.toB256 (M.read 64 32).1 = p ∧
    Bytes.toB256 (N3.read 64 32).1 = p + 64 ∧
    Bytes.toB256 (N5.read 64 32).1 = p + 64 ∧
    Bytes.toB256 (N8.read 64 32).1 = p + 164 ∧
    Bytes.toB256 (N8.read (p + 64).toNat 32).1 = 68 ∧
    p + 64 + 36 = p + 100 ∧ p + 64 + 68 = p + 132 ∧
    p + 64 + 100 = p + 164 ∧ p + 64 + 32 = p + 96 := by
  obtain ⟨c32, c64, e100, e132, e164, nat96, nat164, nat228,
    nat32, nat64, nat100, nat132, nat196⟩ := safeTransfer_stageOffset width
  have addNat (k : Nat) (hk : k ≤ 164) : (p + k.toB256).toNat = p.toNat + k := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
      Nat.lo_eq_of_lt (by omega)]
  let N1 := M.write 64 (p + 64).toBytes
  let N2 := N1.write p.toNat (25 : B256).toBytes
  let N3 := N2.write (p + 32).toNat
    (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
  let N4 := N3.write (p + 100).toNat
    ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
  let N5 := N4.write (p + 132).toNat amount.toBytes
  let N6 := N5.write (p + 64).toNat (68 : B256).toBytes
  let N7 := N6.write 64 (p + 164).toBytes
  let N8 := N7.write (p + 96).toNat
    ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
      ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
        Bytes.toB256 (N7.read (p + 96).toNat 32).1)) : B256).toBytes
  have h1 : PtrMem (p + 64) N1.size N1 := by
    have hc : PtrMem (p + 64) n N1 := mem.set
    rw [hc.size]; exact hc
  have h2 : PtrMem (p + 64) N2.size N2 := by
    have hc := h1.write p.toNat 25 (Or.inr (by omega))
    rw [hc.size]; exact hc
  have h3 : PtrMem (p + 64) N3.size N3 := by
    have hc := h2.write (p + 32).toNat
      (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256)
      (Or.inr (by rw [nat32]; omega))
    rw [hc.size]; exact hc
  have h4 : PtrMem (p + 64) N4.size N4 := by
    have hc := h3.write (p + 100).toNat
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord)
      (Or.inr (by rw [nat100]; omega))
    rw [hc.size]; exact hc
  have h5 : PtrMem (p + 64) N5.size N5 := by
    have hc := h4.write (p + 132).toNat amount (Or.inr (by rw [nat132]; omega))
    rw [hc.size]; exact hc
  have fit5 : p.toNat + 164 ≤ N5.size := by
    calc
      p.toNat + 164 = (p + 132).toNat + 32 := by rw [nat132]
      _ ≤ N5.size := (Mem.memWord_write_word N4 (p + 132).toNat amount).2
  have h6 : PtrMem (p + 64) N6.size N6 := by
    have hc := h5.write (p + 64).toNat 68 (Or.inr (by rw [nat64]; omega))
    rw [hc.size]; exact hc
  have fit6 : p.toNat + 164 ≤ N6.size :=
    le_trans fit5 (Mem.write_agree N5 (p + 64).toNat (68 : B256).toBytes).1
  have h7 : PtrMem (p + 164) N7.size N7 := by
    have hc : PtrMem (p + 164) N6.size N7 := h6.set
    rw [hc.size]; exact hc
  have fit7 : p.toNat + 164 ≤ N7.size :=
    le_trans fit6 (Mem.write_agree N6 64 (p + 164).toBytes).1
  have h8 : PtrMem (p + 164) N8.size N8 := by
    have hc := h7.write (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1))
      (Or.inr (by rw [nat96]; omega))
    rw [hc.size]; exact hc
  have fit8 : p.toNat + 164 ≤ N8.size :=
    le_trans fit7 (Mem.write_agree N7 (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1)).toBytes).1
  have length6 := (Mem.memWord_write_word N5 (p + 64).toNat 68).1
  have length7 : memWord N7 (p + 64).toNat = 68 := by
    rw [memWord_congr (μ := N6) (fun k hk =>
      (Mem.write_agree N6 64 (p + 164).toBytes).2 ((p + 64).toNat + k)
        (by rw [nat64]; omega) (by rw [nat64, B256.length_toBytes]; right; omega))]
    exact length6
  have length8 : memWord N8 (p + 64).toNat = 68 := by
    rw [memWord_congr (μ := N7) (fun k hk =>
      (Mem.write_agree N7 (p + 96).toNat
        ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 : B256) |||
          ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&& Bytes.toB256 (N7.read (p + 96).toNat 32).1)).toBytes).2 ((p + 64).toNat + k)
        (by rw [nat64]; omega) (by rw [nat64, nat96]; left; omega))]
    exact length7
  have read0 : Bytes.toB256 (M.read 64 32).1 = p := mem.word
  have read3 : Bytes.toB256 (N3.read 64 32).1 = p + 64 := h3.word
  have read5 : Bytes.toB256 (N5.read 64 32).1 = p + 64 := h5.word
  have read8 : Bytes.toB256 (N8.read 64 32).1 = p + 164 := h8.word
  have length8r : Bytes.toB256 (N8.read (p + 64).toNat 32).1 = 68 := length8
  have combine36 : p + 64 + 36 = p + 100 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat100, show (36 : B256).toNat = 36 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have combine68 : p + 64 + 68 = p + 132 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat132, show (68 : B256).toNat = 68 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have combine100 : p + 64 + 100 = p + 164 := by
    have nat164' : (p + 164).toNat = p.toNat + 164 := nat164
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat164', show (100 : B256).toNat = 100 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  have combine32 : p + 64 + 32 = p + 96 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, nat64, nat96, show (32 : B256).toNat = 32 from rfl,
      Nat.lo_eq_of_lt (by omega)]
  exact ⟨h3, h5, h7, h8, fit7, fit8, read0, read3, read5, read8, length8r,
    combine36, combine68, combine100, combine32⟩

/-- Exact moving initializer: specializes `safeTransfer_initialize_exact` to the
free pointer `p`, with the fourteen memory charges over the dynamic staging
memories. -/
private theorem safeTransfer_initialize_dynamic_exact {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (room : R.length ≤ 1008) :
    let N1 := M.write 64 (p + 64).toBytes
    let N2 := N1.write p.toNat (25 : B256).toBytes
    let N3 := N2.write (p + 32).toNat
      (0x7472616e7366657228616464726573732c75696e743235362900000000000000 : B256).toBytes
    let N4 := N3.write (p + 100).toNat
      ((0xffffffffffffffffffffffffffffffffffffffff &&& toWord) : B256).toBytes
    let N5 := N4.write (p + 132).toNat amount.toBytes
    let N6 := N5.write (p + 64).toNat (68 : B256).toBytes
    let N7 := N6.write 64 (p + 164).toBytes
    let N8 := N7.write (p + 96).toNat
      ((0xa9059cbb00000000000000000000000000000000000000000000000000000000 |||
        ((0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff : B256) &&&
          Bytes.toB256 (N7.read (p + 96).toNat 32).1)) : B256).toBytes
    let d1 := gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]
    let d2 := gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]
    let d3 := gVerylow + (St b [] N1 0).extCost [⟨p.toNat, 32⟩]
    let d4 := gVerylow + (St b [] N2 0).extCost [⟨(p + 32).toNat, 32⟩]
    let d5 := gVerylow + (St b [] N3 0).extCost [⟨64, 32⟩]
    let d6 := gVerylow + (St b [] N3 0).extCost [⟨(p + 100).toNat, 32⟩]
    let d7 := gVerylow + (St b [] N4 0).extCost [⟨(p + 132).toNat, 32⟩]
    let d8 := gVerylow + (St b [] N5 0).extCost [⟨64, 32⟩]
    let d9 := gVerylow + (St b [] N5 0).extCost [⟨(p + 64).toNat, 32⟩]
    let d10 := gVerylow + (St b [] N6 0).extCost [⟨64, 32⟩]
    let d11 := gVerylow + (St b [] N7 0).extCost [⟨(p + 96).toNat, 32⟩]
    let d12 := gVerylow + (St b [] N7 0).extCost [⟨(p + 96).toNat, 32⟩]
    let d13 := gVerylow + (St b [] N8 0).extCost [⟨64, 32⟩]
    let d14 := gVerylow + (St b [] N8 0).extCost [⟨(p + 64).toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b ((p + 96) :: (p + 164) :: 68 :: 68 :: (p + 96) :: (p + 164) ::
        (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) N8 G) t_20a4_c57 o →
    SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M
        (G + 199 + d1 + d2 + d3 + d4 + d5 + d6 + d7 + d8 + d9 + d10 + d11 + d12 + d13 + d14))
      t_1fdb_c57 o := by
  dsimp only
  intro continuation
  have raw := safeTransfer_initialize_exact (sevm := sevm) (b := b) (M := M)
    (R := R) (G := G) (o := o) (amount := amount) (toWord := toWord)
    (tokenWord := tokenWord) (rho := rho) room
  dsimp only at raw
  simp only [show (64 : B256).toNat = 64 from rfl] at raw
  obtain ⟨h3, h5, h7, h8, fit7, fit8, read0, read3, read5, read8, length8r,
    combine36, combine68, combine100, combine32⟩ :=
    safeTransfer_dynamicPayload_facts (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨_, _, _, _, _, nat96, _, _,
    _, nat64, _, _, _⟩ :=
    safeTransfer_stageOffset width
  rw [read0, mem.read_self mem.ge,
    show (64 : B256) + p = p + 64 from B256.add_comm,
    show (32 : B256) + p = p + 32 from B256.add_comm] at raw
  rw [read3, h3.read_self h3.ge, combine36, combine68] at raw
  rw [read5, h5.read_self h5.ge,
    show (68 : B256) + ((p + 64) - (p + 64)) = 68 from by rw [B256.sub_self, B256.add_zero],
    combine100, combine32] at raw
  rw [h7.read_self (by rw [nat96]; omega)] at raw
  rw [read8, h8.read_self h8.ge, length8r,
    h8.read_self (by
      have hle : (p + 64).toNat + 32 ≤ p.toNat + 164 := by rw [nat64]; omega
      exact Nat.le_trans hle fit8)] at raw
  exact raw continuation

/-- The payload read at `p + 96` covers itself: standalone rewrite for the
copy specialization. -/
theorem safeTransfer_copyRead96 {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
      (p + 96).toNat 32).2 = safeTransfer_dynamicPayloadMemory M p amount toWord := by
  obtain ⟨_, _, _, h8, _, fit8, _, _, _, _, _, _, _, _, _⟩ :=
    safeTransfer_dynamicPayload_facts (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨_, _, _, _, _, nat96, _, _,
    _, _, _, _, _⟩ := safeTransfer_stageOffset width
  exact h8.read_self (by
    have hle : (p + 96).toNat + 32 ≤ p.toNat + 164 := by rw [nat96]; omega
    exact Nat.le_trans hle fit8)

/-- Nat offset bridges for the copy window, standalone rewrites. -/
private theorem safeTransfer_copyOffsets {p : B256}
    (width : p.toNat + 260 < 2 ^ 256) :
    (p + 128).toNat = (p + 96).toNat + 32 ∧
    (p + 196).toNat = (p + 164).toNat + 32 := by
  obtain ⟨_, _, _, _, _, nat96, nat164, _,
    _, _, _, _, nat196⟩ := safeTransfer_stageOffset width
  have nat128 : (p + 128).toNat = p.toNat + 128 := by
    have addNat128 (k : Nat) (hk : k ≤ 260) : (p + k.toB256).toNat = p.toNat + k := by
      rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega),
        Nat.lo_eq_of_lt (by omega)]
    simpa only [show (128 : Nat).toB256 = (128 : B256) from rfl] using addNat128 128 (by decide)
  exact ⟨by rw [nat128, nat96], by rw [nat196, nat164]⟩

/-- Pointer carrier for the first copy word: standalone `PtrMem` for the
`C1` staging memory (split out so each command fits its heartbeat budget). -/
private theorem safeTransfer_copyPtr128 {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    PtrMem (p + 164)
      (((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
        (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
          (p + 96).toNat 32).1).toBytes).size)
      (((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
        (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
          (p + 96).toNat 32).1).toBytes)) := by
  obtain ⟨_, _, _, h8, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    safeTransfer_dynamicPayload_facts (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨_, _, _, _, _, _, nat164, _, _, _, _, _, _⟩ :=
    safeTransfer_stageOffset width
  have hP : PtrMem (p + 164) (safeTransfer_dynamicPayloadMemory M p amount toWord).size
      (safeTransfer_dynamicPayloadMemory M p amount toWord) := h8
  have hc1raw := hP.write (p + 164).toNat
    (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
      (p + 96).toNat 32).1) (Or.inr (by omega))
  rw [hc1raw.size]; exact hc1raw

/-- Size fit for the second copy read: the `(p + 128)` window lies inside `C1`. -/
private theorem safeTransfer_copyFit128 {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    (p + 128).toNat + 32 ≤
      (((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
        (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
          (p + 96).toNat 32).1).toBytes).size) := by
  obtain ⟨_, _, _, h8, _, fit8, _, _, _, _, _, _, _, _, _⟩ :=
    safeTransfer_dynamicPayload_facts (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨_, _, _, _, _, nat96, _, _,
    _, _, _, _, _⟩ := safeTransfer_stageOffset width
  obtain ⟨o128, _⟩ := safeTransfer_copyOffsets width
  have hP : PtrMem (p + 164) (safeTransfer_dynamicPayloadMemory M p amount toWord).size
      (safeTransfer_dynamicPayloadMemory M p amount toWord) := h8
  have hle : (p + 128).toNat + 32 ≤ p.toNat + 164 := by
    rw [o128, nat96]; omega
  have hle2 : p.toNat + 164 ≤
      (safeTransfer_dynamicPayloadMemory M p amount toWord).size := fit8
  have s : (((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
        (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
          (p + 96).toNat 32).1).toBytes).size) =
      memExtSize (safeTransfer_dynamicPayloadMemory M p amount toWord).size
        (p + 164).toNat 32 :=
    Mem.size_write_of_size rfl hP.n32 (B256.length_toBytes _)
  have ge1 : (safeTransfer_dynamicPayloadMemory M p amount toWord).size ≤
      (((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
        (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
          (p + 96).toNat 32).1).toBytes).size) := by
    rw [s]; exact memExtSize_ge _ _ _
  exact Nat.le_trans (Nat.le_trans hle hle2) ge1

/-- The second copy read covers itself: the rewrite the `convert` residue
exposed (`(C1.read (p + 128).toNat 32).2 = C1`). -/
theorem safeTransfer_copyRead128 {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) :
    (((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
      (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
        (p + 96).toNat 32).1).toBytes).read (p + 128).toNat 32).2 =
    ((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
      (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
        (p + 96).toNat 32).1).toBytes) := by
  have hC1 := safeTransfer_copyPtr128 (amount := amount) (toWord := toWord) mem lower width
  have fit := safeTransfer_copyFit128 (amount := amount) (toWord := toWord) mem lower width
  exact hC1.read_self fit

/-- Exact moving 68-byte copy: specializes `safeTransfer_copy68_exact` to the
staging window `p + 96 → p + 164`, with the four memory charges over the copy
memories. -/
private theorem safeTransfer_copy_dynamic_exact {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (room : R.length ≤ 1004) :
    let P := safeTransfer_dynamicPayloadMemory M p amount toWord
    let C1 := P.write (p + 164).toNat
      (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
    let C2 := C1.write (p + 196).toNat
      (Bytes.toB256 (C1.read (p + 128).toNat 32).1).toBytes
    let eR0 := gVerylow + (St b [] P 0).extCost [⟨(p + 96).toNat, 32⟩]
    let eS0 := gVerylow + (St b [] P 0).extCost [⟨(p + 164).toNat, 32⟩]
    let eR1 := gVerylow + (St b [] C1 0).extCost [⟨(p + 128).toNat, 32⟩]
    let eS1 := gVerylow + (St b [] C1 0).extCost [⟨(p + 196).toNat, 32⟩]
    SFunc.RunExact cert.prog sevm
      (St b ((p + 160) :: (p + 228) :: 4 :: 68 :: (p + 96) :: (p + 164) ::
        (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) C2 G) t_20e1_c57 o →
    SFunc.RunExact cert.prog sevm
      (St b ((p + 96) :: (p + 164) :: 68 :: 68 :: (p + 96) :: (p + 164) ::
        (p + 164) :: (p + 64) :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) P
        (G + 169 + eR0 + eS0 + eR1 + eS1)) t_20a4_c57 o := by
  dsimp only
  intro continuation
  obtain ⟨adv96, adv128, adv164, adv196, _⟩ := safeTransfer_stageAdvance width
  have r96 := safeTransfer_copyRead96 (amount := amount) (toWord := toWord) mem lower width
  have r128 := safeTransfer_copyRead128 (amount := amount) (toWord := toWord) mem lower width
  have raw := safeTransfer_copy68_exact (sevm := sevm) (b := b)
    (R := 68 :: (p + 96) :: (p + 164) :: (p + 164) :: (p + 64) ::
      (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
    (M := safeTransfer_dynamicPayloadMemory M p amount toWord)
    (G := G) (o := o) (src := p + 96) (dst := p + 164)
    (by simp only [List.length_cons]; omega)
  dsimp only at raw
  rw [r96, adv96, adv128, adv164, adv196, r128] at raw
  exact raw continuation


/-! ## The moving `_safeTransfer`: merge, CALL operands, reply and return -/

/-- A 32-byte access charge over a memory of known size, as a cost difference. -/
private theorem safeTransfer_wordCharge {b : Devm} {X : Mem} {s i : Nat} (hs : X.size = s) :
    gVerylow + (St b [] X 0).extCost [⟨i, 32⟩] =
      3 + (calculateMemoryGasCost (memExtSize s i 32) - calculateMemoryGasCost s) := by
  rw [St.extCost_eq hs]
  rfl

/-- Exact moving merge and CALL preparation (`safeTransfer_partialCall_exact` at the staging
window `p + 160 → p + 228`), over any staged memory `C` carrying the free pointer `p + 164`: the
177 literal gas plus the growth of the destination read. -/
private theorem safeTransfer_partial_dynamic_exact {sevm : Sevm} {b : Devm}
    {R : List B256} {C : Mem} {G s : Nat} {o : Outcome} {p token : B256}
    (hC : PtrMem (p + 164) s C) (fit : (p + 160).toNat + 32 ≤ s)
    (width : p.toNat + 260 < 2 ^ 256) (room : R.length ≤ 1010) :
    let mask := B256.bexp 256 (32 - 4) - 1
    let D := (C.read (p + 228).toNat 32).2
    let C3 := D.write (p + 228).toNat
      (((Bytes.toB256 (C.read (p + 160).toNat 32).1) &&& ~~~mask) |||
        ((Bytes.toB256 (C.read (p + 228).toNat 32).1) &&& mask)).toBytes
    SFunc.RunExact cert.prog sevm
      (St b (G.toB256 :: token :: 0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        token :: R) C3 G) (.next (.exec .call) safeTransfer_afterCall) o →
    SFunc.RunExact cert.prog sevm
      (St b ((p + 160) :: (p + 228) :: 4 :: 68 :: (p + 96) :: (p + 164) :: (p + 164) ::
        (p + 64) :: token :: R) C
        (G + 177 + (calculateMemoryGasCost (memExtSize s (p + 228).toNat 32) -
          calculateMemoryGasCost s))) t_20e1_c57 o := by
  dsimp only
  intro continuation
  obtain ⟨_, _, _, _, _, _, nat164, nat228, _, _, _, _, _⟩ := safeTransfer_stageOffset width
  obtain ⟨_, _, _, _, inputSize⟩ := safeTransfer_stageAdvance width
  have rSrc : (C.read (p + 160).toNat 32).2 = C := hC.read_self fit
  let D := (C.read (p + 228).toNat 32).2
  have hD : PtrMem (p + 164) (memExtSize s (p + 228).toNat 32) D := by
    refine ⟨?_, memExtSize_mod_32 hC.n32, hC.wf.extend _ 32, ?_⟩
    · change memExtSize C.size (p + 228).toNat 32 = _
      rw [hC.size]
    · exact MemMatches.of_data_eq (μ := C) (μ' := D) rfl (memExtSize_ge C.size _ 32) hC.map
  have coverD : (p + 228).toNat + 32 ≤ memExtSize s (p + 228).toNat 32 :=
    memExtSize_access_le _ _ _ (by decide)
  let mask := B256.bexp 256 (32 - 4) - 1
  let word := ((Bytes.toB256 (C.read (p + 160).toNat 32).1) &&& ~~~mask) |||
    ((Bytes.toB256 (C.read (p + 228).toNat 32).1) &&& mask)
  have hC3 := hD.write (p + 228).toNat word (Or.inr (by omega))
  rw [memExtSize_of_le hD.n32 coverD] at hC3
  have raw := safeTransfer_partialCall_exact (sevm := sevm) (b := b) (R := R) (M := C) (G := G)
    (o := o) (src := p + 160) (dst := p + 228) (a := 68) (x := p + 96) (y := p + 164)
    (z := p + 164) (w := p + 64) (token := token) room
  dsimp only at raw
  rw [rSrc] at raw
  change SFunc.RunExact cert.prog sevm
    (St b (G.toB256 :: token :: 0 :: Bytes.toB256 ((D.write (p + 228).toNat word.toBytes).read 64 32).1 ::
      ((68 + (p + 164)) - Bytes.toB256 ((D.write (p + 228).toNat word.toBytes).read 64 32).1) ::
      Bytes.toB256 ((D.write (p + 228).toNat word.toBytes).read 64 32).1 :: 0 ::
      (68 + (p + 164)) :: token :: R)
      ((D.write (p + 228).toNat word.toBytes).read 64 32).2 G)
      (.next (.exec .call) safeTransfer_afterCall) o →
    SFunc.RunExact cert.prog sevm
      (St b ((p + 160) :: (p + 228) :: 4 :: 68 :: (p + 96) :: (p + 164) :: (p + 164) ::
        (p + 64) :: token :: R) C
        (G + 165 + (gVerylow + (St b [] C 0).extCost [⟨(p + 160).toNat, 32⟩]) +
          (gVerylow + (St b [] C 0).extCost [⟨(p + 228).toNat, 32⟩]) +
          (gVerylow + (St b [] D 0).extCost [⟨(p + 228).toNat, 32⟩]) +
          (gVerylow + (St b [] (D.write (p + 228).toNat word.toBytes) 0).extCost [⟨64, 32⟩])))
      t_20e1_c57 o at raw
  have fit64 : 64 + 32 ≤ memExtSize s (p + 228).toNat 32 := by
    have := hC3.ge
    omega
  have w64 : Bytes.toB256 ((D.write (p + 228).toNat word.toBytes).read 64 32).1 = p + 164 :=
    hC3.word
  rw [w64, hC3.read_self fit64, inputSize,
    safeTransfer_wordCharge hC.size, memExtSize_of_le hC.n32 fit, Nat.sub_self,
    safeTransfer_wordCharge hC.size,
    safeTransfer_wordCharge hD.size, memExtSize_of_le hD.n32 coverD, Nat.sub_self,
    safeTransfer_wordCharge hC3.size, memExtSize_of_le hC3.n32 fit64, Nat.sub_self] at raw
  have gas : G + 165 + (3 + 0) +
      (3 + (calculateMemoryGasCost (memExtSize s (p + 228).toNat 32) - calculateMemoryGasCost s)) +
      (3 + 0) + (3 + 0) =
      G + 177 + (calculateMemoryGasCost (memExtSize s (p + 228).toNat 32) -
        calculateMemoryGasCost s) := by omega
  rw [gas] at raw
  exact raw continuation

/-- Forward moving reply handling at an arbitrary pointer `q` (the forward dual of
`safeTransfer_afterCall_inv`): the actual returndata, accepted as an optional `bool`, is allocated at `q` as a bytes
array, decoded and the helper returns. -/
private theorem safeTransfer_afterCall_dynamic_exact {sevm : Sevm} {d : Devm}
    {R : List B256} {V : Mem} {G n : Nat} {q endWord token amount toWord tokenWord rho : B256}
    (mem : PtrMem q n V) (lower : 128 ≤ q.toNat) (cover : q.toNat + 32 ≤ n)
    (qwidth : q.toNat + 64 < 2 ^ 256) (sentinel : memWord V 96 = 0)
    (short : d.returnData.length < 2 ^ 256)
    (accepted : d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
      Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0))
    (room : R.length ≤ 1011) :
    let len := d.returnData.length.toB256
    let N1 := V.write 64 (q + ((len + 63) &&& ~~~31)).toBytes
    let N2 := N1.write q.toNat len.toBytes
    let copyCharge := gVerylow + gReturnDataCopy * ceilDiv d.returnData.length 32 +
      (St d [] N2 0).extCost [⟨(q + 32).toNat, d.returnData.length⟩]
    SFunc.RunExact cert.prog sevm
      (St d (1 :: endWord :: token :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        V (G + if d.returnData = [] then 138 else 253 + copyCharge))
      safeTransfer_afterCall
      (.returned (St d R (if d.returnData = [] then V else
        Blanc.Lift.bytesArrayMemory V q d.returnData) G)) := by
  dsimp only
  have q32 : (q + 32).toNat = q.toNat + 32 := by
    rw [B256.toNat_add, show (32 : B256).toNat = 32 from rfl, Nat.lo_eq_of_lt (by omega)]
  have q32' : ((32 : B256) + q).toNat = q.toNat + 32 := by rw [B256.add_comm]; exact q32
  let len := d.returnData.length.toB256
  have freeRead : Bytes.toB256 (V.read 64 32).1 = q := mem.word
  have freeMemory : (V.read 64 32).2 = V := mem.read_self (by have := mem.ge; omega)
  have cRead : gVerylow + (St d [] V 0).extCost [⟨64, 32⟩] = 3 := by
    rw [St.extCost_eq mem.size, memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  by_cases empty : d.returnData = []
  · have zeroLen : len = 0 := by dsimp only [len]; rw [empty]; rfl
    have decoded := safeTransfer_success_exact (R := R) (sevm := sevm) (b := d) (M := V)
      (G := G) (x := len) (ptr := 96) (success := 1) (y := 96) (z := 0)
      (value := amount) (toWord := toWord) (tokenWord := tokenWord) (ρ := rho)
      (by decide) (Or.inl sentinel) (by omega)
    have read96 : (V.read (96 : B256).toNat 32).2 = V := mem.read_self (by
      change 96 + 32 ≤ n; omega)
    have c96 : gVerylow + (St d [] V 0).extCost [⟨(96 : B256).toNat, 32⟩] = 3 := by
      rw [St.extCost_eq mem.size, memExtSize_of_le mem.n32 (by change 96 + 32 ≤ n; omega),
        Nat.sub_self]
      rfl
    change Bytes.toB256 (V.read (96 : B256).toNat 32).1 = 0 at sentinel
    dsimp only at decoded
    simp only [read96, sentinel, ite_true, c96] at decoded
    have post := safeTransfer_afterCall_exact (R := R) (sevm := sevm) (b := d) (M := V)
      (G := G + 95) (o := .returned (St d R V G)) (success := 1) (endWord := endWord)
      (token := token) (y := 96) (z := 0) (value := amount) (toWord := toWord)
      (tokenWord := tokenWord) (ρ := rho) room
    dsimp only at post
    rw [show d.returnData.length.toB256 = 0 from zeroLen, ite_eq_left rfl] at post
    simp only [ite_true] at post
    rw [zeroLen, show G + 24 + 3 + 33 + 35 = G + 95 by omega] at decoded
    have result := post decoded
    simpa only [ite_eq_left empty, show G + 95 + 34 + 9 = G + 138 by omega] using result
  · obtain ⟨enough, head⟩ := accepted.resolve_left empty
    have nonzero : len ≠ 0 := by
      intro eq
      have lengthWord := B256.toNat_toB256_of_lt short
      change len.toNat = d.returnData.length at lengthWord
      rw [eq] at lengthWord
      change 0 = d.returnData.length at lengthWord
      omega
    let A := Blanc.Lift.bytesArrayMemory V q d.returnData
    have images := Blanc.Lift.bytesArrayMemory_image (bytes := d.returnData) mem (by omega) cover
      (by omega)
    have carrier : PtrMem (q + ((len + 63) &&& ~~~31))
        (memExtSize n (q + 32).toNat d.returnData.length) A := images.1
    have big : q.toNat + 64 ≤ memExtSize n (q + 32).toNat d.returnData.length := by
      have h := memExtSize_access_le n (q + 32).toNat d.returnData.length (by omega)
      omega
    have readQ : (A.read q.toNat 32).2 = A := carrier.read_self (by omega)
    have readQ32 : (A.read ((32 : B256) + q).toNat 32).2 = A :=
      carrier.read_self (by rw [q32']; omega)
    have lengthWord : Bytes.toB256 (A.read q.toNat 32).1 = len := images.2.1
    have headWord : Bytes.toB256 (A.read ((32 : B256) + q).toNat 32).1 ≠ 0 := by
      rw [show ((32 : B256) + q) = q + 32 from B256.add_comm, images.2.2 enough]
      exact head
    have decoderAccepted : Bytes.toB256 (A.read q.toNat 32).1 = 0 ∨
        (32 ≤ (Bytes.toB256 ((A.read q.toNat 32).2.read q.toNat 32).1).toNat ∧
          Bytes.toB256 (((A.read q.toNat 32).2.read q.toNat 32).2.read
            ((32 : B256) + q).toNat 32).1 ≠ 0) := by
      rw [readQ, readQ, lengthWord, B256.toNat_toB256_of_lt short]
      exact Or.inr ⟨enough, headWord⟩
    have cQ : gVerylow + (St d [] A 0).extCost [⟨q.toNat, 32⟩] = 3 := by
      rw [St.extCost_eq carrier.size, memExtSize_of_le carrier.n32 (by omega), Nat.sub_self]
      rfl
    have cQ32 : gVerylow + (St d [] A 0).extCost [⟨((32 : B256) + q).toNat, 32⟩] = 3 := by
      rw [St.extCost_eq carrier.size, memExtSize_of_le carrier.n32 (by rw [q32']; omega),
        Nat.sub_self]
      rfl
    have decoded := safeTransfer_success_exact (R := R) (sevm := sevm) (b := d) (M := A)
      (G := G) (x := len) (ptr := q) (success := 1) (y := 96) (z := 0)
      (value := amount) (toWord := toWord) (tokenWord := tokenWord) (ρ := rho)
      (by decide) decoderAccepted (by omega)
    dsimp only at decoded
    simp only [readQ, lengthWord, ite_eq_right nonzero, readQ32, cQ, cQ32] at decoded
    have N1mem : PtrMem (q + ((len + 63) &&& ~~~31)) n
        (V.write 64 (q + ((len + 63) &&& ~~~31)).toBytes) := mem.set
    have post := safeTransfer_afterCall_exact (R := R) (sevm := sevm) (b := d) (M := V)
      (G := G + 146) (o := .returned (St d R A G)) (success := 1) (endWord := endWord)
      (token := token) (y := 96) (z := 0) (value := amount) (toWord := toWord)
      (tokenWord := tokenWord) (ρ := rho) room
    dsimp only at post
    have cLen : gVerylow + (St d [] (V.write 64 (q + ((len + 63) &&& ~~~31)).toBytes) 0).extCost
        [⟨q.toNat, 32⟩] = 3 := by
      rw [St.extCost_eq N1mem.size, memExtSize_of_le N1mem.n32 (by omega), Nat.sub_self]
      rfl
    dsimp only [len] at nonzero cLen
    simp only [ite_eq_right nonzero, freeRead, freeMemory, cRead,
      cLen, Bytes.sliceD_zero_length rfl, B256.toNat_toB256_of_lt short] at post
    rw [show G + 24 + 3 + (78 + 3 + 3) + 35 = G + 146 by omega] at decoded
    have result := post decoded
    let copyCharge := gVerylow + gReturnDataCopy * ceilDiv d.returnData.length 32 +
      (St d [] ((V.write 64 (q + ((len + 63) &&& ~~~31)).toBytes).write q.toNat len.toBytes) 0).extCost
        [⟨(q + 32).toNat, d.returnData.length⟩]
    change SFunc.RunExact cert.prog sevm
      (St d (1 :: endWord :: token :: 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        V (G + 146 + 34 + (64 + 3 + 3 + 3 + copyCharge))) safeTransfer_afterCall
      (.returned (St d R A G)) at result
    rw [show G + 146 + 34 + (64 + 3 + 3 + 3 + copyCharge) = G + (253 + copyCharge) by omega] at result
    simpa only [ite_eq_right empty] using result

/-! ## Closed charges of the moving pre-CALL stages -/

/-- A 32-byte access charge as a cost difference over the memory's own size. -/
private theorem safeTransfer_wordCharge' {b : Devm} {X : Mem} {i : Nat} :
    gVerylow + (St b [] X 0).extCost [⟨i, 32⟩] =
      3 + (calculateMemoryGasCost (memExtSize X.size i 32) - calculateMemoryGasCost X.size) :=
  safeTransfer_wordCharge rfl

/-- The fourteen initializer charges telescope to the payload image's growth. -/
private theorem safeTransfer_initGas {b : Devm} {M N1 N2 N3 N4 N5 N6 N7 N8 Q : Mem} {G : Nat}
    {p : B256} (aM : M.size % 32 = 0) (geM : 96 ≤ M.size)
    (z1 : N1.size = memExtSize M.size 64 32)
    (z2 : N2.size = memExtSize N1.size p.toNat 32)
    (z3 : N3.size = memExtSize N2.size (p + 32).toNat 32) (a3 : N3.size % 32 = 0)
    (z4 : N4.size = memExtSize N3.size (p + 100).toNat 32)
    (z5 : N5.size = memExtSize N4.size (p + 132).toNat 32) (a5 : N5.size % 32 = 0)
    (c5 : (p + 132).toNat + 32 ≤ N5.size)
    (z6 : N6.size = memExtSize N5.size (p + 64).toNat 32)
    (c6 : (p + 64).toNat + 32 ≤ N6.size)
    (z7 : N7.size = memExtSize N6.size 64 32) (a7 : N7.size % 32 = 0)
    (z8 : N8.size = memExtSize N7.size (p + 96).toNat 32) (a8 : N8.size % 32 = 0)
    (nat96 : (p + 96).toNat = p.toNat + 96) (nat132 : (p + 132).toNat = p.toNat + 132)
    (hQ : N8 = Q) :
    G + 199 + (gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]) +
      (gVerylow + (St b [] M 0).extCost [⟨64, 32⟩]) +
      (gVerylow + (St b [] N1 0).extCost [⟨p.toNat, 32⟩]) +
      (gVerylow + (St b [] N2 0).extCost [⟨(p + 32).toNat, 32⟩]) +
      (gVerylow + (St b [] N3 0).extCost [⟨64, 32⟩]) +
      (gVerylow + (St b [] N3 0).extCost [⟨(p + 100).toNat, 32⟩]) +
      (gVerylow + (St b [] N4 0).extCost [⟨(p + 132).toNat, 32⟩]) +
      (gVerylow + (St b [] N5 0).extCost [⟨64, 32⟩]) +
      (gVerylow + (St b [] N5 0).extCost [⟨(p + 64).toNat, 32⟩]) +
      (gVerylow + (St b [] N6 0).extCost [⟨64, 32⟩]) +
      (gVerylow + (St b [] N7 0).extCost [⟨(p + 96).toNat, 32⟩]) +
      (gVerylow + (St b [] N7 0).extCost [⟨(p + 96).toNat, 32⟩]) +
      (gVerylow + (St b [] N8 0).extCost [⟨64, 32⟩]) +
      (gVerylow + (St b [] N8 0).extCost [⟨(p + 64).toNat, 32⟩]) =
    G + 241 + (calculateMemoryGasCost Q.size - calculateMemoryGasCost M.size) := by
  subst hQ
  have g2 : N1.size ≤ N2.size := by rw [z2]; exact memExtSize_ge _ _ _
  have g3 : N2.size ≤ N3.size := by rw [z3]; exact memExtSize_ge _ _ _
  have g4 : N3.size ≤ N4.size := by rw [z4]; exact memExtSize_ge _ _ _
  have g5 : N4.size ≤ N5.size := by rw [z5]; exact memExtSize_ge _ _ _
  have g6 : N5.size ≤ N6.size := by rw [z6]; exact memExtSize_ge _ _ _
  have g7 : N6.size ≤ N7.size := by rw [z7]; exact memExtSize_ge _ _ _
  have g8 : N7.size ≤ N8.size := by rw [z8]; exact memExtSize_ge _ _ _
  have r7 : (p + 96).toNat + 32 ≤ N7.size := by omega
  have r8 : (p + 64).toNat + 32 ≤ N8.size := by omega
  have e1 : memExtSize M.size 64 32 = M.size := memExtSize_of_le aM (by omega)
  have g1 : N1.size = M.size := by rw [z1, e1]
  have e5 : memExtSize N3.size 64 32 = N3.size := memExtSize_of_le a3 (by omega)
  have e8 : memExtSize N5.size 64 32 = N5.size := memExtSize_of_le a5 (by omega)
  have e11 : memExtSize N7.size (p + 96).toNat 32 = N7.size := memExtSize_of_le a7 r7
  have e13 : memExtSize N8.size 64 32 = N8.size := memExtSize_of_le a8 (by omega)
  have e14 : memExtSize N8.size (p + 64).toNat 32 = N8.size := memExtSize_of_le a8 r8
  simp only [safeTransfer_wordCharge']
  rw [e1, ← z2, ← z3, e5, ← z4, ← z5, e8, ← z6, ← z7, e11, e13, e14]
  rw [e11] at z8
  rw [z8]
  have m2 := calculateMemoryGasCost_mono g2
  have m3 := calculateMemoryGasCost_mono g3
  have m4 := calculateMemoryGasCost_mono g4
  have m5 := calculateMemoryGasCost_mono g5
  have m6 := calculateMemoryGasCost_mono g6
  have m7 := calculateMemoryGasCost_mono g7
  rw [g1] at m2 ⊢
  generalize calculateMemoryGasCost M.size = cM at *
  generalize calculateMemoryGasCost N2.size = c2 at *
  generalize calculateMemoryGasCost N3.size = c3 at *
  generalize calculateMemoryGasCost N4.size = c4 at *
  generalize calculateMemoryGasCost N5.size = c5 at *
  generalize calculateMemoryGasCost N6.size = c6 at *
  generalize calculateMemoryGasCost N7.size = c7 at *
  omega

/-- The four copy charges telescope to the copy's growth. -/
private theorem safeTransfer_copyGas {b : Devm} {P C1 C2 : Mem} {G : Nat} {p : B256}
    (aP : P.size % 32 = 0) (rP : (p + 96).toNat + 32 ≤ P.size)
    (z1 : C1.size = memExtSize P.size (p + 164).toNat 32) (a1 : C1.size % 32 = 0)
    (r1 : (p + 128).toNat + 32 ≤ C1.size)
    (z2 : C2.size = memExtSize C1.size (p + 196).toNat 32) :
    G + 169 + (gVerylow + (St b [] P 0).extCost [⟨(p + 96).toNat, 32⟩]) +
      (gVerylow + (St b [] P 0).extCost [⟨(p + 164).toNat, 32⟩]) +
      (gVerylow + (St b [] C1 0).extCost [⟨(p + 128).toNat, 32⟩]) +
      (gVerylow + (St b [] C1 0).extCost [⟨(p + 196).toNat, 32⟩]) =
    G + 181 + (calculateMemoryGasCost C2.size - calculateMemoryGasCost P.size) := by
  have g1 : P.size ≤ C1.size := by rw [z1]; exact memExtSize_ge _ _ _
  have g2 : C1.size ≤ C2.size := by rw [z2]; exact memExtSize_ge _ _ _
  have eR0 : memExtSize P.size (p + 96).toNat 32 = P.size := memExtSize_of_le aP rP
  have eR1 : memExtSize C1.size (p + 128).toNat 32 = C1.size := memExtSize_of_le a1 r1
  simp only [safeTransfer_wordCharge']
  rw [eR0, ← z1, eR1, ← z2]
  have m1 := calculateMemoryGasCost_mono g1
  have m2 := calculateMemoryGasCost_mono g2
  generalize calculateMemoryGasCost P.size = c0 at *
  generalize calculateMemoryGasCost C1.size = c1 at *
  generalize calculateMemoryGasCost C2.size = c2 at *
  omega

/-- The merged CALL image keeps the moved free pointer over the read-extended allocation. -/
private theorem safeTransfer_mergePtr {C : Mem} {s : Nat} {p : B256}
    (hC : PtrMem (p + 164) s C) (width : p.toNat + 260 < 2 ^ 256) :
    let mask := B256.bexp 256 (32 - 4) - 1
    PtrMem (p + 164) (memExtSize s (p + 228).toNat 32)
      ((C.read (p + 228).toNat 32).2.write (p + 228).toNat
        (((Bytes.toB256 (C.read (p + 160).toNat 32).1) &&& ~~~mask) |||
          ((Bytes.toB256 (C.read (p + 228).toNat 32).1) &&& mask)).toBytes) := by
  dsimp only
  obtain ⟨_, _, _, _, _, _, nat164, nat228, _, _, _, _, _⟩ := safeTransfer_stageOffset width
  let D := (C.read (p + 228).toNat 32).2
  have hD : PtrMem (p + 164) (memExtSize s (p + 228).toNat 32) D := by
    refine ⟨?_, memExtSize_mod_32 hC.n32, hC.wf.extend _ 32, ?_⟩
    · change memExtSize C.size (p + 228).toNat 32 = _
      rw [hC.size]
    · exact MemMatches.of_data_eq (μ := C) (μ' := D) rfl (memExtSize_ge C.size _ 32) hC.map
  have coverD : (p + 228).toNat + 32 ≤ memExtSize s (p + 228).toNat 32 :=
    memExtSize_access_le _ _ _ (by decide)
  have h := hD.write (p + 228).toNat
    (((Bytes.toB256 (C.read (p + 160).toNat 32).1) &&& ~~~(B256.bexp 256 (32 - 4) - 1)) |||
      ((Bytes.toB256 (C.read (p + 228).toNat 32).1) &&& (B256.bexp 256 (32 - 4) - 1)))
    (Or.inr (by omega))
  rw [memExtSize_of_le hD.n32 coverD] at h
  exact h

/-- The staged copy and merge images are the moving CALL memory. -/
theorem safeTransfer_callMemory_eq {M : Mem} {p amount toWord : B256}
    (width : p.toNat + 260 < 2 ^ 256) :
    let P := safeTransfer_dynamicPayloadMemory M p amount toWord
    let C1 := P.write (p + 164).toNat (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
    let C2 := C1.write (p + 196).toNat (Bytes.toB256 (C1.read (p + 128).toNat 32).1).toBytes
    let mask := B256.bexp 256 (32 - 4) - 1
    (C2.read (p + 228).toNat 32).2.write (p + 228).toNat
        (((Bytes.toB256 (C2.read (p + 160).toNat 32).1) &&& ~~~mask) |||
          ((Bytes.toB256 (C2.read (p + 228).toNat 32).1) &&& mask)).toBytes =
      safeTransfer_dynamicCallMemory M p amount toWord := by
  obtain ⟨_, _, _, _, _, nat96, nat164, nat228, _, _, _, _, nat196⟩ := safeTransfer_stageOffset width
  obtain ⟨o128, _⟩ := safeTransfer_copyOffsets width
  have o196 : (p + 196).toNat = (p + 164).toNat + 32 := by rw [nat196, nat164]
  have o228 : (p + 228).toNat = (p + 164).toNat + 64 := by rw [nat228, nat164]
  have o160 : (p + 160).toNat = (p + 96).toNat + 64 := by
    rw [nat96, B256.toNat_add, show (160 : B256).toNat = 160 from rfl, Nat.lo_eq_of_lt (by omega)]
  dsimp only
  rw [o128, o196, o228, o160]
  rfl

/-- **Moving pre-CALL forward construction**: initializer, 68-byte copy and merge, ending at the
primitive `CALL` over the staged CALL memory, with the closed charge `safeTransferPreCharge`. -/
private theorem safeTransfer_dynamicPrepare_closed {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome}
    {p amount toWord tokenWord rho : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (room : R.length ≤ 1000)
    (continuation : SFunc.RunExact cert.prog sevm
      (St b (G.toB256 :: (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
        (tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
        96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R)
        (safeTransfer_dynamicCallMemory M p amount toWord) G)
      (.next (.exec .call) safeTransfer_afterCall) o) :
    SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M (G + safeTransferPreCharge n p))
      t_1fdb_c57 o := by
  obtain ⟨_, _, _, _, _, nat96, nat164, nat228, _, nat64, _, nat132, nat196⟩ :=
    safeTransfer_stageOffset width
  obtain ⟨o128, _⟩ := safeTransfer_copyOffsets width
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8, a1, a2, a3, a4, a5, a6, a7, a8,
    c1, c2, c3, c4, c5, c6, c7, c8, payFold, payMod, payBound⟩ :=
    safeTransfer_payloadSizes (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨preEq, _⟩ := safeTransfer_copySizes (amount := amount) (toWord := toWord) mem lower width
  let P := safeTransfer_dynamicPayloadMemory M p amount toWord
  let C1 := P.write (p + 164).toNat (Bytes.toB256 (P.read (p + 96).toNat 32).1).toBytes
  let C2 := C1.write (p + 196).toNat (Bytes.toB256 (C1.read (p + 128).toNat 32).1).toBytes
  have hC1 : PtrMem (p + 164) C1.size C1 :=
    safeTransfer_copyPtr128 (amount := amount) (toWord := toWord) mem lower width
  have fit128 : (p + 128).toNat + 32 ≤ C1.size :=
    safeTransfer_copyFit128 (amount := amount) (toWord := toWord) mem lower width
  have hC2 := hC1.write (p + 196).toNat (Bytes.toB256 (C1.read (p + 128).toNat 32).1)
    (Or.inr (by omega))
  have cover2 : (p + 196).toNat + 32 ≤ memExtSize C1.size (p + 196).toNat 32 :=
    memExtSize_access_le _ _ _ (by decide)
  have fit2 : (p + 160).toNat + 32 ≤ memExtSize C1.size (p + 196).toNat 32 := by
    have h160 : (p + 160).toNat = p.toNat + 160 := by
      rw [B256.toNat_add, show (160 : B256).toNat = 160 from rfl, Nat.lo_eq_of_lt (by omega)]
    omega
  have part := safeTransfer_partial_dynamic_exact (sevm := sevm) (b := b)
    (R := 96 :: 0 :: amount :: toWord :: tokenWord :: rho :: R) (G := G) (o := o)
    (token := tokenWord &&& 0xffffffffffffffffffffffffffffffffffffffff) hC2 fit2 width
    (by simp only [List.length_cons]; omega)
  have ceq := safeTransfer_callMemory_eq (M := M) (amount := amount) (toWord := toWord) width
  dsimp only at part ceq
  rw [ceq] at part
  have run1 := part continuation
  have copy := safeTransfer_copy_dynamic_exact (sevm := sevm) (b := b) (R := R)
    (G := G + 177 + (calculateMemoryGasCost (memExtSize (memExtSize C1.size (p + 196).toNat 32)
      (p + 228).toNat 32) - calculateMemoryGasCost (memExtSize C1.size (p + 196).toNat 32)))
    (o := o) (amount := amount) (toWord := toWord) (tokenWord := tokenWord) (rho := rho)
    mem lower width (by omega)
  dsimp only at copy
  have run2 := copy run1
  have run3 := safeTransfer_initialize_dynamic_exact (sevm := sevm) (b := b) (R := R)
    (o := o) (amount := amount) (toWord := toWord) (tokenWord := tokenWord) (rho := rho)
    mem lower width (by omega) run2
  rw [← mem.size] at z1
  have aM : M.size % 32 = 0 := by rw [mem.size]; exact mem.n32
  have geM : 96 ≤ M.size := by rw [mem.size]; exact mem.ge
  have finish : ∀ {k : Nat}, SFunc.RunExact cert.prog sevm
      (St b (amount :: toWord :: tokenWord :: rho :: R) M k) t_1fdb_c57 o →
      k = G + safeTransferPreCharge n p →
      SFunc.RunExact cert.prog sevm
        (St b (amount :: toWord :: tokenWord :: rho :: R) M (G + safeTransferPreCharge n p))
        t_1fdb_c57 o := fun r e => e ▸ r
  refine finish run3 ?_
  rw [safeTransfer_initGas (Q := safeTransfer_dynamicPayloadMemory M p amount toWord) aM geM z1 z2 z3 a3 z4 z5 a5 c5 z6 c6 z7 a7 z8 a8 nat96 nat132 rfl]
  have zC1 : C1.size = memExtSize P.size (p + 164).toNat 32 :=
    Mem.size_write_of_size rfl payMod (B256.length_toBytes _)
  rw [safeTransfer_copyGas payMod (by omega) zC1 hC1.n32 fit128 hC2.size]
  have hC3 := safeTransfer_mergePtr hC2 width
  dsimp only at hC3
  rw [ceq] at hC3
  have gP : P.size ≤ C1.size := by rw [zC1]; exact memExtSize_ge _ _ _
  have gC2 : C1.size ≤ memExtSize C1.size (p + 196).toNat 32 := memExtSize_ge _ _ _
  have gE : memExtSize C1.size (p + 196).toNat 32 ≤
      memExtSize (memExtSize C1.size (p + 196).toNat 32) (p + 228).toNat 32 := memExtSize_ge _ _ _
  have gM : M.size ≤ P.size := by
    rw [mem.size]
    change n ≤ (safeTransfer_dynamicPayloadMemory M p amount toWord).size
    rw [payFold]
    iterate 14 refine Nat.le_trans ?_ (memExtSize_ge _ _ _)
    exact Nat.le_refl n
  unfold safeTransferPreCharge
  rw [← preEq, hC3.size, ← mem.size, hC2.size]
  have m1 := calculateMemoryGasCost_mono gM
  have m2 := calculateMemoryGasCost_mono gP
  have m3 := calculateMemoryGasCost_mono gC2
  have m4 := calculateMemoryGasCost_mono gE
  generalize calculateMemoryGasCost M.size = cM at *
  generalize calculateMemoryGasCost P.size = cP at *
  generalize calculateMemoryGasCost C1.size = c1 at *
  generalize calculateMemoryGasCost (memExtSize C1.size (p + 196).toNat 32) = c2 at *
  generalize calculateMemoryGasCost (memExtSize (memExtSize C1.size (p + 196).toNat 32)
    (p + 228).toNat 32) = c3 at *
  omega

/-- The moving CALL memory carries the moved free pointer `p + 164` over its whole staged size. -/
theorem safeTransfer_callMemory_ptr {M : Mem} {p amount toWord : B256} {n : Nat}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    PtrMem (p + 164) (safeTransfer_dynamicCallMemory M p amount toWord).size
      (safeTransfer_dynamicCallMemory M p amount toWord) := by
  have hC1 := safeTransfer_copyPtr128 (amount := amount) (toWord := toWord) mem lower width
  have fit128 := safeTransfer_copyFit128 (amount := amount) (toWord := toWord) mem lower width
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, nat196⟩ := safeTransfer_stageOffset width
  have hC2 := hC1.write (p + 196).toNat
    (Bytes.toB256 ((((safeTransfer_dynamicPayloadMemory M p amount toWord).write (p + 164).toNat
      (Bytes.toB256 ((safeTransfer_dynamicPayloadMemory M p amount toWord).read
        (p + 96).toNat 32).1).toBytes)).read (p + 128).toNat 32).1) (Or.inr (by omega))
  have hC3 := safeTransfer_mergePtr hC2 width
  have ceq := safeTransfer_callMemory_eq (M := M) (amount := amount) (toWord := toWord) width
  dsimp only at hC3 ceq
  rw [ceq] at hC3
  rw [hC3.size]
  exact hC3

/-- The post-CALL charge is the after-CALL allocation's charge over the staged CALL memory. -/
private theorem safeTransfer_postCharge_eq {M : Mem} {p amount toWord : B256} {n : Nat}
    {b : Devm} {reply : Bytes}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256) :
    let V := safeTransfer_dynamicCallMemory M p amount toWord
    let len := reply.length.toB256
    let N2 := (V.write 64 ((p + 164) + ((len + 63) &&& ~~~31)).toBytes).write (p + 164).toNat
      len.toBytes
    safeTransferPostCharge n p reply = if reply = [] then 138 else
      253 + (gVerylow + gReturnDataCopy * ceilDiv reply.length 32 +
        (St b [] N2 0).extCost [⟨((p + 164) + 32).toNat, reply.length⟩]) := by
  dsimp only
  obtain ⟨_, _, _, _, _, _, nat164, _, _, _, _, _, nat196⟩ := safeTransfer_stageOffset width
  obtain ⟨_, _, adv164, _, _⟩ := safeTransfer_stageAdvance width
  obtain ⟨preEq, _⟩ := safeTransfer_copySizes (amount := amount) (toWord := toWord) mem lower width
  have hV := safeTransfer_callMemory_ptr (amount := amount) (toWord := toWord) mem lower width
  have fitV := safeTransfer_dynamicCall_fit (amount := amount) (toWord := toWord) mem lower width
  by_cases empty : reply = []
  · rw [ite_eq_left empty]
    subst empty
    rfl
  · rw [ite_eq_right empty]
    unfold safeTransferPostCharge
    rw [ite_eq_right empty]
    have h1 := hV.set (q := (p + 164) + ((reply.length.toB256 + 63) &&& ~~~31))
    have h2 := h1.write (p + 164).toNat reply.length.toB256 (Or.inr (by omega))
    have e2 : memExtSize (safeTransfer_dynamicCallMemory M p amount toWord).size (p + 164).toNat 32 =
        (safeTransfer_dynamicCallMemory M p amount toWord).size :=
      memExtSize_of_le hV.n32 (by omega)
    rw [e2] at h2
    rw [St.extCost_eq h2.size]
    unfold safeTransferPostSize
    rw [← preEq]
    dsimp only
    have e64 : memExtSize (safeTransfer_dynamicCallMemory M p amount toWord).size 64 32 =
        (safeTransfer_dynamicCallMemory M p amount toWord).size :=
      memExtSize_of_le hV.n32 (by have := hV.ge; omega)
    have e164 : memExtSize (safeTransfer_dynamicCallMemory M p amount toWord).size
        (p.toNat + 164) 32 = (safeTransfer_dynamicCallMemory M p amount toWord).size :=
      memExtSize_of_le hV.n32 (by omega)
    have q196 : ((p + 164) + 32).toNat = p.toNat + 196 := by
      rw [show (p + 164) + 32 = (32 : B256) + (p + 164) from B256.add_comm, adv164, nat196]
    rw [e64, e164, q196]

/-- **The moving `_safeTransfer` forward theorem.**  At any free pointer `p` (with the zero slot
clear and the staging area representable), the helper reaches its token `CALL` after exactly
`safeTransferPreCharge n p` gas with the canonical operands and staged memory, and from that
`CALL`'s successful, accepted reply with residual `G + safeTransferPostCharge n p reply` returns to its
caller with the transfer memory and gas `G`.  This discharges the cross-host hypothesis
`SwapSafeTransferForward` for the actual charge functions. -/
theorem safeTransfer_dynamic_forward :
    SwapSafeTransferForward safeTransferPreCharge safeTransferPostCharge := by
  intro sevm b d L M n callGas G p amount toWord token rho fork mem sentinel lower width room
    call success accepted returnedGas
  obtain ⟨_, _, _, _, _, _, nat164, _, _, _, _, _, _⟩ := safeTransfer_stageOffset width
  let V := safeTransfer_dynamicCallMemory M p amount toWord
  have hV : PtrMem (p + 164) V.size V :=
    safeTransfer_callMemory_ptr (amount := amount) (toWord := toWord) mem lower width
  have fitV : p.toNat + 260 ≤ V.size :=
    safeTransfer_dynamicCall_fit (amount := amount) (toWord := toWord) mem lower width
  have sentV : memWord V 96 = 0 :=
    safeTransfer_dynamicCall_sentinel (amount := amount) (toWord := toWord) mem lower width sentinel
  let S := callGas.toB256 :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
    0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
    (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
    96 :: 0 :: amount :: toWord :: token :: rho :: L
  have raw : Ninst.Run sevm (St b S V callGas) (.exec .call) d := by
    obtain ⟨xl, filled, step⟩ := call
    exact ⟨xl, filled, 0, step 0⟩
  have operands : S <<+ (St b S V callGas).stack := by
    simpa only [St.stack, List.append_nil] using (pref_append S [])
  have memory : d.memory = V := by
    rcases of_run_call_val_with_depth_frame operands raw fork with failed | entered
    · rw [success] at failed
      have zero : (1 : B256) = 0 := (pref_head_unique failed.1
        (pref_append [1] ((68 + (p + 164)) ::
          (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
          96 :: 0 :: amount :: toWord :: token :: rho :: L))).symm
      exact ((by decide : (1 : B256) ≠ 0) zero).elim
    · obtain ⟨parent, child, xl, dp, na, code, avail, pc, step, depth, parentStack,
        parentState, parentMemory, parentLogs, parentOutput, delegation, filled, process,
        clean, resume, childState, returned, image, resultStack⟩ := entered
      rw [image, parentMemory]
      simp only [St.memory, show (68 : B256).toNat = 68 from rfl,
        show (0 : B256).toNat = 0 from rfl, List.take_zero]
      generalize V = W at hV fitV ⊢
      change W.extends [((p + 164).toNat, 68), ((p + 164).toNat, 0)] = W
      change (⟨W.data, memExtsSize W.size [((p + 164).toNat, 68), ((p + 164).toNat, 0)]⟩ : Mem) = W
      have size : memExtsSize W.size [((p + 164).toNat, 68), ((p + 164).toNat, 0)] = W.size := by
        change memExtSize (memExtSize W.size (p + 164).toNat 68) (p + 164).toNat 0 = W.size
        rw [memExtSize_of_le hV.n32 (by omega)]
        rfl
      rw [size]
  have short := ReturnDataBound.call_returnData_length_lt raw fork
  have after := safeTransfer_afterCall_dynamic_exact (sevm := sevm) (d := d) (R := L) (V := V)
    (G := G) (q := p + 164) (endWord := 68 + (p + 164))
    (token := token &&& 0xffffffffffffffffffffffffffffffffffffffff) (amount := amount)
    (toWord := toWord) (tokenWord := token) (rho := rho) hV (by omega) (by omega) (by omega)
    sentV short accepted (by omega)
  have postEq := safeTransfer_postCharge_eq (b := d) (reply := d.returnData) (amount := amount)
    (toWord := toWord) mem lower width
  dsimp only at after postEq
  rw [← postEq, ← returnedGas] at after
  have image : d = St d (1 :: (68 + (p + 164)) ::
      (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: token :: rho :: L) V d.gasLeft := St.self success memory
  rw [← image] at after
  exact safeTransfer_dynamicPrepare_closed (sevm := sevm) (b := b) (R := L) (G := callGas)
    (amount := amount) (toWord := toWord) (tokenWord := token) (rho := rho) mem lower width room
    (.next call after)

end Blanc.Lift.UniswapV2Pair
