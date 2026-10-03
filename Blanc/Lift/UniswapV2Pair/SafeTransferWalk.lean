import Blanc.Lift.UniswapV2Pair.BurnPricingWalk
import Blanc.Lift.ByteWindowMemory
import Blanc.Lift.ReturnDataBound

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
private theorem safeTransfer_success_inv {P : Sevm → Devm → Ninst → Devm → Prop}
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
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := src) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := dst) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup (w := 32) rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  cases h with
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
private def safeTransfer_afterCall : SFunc :=
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
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_exp (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_not (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_and (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_or (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mstore (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_add (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_swap rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_pop (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_mload (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_sub (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_push (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨_, rfl⟩ := ri_dup rfl (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h; obtain ⟨forwarded, callGas, rfl⟩ := ri_gas (project hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  exact ⟨forwarded, callGas, d, hd, h⟩

end Blanc.Lift.UniswapV2Pair
