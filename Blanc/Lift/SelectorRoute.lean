import Blanc.Lift.ReachDispatch
import Blanc.Lift.InvWalkWorld

/-!
# The route of a selector word through a solc binary-search dispatcher

A solc dispatcher keeps the selector word `σ` on top of the stack and compares it against literal
`PUSH4` constants: `DUP1 PUSH4 c GT PUSH2 d JUMPI` splits the search, `DUP1 PUSH4 c EQ PUSH2 d JUMPI`
enters the wrapper of `c`.  `SFunc.selWalk σ f` evaluates those comparisons for a given word: it ends
at the goto `(c, j)` of the first equal constant, or at the first tree that is no comparison (the
fallback).  The walk is a function of `σ`, so for a concrete selector the kernel computes the
wrapper the dispatcher enters.

* `Reach.selWalk_inl`, `SFunc.RunCut.selWalk_inl`/`_inr`: a reach to an external instruction, or a cut run, from a
  comparison tree with `σ` on top continues from the walk's end, with `σ` still on top and the base
  machine unchanged; at a goto, `σ` is the constant compared (`SFunc.selWalk_inl`);
* `SFunc.selWalk_mem_pairs`, `SFunc.selWalk_mem_leaves`: wherever the walk ends, it ends at one of
  the tree's gotos (`selPairs`) or leaves (`selLeaves`), which do not depend on `σ`;
* `SFunc.toCall`: every successful path of a tree runs state-preserving instructions and branches
  whose other arm cannot succeed, up to an internal call of entry `k` (the shape of a solc wrapper's
  ABI decoding before it calls the function body); `SFunc.RunP.callee_of_toCall` then gives a run of
  the callee from a machine with the same persistent state.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The dispatcher's walk for the selector word `σ`: the goto `(c, j)` of the first equal constant,
or the first tree that is no comparison. -/
def SFunc.selWalk (σ : B256) : SFunc → (B256 × Nat) ⊕ SFunc
  | .dest f => f.selWalk σ
  | .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] _) (.next (.reg .gt)
      (.next (.push [_, _] _) (.branch f g)))) =>
      if B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 then f.selWalk σ else g.selWalk σ
  | .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] _) (.next (.reg .eq)
      (.next (.push [_, _] _) (.branchTo f j)))) =>
      if B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 then f.selWalk σ
      else .inl (Bytes.toB256 [c0, c1, c2, c3], j)
  | t => .inr t

/-- The gotos of a comparison tree: every `(c, j)` its walk can end at, whatever the word. -/
def SFunc.selPairs : SFunc → List (B256 × Nat)
  | .dest f => f.selPairs
  | .next (.reg (.dup 0)) (.next (.push [_, _, _, _] _) (.next (.reg .gt)
      (.next (.push [_, _] _) (.branch f g)))) => f.selPairs ++ g.selPairs
  | .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] _) (.next (.reg .eq)
      (.next (.push [_, _] _) (.branchTo f j)))) => (Bytes.toB256 [c0, c1, c2, c3], j) :: f.selPairs
  | _ => []

/-- The leaves of a comparison tree: every tree its walk can end at, whatever the word. -/
def SFunc.selLeaves : SFunc → List SFunc
  | .dest f => f.selLeaves
  | .next (.reg (.dup 0)) (.next (.push [_, _, _, _] _) (.next (.reg .gt)
      (.next (.push [_, _] _) (.branch f g)))) => f.selLeaves ++ g.selLeaves
  | .next (.reg (.dup 0)) (.next (.push [_, _, _, _] _) (.next (.reg .eq)
      (.next (.push [_, _] _) (.branchTo f _)))) => f.selLeaves
  | t => [t]

theorem SFunc.selWalk_mem_pairs {σ : B256} {f : SFunc} {p : B256 × Nat}
    (hw : f.selWalk σ = .inl p) : p ∈ f.selPairs := by
  fun_induction SFunc.selWalk σ f with
  | case1 f ih => rw [SFunc.selPairs]; exact ih hw
  | case2 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      rw [SFunc.selPairs]; exact List.mem_append_left _ (ih hw)
  | case3 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      rw [SFunc.selPairs]; exact List.mem_append_right _ (ih hw)
  | case4 c0 c1 c2 c3 _ _ _ _ f j h ih =>
      rw [SFunc.selPairs]; exact List.mem_cons_of_mem _ (ih hw)
  | case5 c0 c1 c2 c3 _ _ _ _ f j h =>
      rw [SFunc.selPairs, ← Sum.inl.inj hw]; exact List.mem_cons_self
  | case6 => cases hw

theorem SFunc.selWalk_mem_leaves {σ : B256} {f t : SFunc}
    (hw : f.selWalk σ = .inr t) : t ∈ f.selLeaves := by
  fun_induction SFunc.selWalk σ f with
  | case1 f ih => rw [SFunc.selLeaves]; exact ih hw
  | case2 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      rw [SFunc.selLeaves]; exact List.mem_append_left _ (ih hw)
  | case3 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      rw [SFunc.selLeaves]; exact List.mem_append_right _ (ih hw)
  | case4 c0 c1 c2 c3 _ _ _ _ f j h ih =>
      rw [SFunc.selLeaves]; exact ih hw
  | case5 => cases hw
  | case6 t' h1 h2 h3 =>
      rw [SFunc.selLeaves.eq_4 t' h1 h2 h3, ← Sum.inr.inj hw]; exact List.mem_cons_self

section Walk

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-- One equality comparison of a reach, either way. -/
theorem rr_cmp_eq_either (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf} {σ : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f : SFunc} {j : Nat}
    (run : Reach P fs sevm ⟨St b (σ :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j)))), K⟩ T)
    (hT : AtExec T) :
    (B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 ∧
        ∃ G', Reach P fs sevm ⟨St b (σ :: S) M G', f, K⟩ T) ∨
      (B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ ≠ 0 ∧
        ∃ g G', fs[j]? = some g ∧ Reach P fs sevm ⟨St b (σ :: S) M G', g, K⟩ T) := by
  obtain ⟨d, hd, h⟩ := rr_next run hT
  obtain ⟨_, rfl⟩ := ri_dup rfl (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_eq (hP hd)
  obtain ⟨d, hd, h⟩ := rr_next h hT
  obtain ⟨_, rfl⟩ := ri_push (hP hd)
  rcases Reach.branchTo h hT with ⟨t, d, pop, h⟩ | ⟨t, w, g, d, nonzero, entry, pop, h⟩
  · obtain ⟨_, zero, eq⟩ := St.of_pop2 pop
    exact .inl ⟨zero, _, eq ▸ h⟩
  · obtain ⟨_, word, eq⟩ := St.of_pop2 pop
    exact .inr ⟨word ▸ nonzero, g, _, entry, eq ▸ h⟩

theorem eq_of_eqCheck_ne {x y : B256} (h : B256.eqCheck x y ≠ 0) : x = y := by
  unfold B256.eqCheck at h
  split at h
  · assumption
  · exact absurd rfl h

/-- **A reach at the goto of the walk.**  The selector word is the constant compared, and the reach
continues from the goto's entry. -/
theorem Reach.selWalk_inl (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {σ c : B256}
    {f : SFunc} {j : Nat} (hw : f.selWalk σ = .inl (c, j)) {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {K : List SFunc} {T : Conf} (run : Reach P fs sevm ⟨St b (σ :: S) M G, f, K⟩ T)
    (hT : AtExec T) :
    σ = c ∧ ∃ g G', fs[j]? = some g ∧ Reach P fs sevm ⟨St b (σ :: S) M G', g, K⟩ T := by
  fun_induction SFunc.selWalk σ f generalizing G with
  | case1 f ih =>
      obtain ⟨G', r⟩ := rr_dest run hT
      exact ih hw r
  | case2 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := rr_cmp_gt hP run hT
      rw [ite_eq_left h] at r
      exact ih hw r
  | case3 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := rr_cmp_gt hP run hT
      rw [ite_eq_right h] at r
      exact ih hw r
  | case4 c0 c1 c2 c3 _ _ _ _ f j h ih =>
      rcases rr_cmp_eq_either hP run hT with ⟨-, G', r⟩ | ⟨ne, -⟩
      · exact ih hw r
      · exact absurd h ne
  | case5 c0 c1 c2 c3 _ _ _ _ f j h =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inl.inj hw)
      rcases rr_cmp_eq_either hP run hT with ⟨zero, -⟩ | ⟨ne, r⟩
      · exact absurd zero h
      · exact ⟨(eq_of_eqCheck_ne ne).symm, r⟩
  | case6 => cases hw

/-! ### Cut runs -/

/-- One equality comparison of a cut run with nothing cut, either way. -/
theorem ric_cmp_eq_either {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {r : Seg} {σ : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f : SFunc} {j : Nat}
    (run : SFunc.RunCut fs sevm [] (St b (σ :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j))))) r) :
    (B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 ∧
        ∃ G', SFunc.RunCut fs sevm [] (St b (σ :: S) M G') f r) ∨
      (B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ ≠ 0 ∧
        ∃ g G', fs[j]? = some g ∧ SFunc.RunCut fs sevm [] (St b (σ :: S) M G') g r) := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_eq hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  cases h with
  | toZero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | toSuccCut _ _ _ hk' _ => exact absurd hk' List.not_mem_nil
  | toSucc d0 w0 hw _ hk' h k =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, _, hk', e ▸ k⟩

theorem SFunc.RunCut.selWalk_inr {fs : List SFunc} {sevm : Sevm} {σ : B256}
    {f t : SFunc} (hw : f.selWalk σ = .inr t) {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {r : Seg} (run : SFunc.RunCut fs sevm [] (St b (σ :: S) M G) f r) :
    ∃ G', SFunc.RunCut fs sevm [] (St b (σ :: S) M G') t r := by
  fun_induction SFunc.selWalk σ f generalizing G with
  | case1 f ih =>
      obtain ⟨G', r⟩ := ric_dest run
      exact ih hw r
  | case2 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := ric_cmp_gt run
      rw [ite_eq_left h] at r
      exact ih hw r
  | case3 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := ric_cmp_gt run
      rw [ite_eq_right h] at r
      exact ih hw r
  | case4 c0 c1 c2 c3 _ _ _ _ f j h ih =>
      rcases ric_cmp_eq_either run with ⟨-, G', r⟩ | ⟨ne, -⟩
      · exact ih hw r
      · exact absurd h ne
  | case5 => cases hw
  | case6 => cases hw; exact ⟨_, run⟩

theorem SFunc.RunCut.selWalk_inl {fs : List SFunc} {sevm : Sevm} {σ c : B256}
    {f : SFunc} {j : Nat} (hw : f.selWalk σ = .inl (c, j)) {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {r : Seg} (run : SFunc.RunCut fs sevm [] (St b (σ :: S) M G) f r) :
    σ = c ∧ ∃ g G', fs[j]? = some g ∧ SFunc.RunCut fs sevm [] (St b (σ :: S) M G') g r := by
  fun_induction SFunc.selWalk σ f generalizing G with
  | case1 f ih =>
      obtain ⟨G', r⟩ := ric_dest run
      exact ih hw r
  | case2 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := ric_cmp_gt run
      rw [ite_eq_left h] at r
      exact ih hw r
  | case3 c0 c1 c2 c3 _ _ _ _ f g h ih =>
      obtain ⟨G', r⟩ := ric_cmp_gt run
      rw [ite_eq_right h] at r
      exact ih hw r
  | case4 c0 c1 c2 c3 _ _ _ _ f j h ih =>
      rcases ric_cmp_eq_either run with ⟨-, G', r⟩ | ⟨ne, -⟩
      · exact ih hw r
      · exact absurd h ne
  | case5 c0 c1 c2 c3 _ _ _ _ f j h =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inl.inj hw)
      rcases ric_cmp_eq_either run with ⟨zero, -⟩ | ⟨ne, r⟩
      · exact absurd zero h
      · exact ⟨(eq_of_eqCheck_ne ne).symm, r⟩
  | case6 => cases hw

end Walk

/-! ## Through a wrapper to the function body -/

/-- Every successful path of the tree runs state-preserving instructions (`regSilent`) and
branches whose other arm has no successful run (`SFunc.noOk`), up to an internal call of
entry `k`. -/
def SFunc.toCall (k : Nat) : SFunc → Bool
  | .next n f => regSilent n && f.toCall k
  | .dest f => f.toCall k
  | .branch f g => (f.noOk || f.toCall k) && (g.noOk || g.toCall k)
  | .callNext j _ => j == k
  | _ => false

/-- **Into the body.**  A run of a `toCall k` tree contains a run of entry `k` from a machine with
the same persistent state. -/
theorem SFunc.RunP.callee_of_toCall {P : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {fs : List SFunc} {sevm : Sevm}
    {k : Nat} {g : SFunc} (hk : fs[k]? = some g) {d : Devm} {f : SFunc} {o : Outcome}
    (hf : f.toCall k = true) (run : SFunc.RunP P fs sevm d f o) :
    ∃ d' o', d'.state = d.state ∧ SFunc.RunP P fs sevm d' g o' := by
  have noOk : ∀ {d f o}, f.noOk = true → SFunc.RunP P fs sevm d f o → False :=
    fun hn run => (SFunc.runP_iff_runCutP_nil.mp run).false_of_noOk hn
  induction run with
  | zero dd pop run ih =>
      simp only [SFunc.toCall, Bool.and_eq_true, Bool.or_eq_true] at hf
      rcases hf.1 with hn | hc
      · exact (noOk hn run).elim
      · obtain ⟨d', o', hs, r⟩ := ih hc
        exact ⟨d', o', hs.trans pop.state.symm, r⟩
  | succ dd w _ pop run ih =>
      simp only [SFunc.toCall, Bool.and_eq_true, Bool.or_eq_true] at hf
      rcases hf.2 with hn | hc
      · exact (noOk hn run).elim
      · obtain ⟨d', o', hs, r⟩ := ih hc
        exact ⟨d', o', hs.trans pop.state.symm, r⟩
  | next hn _ ih =>
      simp only [SFunc.toCall, Bool.and_eq_true] at hf
      obtain ⟨d', o', hs, r⟩ := ih hf.2
      exact ⟨d', o', hs.trans (Ninst.Run.state_of_regSilent hf.1 (hP hn)), r⟩
  | dest burn _ ih =>
      obtain ⟨d', o', hs, r⟩ := ih hf
      exact ⟨d', o', hs.trans burn.state.symm, r⟩
  | callHalt dd lookup pop run =>
      simp only [SFunc.toCall, beq_iff_eq] at hf
      subst hf
      rw [hk] at lookup
      cases lookup
      exact ⟨_, _, pop.state.symm, run⟩
  | callRet dd lookup pop run _ =>
      simp only [SFunc.toCall, beq_iff_eq] at hf
      subst hf
      rw [hk] at lookup
      cases lookup
      exact ⟨_, _, pop.state.symm, run⟩
  | _ => simp only [SFunc.toCall, Bool.false_eq_true] at hf

/-! ## A wrapper's calldata-size guard -/

/-- The static-head guard solc 0.6 puts at the top of a wrapper with arguments,
`JUMPDEST PUSH2 ret PUSH1 4 DUP1 CALLDATASIZE SUB PUSH n DUP2 LT ISZERO PUSH2 d JUMPI`, whose
failing arm has no successful run: the head size `n`. -/
def SFunc.headWord : SFunc → Option B256
  | .dest (.next (.push _ _) (.next (.push four _) (.next (.reg (.dup 0))
      (.next (.reg .calldatasize) (.next (.reg .sub) (.next (.push nb _) (.next (.reg (.dup 1))
      (.next (.reg .lt) (.next (.reg .iszero) (.next (.push _ _) (.branch f _))))))))))) =>
      if Bytes.toB256 four = 4 ∧ f.noOk = true then some (Bytes.toB256 nb) else none
  | _ => none

/-- **Past the size guard.**  A cut run of a wrapper with head size `n` has at least `n` bytes of
calldata after the selector, as the machine reads it. -/
theorem SFunc.RunCut.headWord {fs : List SFunc} {sevm : Sevm} {C : List Nat} {t : SFunc}
    {n : B256} (hw : t.headWord = some n) {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    {r : Seg} (run : SFunc.RunCut fs sevm C (St b S M G) t r) :
    B256.ltCheck (sevm.data.length.toB256 - 4) n = 0 := by
  unfold SFunc.headWord at hw
  split at hw
  · split at hw
    · rename_i cond
      cases hw
      obtain ⟨_, h⟩ := ric_dest run
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_calldatasize hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_sub hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_push hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_dup rfl hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_lt hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_iszero hd
      obtain ⟨d, hd, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_push hd
      rcases ric_branch h with ⟨-, _, h'⟩ | ⟨nz, -⟩
      · exact (h'.false_of_noOk cond.2).elim
      · rw [← cond.1]
        exact eq_of_eqCheck_ne nz
    · cases hw
  · cases hw

theorem not_lt_of_ltCheck_zero {x y : B256} (h : B256.ltCheck x y = 0) : ¬ x < y := by
  unfold B256.ltCheck at h
  split at h
  · exact absurd h (by decide)
  · assumption

/-- **The head fits.**  Calldata of `L` bytes the machine reads as at least four bytes, and then
as at least `32 h` bytes after the selector, has `4 + 32 h` bytes. -/
theorem calldata_head_fits {L h : Nat} (h0 : B256.ltCheck L.toB256 4 = 0)
    (hh : h = 0 ∨ B256.ltCheck (L.toB256 - 4) (Nat.toB256 (32 * h)) = 0)
    (small : 4 + 32 * h ≤ 2 ^ 256) : 4 + 32 * h ≤ L := by
  by_cases big : 2 ^ 256 ≤ L
  · omega
  have hL : L.toB256.toNat = L := B256.toNat_toB256_of_lt (by omega)
  have four : (4 : B256).toNat = 4 := rfl
  have le4 : 4 ≤ L := by
    have := not_lt_of_ltCheck_zero h0
    rw [B256.lt_iff_toNat_lt_toNat, hL, four] at this
    omega
  rcases hh with rfl | hh
  · omega
  have hle : (4 : B256) ≤ L.toB256 := B256.le_of_toNat_le_toNat (by rw [hL, four]; exact le4)
  have := not_lt_of_ltCheck_zero hh
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_sub_eq_of_le _ _ hle, hL, four,
    B256.toNat_toB256_of_lt (by omega)] at this
  omega

end Blanc.Lift
