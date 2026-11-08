import Blanc.Lift.ReachDispatch
import Blanc.Lift.InvWalkWorld
import Jaune.WordFacts
import Blanc.Lift.WalkInvKit

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

/-- A raw reach through the comparison walk retains its first non-comparison leaf. -/
theorem Reach.selWalk_inr (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {σ : B256} {f t : SFunc} (hw : f.selWalk σ = .inr t) {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : Reach P fs sevm ⟨St b (σ :: S) M G, f, K⟩ T) (hT : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b (σ :: S) M G', t, K⟩ T := by
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
  | case5 => cases hw
  | case6 => cases hw; exact ⟨_, run⟩

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
      · exact ⟨(B256.eq_of_eqCheck_ne_zero ne).symm, r⟩
  | case6 => cases hw

/-! ### Cut runs -/

end Walk

/-! ## Through a wrapper to the function body -/

/-! ## A wrapper's calldata-size guard -/

end Blanc.Lift
