import Blanc.Lift.SelectorRoute
import Blanc.Lift.ExactWalk
import Blanc.Lift.ExactWalkOps

/-!
# The route of a selector word, forward and gas-exact

The forward twin of `Blanc/Lift/SelectorRoute.lean`'s `SFunc.selWalk`: `SFunc.selCost σ f` is the
gas the solc binary-search dispatcher spends along the walk of `σ` (22 per `DUP1 PUSH4 c GT/EQ
PUSH2 d JUMPI` row, 1 per `JUMPDEST`), computed by the kernel for a concrete selector.

* `SFunc.RunExact.selWalk_inl`: where the walk ends at the goto `(c, j)`, a run of entry `j`
  (with the selector word still on top) is a run of the tree, for `selCost` more gas;
* `SFunc.RunExact.selWalk_inr`: the same at a leaf the walk ends at (the fallback);
* `SFunc.selGoto fs σ f`: the entry tree the walk enters, so a contract's forward and inverse
  dispatch facts take one kernel-checked hypothesis (`SFunc.RunExact.selGoto`, `SFunc.selGoto_spec`).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- The gas the dispatcher spends along `f.selWalk σ`. -/
def SFunc.selCost (σ : B256) : SFunc → Nat
  | .dest f => f.selCost σ + 1
  | .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] _) (.next (.reg .gt)
      (.next (.push [_, _] _) (.branch f g)))) =>
      if B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 then f.selCost σ + 22
      else g.selCost σ + 22
  | .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] _) (.next (.reg .eq)
      (.next (.push [_, _] _) (.branchTo f _)))) =>
      if B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) σ = 0 then f.selCost σ + 22 else 22
  | _ => 0

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {o : Outcome}

/-- One comparison row's prefix, `DUP1 PUSH4 c op PUSH2 d`, forward (12 gas). -/
private theorem rx_row {σ : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {op : Rinst} {fn : B256 → B256 → B256}
    (hop : ∀ {x y v : B256} {G : Nat} {f : SFunc}, fn x y = v →
      SFunc.RunExact fs sevm (St b (v :: σ :: S) M G) f o →
      SFunc.RunExact fs sevm (St b (x :: y :: σ :: S) M (G + 3)) (.next (.reg op) f) o)
    (hS : S.length + 2 < 1024) {G : Nat} {t : SFunc}
    (k : SFunc.RunExact fs sevm (St b (Bytes.toB256 [d0, d1] ::
      fn (Bytes.toB256 [c0, c1, c2, c3]) σ :: σ :: S) M G) t o) :
    SFunc.RunExact fs sevm (St b (σ :: S) M (G + 12))
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1) (.next (.reg op)
        (.next (.push [d0, d1] l2) t)))) o := by
  rw [show G + 12 = G + 3 + 3 + 3 + 3 by omega]
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine hop rfl ?_
  exact rx_push rfl (by simp only [List.length_cons]; omega) k

theorem SFunc.RunExact.selWalk_inl {σ c : B256} {f g : SFunc} {j : Nat}
    (hw : f.selWalk σ = .inl (c, j)) (hj : fs[j]? = some g) (hS : S.length + 2 < 1024) {G : Nat}
    (k : SFunc.RunExact fs sevm (St b (σ :: S) M G) g o) :
    SFunc.RunExact fs sevm (St b (σ :: S) M (G + f.selCost σ)) f o := by
  have hgt := fun {x y v : B256} {G : Nat} {f : SFunc} (hv : B256.gtCheck x y = v)
    (k : SFunc.RunExact fs sevm (St b (v :: σ :: S) M G) f o) =>
    rx_gt hv (by simp only [List.length_cons]; omega) k
  have heq := fun {x y v : B256} {G : Nat} {f : SFunc} (hv : B256.eqCheck x y = v)
    (k : SFunc.RunExact fs sevm (St b (v :: σ :: S) M G) f o) =>
    rx_eq hv (by simp only [List.length_cons]; omega) k
  fun_induction SFunc.selWalk σ f generalizing G with
  | case1 f ih =>
      rw [SFunc.selCost, ← Nat.add_assoc]
      exact rx_dest (ih hw k)
  | case2 c0 c1 c2 c3 _ _ _ _ f g' h ih =>
      rw [SFunc.selCost, ite_eq_left h, ← Nat.add_assoc, show G + f.selCost σ + 22 =
        G + f.selCost σ + 10 + 12 by omega]
      exact rx_row hgt hS (by rw [h]; exact rx_branch_zero (ih hw k))
  | case3 c0 c1 c2 c3 _ _ _ _ f g' h ih =>
      rw [SFunc.selCost, ite_eq_right h, ← Nat.add_assoc, show G + g'.selCost σ + 22 =
        G + g'.selCost σ + 10 + 12 by omega]
      exact rx_row hgt hS (rx_branch_succ h (ih hw k))
  | case4 c0 c1 c2 c3 _ _ _ _ f j' h ih =>
      rw [SFunc.selCost, ite_eq_left h, ← Nat.add_assoc, show G + f.selCost σ + 22 =
        G + f.selCost σ + 10 + 12 by omega]
      exact rx_row heq hS (by rw [h]; exact rx_branchTo_zero (ih hw k))
  | case5 c0 c1 c2 c3 _ _ _ _ f j' h =>
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Sum.inl.inj hw)
      rw [SFunc.selCost, ite_eq_right h, show G + 22 = G + 10 + 12 by omega]
      exact rx_row heq hS (rx_branchTo_succ h hj k)
  | case6 => cases hw

theorem SFunc.RunExact.selWalk_inr {σ : B256} {f t : SFunc}
    (hw : f.selWalk σ = .inr t) (hS : S.length + 2 < 1024) {G : Nat}
    (k : SFunc.RunExact fs sevm (St b (σ :: S) M G) t o) :
    SFunc.RunExact fs sevm (St b (σ :: S) M (G + f.selCost σ)) f o := by
  have hgt := fun {x y v : B256} {G : Nat} {f : SFunc} (hv : B256.gtCheck x y = v)
    (k : SFunc.RunExact fs sevm (St b (v :: σ :: S) M G) f o) =>
    rx_gt hv (by simp only [List.length_cons]; omega) k
  have heq := fun {x y v : B256} {G : Nat} {f : SFunc} (hv : B256.eqCheck x y = v)
    (k : SFunc.RunExact fs sevm (St b (v :: σ :: S) M G) f o) =>
    rx_eq hv (by simp only [List.length_cons]; omega) k
  fun_induction SFunc.selWalk σ f generalizing G with
  | case1 f ih =>
      rw [SFunc.selCost, ← Nat.add_assoc]
      exact rx_dest (ih hw k)
  | case2 c0 c1 c2 c3 _ _ _ _ f g' h ih =>
      rw [SFunc.selCost, ite_eq_left h, ← Nat.add_assoc, show G + f.selCost σ + 22 =
        G + f.selCost σ + 10 + 12 by omega]
      exact rx_row hgt hS (by rw [h]; exact rx_branch_zero (ih hw k))
  | case3 c0 c1 c2 c3 _ _ _ _ f g' h ih =>
      rw [SFunc.selCost, ite_eq_right h, ← Nat.add_assoc, show G + g'.selCost σ + 22 =
        G + g'.selCost σ + 10 + 12 by omega]
      exact rx_row hgt hS (rx_branch_succ h (ih hw k))
  | case4 c0 c1 c2 c3 _ _ _ _ f j' h ih =>
      rw [SFunc.selCost, ite_eq_left h, ← Nat.add_assoc, show G + f.selCost σ + 22 =
        G + f.selCost σ + 10 + 12 by omega]
      exact rx_row heq hS (by rw [h]; exact rx_branchTo_zero (ih hw k))
  | case5 => cases hw
  | case6 t' h1 h2 h3 =>
      cases hw
      rw [SFunc.selCost.eq_4 _ _ h1 h2 h3]
      exact k

/-- The entry tree the walk of `σ` enters, if it ends at a goto. -/
def SFunc.selGoto (fs : List SFunc) (σ : B256) (f : SFunc) : Option SFunc :=
  match f.selWalk σ with
  | .inl (_, j) => fs[j]?
  | .inr _ => none

theorem SFunc.selGoto_spec {fs : List SFunc} {σ : B256} {f g : SFunc}
    (h : f.selGoto fs σ = some g) : ∃ c j, f.selWalk σ = .inl (c, j) ∧ fs[j]? = some g := by
  unfold SFunc.selGoto at h
  split at h
  · rename_i c j hw
    exact ⟨c, j, hw, h⟩
  · cases h

/-- **Into the goto's entry, forward.** -/
theorem SFunc.RunExact.selGoto {σ : B256} {f g : SFunc} (h : f.selGoto fs σ = some g)
    (hS : S.length + 2 < 1024) {G : Nat}
    (k : SFunc.RunExact fs sevm (St b (σ :: S) M G) g o) :
    SFunc.RunExact fs sevm (St b (σ :: S) M (G + f.selCost σ)) f o := by
  obtain ⟨_, _, hw, hj⟩ := SFunc.selGoto_spec h
  exact SFunc.RunExact.selWalk_inl hw hj hS k

end Fwd

end Blanc.Lift
