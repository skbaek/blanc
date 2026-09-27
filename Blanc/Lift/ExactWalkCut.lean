import Blanc.Lift.ExactWalkOps
import Blanc.Lift.Loop

/-!
# Forward walk steps for exact cut runs

`SFunc.RunExactCut.iterate` (`Blanc/Lift/Loop.lean`) builds a loop run out of
per-iteration runs *cut* at the loop head.  This module gives those runs the
same forward walk kit `Blanc/Lift/ExactWalk.lean` gives exact runs: `rxc_*`
is `rx_*` with `SFunc.RunExactCut fs sevm C` in place of `SFunc.RunExact fs
sevm`, plus the cut goto `rxc_jumpCut` that ends an iteration.

It also lets a walk built with the uncut kit be used under a cut:
`SFunc.RunExact.toCut` turns an exact run into an exact cut run when the tree,
and every entry it may goto, only jumps to entries outside the cut list — a
property of the syntax, checked by the Boolean `SFunc.avoids` (usually by
`decide`).
-/

namespace Blanc.Lift

open Jaune

/-! ## Gotos that stay out of a cut list -/

/-- Every goto in the tree (not in callees: those run uncut) targets an entry
of `E` that is not in the cut list `C`. -/
def SFunc.avoids (C E : List Nat) : SFunc → Bool
  | .branch f g => f.avoids C E && g.avoids C E
  | .branchTo f k => (E.contains k && !C.contains k) && f.avoids C E
  | .last _ => true
  | .next _ f => f.avoids C E
  | .dest f => f.avoids C E
  | .jump k => E.contains k && !C.contains k
  | .callNext _ f => f.avoids C E
  | .ret => true
  | .pcAt _ f => f.avoids C E
  | .undefined => true

/-- An exact run whose gotos all avoid the cut list is an exact cut run. -/
theorem SFunc.RunExact.toCut {fs : List SFunc} {sevm : Sevm} {C E : List Nat}
    (hE : ∀ j t, j ∈ E → fs[j]? = some t → t.avoids C E = true)
    {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunExact fs sevm devm f o) (hf : f.avoids C E = true) :
    SFunc.RunExactCut fs sevm C devm f (.done o) := by
  induction run with
  | zero d pop _ ih =>
    simp only [SFunc.avoids, Bool.and_eq_true] at hf
    exact .zero d pop (ih hf.1)
  | succ d w hw pop _ ih =>
    simp only [SFunc.avoids, Bool.and_eq_true] at hf
    exact .succ d w hw pop (ih hf.2)
  | toZero d pop _ ih =>
    simp only [SFunc.avoids, Bool.and_eq_true] at hf
    exact .toZero d pop (ih hf.2)
  | @toSucc _ _ _ g k _ d w hw hget pop _ ih =>
    simp only [SFunc.avoids, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hf
    have hnot : k ∉ C := by simp_all
    exact .toSucc d w hw hnot hget pop (ih (hE k g hf.1.1 hget))
  | last h => exact .last h
  | next h _ ih =>
    simp only [SFunc.avoids] at hf
    exact .next h (ih hf)
  | dest burn _ ih =>
    simp only [SFunc.avoids] at hf
    exact .dest burn (ih hf)
  | @jump _ _ k g _ d hget pop _ ih =>
    simp only [SFunc.avoids, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hf
    have hnot : k ∉ C := by simp_all
    exact .jump d hnot hget pop (ih (hE k g hf.1 hget))
  | ret d pop => exact .ret d pop
  | callHalt d hget pop hrun => exact .callHalt d hget pop hrun
  | callRet d hget pop hrun _ _ ih =>
    simp only [SFunc.avoids] at hf
    exact .callRet d hget pop hrun (ih hf)
  | pcAt hpc _ ih =>
    simp only [SFunc.avoids] at hf
    exact .pcAt hpc (ih hf)

/-! ## Cut walk steps -/

section Steps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {f g : SFunc} {r : Seg}
  {S : List B256} {M : Mem} {G : Nat}

theorem rxc_dest (k : SFunc.RunExactCut fs sevm C (St b S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 1)) (.dest f) r :=
  .dest (Devm.burnBy_setMach_gas (devm := St b S M (G + 1)) rfl) k

theorem rxc_branch_zero {d : B256} (k : SFunc.RunExactCut fs sevm C (St b S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (d :: 0 :: S) M (G + 10)) (.branch f g) r :=
  .zero d popBurnBy_St2 k

theorem rxc_branch_succ {d w : B256} (hw : w ≠ 0)
    (k : SFunc.RunExactCut fs sevm C (St b S M G) g r) :
    SFunc.RunExactCut fs sevm C (St b (d :: w :: S) M (G + 10)) (.branch f g) r :=
  .succ d w hw popBurnBy_St2 k

/-- A `JUMP` into a cut entry: the iteration ends there. -/
theorem rxc_jumpCut {d : B256} {j : Nat} (hj : j ∈ C) :
    SFunc.RunExactCut fs sevm C (St b (d :: S) M (G + 8)) (.jump j) (.at j (St b S M G)) :=
  .jumpCut d hj popBurnBy_St1

theorem rxc_push {x : UInt8} {xs : Bytes} {le : (x :: xs).length ≤ 32} {w : B256}
    (hw : Bytes.toB256 (x :: xs) = w) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (w :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 3)) (.next (.push (x :: xs) le) f) r := by
  subst hw
  exact .next (Ninst.runCompiled_pushBytes (devm := St b S M (G + 3)) (c := gVerylow)
    (G := G) rfl rfl hroom) k

theorem rxc_binary {rr : Rinst} {fn : B256 → B256 → B256} {c : Nat} {x y v : B256}
    (hne : rr ≠ .pc) (hdef : ∀ d : Devm, Rinst.runCore 0 d sevm rr = applyBinary fn c d)
    (hv : fn x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + c)) (.next (.reg rr) f) r :=
  .next (Ninst.runCompiled_binary (devm := St b (x :: y :: S) M (G + c)) (G := G) hne
    (hdef _) rfl hv rfl hroom) k

theorem rxc_unary {rr : Rinst} {fn : B256 → B256} {c : Nat} {x v : B256}
    (hne : rr ≠ .pc) (hdef : ∀ d : Devm, Rinst.runCore 0 d sevm rr = applyUnary fn c d)
    (hv : fn x = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: S) M (G + c)) (.next (.reg rr) f) r :=
  .next (Ninst.runCompiled_unary (devm := St b (x :: S) M (G + c)) (G := G) hne
    (hdef _) rfl hv rfl hroom) k

theorem rxc_add {x y : B256} (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b ((x + y) :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .add) f) r :=
  rxc_binary (fn := (· + ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl hroom k

theorem rxc_lt {x y v : B256} (hv : B256.ltCheck x y = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: y :: S) M (G + 3)) (.next (.reg .lt) f) r :=
  rxc_binary (fn := B256.ltCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_iszero {x v : B256} (hv : B256.eqCheck x 0 = v) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: S) M (G + 3)) (.next (.reg .iszero) f) r :=
  rxc_unary (fn := (B256.eqCheck · 0)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) hv hroom k

theorem rxc_dup {n : Fin 16} {w : B256} (hget : S[n.val]? = some w) (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (w :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 3)) (.next (.reg (.dup n)) f) r :=
  .next (Ninst.runCompiled_dup (devm := St b S M (G + 3)) (G := G) hget rfl hroom) k

theorem rxc_swap {n : Fin 16} {S' : List B256} (hsw : Jaune.List.swap S n.val = some S')
    (k : SFunc.RunExactCut fs sevm C (St b S' M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 3)) (.next (.reg (.swap n)) f) r :=
  .next (Ninst.runCompiled_swap (devm := St b S M (G + 3)) (G := G) hsw rfl) k

theorem rxc_pop {x : B256}
    (k : SFunc.RunExactCut fs sevm C (St b S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (x :: S) M (G + 2)) (.next (.reg .pop) f) r :=
  .next (Ninst.runCompiled_pop (devm := St b (x :: S) M (G + 2)) (G := G) rfl rfl) k

theorem rxc_mstore {i v : B256} {c : Nat} {M' : Mem}
    (hc : gVerylow + (St b (i :: v :: S) M (G + c)).extCost [⟨i.toNat, 32⟩] = c)
    (hw : M.write i.toNat v.toBytes = M')
    (k : SFunc.RunExactCut fs sevm C (St b S M' G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: v :: S) M (G + c)) (.next (.reg .mstore) f) r :=
  .next (Ninst.runCompiled_mstore (devm := St b (i :: v :: S) M (G + c)) (G := G) rfl
    (by rw [hc]; rfl) hw) k

theorem rxc_mload {i v : B256} {c : Nat}
    (hc : gVerylow + (St b (i :: S) M (G + c)).extCost [⟨i.toNat, 32⟩] = c)
    (hv : Bytes.toB256 (M.read i.toNat 32).1 = v) (hM : (M.read i.toNat 32).2 = M)
    (hroom : S.length < 1024)
    (k : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: S) M (G + c)) (.next (.reg .mload) f) r :=
  .next (Ninst.runCompiled_mload_of (devm := St b (i :: S) M (G + c)) (G := G) rfl hc hv hM
    rfl hroom) k

end Steps

end Blanc.Lift
