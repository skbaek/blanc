import Blanc.Lift.CheckFast
import Blanc.Lift.Silent

/-!
# Refining a checked certificate's entry frames (contract-neutral)

A checked certificate's declared entry frames may be sharpened: `Cert.refine c k i v` replaces
position `i` of entry `k`'s frame by `v` and keeps every tree.  The refined certificate is again
checked by `Cert.check` from scratch; `Cert.check_of_agree` reduces that check to the entries in
a list `T` (re-decided) when every other entry is unchanged and references no refined entry, so the
per-entry decisions of the original certificate are reused through `checkNode_congr`.  A refined
`.const` frame position then reaches every cursor of the refined certificate.  Hoist candidates for
`Blanc/Lift/Check.lean`.
-/

namespace Blanc.Lift

open Jaune

/-- `checkNode` reads the entry list only at the tree's references. -/
theorem checkNode_congr {code : ByteArray} {es es' : List Entry} {m : Nat} :
    ∀ (f : SFunc) (pc : Nat) (a : List AVal), (∀ k ∈ f.refs, es[k]? = es'[k]?) →
      checkNode code es m pc a f = checkNode code es' m pc a f := by
  intro f
  induction f with
  | branch f g ihf ihg =>
      intro pc a h
      simp only [SFunc.refs, List.mem_append] at h
      simp only [checkNode]
      split
      · rw [ihf _ _ fun k hk => h k (Or.inl hk), ihg _ _ fun k hk => h k (Or.inr hk)]
      · rfl
  | branchTo f k ih =>
      intro pc a h
      simp only [SFunc.refs, List.mem_cons] at h
      simp only [checkNode]
      rw [h k (Or.inl rfl)]
      split
      · rw [ih _ _ fun j hj => h j (Or.inr hj)]
      · rfl
  | last l => intro pc a _; rfl
  | next n f ih =>
      intro pc a h
      simp only [SFunc.refs] at h
      simp only [checkNode]
      split
      · rw [ih _ _ h]
      · rfl
  | dest f ih =>
      intro pc a h
      simp only [SFunc.refs] at h
      simp only [checkNode]
      rw [ih _ _ h]
  | jump k =>
      intro pc a h
      simp only [SFunc.refs, List.mem_singleton] at h
      simp only [checkNode]
      rw [h k rfl]
  | callNext k f ih =>
      intro pc a h
      simp only [SFunc.refs, List.mem_cons] at h
      have hk := h k (Or.inl rfl)
      have hf := fun j hj => h j (Or.inr hj)
      simp only [checkNode]
      rw [hk]
      split
      · split
        · split
          · rw [ih _ _ hf]
          · rfl
        · rfl
      · rfl
  | ret => intro pc a _; rfl
  | pcAt p f ih =>
      intro pc a h
      simp only [SFunc.refs] at h
      simp only [checkNode]
      rw [ih _ _ h]
  | undefined => intro pc a _; rfl

/-- Entry `i` of `c` checks against the entry list `es` (vacuous past the end). -/
def Cert.entryOk (code : ByteArray) (es : List Entry) (c : Cert) (i : Nat) : Bool :=
  match c[i]? with
  | some p => checkNode code es p.1.rets p.1.pc p.1.frame p.2
  | none => true

/-- `Cert.entryOk` over trie-backed byte reads. -/
def Cert.entryOkT (code : ByteArray) (d : Nat) (bytes : LTrie UInt8) (es : List Entry) (c : Cert)
    (i : Nat) : Bool :=
  match c[i]? with
  | some p => checkNodeT code d bytes es p.1.rets p.1.pc p.1.frame p.2
  | none => true

theorem Cert.entryOkT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (es : List Entry)
    (c : Cert) (i : Nat) : Cert.entryOkT code d T.bytes es c i = Cert.entryOk code es c i := by
  unfold Cert.entryOkT Cert.entryOk
  cases c[i]? with
  | none => rfl
  | some p => exact checkNodeT_eq T es _ _ _ _

/-- **Checking a certificate that agrees with a checked one off `T`.** -/
theorem Cert.check_of_agree {code : ByteArray} {c c' : Cert} (hc : Cert.check code c = true)
    (hhead : c'.head?.map Prod.fst = c.head?.map Prod.fst) (T : List Nat)
    (hT : ∀ i ∈ T, Cert.entryOk code c'.entries c' i = true)
    (hsame : ∀ i, i ∉ T → c'[i]? = c[i]?)
    (hrefs : ∀ i, i ∉ T → ∀ p, c[i]? = some p → ∀ k ∈ p.2.refs, c'.entries[k]? = c.entries[k]?) :
    Cert.check code c' = true := by
  unfold Cert.check at hc ⊢
  rw [Bool.and_eq_true] at hc ⊢
  refine ⟨?_, ?_⟩
  · cases c with
    | nil => exact absurd hc.1 (by simp only [Bool.false_eq_true, not_false_eq_true])
    | cons p c =>
        cases c' with
        | nil => simp only [List.head?_nil, Option.map_none, List.head?_cons, Option.map_some,
            reduceCtorEq] at hhead
        | cons p' c' =>
            simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
            obtain ⟨e, f⟩ := p
            obtain ⟨e', f'⟩ := p'
            dsimp only at hhead
            subst hhead
            exact hc.1
  · rw [List.all_eq_true] at hc ⊢
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    by_cases hiT : i ∈ T
    · have := hT i hiT
      unfold Cert.entryOk at this
      rw [hi] at this
      obtain ⟨e, f⟩ := p
      exact this
    · have hci : c[i]? = some p := (hsame i hiT).symm.trans hi
      have := hc.2 p (List.mem_of_getElem? hci)
      have hr := hrefs i hiT p hci
      obtain ⟨e, f⟩ := p
      dsimp only at this hr ⊢
      rw [checkNode_congr (es' := c.entries) _ _ _ hr]
      exact this

/-- Replace position `i` of entry `k`'s declared frame by `v`; every tree is kept. -/
def Cert.refine (c : Cert) (k i : Nat) (v : AVal) : Cert :=
  c.modify k fun p => ({ p.1 with frame := p.1.frame.set i v }, p.2)

theorem Cert.refine_getElem?_ne {c : Cert} {k i j : Nat} {v : AVal} (h : j ≠ k) :
    (c.refine k i v)[j]? = c[j]? := by
  unfold Cert.refine
  rw [List.getElem?_modify]
  simp only [Ne.symm h, ite_false]
  cases c[j]? <;> rfl

theorem Cert.refine_prog {c : Cert} {k i : Nat} {v : AVal} :
    (c.refine k i v).prog = c.prog := by
  unfold Cert.refine Cert.prog
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_modify]
  split <;> cases c[j]? <;> rfl

end Blanc.Lift
