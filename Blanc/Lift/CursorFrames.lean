import Blanc.Lift.Cursor

/-!
# A frame predicate at every reachable cursor node (contract-neutral)

`SFunc.framesSat es P a f` walks a certificate tree with the abstract frames the checker computes
(`absNinst`, branch pops, the callee frame of a `callNext` continuation, the `PC` literal) and
checks `P n a` at every straight-line node `.next n _`.  `Cursor.FramesSat` holds it at the active
tree and at every pending continuation; `SStep.framesSat` keeps it, so from a certificate whose
every entry passes it (`Cert.framesSat`), every reachable cursor satisfies it
(`Cursor.framesSat_of_reachable`), and at a cursor-placed node `P` holds of the node's actual
instruction and abstract frame.  With `FrameMatches`, a `.const` position of that frame is the actual
stack word (`FrameMatches.getElem?_const`).  Hoist candidate for `Blanc/Lift/CallRestriction.lean`.
-/

namespace Blanc.Lift

open Jaune

/-- `P` at every straight-line node of the tree, over the checker's abstract frames. -/
def SFunc.framesSat (es : List Entry) (P : Ninst → List AVal → Bool) :
    List AVal → SFunc → Bool
  | a, .next n f => P n a && (match absNinst n a with
      | some a' => SFunc.framesSat es P a' f
      | none => true)
  | a, .dest f => SFunc.framesSat es P a f
  | a, .branch f g => (match a with
      | .const _ :: _ :: a' => SFunc.framesSat es P a' f && SFunc.framesSat es P a' g
      | _ => true)
  | a, .branchTo f _ => (match a with
      | .const _ :: _ :: a' => SFunc.framesSat es P a' f
      | _ => true)
  | a, .callNext k f => (match a, es[k]? with
      | .const _ :: a', some e =>
          SFunc.framesSat es P (List.replicate e.rets .unk ++ a'.drop e.frame.length) f
      | _, _ => true)
  | a, .pcAt p f => SFunc.framesSat es P (.const (Nat.toB256 p) :: a) f
  | _, _ => true

/-- Every entry of the certificate passes `framesSat` at its declared frame. -/
def Cert.framesSat (c : Cert) (P : Ninst → List AVal → Bool) : Bool :=
  c.all fun (e, f) => f.framesSat c.entries P e.frame

/-- The active tree and every pending continuation pass `framesSat`. -/
def Cursor.FramesSat (es : List Entry) (P : Ninst → List AVal → Bool) (κ : Cursor) : Prop :=
  κ.f.framesSat es P κ.a = true ∧
    ∀ k ∈ κ.K, k.f.framesSat es P (List.replicate k.rets .unk ++ k.a) = true

private theorem Cert.framesSat_lookup {c : Cert} {P : Ninst → List AVal → Bool}
    (hc : c.framesSat P = true) {k : Nat} {e : Entry} {g : SFunc}
    (he : c.entries[k]? = some e) (hg : c.prog[k]? = some g) :
    g.framesSat c.entries P e.frame = true := by
  have hk : c[k]? = some (e, g) := by
    simp only [Cert.entries, Cert.prog, List.getElem?_map] at he hg
    cases h : c[k]? with
    | none => rw [h] at he; cases he
    | some p =>
        rw [h] at he hg
        simp only [Option.map_some, Option.some.injEq] at he hg
        rw [← he, ← hg]
  exact List.all_eq_true.mp hc _ (List.mem_of_getElem? hk)

theorem SStep.framesSat {c : Cert} {P : Ninst → List AVal → Bool} (hc : c.framesSat P = true)
    {κ κ' : Cursor} (step : SStep c κ κ') (h : κ.FramesSat c.entries P) :
    κ'.FramesSat c.entries P := by
  obtain ⟨hf, hK⟩ := h
  cases step with
  | next ha =>
      simp only [SFunc.framesSat, ha, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | dest => exact ⟨hf, hK⟩
  | zero =>
      simp only [SFunc.framesSat, Bool.and_eq_true] at hf
      exact ⟨hf.1, hK⟩
  | succ =>
      simp only [SFunc.framesSat, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | toZero => exact ⟨hf, hK⟩
  | toSucc he hg => exact ⟨Cert.framesSat_lookup hc he hg, hK⟩
  | jump he hg => exact ⟨Cert.framesSat_lookup hc he hg, hK⟩
  | call κc he hg hcf hca _ hcr =>
      refine ⟨Cert.framesSat_lookup hc he hg, fun k hk => ?_⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · simp only [SFunc.framesSat, he] at hf
        rw [hcf, hca, hcr]
        exact hf
      · exact hK k hk
  | ret => exact ⟨hK _ List.mem_cons_self, fun k hk => hK k (List.mem_cons_of_mem _ hk)⟩
  | pcAt => exact ⟨hf, hK⟩

theorem Cursor.framesSat_of_reachable {c : Cert} {P : Ninst → List AVal → Bool}
    (hc : c.framesSat P = true) (h0 : ∀ p ∈ c.head?, p.2.framesSat c.entries P [] = true)
    {κ : Cursor} (reach : Relation.ReflTransGen (SStep c) (Cursor.start c) κ) :
    κ.FramesSat c.entries P := by
  induction reach with
  | refl =>
      cases c with
      | nil => exact ⟨rfl, fun _ h => by cases h⟩
      | cons p c => exact ⟨h0 p rfl, fun _ h => by cases h⟩
  | tail _ step ih => exact step.framesSat hc ih

/-- At a cursor-placed node decoding an external instruction, `P` holds of it. -/
theorem CursorOK.framesSat_exec {code : ByteArray} {c : Cert} {n : Exec.Deriv} {κ : Cursor}
    {P : Ninst → List AVal → Bool} (ok : CursorOK code c n κ) (h : κ.FramesSat c.entries P)
    {x : Xinst} (hat : Ninst.At n.sevm.code n.pc (.exec x)) : P (.exec x) κ.a = true := by
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hat
  have := h.1
  rw [hf] at this
  simp only [SFunc.framesSat, Bool.and_eq_true] at this
  exact this.1

/-- A constant position of a matched frame is the actual word. -/
theorem FrameMatches.getElem?_const {ρ : B256} :
    ∀ {a : List AVal} {S : List B256} (_ : FrameMatches ρ a S) {i : Nat} {w : B256},
      a[i]? = some (.const w) → S[i]? = some w
  | [], [], _, _, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | _ :: _, _ :: _, .cons hv _, 0, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h ⊢
      subst h
      exact hv
  | _ :: _, _ :: _, .cons _ ht, i + 1, _, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact FrameMatches.getElem?_const ht h

/-- The actual operand-stack word at a constant position of a cursor's frame. -/
theorem CursorOK.stack_const {code : ByteArray} {c : Cert} {n : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c n κ) {i : Nat} {w : B256} (h : κ.a[i]? = some (.const w)) :
    n.devm.stack[i]? = some w := by
  obtain ⟨S, rest, hstack, matched, -⟩ := ok.stack
  have hS := FrameMatches.getElem?_const matched h
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hS
  rw [hstack, List.getElem?_append_left hi]
  exact hS

end Blanc.Lift
