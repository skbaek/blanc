import Blanc.Lift.Cursor
import Blanc.Lift.CursorCuts
import Blanc.Lift.CallSiteChildren

/-!
# A window of a certificate, tracked forward along a frame's chain

A *window* is a finite set of certificate trees `W`, each with the one tree `p` it may be entered from
and an index `j` (`WindowEntry`, `(W, p, j)`).  `Cert.windowOk E sites` checks, over every tree of the
certificate, that a window tree occurs only as a child of its predecessor, never as a function body or a
call continuation, and that every `CALL` node is one of `sites`.  Then along the chain of a frame of the
certified code a cursor sits at a window tree only right after a synthetic step from its predecessor
(`Cursor.Checked.entrance`), so a property `Track j` of the actual node can be carried forward one
window edge at a time (`window_track`), with no backward walk.  Contract-neutral.
-/

namespace Blanc.Lift

open Jaune

/-- A window tree, the one tree it may be entered from, and its index. -/
abbrev WindowEntry := SFunc × SFunc × Nat

/-- If `child` is a window tree, `parent` is its predecessor. -/
def windowEdgeOk (E : List WindowEntry) (parent child : SFunc) : Bool :=
  E.all fun e => !(e.1 == child) || (parent == e.2.1)

/-- `f` is no window tree. -/
def notWindow (E : List WindowEntry) (f : SFunc) : Bool :=
  E.all fun e => !(e.1 == f)

/-- A `CALL` node is one of the listed sites. -/
def callSiteIn (sites : List SFunc) : SFunc → Bool
  | .next (.exec .call) g => sites.contains (.next (.exec .call) g)
  | _ => true

/-- Every edge of the tree enters a window tree only from its predecessor, call continuations are no
window trees, and every `CALL` node is a listed site. -/
def SFunc.windowEdges (E : List WindowEntry) (sites : List SFunc) : SFunc → Bool
  | .next n f => callSiteIn sites (.next n f) && windowEdgeOk E (.next n f) f &&
      SFunc.windowEdges E sites f
  | .dest f => windowEdgeOk E (.dest f) f && SFunc.windowEdges E sites f
  | .branch f g => windowEdgeOk E (.branch f g) f && windowEdgeOk E (.branch f g) g &&
      SFunc.windowEdges E sites f && SFunc.windowEdges E sites g
  | .branchTo f k => windowEdgeOk E (.branchTo f k) f && SFunc.windowEdges E sites f
  | .callNext _ f => notWindow E f && SFunc.windowEdges E sites f
  | .pcAt p f => windowEdgeOk E (.pcAt p f) f && SFunc.windowEdges E sites f
  | _ => true

/-- The certificate-wide window check. -/
def Cert.windowOk (E : List WindowEntry) (sites : List SFunc) (c : Cert) : Bool :=
  c.prog.all fun g => g.windowEdges E sites && notWindow E g

/-- The cursor's tree and pending continuations pass the window check. -/
def Cursor.Checked (E : List WindowEntry) (sites : List SFunc) (κ : Cursor) : Prop :=
  κ.f.windowEdges E sites = true ∧
    ∀ k ∈ κ.K, k.f.windowEdges E sites = true ∧ notWindow E k.f = true

theorem windowEdgeOk_spec {E : List WindowEntry} {parent child : SFunc}
    (h : windowEdgeOk E parent child = true) {e : WindowEntry} (he : e ∈ E) (same : e.1 = child) :
    parent = e.2.1 := by
  have := List.all_eq_true.mp h e he
  simp only [same, beq_self_eq_true, Bool.not_true, Bool.false_or, beq_iff_eq] at this
  exact this

theorem notWindow_spec {E : List WindowEntry} {f : SFunc} (h : notWindow E f = true)
    {e : WindowEntry} (he : e ∈ E) : e.1 ≠ f := by
  have := List.all_eq_true.mp h e he
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq] at this
  exact this

private theorem Cert.windowOk_prog {E : List WindowEntry} {sites : List SFunc} {c : Cert}
    (hw : c.windowOk E sites = true) {k : Nat} {g : SFunc} (hg : c.prog[k]? = some g) :
    g.windowEdges E sites = true ∧ notWindow E g = true := by
  have := List.all_eq_true.mp hw g (List.mem_of_getElem? hg)
  simpa only [Bool.and_eq_true] using this

theorem Cursor.Checked.step {E : List WindowEntry} {sites : List SFunc} {c : Cert}
    (hw : c.windowOk E sites = true) {κ κ' : Cursor} (h : κ.Checked E sites)
    (step : SStep c κ κ') : κ'.Checked E sites := by
  obtain ⟨hf, hK⟩ := h
  cases step with
  | next =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | dest =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | zero =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact ⟨hf.1.2, hK⟩
  | succ =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | toZero =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩
  | toSucc _ hg => exact ⟨(Cert.windowOk_prog hw hg).1, hK⟩
  | jump _ hg => exact ⟨(Cert.windowOk_prog hw hg).1, hK⟩
  | call κc _ hg hcf =>
      refine ⟨(Cert.windowOk_prog hw hg).1, fun k hk => ?_⟩
      rcases List.mem_cons.mp hk with rfl | hk
      · simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
        rw [hcf]
        exact ⟨hf.2, hf.1⟩
      · exact hK k hk
  | ret => exact ⟨(hK _ List.mem_cons_self).1, fun k hk => hK k (List.mem_cons_of_mem _ hk)⟩
  | pcAt =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact ⟨hf.2, hK⟩

/-- **Entering a window tree.**  A synthetic step from a checked cursor to a window tree starts at that
tree's predecessor. -/
theorem Cursor.Checked.entrance {E : List WindowEntry} {sites : List SFunc} {c : Cert}
    (hw : c.windowOk E sites = true) {κ κ' : Cursor} (h : κ.Checked E sites)
    (step : SStep c κ κ') {e : WindowEntry} (he : e ∈ E) (at' : κ'.f = e.1) : κ.f = e.2.1 := by
  obtain ⟨hf, hK⟩ := h
  cases step with
  | next =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact windowEdgeOk_spec hf.1.2 he at'.symm
  | dest =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact windowEdgeOk_spec hf.1 he at'.symm
  | zero =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact windowEdgeOk_spec hf.1.1.1 he at'.symm
  | succ =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact windowEdgeOk_spec hf.1.1.2 he at'.symm
  | toZero =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact windowEdgeOk_spec hf.1 he at'.symm
  | toSucc _ hg => exact (notWindow_spec (Cert.windowOk_prog hw hg).2 he at'.symm).elim
  | jump _ hg => exact (notWindow_spec (Cert.windowOk_prog hw hg).2 he at'.symm).elim
  | call _ _ hg => exact (notWindow_spec (Cert.windowOk_prog hw hg).2 he at'.symm).elim
  | ret => exact (notWindow_spec (hK _ List.mem_cons_self).2 he at'.symm).elim
  | pcAt =>
      simp only [SFunc.windowEdges, Bool.and_eq_true] at hf
      exact windowEdgeOk_spec hf.1 he at'.symm

/-- A checked cursor at a `CALL` node sits at a listed site. -/
theorem Cursor.Checked.callSite {E : List WindowEntry} {sites : List SFunc} {κ : Cursor}
    (h : κ.Checked E sites) {g : SFunc} (tree : κ.f = .next (.exec .call) g) :
    SFunc.next (.exec .call) g ∈ sites := by
  have hf := h.1
  rw [tree] at hf
  simp only [SFunc.windowEdges, callSiteIn, Bool.and_eq_true, List.contains_iff_mem] at hf
  exact hf.1.1

/-- **Window tracking.**  Along the chain of a frame of certified code entered at pc `0`, every node sits
at a checked cursor, and at a window tree `W` of index `j` the node satisfies `Track j`, provided `Track`
is carried along every window edge: from the predecessor's node (and `Track` of the predecessor's own
window indices) across the actual step to the window tree. -/
theorem window_track {code : ByteArray} {c : Cert} (hc : Cert.check code c = true)
    {E : List WindowEntry} {sites : List SFunc} (hw : c.windowOk E sites = true)
    {R : Exec.Deriv} (hpc : R.pc = 0) (hcode : R.sevm.code = code)
    (hfork : CoveredFork R.sevm.benvStat.fork) (Track : Nat → Exec.Deriv → Prop)
    (carry : ∀ {F F' : Exec.Deriv} {κ κ' : Cursor} {e : WindowEntry},
      Exec.Deriv.ParentPrefix R F → e ∈ E → κ.f = e.2.1 → κ'.f = e.1 → CursorOK code c F κ →
      ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm (κ.conf F.devm) (κ'.conf F'.devm) →
      Exec.Deriv.ParentStep F' F → (∀ e' ∈ E, κ.f = e'.1 → Track e'.2.2 F) → Track e.2.2 F')
    {N : Exec.Deriv} (chain : Exec.Deriv.ParentPrefix R N) :
    ∃ κ, CursorOK code c N κ ∧ κ.Checked E sites ∧ ∀ e ∈ E, κ.f = e.1 → Track e.2.2 N := by
  suffices h : ∀ {F n : Exec.Deriv}, Exec.Deriv.ParentPrefix F n →
      ∀ κ₀, CursorOK code c F κ₀ → CoveredFork F.sevm.benvStat.fork →
      Exec.Deriv.ParentPrefix R F → κ₀.Checked E sites →
      (∀ e ∈ E, κ₀.f = e.1 → Track e.2.2 F) →
      ∃ κ, CursorOK code c n κ ∧ κ.Checked E sites ∧ ∀ e ∈ E, κ.f = e.1 → Track e.2.2 n by
    have startChecked : (Cursor.start c).Checked E sites ∧ notWindow E (Cursor.start c).f = true := by
      cases c with
      | nil => simp only [Cert.check, List.all_nil, Bool.and_true, Bool.false_eq_true] at hc
      | cons p c =>
          have := Cert.windowOk_prog hw (k := 0) (g := p.2) rfl
          exact ⟨⟨this.1, fun _ h => by cases h⟩, this.2⟩
    exact h chain _ (cursor_start hc hpc hcode) hfork (.refl R) startChecked.1
      (fun e he at₀ => (notWindow_spec startChecked.2 he at₀.symm).elim)
  intro F n hp
  induction hp with
  | refl root => exact fun κ₀ ok _ _ checked track => ⟨κ₀, ok, checked, track⟩
  | step head _ ih =>
      intro κ₀ ok fork prefixR checked track
      obtain ⟨κ₁, synthetic, stateful, ok₁⟩ := cursor_stepS hc ok head fork
      have checked₁ := checked.step hw synthetic
      have track₁ : ∀ e ∈ E, κ₁.f = e.1 → Track e.2.2 _ := fun e he at₁ =>
        carry prefixR he (checked.entrance hw synthetic he at₁) at₁ ok stateful head track
      exact ih κ₁ ok₁ (by rw [Cursor.parentStep_sevm head]; exact fork) (prefixR.snoc head)
        checked₁ track₁

end Blanc.Lift
