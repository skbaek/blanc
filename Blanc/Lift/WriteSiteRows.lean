import Blanc.Lift.WriteSiteLocality

/-! ## Write locality for one owner's rows of a two-level mapping

`ws_locality_keys` instantiated at the rows `m[p][g]` of a solc two-level mapping at base slot `b`
(`mapSlot g (mapSlot p b)`), over the root site list a write-site certificate lists.  The key type
is a row `(owner, key)` or a raw slot, so every listed site names a key:

- a row site `kecc k (kecc o (const b))` names the row of its two words in the frame;
- any other known site names its slot word;
- a `top` site (an `SLOAD`-derived slot, e.g. an initializer's string copy) names a tracked row of
  `p` or a slot that is none.

Collision freedom enters only as the frame-local `RowSep`: the tracked rows of `p` are pairwise
distinct, a listed row site meets one only as that row, and no other listed slot of the frame is
one.  Each is a statement about finitely many words of one frame (the consumer takes them from its
footprint's `Inj`/`Apart` and `FreshKeys` over the frame's touched keys); no hash injectivity is
assumed over all words.  Contract-neutral: no address, base or selector is fixed here. -/

namespace Blanc.Lift.WriteSite

open Jaune

/-- A listed site's guards hold in `ε`. -/
def Site.GuardsHold (s : Site) (ε : Env) : Prop := ∀ g ∈ s.guards, g.1.Den ε g.2

/-- The row `m[o][k]` of the two-level mapping at base slot `b`. -/
def rowSlot (b o k : B256) : B256 := mapSlot k (mapSlot o b)

/-- The owner and key terms of a row slot term `kecc k (kecc o (const b))`. -/
def rowOf (b : B256) : Term → Option (Term × Term)
  | .kecc k (.kecc o (.const c)) => if c = b then some (o, k) else none
  | _ => none

theorem rowOf_eval {b : B256} {t o k : Term} (h : rowOf b t = some (o, k)) (ε : Env) :
    t.eval ε = rowSlot b (o.eval ε) (k.eval ε) := by
  unfold rowOf at h
  split at h
  · split at h
    · rename_i hc
      cases h
      subst hc
      rfl
    · cases h
  · cases h

/-- The frame-local separation premise for owner `p`'s tracked rows (`T`, over key words) against
the listed sites `sites`, read in `ε`. -/
structure RowSep (b p : B256) (T : B256 → Prop) (sites : List Site) (ε : Env) : Prop where
  /-- The tracked rows of `p` are pairwise distinct. -/
  inj : ∀ g g', T g → T g' → rowSlot b p g = rowSlot b p g' → g = g'
  /-- A listed row site of the frame meets a tracked row of `p` only as that row. -/
  row : ∀ s ∈ sites, s.nonInc = false → s.GuardsHold ε → s.slot.known = true →
    ∀ o k, rowOf b s.slot = some (o, k) → ∀ g, T g →
      rowSlot b (o.eval ε) (k.eval ε) = rowSlot b p g → o.eval ε = p ∧ k.eval ε = g
  /-- No other known listed slot of the frame is a tracked row of `p`. -/
  other : ∀ s ∈ sites, s.nonInc = false → s.GuardsHold ε → s.slot.known = true →
    rowOf b s.slot = none → ∀ g, T g → s.slot.eval ε ≠ rowSlot b p g

/-- The key a listed site names in `ε` (see the module note).  A non-increasing site names a key
the way a `top` site does: the corollary never asks it for one. -/
def rowNamed (b p : B256) (T : B256 → Prop) (s : Site) (ε : Env) (κ : (B256 × B256) ⊕ B256) :
    Prop :=
  s.GuardsHold ε ∧
  match !s.nonInc && s.slot.known, rowOf b s.slot with
  | true, some (o, k) => κ = .inl (o.eval ε, k.eval ε)
  | true, none => κ = .inr (s.slot.eval ε)
  | false, _ =>
    (∃ g, T g ∧ κ = .inl (p, g)) ∨ (∃ x, κ = .inr x ∧ ∀ g, T g → rowSlot b p g ≠ x)

/-- The slot of a row-or-raw key. -/
def rowKeySlot (b : B256) : (B256 × B256) ⊕ B256 → B256
  | .inl (o, k) => rowSlot b o k
  | .inr x => x

/-- `GuardObs` is antitone in its slot family. -/
theorem GuardObs.mono {K K' : B256 → Prop} (hK : ∀ x, K' x → K x) {allowed : Prop} {sevm : Sevm}
    {d : Devm} {n : Ninst} (h : GuardObs K allowed sevm d n) : GuardObs K' allowed sevm d n :=
  fun hn x v rest hs hx => h hn x v rest hs (hK x hx)

/-- **Row locality.**  In a run whose `SSTORE`s meet the listed sites, every write at a tracked row
of owner `p` is non-increasing or in an `allowed` frame, provided every listed row site whose owner
word is `p` (`hown`) and every listed `top` site (`htop`) may increase its slot only in an `allowed`
frame. -/
theorem ws_row_locality {b p : B256} {T : B256 → Prop} {sites : List Site} {ε : Env}
    {allowed : Prop} (sep : RowSep b p T sites ε)
    (hown : ∀ s ∈ sites, s.nonInc = false → s.GuardsHold ε → s.slot.known = true →
      ∀ o k, rowOf b s.slot = some (o, k) → o.eval ε = p → allowed)
    (htop : ∀ s ∈ sites, s.nonInc = false → s.GuardsHold ε → s.slot.known = false → allowed)
    {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {pre post : Devm}
    (run : SProg.RunP (WsStep sites ε P) fs sevm pre post) :
    SProg.RunP (fun s d n d' => P s d n d' ∧
        GuardObs (fun x => ∃ g, T g ∧ rowSlot b p g = x) allowed s d n) fs sevm pre post := by
  have hloc := ws_locality_keys (rowKeySlot b) (fun κ => ∃ g, T g ∧ κ = .inl (p, g))
    (rowNamed b p T) (allowed := allowed) ?hname ?hinj ?howner run
  case hname =>
    intro s _ hni hg x hx
    cases hk : s.slot.known with
    | true =>
      have hc : (!s.nonInc && s.slot.known) = true := by simp only [hni, hk, Bool.not_false,
        Bool.and_self]
      cases hr : rowOf b s.slot with
      | some ok =>
        obtain ⟨o, k⟩ := ok
        refine ⟨.inl (o.eval ε, k.eval ε), ⟨hg, ?_⟩, ?_⟩
        · simp only [hc, hr]
        · rw [hx hk, rowOf_eval hr ε]
          rfl
      | none =>
        refine ⟨.inr (s.slot.eval ε), ⟨hg, ?_⟩, ?_⟩
        · simp only [hc, hr]
        · rw [hx hk]
          rfl
    | false =>
      have hc : (!s.nonInc && s.slot.known) = false := by simp only [hk, Bool.and_false]
      by_cases hrow : ∃ g, T g ∧ rowSlot b p g = x
      · obtain ⟨g, hTg, hgx⟩ := hrow
        refine ⟨.inl (p, g), ⟨hg, ?_⟩, hgx⟩
        simp only [hc]
        exact Or.inl ⟨g, hTg, rfl⟩
      · refine ⟨.inr x, ⟨hg, ?_⟩, rfl⟩
        simp only [hc]
        exact Or.inr ⟨x, rfl, fun g hTg hgx => hrow ⟨g, hTg, hgx⟩⟩
  case hinj =>
    intro s hs κ κ' hnamed hprot hslot
    obtain ⟨g', hTg', rfl⟩ := hprot
    obtain ⟨hg, hnm⟩ := hnamed
    cases hc : (!s.nonInc && s.slot.known) with
    | true =>
      have hni : s.nonInc = false := by
        cases h : s.nonInc
        · rfl
        · simp only [h, Bool.not_true, Bool.false_and] at hc; cases hc
      have hk : s.slot.known = true := by
        simp only [hni, Bool.not_false, Bool.true_and] at hc; exact hc
      cases hr : rowOf b s.slot with
      | some ok =>
        obtain ⟨o, k⟩ := ok
        simp only [hc, hr] at hnm
        subst hnm
        obtain ⟨ho, hkk⟩ := sep.row s hs hni hg hk o k hr g' hTg' hslot
        rw [ho, hkk]
      | none =>
        simp only [hc, hr] at hnm
        subst hnm
        exact absurd hslot (sep.other s hs hni hg hk hr g' hTg')
    | false =>
      simp only [hc] at hnm
      rcases hnm with ⟨g, hTg, rfl⟩ | ⟨x, rfl, hx⟩
      · rw [sep.inj g g' hTg hTg' hslot]
      · exact absurd hslot.symm (hx g' hTg')
  case howner =>
    intro s hs hni hg κ hnamed hprot
    obtain ⟨g, _, rfl⟩ := hprot
    obtain ⟨_, hnm⟩ := hnamed
    cases hk : s.slot.known with
    | true =>
      have hc : (!s.nonInc && s.slot.known) = true := by simp only [hni, hk, Bool.not_false,
        Bool.and_self]
      cases hr : rowOf b s.slot with
      | some ok =>
        obtain ⟨o, k⟩ := ok
        simp only [hc, hr] at hnm
        cases hnm
        exact hown s hs hni hg hk o k hr rfl
      | none =>
        simp only [hc, hr] at hnm
        cases hnm
    | false => exact htop s hs hni hg hk
  refine SProg.RunP.mono ?_ hloc
  intro s d n d' h
  refine ⟨h.1, GuardObs.mono ?_ h.2⟩
  intro x ⟨g, hTg, hgx⟩
  exact ⟨.inl (p, g), ⟨g, hTg, rfl⟩, hgx⟩

end Blanc.Lift.WriteSite
