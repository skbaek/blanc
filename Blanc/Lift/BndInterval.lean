/-!
# The shared symbol-interval reading of the bound checkers (unit H1b)

`Blanc.Lift.FreePtr` and `Blanc.Lift.LockCheck` check different `Fact` types,
but both read numeric bounds through the same two folds: `bndOf` (the `bnd`
facts' interval for one symbol) and `bnd2` (`bndOf`, refined once through the
order facts). This module owns that shared shape once, parameterized over a
small projection interface:

* `getBnd : F → Option (Nat × Nat × Nat)` reads a `bnd` fact's
  `(symbol, lo, hi)`;
* `getOrd : F → Option (Bool × Nat × Nat)` reads an order fact's
  `(isStrict, a, b)`: `lt` is strict, `le` is not.

Both checkers keep their own `Fact` types, their `bndOf`/`bnd2` names, and
their soundness statements: each is a two-line wrapper around the shared fold,
plus a per-fact bridge discharged once by casing on its own `Fact`. The fold
inductions (`bndOfG_sound`, `bnd2G_sound`) live here, over a valuation
`val : Nat → Nat` and the two projection laws, so neither checker restates
them.

Contract-neutral (imports nothing but core Lean): SHARED.
-/

namespace Blanc.Lift.BndInterval

/-- Fold the `bnd` facts of `fs` (read through `getBnd`) into the interval of
symbol `s`; `maxW` is the checker's largest word. -/
def bndOfG {F : Type} (getBnd : F → Option (Nat × Nat × Nat)) (maxW : Nat)
    (fs : List F) (s : Nat) : Nat × Nat :=
  fs.foldl (fun p f => match getBnd f with
    | some (s', lo, hi) => if s' = s then (max p.1 lo, min p.2 hi) else p
    | none => p) (0, maxW)

/-- `bndOfG`, refined once through the order facts (read through `getOrd`). -/
def bnd2G {F : Type} (getBnd : F → Option (Nat × Nat × Nat))
    (getOrd : F → Option (Bool × Nat × Nat)) (maxW : Nat)
    (fs : List F) (s : Nat) : Nat × Nat :=
  fs.foldl (fun p f => match getOrd f with
    | some (true, a, b) =>
      if a = s then (p.1, min p.2 ((bndOfG getBnd maxW fs b).2 - 1))
      else if b = s then (max p.1 ((bndOfG getBnd maxW fs a).1 + 1), p.2) else p
    | some (false, a, b) =>
      if a = s then (p.1, min p.2 (bndOfG getBnd maxW fs b).2)
      else if b = s then (max p.1 (bndOfG getBnd maxW fs a).1, p.2) else p
    | none => p) (bndOfG getBnd maxW fs s)

/-- The shared `bndOf` fold stays around the valuation. -/
theorem bndOfG_sound {F : Type} {getBnd : F → Option (Nat × Nat × Nat)}
    {maxW : Nat} {fs : List F} {val : Nat → Nat}
    (hle : ∀ t, val t ≤ maxW)
    (hbnd : ∀ f ∈ fs, ∀ s' lo hi,
      getBnd f = some (s', lo, hi) → lo ≤ val s' ∧ val s' ≤ hi)
    (s : Nat) :
    (bndOfG getBnd maxW fs s).1 ≤ val s ∧
      val s ≤ (bndOfG getBnd maxW fs s).2 := by
  unfold bndOfG
  have key : ∀ (gs : List F) (p : Nat × Nat), (∀ g ∈ gs, g ∈ fs) →
      p.1 ≤ val s ∧ val s ≤ p.2 →
      (gs.foldl (fun p f => match getBnd f with
        | some (s', lo, hi) => if s' = s then (max p.1 lo, min p.2 hi) else p
        | none => p) p).1 ≤ val s ∧
      val s ≤ (gs.foldl (fun p f => match getBnd f with
        | some (s', lo, hi) => if s' = s then (max p.1 lo, min p.2 hi) else p
        | none => p) p).2 := by
    intro gs
    induction gs with
    | nil => intro p _ hp; exact hp
    | cons g gs ih =>
      intro p hsub hp
      simp only [List.foldl_cons]
      apply ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      match hg : getBnd g with
      | some (s', lo, hi) =>
        have hfact := hbnd _ (hsub _ List.mem_cons_self) _ _ _ hg
        by_cases hs : s' = s
        · subst hs
          simp only [ite_true]
          exact ⟨Nat.max_le.mpr ⟨hp.1, hfact.1⟩, Nat.le_min.mpr ⟨hp.2, hfact.2⟩⟩
        · simp only [hs, ite_false]; exact hp
      | none =>
        exact hp
  exact key fs _ (fun _ h => h) ⟨Nat.zero_le _, hle s⟩

/-- The shared `bnd2` fold stays around the valuation. -/
theorem bnd2G_sound {F : Type} {getBnd : F → Option (Nat × Nat × Nat)}
    {getOrd : F → Option (Bool × Nat × Nat)} {maxW : Nat}
    {fs : List F} {val : Nat → Nat}
    (hle : ∀ t, val t ≤ maxW)
    (hbnd : ∀ f ∈ fs, ∀ s' lo hi,
      getBnd f = some (s', lo, hi) → lo ≤ val s' ∧ val s' ≤ hi)
    (hord : ∀ f ∈ fs, ∀ strict a b,
      getOrd f = some (strict, a, b) →
      (strict = true → val a < val b) ∧ (strict = false → val a ≤ val b))
    (s : Nat) :
    (bnd2G getBnd getOrd maxW fs s).1 ≤ val s ∧
      val s ≤ (bnd2G getBnd getOrd maxW fs s).2 := by
  unfold bnd2G
  have key : ∀ (gs : List F) (p : Nat × Nat), (∀ g ∈ gs, g ∈ fs) →
      p.1 ≤ val s ∧ val s ≤ p.2 →
      (gs.foldl (fun p f => match getOrd f with
        | some (true, a, b) =>
          if a = s then (p.1, min p.2 ((bndOfG getBnd maxW fs b).2 - 1))
          else if b = s then (max p.1 ((bndOfG getBnd maxW fs a).1 + 1), p.2) else p
        | some (false, a, b) =>
          if a = s then (p.1, min p.2 (bndOfG getBnd maxW fs b).2)
          else if b = s then (max p.1 (bndOfG getBnd maxW fs a).1, p.2) else p
        | none => p) p).1 ≤ val s ∧
      val s ≤ (gs.foldl (fun p f => match getOrd f with
        | some (true, a, b) =>
          if a = s then (p.1, min p.2 ((bndOfG getBnd maxW fs b).2 - 1))
          else if b = s then (max p.1 ((bndOfG getBnd maxW fs a).1 + 1), p.2) else p
        | some (false, a, b) =>
          if a = s then (p.1, min p.2 (bndOfG getBnd maxW fs b).2)
          else if b = s then (max p.1 (bndOfG getBnd maxW fs a).1, p.2) else p
        | none => p) p).2 := by
    intro gs
    induction gs with
    | nil => intro p _ hp; exact hp
    | cons g gs ih =>
      intro p hsub hp
      simp only [List.foldl_cons]
      apply ih _ (fun x hx => hsub x (List.mem_cons_of_mem _ hx))
      match hg : getOrd g with
      | some (true, a, b) =>
        have hlt := (hord _ (hsub _ List.mem_cons_self) _ _ _ hg).1 rfl
        by_cases ha : a = s
        · subst ha
          have hb := bndOfG_sound hle hbnd b
          simp only [ite_true]
          exact ⟨hp.1, Nat.le_min.mpr ⟨hp.2, by omega⟩⟩
        · by_cases hb : b = s
          · subst hb
            have ha' := bndOfG_sound hle hbnd a
            simp only [ha, ite_false, ite_true]
            exact ⟨Nat.max_le.mpr ⟨hp.1, by omega⟩, hp.2⟩
          · simp only [ha, hb, ite_false]; exact hp
      | some (false, a, b) =>
        have hle' := (hord _ (hsub _ List.mem_cons_self) _ _ _ hg).2 rfl
        by_cases ha : a = s
        · subst ha
          have hb := bndOfG_sound hle hbnd b
          simp only [ite_true]
          exact ⟨hp.1, Nat.le_min.mpr ⟨hp.2, by omega⟩⟩
        · by_cases hb : b = s
          · subst hb
            have ha' := bndOfG_sound hle hbnd a
            simp only [ha, ite_false, ite_true]
            exact ⟨Nat.max_le.mpr ⟨hp.1, by omega⟩, hp.2⟩
          · simp only [ha, hb, ite_false]; exact hp
      | none =>
        exact hp
  exact key fs _ (fun _ h => h) (bndOfG_sound hle hbnd s)

end Blanc.Lift.BndInterval
