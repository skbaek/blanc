import Blanc.Lift.Token.Holder

/-!
# Token interface facet: minter and supply

A separate facet over a `Book`, following the core's facet convention (`Blanc/Lift/Token/Core.lean`):
a token with a privileged minter whose supply moves only by the minter's mints and burns.  It reads
the book's ledger through two projections (`supply`, `minter`) and classifies a message as a mint or
a burn of an amount (`mintOf`, `burnOf`); its laws are one-step facts of the book.  Zero-amount mints
and burns are classified and counted like any other.

`SupplyFacet.run_supply` is the generic run arithmetic: along any accepted run of the book whose
minter-sent messages keep the minter, the minter persists and the final supply plus the burned
amounts equals the initial supply plus the minted amounts.  Contract-neutral; no storage layout.
-/

namespace Blanc.Lift.Token

open Jaune Blanc

/-- **Facet: minter and supply.**  An accepted mint or burn is sent by the minter, moves the supply by
its amount and keeps the minter; any other accepted message keeps the supply; only the minter changes
the minter. -/
structure SupplyFacet (B : Book) where
  supply : B.Ledger → Nat
  minter : B.Ledger → Adr
  /-- The recipient and amount of a mint message, if it is one. -/
  mintOf : Sevm → Option (Adr × Nat)
  /-- The source and amount of a burn message, if it is one. -/
  burnOf : Sevm → Option (Adr × Nat)
  mint_step : ∀ {l l' : B.Ledger} {a : Sevm} {d : Adr} {v : Nat}, B.step l a = some l' →
    mintOf a = some (d, v) →
    a.caller = minter l ∧ supply l' = supply l + v ∧ minter l' = minter l
  burn_step : ∀ {l l' : B.Ledger} {a : Sevm} {d : Adr} {v : Nat}, B.step l a = some l' →
    burnOf a = some (d, v) →
    a.caller = minter l ∧ supply l' + v = supply l ∧ minter l' = minter l
  other_step : ∀ {l l' : B.Ledger} {a : Sevm}, B.step l a = some l' → mintOf a = none →
    burnOf a = none → supply l' = supply l
  minter_step : ∀ {l l' : B.Ledger} {a : Sevm}, B.step l a = some l' →
    minter l' ≠ minter l → a.caller = minter l

namespace SupplyFacet

variable {B : Book}

/-- The total amount the mint messages of `as` mint. -/
def minted (F : SupplyFacet B) (as : List Sevm) : Nat :=
  ((as.filterMap F.mintOf).map Prod.snd).sum

/-- The total amount the burn messages of `as` burn. -/
def burned (F : SupplyFacet B) (as : List Sevm) : Nat :=
  ((as.filterMap F.burnOf).map Prod.snd).sum

/-- A message that, whenever the book accepts it, keeps the minter. -/
def KeepsMinter (F : SupplyFacet B) (a : Sevm) : Prop :=
  ∀ {l l' : B.Ledger}, B.step l a = some l' → F.minter l' = F.minter l

theorem minted_cons (F : SupplyFacet B) (a : Sevm) (as : List Sevm) :
    F.minted (a :: as) = ((F.mintOf a).map Prod.snd).getD 0 + F.minted as := by
  unfold minted
  cases h : F.mintOf a with
  | none => simp only [List.filterMap_cons_none h, Option.map_none, Option.getD_none, Nat.zero_add]
  | some p =>
    simp only [List.filterMap_cons_some h, List.map_cons, List.sum_cons, Option.map_some,
      Option.getD_some]

theorem burned_cons (F : SupplyFacet B) (a : Sevm) (as : List Sevm) :
    F.burned (a :: as) = ((F.burnOf a).map Prod.snd).getD 0 + F.burned as := by
  unfold burned
  cases h : F.burnOf a with
  | none => simp only [List.filterMap_cons_none h, Option.map_none, Option.getD_none, Nat.zero_add]
  | some p =>
    simp only [List.filterMap_cons_some h, List.map_cons, List.sum_cons, Option.map_some,
      Option.getD_some]

theorem minted_append (F : SupplyFacet B) (xs ys : List Sevm) :
    F.minted (xs ++ ys) = F.minted xs + F.minted ys := by
  simp only [minted, List.filterMap_append, List.map_append, List.sum_append]

theorem burned_append (F : SupplyFacet B) (xs ys : List Sevm) :
    F.burned (xs ++ ys) = F.burned xs + F.burned ys := by
  simp only [burned, List.filterMap_append, List.map_append, List.sum_append]

/-- **One accepted step**: the minter is kept unless the minter sent the message, and the supply moves
by exactly the step's minted and burned amounts. -/
theorem step_supply (F : SupplyFacet B) {l l' : B.Ledger} {a : Sevm} (h : B.step l a = some l') :
    (F.minter l' ≠ F.minter l → a.caller = F.minter l) ∧
      F.supply l' + ((F.burnOf a).map Prod.snd).getD 0 =
        F.supply l + ((F.mintOf a).map Prod.snd).getD 0 := by
  refine ⟨F.minter_step h, ?_⟩
  cases hm : F.mintOf a with
  | some p =>
    obtain ⟨d, v⟩ := p
    have hmint := F.mint_step h hm
    cases hb : F.burnOf a with
    | none =>
      simp only [Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
        Nat.add_zero]
      exact hmint.2.1
    | some q =>
      obtain ⟨e, w⟩ := q
      have hburn := F.burn_step h hb
      simp only [Option.map_some, Option.getD_some]
      omega
  | none =>
    cases hb : F.burnOf a with
    | none =>
      simp only [Option.map_none, Option.getD_none, Nat.add_zero]
      exact F.other_step h hm hb
    | some q =>
      obtain ⟨e, w⟩ := q
      have hburn := F.burn_step h hb
      simp only [Option.map_some, Option.map_none, Option.getD_some, Option.getD_none,
        Nat.add_zero]
      exact hburn.2.1

/-- **Supply identity over a run.**  Along an accepted run of the book in which every message the
minter sends keeps the minter, the minter persists and the final supply plus the burned amounts is
the initial supply plus the minted amounts. -/
theorem run_supply (F : SupplyFacet B) :
    ∀ {as : List Sevm} {l l' : B.Ledger}, B.run l as = some l' →
      (∀ a ∈ as, a.caller = F.minter l → F.KeepsMinter a) →
      F.minter l' = F.minter l ∧ F.supply l' + F.burned as = F.supply l + F.minted as := by
  intro as
  induction as with
  | nil =>
    intro l l' hrun _
    simp only [Book.run, Option.some.injEq] at hrun
    subst hrun
    exact ⟨rfl, rfl⟩
  | cons a as ih =>
    intro l l' hrun keeps
    simp only [Book.run] at hrun
    cases hs : B.step l a with
    | none => rw [hs, Option.bind_none] at hrun; cases hrun
    | some m =>
      rw [hs, Option.bind_some] at hrun
      obtain ⟨changed, moved⟩ := F.step_supply hs
      have hm : F.minter m = F.minter l := by
        apply Classical.byContradiction
        intro hne
        exact hne (keeps a List.mem_cons_self (changed hne) hs)
      obtain ⟨ihm, ihs⟩ := ih hrun fun a' ha' hc =>
        keeps a' (List.mem_cons_of_mem a ha') (by rw [hc, hm])
      refine ⟨by rw [ihm, hm], ?_⟩
      rw [minted_cons, burned_cons]
      omega

/-- **A run the minter takes no part in keeps supply and minter**: along an accepted run of the book
none of whose messages the minter sends, no mint or burn is accepted and the minter cannot change,
so the supply and the minter are kept. -/
theorem run_keep (F : SupplyFacet B) :
    ∀ {as : List Sevm} {l l' : B.Ledger}, B.run l as = some l' →
      (∀ a ∈ as, a.caller ≠ F.minter l) →
      F.supply l' = F.supply l ∧ F.minter l' = F.minter l := by
  intro as
  induction as with
  | nil =>
    intro l l' hrun _
    simp only [Book.run, Option.some.injEq] at hrun
    subst hrun
    exact ⟨rfl, rfl⟩
  | cons a as ih =>
    intro l l' hrun foreign
    simp only [Book.run] at hrun
    cases hs : B.step l a with
    | none => rw [hs, Option.bind_none] at hrun; cases hrun
    | some m =>
      rw [hs, Option.bind_some] at hrun
      have other := foreign a List.mem_cons_self
      have hm : F.minter m = F.minter l := by
        apply Classical.byContradiction
        intro hne
        exact other (F.minter_step hs hne)
      have hsup : F.supply m = F.supply l := by
        cases hmint : F.mintOf a with
        | some p => exact absurd (F.mint_step hs hmint).1 other
        | none =>
          cases hburn : F.burnOf a with
          | some p => exact absurd (F.burn_step hs hburn).1 other
          | none => exact F.other_step hs hmint hburn
      obtain ⟨ihs, ihm⟩ := ih hrun fun a' ha' => by
        rw [hm]
        exact foreign a' (List.mem_cons_of_mem a ha')
      exact ⟨ihs.trans hsup, ihm.trans hm⟩

end SupplyFacet

end Blanc.Lift.Token
