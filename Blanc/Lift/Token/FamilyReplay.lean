import Blanc.ExecutionOwnerFamily
import Blanc.Lift.Token.Core

/-!
# The guarded book carrier and the observer bridge (contract-neutral)

A code family's ladder (`Blanc/ExecutionOwnerFamily.lean`) replays over a carrier whose boundary may
depend on storage the family's frames can rewrite (a proxy's implementation slot).  The **guarded
book carrier** reads a book ledger off the owner's storage together with a guard's verdict; a replay
claims, from a guarded boundary and over allowed messages only, that the book runs the steps and the
guard still holds, so the carrier says nothing at an unguarded boundary
(`guardedBookCarrier_unguarded`).

Its observer view sees the message of every non-static observer frame at the owner.  A token core
speaks of entry frames (`entryAsks`).  `ObserverChain` pairs each non-static entry with its observer
(itself, or the adjacent observer with a related message), and `ObserverChain.run_eq` turns the book
run over observer asks into the run over entry asks.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

open Classical in
/-- **The guarded book carrier** at `T`: the boundary is the book ledger `read` off `T`'s storage
with the guard's verdict; a replay claims, from a guarded boundary and over allowed messages only,
that the book runs the steps to the target ledger and the guard still holds. -/
noncomputable def guardedBookCarrier (T : Adr) (B : Book) (read : Stor → B.Ledger)
    (Guard : Stor → Prop) (Allowed : Sevm → Prop) : ReplayCarrier T where
  readsStorage := true
  Snap := B.Ledger × Bool
  Step := Sevm
  Tag := Unit
  Replay a xs b := a.2 = true → (∀ e ∈ xs, Allowed e) → B.run a.1 xs = some b.1 ∧ b.2 = true
  ofState w := (read (w.getStor T), decide (Guard (w.getStor T)))
  frameEntry _ w := (read (w.getStor T), decide (Guard (w.getStor T)))
  nil := fun _ guarded _ => ⟨rfl, guarded⟩
  silent := fun storage _ => by rw [storage rfl]
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_⟩
    rw [storage]
    exact fun guarded _ => ⟨rfl, guarded⟩
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    rw [benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun h1 _ => Or.inl (caller_ne h1))]

open Classical in
/-- Boundaries of states agreeing on `T`'s storage are equal. -/
private theorem guardedBookCarrier_ofState_eq {T : Adr} {B : Book} {read : Stor → B.Ledger}
    {Guard : Stor → Prop} {Allowed : Sevm → Prop} {pre post : State}
    (storage : post.getStor T = pre.getStor T) :
    (guardedBookCarrier T B read Guard Allowed).ofState post =
      (guardedBookCarrier T B read Guard Allowed).ofState pre := by
  show (read (post.getStor T), decide (Guard (post.getStor T))) =
    (read (pre.getStor T), decide (Guard (pre.getStor T)))
  rw [storage]

open Classical in
/-- The messages of the non-static observer frames at `T` among `fs`, in order. -/
noncomputable def observerAsks (T : Adr) (Obs : Exec.Frame → Prop) (fs : List Exec.Frame) :
    List Sevm :=
  (fs.filter fun f => decide (f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f)).map
    (·.sevm)

open Classical in
/-- **The observer view**: a non-static frame at `T` satisfying `Obs` observes its message. -/
noncomputable def observerView (T : Adr) (Obs : Exec.Frame → Prop) {B : Book}
    {read : Stor → B.Ledger} {Guard : Stor → Prop} {Allowed : Sevm → Prop} :
    ReplayObservation (guardedBookCarrier T B read Guard Allowed) where
  O := Sevm
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs f := if f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f then [f.sevm] else []
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_, rfl⟩
    rw [guardedBookCarrier_ofState_eq storage]
    exact (guardedBookCarrier T B read Guard Allowed).nil _

theorem observerView_flatMap (T : Adr) (Obs : Exec.Frame → Prop) {B : Book}
    {read : Stor → B.Ledger} {Guard : Stor → Prop} {Allowed : Sevm → Prop}
    (fs : List Exec.Frame) :
    fs.flatMap (observerView T Obs (B := B) (read := read) (Guard := Guard)
      (Allowed := Allowed)).frameObs = observerAsks T Obs fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      rw [List.flatMap_cons, ih]
      unfold observerAsks
      rw [List.filter_cons]
      by_cases h : f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f
      · simp only [observerView, h, and_self, ↓reduceIte, decide_true, List.map_cons]
        rfl
      · simp only [observerView, h, ↓reduceIte, decide_false, Bool.false_eq_true]
        rfl

theorem guardedBookCarrier_unguarded (T : Adr) (Obs : Exec.Frame → Prop) {B : Book}
    {read : Stor → B.Ledger} {Guard : Stor → Prop} {Allowed : Sevm → Prop} :
    CodeFamily.Unguarded (guardedBookCarrier T B read Guard Allowed)
      (observerView T Obs) Guard := by
  classical
  intro w b os unguarded
  refine ⟨os, fun guarded => absurd (of_decide_eq_true guarded) unguarded, rfl⟩

/-- A replay of the guarded book carrier from a guarded state, over allowed messages, is the book
run. -/
theorem guardedBook_run {T : Adr} {B : Book} {read : Stor → B.Ledger} {Guard : Stor → Prop}
    {Allowed : Sevm → Prop} {w w' : State} {steps : List Sevm}
    (replay : (guardedBookCarrier T B read Guard Allowed).Replay
      ((guardedBookCarrier T B read Guard Allowed).ofState w) steps
      ((guardedBookCarrier T B read Guard Allowed).ofState w'))
    (guard : Guard (w.getStor T)) (allowed : ∀ e ∈ steps, Allowed e) :
    B.run (read (w.getStor T)) steps = some (read (w'.getStor T)) ∧ Guard (w'.getStor T) := by
  classical
  obtain ⟨run, guard'⟩ := replay (decide_eq_true guard) allowed
  exact ⟨run, of_decide_eq_true guard'⟩

/-- **Entries and observers paired along a frame list.**  Each non-static entry at `T` is its own
observer, or is immediately followed by its (non-entry) observer carrying a related message; every
other frame is neither. -/
inductive ObserverChain (T : Adr) (Obs : Exec.Frame → Prop) (R : Sevm → Sevm → Prop) :
    List Exec.Frame → Prop
  | nil : ObserverChain T Obs R []
  | skip {f : Exec.Frame} {fs : List Exec.Frame} :
      ¬ (IsEntry T f ∧ f.sevm.isStatic = false) →
      ¬ (f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f) →
      ObserverChain T Obs R fs → ObserverChain T Obs R (f :: fs)
  | self {f : Exec.Frame} {fs : List Exec.Frame} :
      IsEntry T f → f.sevm.isStatic = false → Obs f →
      ObserverChain T Obs R fs → ObserverChain T Obs R (f :: fs)
  | pair {e o : Exec.Frame} {fs : List Exec.Frame} :
      IsEntry T e → e.sevm.isStatic = false → ¬ Obs e →
      o.sevm.currentTarget = T → o.sevm.isStatic = false → Obs o → ¬ IsEntry T o →
      R e.sevm o.sevm → ObserverChain T Obs R fs → ObserverChain T Obs R (e :: o :: fs)

/-- A chain cut before a frame that is not a non-entry frame at `T` leaves a chain. -/
theorem ObserverChain.prefix {T : Adr} {Obs : Exec.Frame → Prop} {R : Sevm → Sevm → Prop}
    {before after : List Exec.Frame} {f : Exec.Frame}
    (chain : ObserverChain T Obs R (before ++ f :: after))
    (entryAt : f.sevm.currentTarget = T → IsEntry T f) :
    ObserverChain T Obs R before := by
  generalize split : before ++ f :: after = l at chain
  induction chain generalizing before with
  | nil => exact absurd split (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | skip notEntry notObs _ ih =>
      cases before with
      | nil => exact .nil
      | cons g b =>
          obtain ⟨rfl, rest⟩ := List.cons.inj split
          exact .skip notEntry notObs (ih rest)
  | self isEntry nonstatic obs _ ih =>
      cases before with
      | nil => exact .nil
      | cons g b =>
          obtain ⟨rfl, rest⟩ := List.cons.inj split
          exact .self isEntry nonstatic obs (ih rest)
  | pair eEntry eStatic eObs oTarget oStatic oObs oEntry related _ ih =>
      cases before with
      | nil => exact .nil
      | cons g b =>
          obtain ⟨rfl, rest⟩ := List.cons.inj split
          cases b with
          | nil =>
              obtain ⟨rfl, -⟩ := List.cons.inj rest
              exact (oEntry (entryAt oTarget)).elim
          | cons g' b' =>
              obtain ⟨rfl, rest'⟩ := List.cons.inj rest
              exact .pair eEntry eStatic eObs oTarget oStatic oObs oEntry related (ih rest')

open Classical in
private theorem entryAsks_cons_pos {T : Adr} {f : Exec.Frame} (fs : List Exec.Frame)
    (h : IsEntry T f ∧ f.sevm.isStatic = false) :
    entryAsks T (f :: fs) = f.sevm :: entryAsks T fs := by
  unfold entryAsks
  rw [List.filter_cons_of_pos (by exact decide_eq_true h), List.map_cons]

open Classical in
private theorem entryAsks_cons_neg {T : Adr} {f : Exec.Frame} (fs : List Exec.Frame)
    (h : ¬ (IsEntry T f ∧ f.sevm.isStatic = false)) :
    entryAsks T (f :: fs) = entryAsks T fs := by
  unfold entryAsks
  rw [List.filter_cons_of_neg (by exact fun e => h (of_decide_eq_true e))]

open Classical in
private theorem observerAsks_cons_pos {T : Adr} {Obs : Exec.Frame → Prop} {f : Exec.Frame}
    (fs : List Exec.Frame) (h : f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f) :
    observerAsks T Obs (f :: fs) = f.sevm :: observerAsks T Obs fs := by
  unfold observerAsks
  rw [List.filter_cons_of_pos (by exact decide_eq_true h), List.map_cons]

open Classical in
private theorem observerAsks_cons_neg {T : Adr} {Obs : Exec.Frame → Prop} {f : Exec.Frame}
    (fs : List Exec.Frame) (h : ¬ (f.sevm.currentTarget = T ∧ f.sevm.isStatic = false ∧ Obs f)) :
    observerAsks T Obs (f :: fs) = observerAsks T Obs fs := by
  unfold observerAsks
  rw [List.filter_cons_of_neg (by exact fun e => h (of_decide_eq_true e))]

/-- Along a chain, the book runs the entry asks as it runs the observer asks. -/
theorem ObserverChain.run_eq {T : Adr} {Obs : Exec.Frame → Prop} {R : Sevm → Sevm → Prop}
    {B : Book} (congr : ∀ {a b : Sevm}, R a b → ∀ l, B.step l a = B.step l b)
    {fs : List Exec.Frame} (chain : ObserverChain T Obs R fs) (l : B.Ledger) :
    B.run l (entryAsks T fs) = B.run l (observerAsks T Obs fs) := by
  induction chain generalizing l with
  | nil => rfl
  | skip notEntry notObs _ ih =>
      rw [entryAsks_cons_neg _ notEntry, observerAsks_cons_neg _ notObs]
      exact ih l
  | @self f _ isEntry nonstatic obs _ ih =>
      rw [entryAsks_cons_pos _ ⟨isEntry, nonstatic⟩,
        observerAsks_cons_pos _ ⟨isEntry.1, nonstatic, obs⟩, Book.run, Book.run]
      exact congrArg (Option.bind (B.step l f.sevm)) (funext ih)
  | @pair e o _ eEntry eStatic eObs oTarget oStatic oObs oEntry related _ ih =>
      rw [entryAsks_cons_pos _ ⟨eEntry, eStatic⟩, entryAsks_cons_neg _ fun h => oEntry h.1,
        observerAsks_cons_neg _ fun h => eObs h.2.2,
        observerAsks_cons_pos _ ⟨oTarget, oStatic, oObs⟩, Book.run, Book.run, congr related l]
      exact congrArg (Option.bind (B.step l o.sevm)) (funext ih)

end Blanc.Lift.Token
