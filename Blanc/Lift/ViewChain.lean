import Blanc.Lift.RootChain
import Blanc.ExecutionAccountingPositionalHistory

/-!
# Frames carrying a view of an account's storage

`ViewChain T V Good a fs b` is `FrameChain` through a view `V` of the words: frames `fs` carry `V`
of `T`'s storage from `a` to `b`. A proxy's upgrade writes its implementation slot between two token
frames, so its token frames chain only on the words apart from the proxy's own slots.

`viewCarrier`, `viewObservation` are `chainCarrier` and `chainView` through `V`.
`mid_viewChain` assembles the settled chain of a mid history from a target handler, the deletion
exclusions (`RootChain`) and what each settled root needs (`RootsReady`), with no
`InstalledRuntimeSafety`.

`FrameChain` is left as it is, for the coins whose whole storage chains.
-/

namespace Blanc.Lift

open Jaune Blanc Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

/-- Frames `fs` carry `V` of `T`'s words from `a` to `b`, each entered where the last one left it. -/
def ViewChain (T : Adr) (V : StorWords → StorWords) (Good : Exec.Frame → Prop) :
    StorWords → List Exec.Frame → StorWords → Prop
  | a, [], b => b = a
  | a, F :: fs, b => Good F ∧ V (wordsAt T F.pre.state) = a ∧
      ViewChain T V Good (V (wordsAt T F.post.state)) fs b

namespace ViewChain

variable {T : Adr} {V : StorWords → StorWords} {Good : Exec.Frame → Prop}

theorem append : ∀ {a b c : StorWords} {xs ys : List Exec.Frame},
    ViewChain T V Good a xs b → ViewChain T V Good b ys c → ViewChain T V Good a (xs ++ ys) c
  | _, _, _, [], _, hx, hy => by
    cases hx
    exact hy
  | _, _, _, _ :: _, _, hx, hy => ⟨hx.1, hx.2.1, append hx.2.2 hy⟩

theorem good : ∀ {a b : StorWords} {xs : List Exec.Frame}, ViewChain T V Good a xs b →
    ∀ F ∈ xs, Good F
  | _, _, [], _, _, h => absurd h List.not_mem_nil
  | _, _, _ :: _, hx, F, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact hx.1
    · exact good hx.2.2 F h

/-- A property every frame carries holds at each frame's entry and exit. -/
theorem inv_all {I : StorWords → Prop} :
    ∀ {a b : StorWords} {xs : List Exec.Frame}, ViewChain T V Good a xs b →
      (∀ F ∈ xs, Good F → I (V (wordsAt T F.pre.state)) → I (V (wordsAt T F.post.state))) → I a →
      ∀ F ∈ xs, I (V (wordsAt T F.pre.state))
  | _, _, [], _, _, _, _, h => absurd h List.not_mem_nil
  | _, _, G :: _, h, keep, ha, F, member => by
    obtain ⟨hg, rfl, rest⟩ := h
    rcases List.mem_cons.mp member with rfl | member
    · exact ha
    · exact inv_all rest (fun H hH => keep H (List.mem_cons_of_mem _ hH))
        (keep G List.mem_cons_self hg ha) F member

end ViewChain

/-- **The view carrier** at `T`. A step `Keep` marks out still has to be allowed, so that its replay can be vacuous,
but it is no link of the chain. -/
noncomputable def viewCarrier (T : Adr) (V : StorWords → StorWords) (Good Allowed : Exec.Frame → Prop)
    (Keep : Exec.Frame → Bool) : ReplayCarrier T where
  readsStorage := true
  Snap := StorWords
  Step := Exec.Frame
  Tag := Unit
  Replay a xs b := (∀ F ∈ xs, Allowed F) → ViewChain T V Good a (xs.filter Keep) b
  ofState w := V (wordsAt T w)
  frameEntry _ w := V (wordsAt T w)
  nil := fun _ _ => rfl
  silent := fun storage _ => congrArg V (congrArg Stor.get (storage rfl))
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], fun _ => congrArg V (congrArg Stor.get storage)⟩
  entry_eq_ofState := by
    intro _ _ caller_ne _ transfer sum_nof
    exact congrArg V (congrArg Stor.get (benvAfterTransfer_getStor_eq_of_safe transfer sum_nof
      (fun h1 _ => Or.inl (caller_ne h1))))

/-- The view carrier's observation: the frames themselves. -/
noncomputable def viewObservation (T : Adr) (V : StorWords → StorWords) (Obs Good Allowed : Exec.Frame → Prop)
    (Keep : Exec.Frame → Bool) : ReplayObservation (viewCarrier T V Good Allowed Keep) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := coinObs T Obs
  credit := by
    intro _ pre post _ storage _ _
    exact ⟨[], fun _ => congrArg V (congrArg Stor.get storage), rfl⟩

theorem viewCarrier_append {T : Adr} {V : StorWords → StorWords} {Good Allowed : Exec.Frame → Prop}
    {Keep : Exec.Frame → Bool} {a b c : StorWords} {xs ys : List Exec.Frame}
    (hx : (viewCarrier T V Good Allowed Keep).Replay a xs b)
    (hy : (viewCarrier T V Good Allowed Keep).Replay b ys c) :
    (viewCarrier T V Good Allowed Keep).Replay a (xs ++ ys) c := fun all => by
  change ViewChain T V Good a ((xs ++ ys).filter Keep) c
  rw [List.filter_append]
  exact (hx fun F h => all F (List.mem_append_left _ h)).append
    (hy fun F h => all F (List.mem_append_right _ h))

/-- What `mid_viewChain` concludes. -/
def ViewSettled (T : Adr) (V : StorWords → StorWords) (Obs Good Allowed : Exec.Frame → Prop)
    (Keep : Exec.Frame → Bool) (a b : StorWords) (frames : List Exec.Frame) : Prop :=
  ((∀ F ∈ coinFrames T Obs frames, Allowed F) →
    ViewChain T V Good a ((coinFrames T Obs frames).filter Keep) b) ∧
    ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
      frames = before ++ f :: after →
      Exec.NoOpaqueAbove (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) before f →
      (∀ F ∈ coinFrames T Obs before, Allowed F) →
      ViewChain T V Good a ((coinFrames T Obs before).filter Keep) (V (wordsAt T f.pre.state))

/-- What a settled root needs for its own accounting. -/
def RootReady (F : Fork → Prop) (T : Adr) (sem : CodeSem) (entry : Sevm → Devm → Prop)
    (R : Exec.Frame) : Prop :=
  F R.sevm.benvStat.fork ∧ sem.At T R.pc R.sevm R.pre ∧ Exec.FrameAdmitted T entry R.run ∧
    sum R.pre.state.bal < 2 ^ 256 ∧ R.pc = 0

section Mid

variable {F : Fork → Prop} {T : Adr} {sem : CodeSem} {entry : Sevm → Devm → Prop}
  {V : StorWords → StorWords} {Obs Good Allowed : Exec.Frame → Prop} {Keep : Exec.Frame → Bool}

local notation "Ca" => viewCarrier T V Good Allowed Keep
local notation "Ob" => viewObservation T V Obs Good Allowed Keep

/-- **Settled roots whose accounting holds carry the view's chain.** -/
theorem viewSettled_of_roots
    (core : ∀ R : Exec.Frame, RootReady F T sem entry R → ∃ steps,
      (Ca).Replay (V (wordsAt T R.pre.state)) steps (V (wordsAt T R.post.state)) ∧
      steps = (Exec.committedFrames R.run).flatMap (coinObs T Obs))
    (positional : ∀ R : Exec.Frame, RootReady F T sem entry R →
      ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
        Exec.committedFrames R.run = before ++ f :: after →
        Exec.NoOpaqueAbove (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) before f →
        ∃ steps, (Ca).Replay (V (wordsAt T R.pre.state)) steps (V (wordsAt T f.pre.state)) ∧
          steps = before.flatMap (coinObs T Obs)) :
    ∀ {a b : StorWords} {roots : List Exec.Frame}, RootChain T a roots b →
      (∀ R ∈ roots, RootReady F T sem entry R) →
      ViewSettled T V Obs Good Allowed Keep (V a) (V b) (roots.flatMap fun R => Exec.committedFrames R.run) := by
  intro a b roots
  induction roots generalizing a with
  | nil =>
    intro h _
    cases h
    refine ⟨fun _ => rfl, fun {before f after} split => ?_⟩
    have empty : ([] : List Exec.Frame) = before ++ f :: after := split
    cases before <;> simp only [List.nil_append, List.cons_append, reduceCtorEq] at empty
  | cons R rest ih =>
    intro h ready
    obtain ⟨rfl, tail⟩ := h
    have here := ready R List.mem_cons_self
    have later := ih tail fun G hG => ready G (List.mem_cons_of_mem _ hG)
    obtain ⟨steps, replay, rfl⟩ := core R here
    rw [List.flatMap_cons]
    refine ⟨fun all => ?_, fun {before f after} split noOpaque all => ?_⟩
    · rw [coinFrames_append] at all ⊢
      rw [List.filter_append]
      exact (replay fun G hG => all G (List.mem_append_left _ hG)).append
        (later.1 fun G hG => all G (List.mem_append_right _ hG))
    · rcases List.split_append_cons split with ⟨m, hx, -⟩ | ⟨n, hb, hy⟩
      · obtain ⟨s, r, rfl⟩ := positional R here before f m hx noOpaque
        exact r all
      · subst hb
        rw [coinFrames_append] at all ⊢
        rw [List.filter_append]
        exact (replay fun G hG => all G (List.mem_append_left _ hG)).append
          (later.2 hy (Exec.NoOpaqueAbove.drop noOpaque)
            fun G hG => all G (List.mem_append_right _ hG))

end Mid

/-! ## Locality through a view, with a `held` that may read the frame -/

/-- **Locality of `held` at `T`, through the view `V`.** `held F` is how the frame `F` reads the view: a
token whose storage layout changes with its code reads it by the code `F` runs. -/
structure EntryLocalAt (T : Adr) (V : StorWords → StorWords) (Obs Good : Exec.Frame → Prop)
    (held : Exec.Frame → StorWords → Nat) (debit credit : Sevm → Nat) (a b : StorWords)
    (settled : List Exec.Frame) : Prop where
  /-- The view moves exactly through these frames, to the end. -/
  chain : ViewChain T V Good a (coinFrames T Obs settled) b
  /-- The same, to the entry of any settled frame no earlier non-static `T` frame encloses. -/
  at_ : ∀ {before : List Exec.Frame} {f : Exec.Frame} {after : List Exec.Frame},
    settled = before ++ f :: after →
    Exec.NoOpaqueAbove (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) before f →
    ViewChain T V Good a (coinFrames T Obs before) (V (wordsAt T f.pre.state))
  /-- Each frame's effect, read as that frame reads it, attributed by its message. -/
  law : ∀ F ∈ coinFrames T Obs settled,
    held F (V (wordsAt T F.pre.state)) + credit F.sevm ≤
      held F (V (wordsAt T F.post.state)) + debit F.sevm

end Blanc.Lift
