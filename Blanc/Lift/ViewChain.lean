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

end Mid

/-! ## Locality through a view, with a `held` that may read the frame -/

end Blanc.Lift
