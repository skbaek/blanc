import Blanc.ExecutionAccountingPositional
import Blanc.Lift.RetainedTargetCompleteness
import Blanc.ExecutionWholeFrameAccounting
import Blanc.ExecutionAccountingCoreIn
import Blanc.ExecutionAccountingMidHistoryIn

/-!
# Positional history: the replay at the entry of every settled frame

`AccountingLadderAdmitted.configuredHistory` replays a whole configured history from its
checkpoint to its endpoint.  `PositionalLadder.rootAt` gives, for one message root, the replay
from the root's entry boundary to the entry of any committed frame of the run.  The two compose
through **the frame carrier** (`framesCarrier`): a ladder whose step is a settled frame and whose
replay carries the positional claim beside the full one. Its `append` is the only assembly, and every
history rung is the ordinary one over this carrier, on any fork domain:

* `PositionalLadder.frames` and `PositionalLadder.configuredHistory_at`, over the covered forks;
* `wholeFramePositionalLadderIn`, over a domain `F` without state gas, hence
  `AccountingLadderAdmittedIn.midHistoryIn` at every settled frame of a mid history.

Modelled on `Blanc.Lift.Curve3Crv.readyLadderH`, which observes every settled frame the same way.
-/

namespace Blanc

open Jaune

namespace ExecutionAccountingReplay

open ExecutionTrace

section Frames

variable {ca : Adr}

/-- Positional replay of a frame list from a boundary: at every split whose earlier part has no
opaque frame enclosing the selected frame, the boundary replays to the selected frame's entry,
observing exactly the earlier frames. -/
def PositionalAt (C : ReplayCarrier ca) (V : ReplayObservation C) (Opaque : Exec.Frame → Prop)
    (start : C.Snap) (frames : List Exec.Frame) : Prop :=
  ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
    frames = before ++ f :: after →
    Exec.NoOpaqueAbove Opaque before f →
    ∃ steps, C.Replay start steps (C.frameEntry f.sevm f.pre.state) ∧
      V.obs steps = before.flatMap V.frameObs

theorem PositionalAt.nil (C : ReplayCarrier ca) (V : ReplayObservation C)
    (Opaque : Exec.Frame → Prop) (start : C.Snap) : PositionalAt C V Opaque start [] := by
  intro before f after split
  exact absurd split.symm (List.append_ne_nil_of_right_ne_nil before (List.cons_ne_nil f after))

/-- **The frame carrier**: a step is a settled frame, and a replay over frames is the carrier's full
replay observing them together with the positional replay at each of them. The ordinary history
rungs run over it, so the positional history needs no rung of its own. -/
def framesCarrier (C : ReplayCarrier ca) (V : ReplayObservation C) (Opaque : Exec.Frame → Prop) :
    ReplayCarrier ca where
  Snap := C.Snap
  Step := Exec.Frame
  Tag := C.Tag
  Replay := fun a frames b =>
    (∃ steps, C.Replay a steps b ∧ V.obs steps = frames.flatMap V.frameObs) ∧
      PositionalAt C V Opaque a frames
  ofState := C.ofState
  frameEntry := C.frameEntry
  nil := fun a => ⟨⟨[], C.nil a, by rw [V.obs_nil, List.flatMap_nil]⟩, PositionalAt.nil C V Opaque a⟩
  readsStorage := C.readsStorage
  silent := C.silent
  credit := by
    intro tag _ _ _ storage balance positive
    obtain ⟨steps, replay, observed⟩ := V.credit tag storage balance positive
    exact ⟨[], ⟨steps, replay, observed⟩, PositionalAt.nil C V Opaque _⟩
  entry_eq_ofState := C.entry_eq_ofState

/-- The frame carrier observes each frame as itself. -/
def framesObservation (C : ReplayCarrier ca) (V : ReplayObservation C)
    (Opaque : Exec.Frame → Prop) : ReplayObservation (framesCarrier C V Opaque) where
  O := Exec.Frame
  obs := id
  obs_nil := rfl
  obs_append := fun _ _ => rfl
  frameObs := fun f => [f]
  credit := by
    intro tag _ _ _ storage balance positive
    obtain ⟨steps, replay, observed⟩ := V.credit tag storage balance positive
    exact ⟨[], ⟨⟨steps, replay, observed⟩, PositionalAt.nil C V Opaque _⟩, rfl⟩

/-- Frame replays compose: a split lands in the earlier part, or after its full replay. -/
theorem framesCarrier_append {C : ReplayCarrier ca} {V : ReplayObservation C}
    {Opaque : Exec.Frame → Prop}
    (append : ∀ {a b c xs ys}, C.Replay a xs b → C.Replay b ys c → C.Replay a (xs ++ ys) c)
    {a b c : C.Snap} {xs ys : List Exec.Frame}
    (left : (framesCarrier C V Opaque).Replay a xs b)
    (right : (framesCarrier C V Opaque).Replay b ys c) :
    (framesCarrier C V Opaque).Replay a (xs ++ ys) c := by
  obtain ⟨⟨leftSteps, leftReplay, leftObserved⟩, leftAt⟩ := left
  obtain ⟨⟨rightSteps, rightReplay, rightObserved⟩, rightAt⟩ := right
  refine ⟨⟨leftSteps ++ rightSteps, append leftReplay rightReplay, ?_⟩, ?_⟩
  · rw [V.obs_append, leftObserved, rightObserved, List.flatMap_append]
  · intro before f after split noOpaque
    rcases List.split_append_cons split with ⟨m, hX, _⟩ | ⟨n, hb, hY⟩
    · exact leftAt before f m hX noOpaque
    · rw [hb] at noOpaque
      obtain ⟨rest, restReplay, restObserved⟩ := rightAt n f after hY
        (Exec.NoOpaqueAbove.drop noOpaque)
      refine ⟨leftSteps ++ rest, append leftReplay restReplay, ?_⟩
      rw [V.obs_append, leftObserved, restObserved, hb, List.flatMap_append]

/-- A root's full and positional replays are its frame replay. -/
theorem framesRoot {C : ReplayCarrier ca} {V : ReplayObservation C} {Opaque : Exec.Frame → Prop}
    {a b : C.Snap} {frames : List Exec.Frame}
    (whole : ∃ steps, C.Replay a steps b ∧ V.obs steps = frames.flatMap V.frameObs)
    (positional : PositionalAt C V Opaque a frames) :
    ∃ steps, (framesCarrier C V Opaque).Replay a steps b ∧
      (framesObservation C V Opaque).obs steps =
        frames.flatMap (framesObservation C V Opaque).frameObs :=
  ⟨frames, ⟨whole, positional⟩, (List.flatMap_singleton' frames).symm⟩

/-- Reading a frame replay at a list of settled frames: the full replay and the positional one. -/
theorem framesCarrier_read {C : ReplayCarrier ca} {V : ReplayObservation C}
    {Opaque : Exec.Frame → Prop} {a b : C.Snap} {steps frames : List Exec.Frame}
    (replay : (framesCarrier C V Opaque).Replay a steps b)
    (observed : (framesObservation C V Opaque).obs steps =
      frames.flatMap (framesObservation C V Opaque).frameObs) :
    (∃ steps, C.Replay a steps b ∧ V.obs steps = frames.flatMap V.frameObs) ∧
      PositionalAt C V Opaque a frames := by
  change steps = frames.flatMap (fun f => [f]) at observed
  rw [List.flatMap_singleton'] at observed
  subst observed
  exact replay

end Frames

namespace PositionalLadder

variable {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}

/-- A positional ladder is an accounting ladder over its frame carrier. -/
def frames (L : PositionalLadder c ca entry) : AccountingLadderAdmitted c ca entry where
  carrier := framesCarrier L.carrier L.view L.Opaque
  append := framesCarrier_append L.append
  tag := L.tag
  preserves := L.preserves
  view := framesObservation L.carrier L.view L.Opaque
  root := by
    intro blockIndex transactionIndex msg entryBenv pc sevm pre out run transfer evmEq committed
      admitted ready callerNe fork bound
    exact framesRoot
      (L.root blockIndex transactionIndex run transfer evmEq committed admitted ready callerNe fork
        bound)
      (L.rootAt blockIndex transactionIndex run transfer evmEq committed admitted ready callerNe fork
        bound)

/-- **Positional history, by position.**  In a configured history admitted at `ca` from a
state-invariant checkpoint, the boundary at the entry of every settled position that no opaque
earlier frame's block covers is the replay, from the checkpoint, of the observations of exactly the
settled frames before it. -/
theorem configuredHistory_atPos (L : PositionalLadder c ca entry) {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (admitted : history.FrameAdmitted ca entry)
    (inv : c.StateInv ca checkpoint.state) :
    ∀ (before : List Exec.Frame) (f : Exec.Frame) (after : List Exec.Frame),
      history.settledFrames = before ++ f :: after →
      Exec.NoOpaqueAbove L.Opaque before f →
      ∃ steps, L.carrier.Replay (L.carrier.ofState checkpoint.state) steps
          (L.carrier.frameEntry f.sevm f.pre.state) ∧
        L.view.obs steps = before.flatMap L.view.frameObs := by
  obtain ⟨steps, replay, observed⟩ := L.frames.configuredHistory history admitted inv
  exact (framesCarrier_read replay observed).2

end PositionalLadder

end ExecutionAccountingReplay

end Blanc
