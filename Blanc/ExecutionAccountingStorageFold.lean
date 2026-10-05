import Blanc.ExecutionAccountingReplay

namespace Blanc.ExecutionAccountingReplay

open Jaune

/-- Each guard is checked against the storage at that occurrence, before its pure update. -/
inductive GuardedStorageReplay {Event : Type} (update : Stor → Event → Stor)
    (valid : Stor → Event → Prop) : Stor → List Event → Stor → Prop where
  | nil (boundary : Stor) : GuardedStorageReplay update valid boundary [] boundary
  | cons {pre post : Stor} {event : Event} {rest : List Event}
      (guard : valid pre event)
      (tail : GuardedStorageReplay update valid (update pre event) rest post) :
      GuardedStorageReplay update valid pre (event :: rest) post

theorem GuardedStorageReplay.append {Event : Type} {update : Stor → Event → Stor}
    {valid : Stor → Event → Prop} {pre mid post : Stor} {left right : List Event}
    (first : GuardedStorageReplay update valid pre left mid)
    (second : GuardedStorageReplay update valid mid right post) :
    GuardedStorageReplay update valid pre (left ++ right) post := by
  induction first with
  | nil => exact second
  | cons guard tail ih => exact .cons guard (ih second)

theorem GuardedStorageReplay.fold_eq {Event : Type} {update : Stor → Event → Stor}
    {valid : Stor → Event → Prop} {pre post : Stor} {events : List Event}
    (replay : GuardedStorageReplay update valid pre events post) :
    events.foldl update pre = post := by
  induction replay with
  | nil => rfl
  | cons guard tail ih =>
    rw [List.foldl_cons]
    exact ih

/-- Storage-only replay: message transfers and incidental balance credits are silent. -/
def storageFoldCarrier (ca : Adr) (Event : Type) (update : Stor → Event → Stor)
    (valid : Stor → Event → Prop) : ReplayCarrier ca where
  Snap := Stor
  Step := Event
  Tag := Unit
  Replay := GuardedStorageReplay update valid
  ofState state := state.getStor ca
  frameEntry _ state := state.getStor ca
  nil := .nil
  silent := fun storage _ => storage
  credit := by
    intro _ pre post _ storage _ _
    refine ⟨[], ?_⟩
    rw [storage]
    exact .nil _
  entry_eq_ofState := by
    intro _ _ _ _ transfer _
    exact congrFun (benvAfterTransfer_getStor_eq transfer) ca

end Blanc.ExecutionAccountingReplay
