import Blanc.ExecutionAccountingStorageFold

/-! Inverse prefix splitting of the exact guarded storage replay. -/

namespace Blanc.ExecutionAccountingReplay

open Jaune

/-- Split at an exact event-list boundary, retaining both guarded segments. -/
theorem GuardedStorageReplay.split {Event : Type} {update : Stor → Event → Stor}
    {valid : Stor → Event → Prop} {pre post : Stor} {left right : List Event}
    (replay : GuardedStorageReplay update valid pre (left ++ right) post) :
    GuardedStorageReplay update valid pre left (left.foldl update pre) ∧
      GuardedStorageReplay update valid (left.foldl update pre) right post := by
  induction left generalizing pre with
  | nil => exact ⟨.nil pre, replay⟩
  | cons event left ih =>
    cases replay with
    | cons guard tail =>
      obtain ⟨prefixReplay, suffixReplay⟩ := ih tail
      exact ⟨.cons guard prefixReplay, suffixReplay⟩

/-- The head guard belongs to the actual incoming boundary of this segment. -/
theorem GuardedStorageReplay.head_guard {Event : Type} {update : Stor → Event → Stor}
    {valid : Stor → Event → Prop} {pre post : Stor} {event : Event} {rest : List Event}
    (replay : GuardedStorageReplay update valid pre (event :: rest) post) :
    valid pre event := by
  cases replay with
  | cons guard tail => exact guard

end Blanc.ExecutionAccountingReplay
