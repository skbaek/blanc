import Blanc.ExecutionAccountingStorageFold
import Blanc.ListChunks

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

/-- The unique selected event carries the guard at its actual folded prefix. -/
theorem GuardedStorageReplay.find_guard_of_filter_one {Event : Type}
    {update : Stor → Event → Stor} {valid : Stor → Event → Prop}
    {start finish : Stor} {left middle right : List Event}
    (replay : GuardedStorageReplay update valid start (left ++ (middle ++ right)) finish)
    (p : Event → Bool) (one : (middle.filter p).length = 1) :
    ∃ event, middle.find? p = some event ∧
      valid ((left ++ middle.takeWhile (fun event => !p event)).foldl update start) event := by
  obtain ⟨before, event, after, split, -, -, found, taken⟩ :=
    Blanc.List.split_of_filter_length_one p one
  have shape : left ++ (middle ++ right) = (left ++ before) ++ event :: (after ++ right) := by
    rw [split]
    simp only [List.append_assoc, List.cons_append]
  rw [shape] at replay
  refine ⟨event, found, ?_⟩
  rw [taken]
  exact (replay.split (left := left ++ before) (right := event :: (after ++ right))).2.head_guard

end Blanc.ExecutionAccountingReplay
