import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.Lift.UniswapV2Pair.MutableTurns

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- An absent original recursive slot has no retained child events. -/
theorem SourceSlotEvents.empty_of_none {root : Exec.Deriv} {x : Xinst}
    {call : CallOccurrenceStep root x} {pair : Adr} {index : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)}
    (queue : SourceSlotEvents call pair index events)
    (none : call.occurrence.slot = .none) : events = [] := by
  rcases queue with ⟨_, empty⟩ |
    ⟨child, raw, callee, resume, pc, run, next, spawn, enter, resumed, slot, original, eventsEq⟩
  · exact empty
  · rw [none] at slot
    cases slot

/-- An unguarded source reply's missing-entry bit is the same original absent
slot; mapping its exact full events therefore gives the empty mutable transcript. -/
theorem SourceCallAt.noCodeMutableTranscript {root : Exec.Deriv} {frame : Frame}
    {request : Request} {reply : ExternalResult} {index : Nat}
    {events : List (Log ⊕ Exec.LocatedFrame)} {turns : List MutableTurn}
    (observed : SourceCallAt root frame request reply index)
    (requires : request.requiresCode = false)
    (queue : SourceSlotEvents observed.call frame.context.pair index events)
    (mapped : turns.map MutableTurn.event = events)
    (missing : reply.codeExists = false) : mutableTranscript turns .done = .done := by
  have bit := observed.unguardedEntry requires
  have none : observed.call.occurrence.slot = .none := by
    cases slot : observed.call.occurrence.slot with
    | none => rfl
    | some selected =>
      rw [slot, missing] at bit
      cases bit
  have empty := queue.empty_of_none none
  have noTurns := List.eq_nil_of_map_eq_nil (mapped.trans empty)
  rw [noTurns]
  rfl

end Blanc.Lift.UniswapV2Pair
