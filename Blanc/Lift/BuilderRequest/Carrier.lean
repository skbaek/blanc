import Blanc.ExecutionKeptConfigured
import Blanc.Lift.BuilderRequest.Deposit.Indexed
import Blanc.Lift.BuilderRequest.Exit.Indexed

/-!
# The builder contracts' history across a covered prefix

A history from the deployed builder contracts may begin with blocks at covered forks (the execution side of the
pre-Gloas consensus steps, a configured history) and continue at Amsterdam. `ConfiguredHistoryTrace.splice` makes it
one kept history, `t.kept ++ ys`, and the occurrence-indexed results (`history_fifo`, `history_block`, `history_fate`,
`history_latency`) apply to it unchanged under `Clean`.

Here, for a covered prefix: its blocks emit nothing and have no request boundary (`history_block`'s covered clause,
block by block), so every submission kept in the prefix is carried across into the later blocks' emissions or the final
queue, in order (`Occurrence.carried`, for either builder contract with `reading`, `linked` and `Clean.premises`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune Delivery ChainLink ExecutionTrace

namespace Occurrence

variable {c : Contract} {ty : UInt8} {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}
  {st : QueueState c.Record}

/-- **Covered blocks emit nothing.** In a history satisfying the premises, a run of blocks at covered forks emits no
record and reads no request boundary. -/
theorem covered_emits_nothing (R : Reading c) (L : Linked c ty) (P : Premises c cfg start blocks stop st)
    {pre post : List KeptBlock} (split : blocks = pre ++ post) (covered : ∀ b ∈ pre, CoveredFork b.fork) :
    emissions R ty pre = [] ∧ ∀ b ∈ pre, queueAtRequests R b = [] := by
  have each : ∀ b ∈ pre, blockEmissions R ty b = [] ∧ queueAtRequests R b = [] := by
    intro b hb
    obtain ⟨l, r, rfl⟩ := List.append_of_mem hb
    have ne : b.fork ≠ .amsterdam := fun e => CoveredFork.not_amsterdam (e ▸ covered b hb)
    have split' : blocks = l ++ b :: (r ++ post) := by rw [split, List.append_assoc, List.cons_append]
    exact (history_block R L P split').2.1 ne
  refine ⟨?_, fun b hb => (each b hb).2⟩
  unfold emissions
  rw [List.flatMap_eq_nil_iff]
  exact fun b hb => (each b hb).1

/-- **Carried across a covered prefix.** In a history from a configured (covered-fork) history spliced with later kept
blocks, the configured blocks emit nothing and read no request boundary, and the start queue and every submission,
the configured blocks' first, are in order the later blocks' emissions followed by the final queue. For the builder
contracts the start queue is empty (`Deposit.Indexed.start_queue`, `Exit.Indexed.start_queue`), so
`carried reading linked H.premises` applies to a `Clean` history as is. -/
theorem carried (R : Reading c) (L : Linked c ty) {checkpoint mid : BlockChain} {ys : List KeptBlock}
    {t : ConfiguredHistoryTrace cfg checkpoint mid} (P : Premises c cfg checkpoint (t.kept ++ ys) stop st) :
    emissions R ty t.kept = [] ∧ (∀ b ∈ t.kept, queueAtRequests R b = []) ∧
      st.queue.map c.out ++ submissions c t.kept ++ submissions c ys = emissions R ty ys ++ remainingQueue R stop := by
  have none := covered_emits_nothing R L P rfl t.kept_covered
  have fifo := history_fifo R L P
  rw [submissions_append, emissions_append, none.1, List.nil_append, ← List.append_assoc] at fifo
  exact ⟨none.1, none.2, fifo⟩

end Occurrence

end Blanc.Lift.BuilderRequest
