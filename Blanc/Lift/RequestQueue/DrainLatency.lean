import Blanc.Lift.RequestQueue.Model

/-!
# Queue positions under consecutive drains

If every effect through a destination is a drain, a record at queue position `q` at effect `j`
is returned by effect `j + q / cap`, at output position `q % cap`. No storage or chain premises.
-/

namespace Blanc.Lift.RequestQueue

open Jaune
open BuilderRequest (QueueState)

/-- A fixed drain slot, before converting its block/offset pair to quotient and remainder. -/
theorem deliveries_drain_slot {Record : Type} (cap : Nat) :
    ∀ (es : List (Effect Record)) (st : QueueState Record) (j k i : Nat) (r : Record) (ds : List Record),
      i < cap →
      (∀ n ≤ j + k, ∃ next, es[n]? = some (.drain next)) →
      ((run cap st (es.take j)).queue)[cap * k + i]? = some r →
      (deliveries cap st es)[j + k]? = some ds → ds[i]? = some r := by
  intro es
  induction es with
  | nil =>
      intro st j k i r ds hi drains queued delivered
      obtain ⟨next, impossible⟩ := drains 0 (Nat.zero_le _)
      cases impossible
  | cons e es ih =>
      intro st j k i r ds hi drains queued delivered
      cases j with
      | succ j =>
          apply ih (apply cap st e) j k i r ds hi
          · intro n hn
            exact drains (n + 1) (by omega)
          · exact queued
          · simpa only [deliveries, Nat.succ_add, List.getElem?_cons_succ] using delivered
      | zero =>
          obtain ⟨next, head⟩ := drains 0 (Nat.zero_le _)
          have same : e = .drain next := Option.some.inj head
          subst e
          cases k with
          | zero =>
              have same : st.queue.take cap = ds := Option.some.inj delivered
              rw [← same, List.getElem?_take, ite_eq_left hi]
              simpa only [run, List.take_zero, List.foldl_nil, Nat.mul_zero, Nat.zero_add] using queued
          | succ k =>
              have queued' : ((apply cap st (.drain next)).queue)[cap * k + i]? = some r := by
                rw [apply_queue_drain, List.getElem?_drop]
                simpa only [run, List.take_zero, List.foldl_nil, Nat.mul_succ, Nat.zero_add,
                  Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using queued
              apply ih (apply cap st (.drain next)) 0 k i r ds hi
              · intro n hn
                exact drains (n + 1) (by omega)
              · exact queued'
              · exact delivered

/-- A queued record is returned at its quotient block and remainder slot during consecutive drains. -/
theorem deliveries_drain_position {Record : Type} (cap : Nat) (positive : 0 < cap)
    (st : QueueState Record) (es : List (Effect Record)) (j q : Nat) (r : Record) (ds : List Record)
    (drains : ∀ n ≤ j + q / cap, ∃ next, es[n]? = some (.drain next))
    (queued : ((run cap st (es.take j)).queue)[q]? = some r)
    (delivered : (deliveries cap st es)[j + q / cap]? = some ds) : ds[q % cap]? = some r := by
  apply deliveries_drain_slot cap es st j (q / cap) (q % cap) r ds (Nat.mod_lt _ positive) drains
  · rwa [Nat.div_add_mod]
  · exact delivered

end Blanc.Lift.RequestQueue
