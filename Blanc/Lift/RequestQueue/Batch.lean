import Blanc.Lift.RequestQueue.Model

/-! Queue projections for pushes and repeated cap-one drains, reusing Model. -/

namespace Blanc.Lift.RequestQueue
open BuilderRequest (QueueState)
variable {Record : Type}
theorem run_pushes_queue (st : QueueState Record) (rs : List Record) :
    (run 1 st (rs.map Effect.push)).queue = st.queue ++ rs := by
  induction rs generalizing st with
  | nil => simp only [run, List.map_nil, List.foldl_nil, List.append_nil]
  | cons r rs ih =>
    change (run 1 (push st r) (rs.map Effect.push)).queue = _
    rw [ih]
    simp only [push, List.append_assoc, List.singleton_append]
theorem run_unit_drains_queue (st : QueueState Record) (d : Nat) :
    (run 1 st (List.replicate d (.drain (fun _ _ => 0)))).queue = st.queue.drop d := by
  induction d generalizing st with
  | zero => rfl
  | succ d ih =>
    rw [List.replicate_succ]
    change (run 1 (apply 1 st (.drain (fun _ _ => 0))) _).queue = _
    rw [ih, apply_queue_drain, List.drop_drop]
    congr 1
    omega
theorem deliveries_unit_drains (st : QueueState Record) (d : Nat) :
    (deliveries 1 st (List.replicate d (.drain (fun _ _ => 0)))).flatten = st.queue.take d := by
  have hp : pushed (List.replicate d (Effect.drain (Record := Record) (fun _ _ => 0))) = [] := by
    induction d with
    | zero => rfl
    | succ d ih => simp only [List.replicate_succ, pushed, ih]
  have h := fifo 1 st (List.replicate d (.drain (fun _ _ => 0)))
  rw [hp, List.append_nil, run_unit_drains_queue] at h
  exact List.append_cancel_right (h.trans (List.take_append_drop _ _).symm)
end Blanc.Lift.RequestQueue
