import Blanc.JointHistory
import Blanc.Lift.WithdrawalRequest.Model
import Blanc.Lift.WithdrawalRequest.FloodTx

/-!
# P3 negative control: the actual seam rejects late requests

(A) The control on the actual seam: the joint step itself refuses a beacon block
carrying requests other than its own execution block's
(`jointStep_rejects_of_requests_ne`, from `jointStep_engine` and Jaune's
`engineVerdict_rejects_of_requests_ne`), so a one-block-late seam cannot occur
along a joint run.

(B) The alignment is what makes P3 true: shifting the consensus side's requests by
one block falsifies P3's delivery bound on a one-entry queue
(`late_seam_breaks_delivery`), while the aligned seam delivers it
(`aligned_seam_delivers_example`). The run below is constant after boundary 1, so
the aligned statement is the full `∀ j` bound on that run.

Controlled theorems: `ValidJoint.latency`
(`Blanc/Lift/WithdrawalRequest/JointLatency.lean`), P3 end-to-end latency, and its
occurrence-indexed form `ValidJoint.latency_indexed` (landing on w4 with the
p3-fifo merge).
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus ExecutionTrace

/-- **P3's negative control: the requests check bites.** If the requests the payload's
execution produces differ from the beacon block's (for example the previous block's,
as a one-block-late seam would carry), there is no joint step. This is the `require`
of `engineVerdict` (`requestsMismatch`): an engine without that check would accept
such a block. The P4 parallel is `Blanc.jointStep_rejects_of_withdrawals_ne`. -/
theorem jointStep_rejects_of_requests_ne {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s : JointState P} {b : AnySignedBlock P} {req : NewPayloadRequest P}
    (hreq : NewPayloadRequest.ofBlock b.2.message = .ok req)
    {f : Jaune.Fork} {st : State} {bout : BlockOutput}
    (hfork : cfg.forkAt (payloadToBlock req).header.number
      (payloadToBlock req).header.timestamp = .ok f)
    (hbody : applyBody (initBenv f s.exec (payloadToBlock req).header) (payloadToBlock req).txs
      (payloadToBlock req).ommers (payloadToBlock req).wds = .ok (st, bout))
    (hne : bout.requests ≠ req.executionRequests) (s' : JointState P) :
    jointStep cfg ccfg bls s b ≠ .ok s' := by
  intro h
  obtain ⟨-, req', hreq', hengine⟩ := jointStep_engine h
  have heq : req' = req := Except.ok.inj (hreq'.symm.trans hreq)
  subst heq
  obtain ⟨e, he⟩ := engineVerdict_rejects_of_requests_ne (cf := b.1) hfork hbody hne
  rw [he] at hengine
  cases hengine

/-- The delivery bound: at every boundary `j`, the queue entry at position `q` is the
`q % 16`-th entry delivered at boundary `j + q / 16`. -/
def DeliveryBound (queueAt delivered : Nat → List Blanc.WithdrawalRequest.Entry) : Prop :=
  ∀ j q e, (queueAt j)[q]? = some e → (delivered (j + q / 16))[q % 16]? = some e

/-- The closed one-entry example, reusing the flood witness entry at caller `0`. -/
def exEntry : Blanc.WithdrawalRequest.Entry := FloodTx.entryWith 0

/-- Two-boundary run, constant after boundary 1: boundary 0 is `initial` (empty queue);
boundary 1 submits `exEntry` after the model block step `system`. -/
def ctrlState : Nat → Blanc.WithdrawalRequest.State
  | Nat.zero => Blanc.WithdrawalRequest.initial
  | Nat.succ _ => Blanc.WithdrawalRequest.submit
      (Blanc.WithdrawalRequest.system Blanc.WithdrawalRequest.initial) exEntry

/-- The queue at boundary `j`. -/
def queueAt (j : Nat) : List Blanc.WithdrawalRequest.Entry := (ctrlState j).queue

/-- The aligned seam: boundary `j` delivers boundary `j`'s emissions. -/
def delivered (j : Nat) : List Blanc.WithdrawalRequest.Entry :=
  Blanc.WithdrawalRequest.emitted (ctrlState j)

/-- The late seam: boundary `j + 1` delivers boundary `j`'s emissions; boundary 0
delivers nothing. -/
def deliveredLate : Nat → List Blanc.WithdrawalRequest.Entry
  | Nat.zero => []
  | Nat.succ n => Blanc.WithdrawalRequest.emitted (ctrlState n)

theorem queueAt_one : queueAt 1 = [exEntry] := rfl

theorem queueAt_zero : queueAt Nat.zero = [] := rfl

theorem queueAt_succ (n : Nat) : queueAt (Nat.succ n) = [exEntry] := rfl

theorem delivered_succ (n : Nat) : delivered (Nat.succ n) = [exEntry] := rfl

theorem deliveredLate_one : deliveredLate 1 = [] := rfl

/-- A one-block-late seam falsifies the delivery bound on the one-entry queue: at
`j = 1, q = 0` the queue holds `exEntry`, but the late seam delivers boundary 0's
emissions, which are empty. -/
theorem late_seam_breaks_delivery : ¬ DeliveryBound queueAt deliveredLate := by
  intro h
  have hfin : ([exEntry] : List Blanc.WithdrawalRequest.Entry)[(0 : Nat)]? =
      some exEntry := rfl
  have hq : (queueAt 1)[0]? = some exEntry := by
    rw [queueAt_one]
    exact hfin
  have hd := h 1 0 exEntry hq
  have e1 : (1 : Nat) + 0 / 16 = 1 := by omega
  have e2 : (0 : Nat) % 16 = 0 := by omega
  rw [e1, e2, deliveredLate_one] at hd
  have hnil : ([] : List Blanc.WithdrawalRequest.Entry)[(0 : Nat)]? = none := rfl
  rw [hnil] at hd
  cases hd

/-- The aligned seam delivers the one-entry queue at every boundary. -/
theorem aligned_seam_delivers_example : DeliveryBound queueAt delivered := by
  intro j q e hq
  cases j with
  | zero =>
      rw [queueAt_zero] at hq
      have hnil : ∀ (m : Nat), ([] : List Blanc.WithdrawalRequest.Entry)[m]? = none :=
        fun m => by cases m <;> rfl
      rw [hnil] at hq
      cases hq
  | succ j =>
      rw [queueAt_succ] at hq
      cases q with
      | zero =>
          have hsome : ([exEntry] : List Blanc.WithdrawalRequest.Entry)[Nat.zero]? =
              some exEntry := rfl
          rw [hsome] at hq
          cases hq
          have e1 : Nat.succ j + Nat.zero / 16 = Nat.succ j := by
            simp only [Nat.zero_div, Nat.add_zero]
          have e2 : Nat.zero % 16 = 0 := by simp only [Nat.zero_mod]
          have hfin : ([exEntry] : List Blanc.WithdrawalRequest.Entry)[(0 : Nat)]? =
              some exEntry := rfl
          simp only [e1, e2, delivered_succ]
          exact hfin
      | succ q =>
          have hnil : ([exEntry] : List Blanc.WithdrawalRequest.Entry)[Nat.succ q]? =
              none := rfl
          rw [hnil] at hq
          cases hq

end Blanc.Lift.WithdrawalRequest
