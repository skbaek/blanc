import Blanc.FakeExponential

/-!
EIP-7002 specification model, transcribed from
https://eips.ethereum.org/EIPS/eip-7002#execution-layer (fee calculation,
add-request and system-call pseudocode). Entries are typed semantic data;
storage packing, logs, return encoding, gas and bytecode refinement are separate.
-/

namespace Blanc.WithdrawalRequest

open Jaune

def maxPerBlock : Nat := 16
def targetPerBlock : Nat := 2
def feeUpdateFraction : Nat := 17
def excessInhibitor : Nat := 2 ^ 256 - 1

structure Entry where
  caller : Adr
  pubkey : { bytes : List UInt8 // bytes.length = 48 }
  amount : UInt64

/-- A successful submission retains its value for later payment provenance. -/
structure Submission where
  entry : Entry
  value : Nat

structure State where
  excess : Nat
  count : Nat
  head : Nat
  tail : Nat
  queue : List Entry

def initial : State := ⟨excessInhibitor, 0, 0, 0, []⟩

/-- Queue pointer coherence; Nat arithmetic has no storage-word wrap. -/
def Coherent (state : State) : Prop := state.head + state.queue.length = state.tail

def fee (state : State) : Nat := fakeExp 1 state.excess feeUpdateFraction

def fee? (state : State) : Option Nat :=
  if state.excess = excessInhibitor then none else some (fee state)

/-- The successful add-request state change; admission is carried by History. -/
def submit (state : State) (entry : Entry) : State :=
  { state with
    count := state.count + 1
    tail := state.tail + 1
    queue := state.queue ++ [entry] }

def effectiveExcess (state : State) : Nat :=
  if state.excess = excessInhibitor then 0 else state.excess

def emitted (state : State) : List Entry := state.queue.take maxPerBlock

/-- Dequeue first, update excess from the old count, then reset count. -/
def system (state : State) : State :=
  { excess := effectiveExcess state + state.count - targetPerBlock,
    count := 0,
    head := if state.queue.length ≤ maxPerBlock then 0
      else state.head + (emitted state).length,
    tail := if state.queue.length ≤ maxPerBlock then 0 else state.tail,
    queue := state.queue.drop maxPerBlock }

/-- Replay of accepted submissions and system steps from an explicit checkpoint.
Initial queued entries remain separate from the recorded new submissions. -/
inductive History (checkpoint : State) : State → List Submission → List Entry → Prop
  | start : History checkpoint checkpoint [] []
  | submit {state submissions outputs} (history : History checkpoint state submissions outputs)
      (submission : Submission) (enabled : state.excess ≠ excessInhibitor)
      (paid : fee state ≤ submission.value) :
      History checkpoint (WithdrawalRequest.submit state submission.entry)
        (submissions ++ [submission]) outputs
  | system {state submissions outputs} (history : History checkpoint state submissions outputs) :
      History checkpoint (WithdrawalRequest.system state) submissions (outputs ++ emitted state)

theorem fee_positive (state : State) : 0 < fee state :=
  Nat.lt_of_lt_of_le (by decide) (FakeExponential.factor_le 1 state.excess
    feeUpdateFraction (by decide))

theorem fee_at_zero_excess (state : State) (zero : state.excess = 0) : fee state = 1 := by
  change fakeExp 1 state.excess feeUpdateFraction = 1
  rw [zero, FakeExponential.value_zero_numerator 1 feeUpdateFraction (by decide)]

theorem initial_coherent : Coherent initial := rfl

theorem submit_queue (state : State) (entry : Entry) :
    (submit state entry).queue = state.queue ++ [entry] := rfl

theorem submit_count (state : State) (entry : Entry) :
    (submit state entry).count = state.count + 1 := rfl

theorem emitted_length (state : State) :
    (emitted state).length = min maxPerBlock state.queue.length :=
  List.length_take

theorem emitted_length_le (state : State) : (emitted state).length ≤ maxPerBlock :=
  List.length_take_le _ _

theorem system_count (state : State) : (system state).count = 0 := rfl

theorem system_excess (state : State) :
    (system state).excess = effectiveExcess state + state.count - targetPerBlock := rfl

theorem system_queue (state : State) :
    (system state).queue = state.queue.drop maxPerBlock := rfl

/-- The system step partitions the queue into a FIFO prefix and its suffix. -/
theorem system_partition (state : State) :
    emitted state ++ (system state).queue = state.queue :=
  List.take_append_drop _ _

/-- Under coherent pointers, the list-model reset test is exactly the EIP's
test that the advanced head equals the old tail. -/
theorem drained_iff_head_reaches_tail {state : State} (coherent : Coherent state) :
    state.queue.length ≤ maxPerBlock ↔
      state.head + (emitted state).length = state.tail := by
  change state.head + state.queue.length = state.tail at coherent
  rw [emitted_length]
  omega

theorem system_drained_pointers (state : State) (drained : state.queue.length ≤ maxPerBlock) :
    (system state).head = 0 ∧ (system state).tail = 0 := by
  simp only [system, ite_eq_left drained, and_self]

theorem system_live_pointers (state : State) (remaining : ¬ state.queue.length ≤ maxPerBlock) :
    (system state).head = state.head + (emitted state).length ∧
    (system state).tail = state.tail := by
  simp only [system, ite_eq_right remaining, and_self]

theorem system_inhibitor_excess (state : State) (inhibited : state.excess = excessInhibitor) :
    (system state).excess = state.count - targetPerBlock := by
  change (if state.excess = excessInhibitor then 0 else state.excess) +
    state.count - targetPerBlock = state.count - targetPerBlock
  rw [ite_eq_left inhibited, Nat.zero_add]

theorem submit_coherent {state : State} (coherent : Coherent state) (entry : Entry) :
    Coherent (submit state entry) := by
  simp only [Coherent, submit, List.length_append, List.length_singleton]
  change state.head + state.queue.length = state.tail at coherent
  omega

theorem system_coherent {state : State} (coherent : Coherent state) :
    Coherent (system state) := by
  change state.head + state.queue.length = state.tail at coherent
  by_cases drained : state.queue.length ≤ maxPerBlock
  · simp only [Coherent, system, ite_eq_left drained, List.length_drop]
    omega
  · simp only [Coherent, system, ite_eq_right drained, emitted, List.length_take,
      List.length_drop]
    omega

/-- Exact ordered conservation, including entries queued at the checkpoint.
This is the model's FIFO/history law, not a theorem about EVM execution. -/
theorem History.conservation {checkpoint state : State} {submissions : List Submission}
    {outputs : List Entry} (history : History checkpoint state submissions outputs) :
    checkpoint.queue ++ submissions.map Submission.entry = outputs ++ state.queue := by
  induction history with
  | start => simp only [List.map_nil, List.append_nil, List.nil_append]
  | submit history submission enabled paid ih =>
    simp only [List.map_append, List.map_singleton, submit_queue]
    rw [← List.append_assoc, ih, List.append_assoc]
  | system history ih =>
    change checkpoint.queue ++ List.map Submission.entry _ =
      (_ ++ List.take maxPerBlock _) ++ List.drop maxPerBlock _
    rw [List.append_assoc, List.take_append_drop]
    exact ih

theorem History.coherent {checkpoint state : State} {submissions : List Submission}
    {outputs : List Entry} (history : History checkpoint state submissions outputs)
    (coherent : Coherent checkpoint) : Coherent state := by
  induction history with
  | start => exact coherent
  | submit history submission enabled paid ih => exact submit_coherent ih submission.entry
  | system history ih => exact system_coherent ih

/-- Every newly recorded successful submission has a strictly positive payment. -/
theorem History.payment_positive {checkpoint state : State} {submissions : List Submission}
    {outputs : List Entry} (history : History checkpoint state submissions outputs) :
    ∀ submission ∈ submissions, 0 < submission.value := by
  induction history with
  | start =>
    intro submission member
    exact False.elim (List.not_mem_nil member)
  | submit history submission enabled paid ih =>
    intro candidate member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | new
    · exact ih candidate old
    · rw [new]
      exact Nat.lt_of_lt_of_le (fee_positive _) paid
  | system history ih => exact ih

end Blanc.WithdrawalRequest
