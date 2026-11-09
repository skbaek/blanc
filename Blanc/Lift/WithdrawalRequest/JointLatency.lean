import Blanc.Lift.WithdrawalRequest.JointHistory
import Blanc.Lift.WithdrawalRequest.RequestCodec
import Blanc.Lift.WithdrawalRequest.HeadlineHistory
import Blanc.Lift.WithdrawalRequest.JointAuthorization

/-!
# End-to-end EIP-7002 latency along a valid joint chain (P3)

A record at index `q` of the EIP-7002 stored queue at the request boundary of joint step
`j₀`'s execution block reaches the consensus layer in joint step `j₀ + q / 16`: that step's
beacon block carries, as withdrawal request `q % 16`, the consensus `WithdrawalRequest`
whose SSZ serialization is the record, preceded in order by exactly the queue entries ahead
of it from position `16 * (q / 16)`.

The distance is counted in joint steps, which are execution blocks: the joint run's execution
blocks are exactly its steps' chosen traces (`JointRun.extendsBy_steps`), and empty slots are
`process_slots` inside a joint step. The proof is Blanc's delivery bound over direct observers
(`history_delivery`, the observer form of `block_word_delivery_from_deployment`) on the joint
history `run.toExec pre`, then the seam's request bridge
(`JointStepTrace.withdrawalRequestRecords_eq`): the requests the execution block computes are
the beacon block's own `execution_requests`, in the same block.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus ExecutionTrace

/-- **P3, end-to-end latency.** Along a valid joint chain, let `record` sit at index `q` of
the stored EIP-7002 queue (`queueAtRequests`, head to tail in withdrawal-output format) at the
request boundary of the execution block of joint step `j₀`, and let the run reach step
`j₀ + q / 16` (step `j₀` counted as `0`). Then that step's beacon block has execution requests
`requests` whose withdrawal request `q % 16` serializes to `record`, and whose first
`q % 16 + 1` withdrawal requests serialize to exactly the queue records at positions
`16 * (q / 16), …, q`. The queue index and the reach condition are the ones Blanc's delivery
bound states; the proof reads exactly the `ValidJoint` fields `deployment`, `admission`,
`otherInstalled`, `senders`, `authorities`, `avoid`, `occurrences`, and `run`/`pre`. -/
theorem ValidJoint.latency {P : Preset}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ q : Nat} {B D : JointRunStep (P := P) cfg ccfg bls}
    (stepB : v.run.steps[j₀]? = some B) (stepD : v.run.steps[j₀ + q / 16]? = some D)
    {record : Bytes} (queued : (queueAtRequests B.stepTrace.trace)[q]? = some record) :
    ∃ requests : ExecutionRequests P,
      Gated.read D.block.2.message.body.execution_requests
          "NewPayloadRequest: execution_requests" = .ok requests ∧
      (∃ wr, requests.withdrawals.toArray[q % 16]? = some wr ∧ Ssz.serialize wr = record) ∧
      (requests.withdrawals.toArray.toList.take (q % 16 + 1)).map Ssz.serialize =
        ((queueAtRequests B.stepTrace.trace).drop (16 * (q / 16))).take (q % 16 + 1) := by
  obtain ⟨historyB, historyD, extension, tail⟩ :=
    v.run.extendsBy_steps v.pre (Nat.le_add_right j₀ (q / 16)) stepB stepD
  rw [Nat.add_sub_cancel_left] at extension
  have occurrences : (submissions (ConfiguredHistoryTrace.step historyD
      D.stepTrace.trace)).length ≤ wordOccurrenceCap := by
    have whole := v.occurrences
    obtain ⟨suffix, frames⟩ := tail.settledFrames
    simp only [submissions, List.length_map, frames, List.flatMap_append,
      List.length_append] at whole ⊢
    omega
  obtain ⟨position, ahead⟩ := history_delivery v.deployment v.admission historyB
    B.stepTrace.trace historyD D.stepTrace.trace extension v.otherInstalled
    (tail.noSenderAt v.senders) (tail.noAuthorityAt v.authorities)
    (fun root member => v.avoid root (tail.rawFrames_mem root member)) occurrences rfl
    record queued
  obtain ⟨requests, hread, records⟩ :=
    JointStepTrace.withdrawalRequestRecords_eq D.stepTrace
  refine ⟨requests, hread, ?_, ?_⟩
  · rw [blockWithdrawals, records, List.getElem?_map, Option.map_eq_some_iff] at position
    obtain ⟨wr, hwr, rfl⟩ := position
    exact ⟨wr, by rwa [Array.getElem?_toList] at hwr, rfl⟩
  · rwa [blockWithdrawals, records, ← List.map_take] at ahead

/-- **P3 in submission terms.** Under `ValidJoint.latency`'s hypotheses, let `n` be the anchor
offset plus the delivering step's feed position. Then `n` is an emitted submission index, the
committed paid submission at `n` is the delivered `record`, and the run's feed at that position
is the latency witness `wr` with `Ssz.serialize wr = record`. This identifies the delivered
record with the committed submission at the delivering step's feed position; it does not prove
that this occurrence index equals the queue position's own occurrence index, which would need a
request-boundary FIFO lemma not proved here. -/
theorem ValidJoint.latency_submission {P : Preset}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ q : Nat} {B D : JointRunStep (P := P) cfg ccfg bls}
    (stepB : v.run.steps[j₀]? = some B) (stepD : v.run.steps[j₀ + q / 16]? = some D)
    {record : Bytes} (queued : (queueAtRequests B.stepTrace.trace)[q]? = some record) :
    ∃ wr, ((emissions v.pre).length + feedPosition v.run (j₀ + q / 16) (q % 16) <
      (emissions (v.run.toExec v.pre)).length) ∧
      (submissions (v.run.toExec v.pre))[(emissions v.pre).length +
        feedPosition v.run (j₀ + q / 16) (q % 16)]? = some record ∧
      (withdrawalFeed v.run)[feedPosition v.run (j₀ + q / 16) (q % 16)]? = some wr ∧
      Ssz.serialize wr = record := by
  obtain ⟨requests, hread, hex, -⟩ := v.latency stepB stepD queued
  obtain ⟨wr, hwr, hser⟩ := hex
  have hstep : (stepWithdrawalRequests D)[q % 16]? = some wr := by
    rw [stepWithdrawalRequests, hread, Array.getElem?_toList]
    exact hwr
  obtain ⟨hfeed, hsub⟩ := v.submission_of_feed stepD hstep
  have hlt : (emissions v.pre).length + feedPosition v.run (j₀ + q / 16) (q % 16) <
      (emissions (v.run.toExec v.pre)).length := by
    have hflen : feedPosition v.run (j₀ + q / 16) (q % 16) <
        (withdrawalFeed v.run).length :=
      (List.getElem?_eq_some_iff.mp hfeed).1
    have hlen := congrArg List.length (emissions_toExec v.pre v.run)
    rw [List.length_append, List.length_map] at hlen
    omega
  rw [hser] at hsub
  exact ⟨wr, hlt, hsub, hfeed, hser⟩

end Blanc.Lift.WithdrawalRequest
