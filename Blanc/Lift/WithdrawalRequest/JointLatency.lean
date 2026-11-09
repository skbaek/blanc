import Blanc.Lift.WithdrawalRequest.JointHistory
import Blanc.Lift.WithdrawalRequest.BoundaryFifo
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

namespace Blanc

open Jaune JauneConsensus ExecutionTrace
open Blanc.Lift.WithdrawalRequest

/-- The last element of `l ++ [x]` sits at index `l.length`: an index of `l ++ [x]` past
`l` is `l.length`, and the element there is `x`. -/
private theorem getElem?_concat_of_not_lt {α : Type} {l : List α} {x y : α} {i : Nat}
    (hi : ¬i < l.length) (h : (l ++ [x])[i]? = some y) : i = l.length ∧ x = y := by
  have hlt := (List.getElem?_eq_some_iff.mp h).1
  rw [List.length_append, List.length_singleton] at hlt
  obtain rfl : i = l.length := by omega
  rw [List.getElem?_concat_length] at h
  exact ⟨rfl, Option.some.inj h⟩

/-- Prefix histories with their emissions: step `i` of a joint run has a configured
history to its pre-execution chain that extends to the whole joint history, and its
emissions are the pre-anchor emissions plus the serialized type-1 feed of the first
`i` steps. Mirrors `JointRun.extendsBy_toExec`, threading the emissions conjunct
through its induction with the `emissions_toExec` pattern. -/
theorem JointRun.prefixHistory_emissions {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    {s : JointState P} → (run : JointRun cfg ccfg bls s₀ s) → {i : Nat} →
    {A : JointRunStep (P := P) cfg ccfg bls} → run.steps[i]? = some A →
    ∃ historyA : ConfiguredHistoryTrace cfg checkpoint A.pre.exec,
      (ConfiguredHistoryTrace.step historyA A.stepTrace.trace).ExtendsBy (run.toExec pre)
        (run.steps.length - 1 - i) ∧
      emissions historyA =
        emissions pre ++ ((run.steps.take i).flatMap stepWithdrawalRequests).map Ssz.serialize
  | _, .nil, _, _, h => by
    simp only [JointRun.steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run b step bound, i, A, h => by
    rw [JointRun.steps_snoc] at h
    rw [JointRun.steps_snoc, List.length_append, List.length_singleton, JointRun.toExec_snoc]
    by_cases hi : i < run.steps.length
    · rw [List.getElem?_append_left hi] at h
      obtain ⟨history, ext, hem⟩ := JointRun.prefixHistory_emissions pre run h
      refine ⟨history, ?_, ?_⟩
      · rw [show run.steps.length + 1 - 1 - i = run.steps.length - 1 - i + 1 by omega]
        exact ext.step _
      · rw [List.take_append_of_le_length (show i ≤ run.steps.length by omega)]
        exact hem
    · obtain ⟨hlen, rfl⟩ := getElem?_concat_of_not_lt hi h
      refine ⟨run.toExec pre, ?_, ?_⟩
      · rw [show run.steps.length + 1 - 1 - i = 0 by omega]
        exact .refl
      · rw [List.take_append_of_le_length (show i ≤ run.steps.length by omega), hlen,
          List.take_length]
        exact emissions_toExec pre run

end Blanc

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus ExecutionTrace

/-- **P3 occurrence-indexed.** The record at queue position `q` of step `j₀`'s request
boundary is the committed submission occurrence
`(emissions v.pre).length + feedPosition v.run j₀ 0 + q` of the joint history:
the pre-anchor emissions, then the run's type-1 feed before step `j₀`, then the `q`
queue entries ahead of it at step `j₀`'s boundary (`history_queueAtRequests`). -/
theorem ValidJoint.latency_occurrence {P : Preset}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ q : Nat} {B : JointRunStep (P := P) cfg ccfg bls} (stepB : v.run.steps[j₀]? = some B)
    {record : Bytes} (queued : (queueAtRequests B.stepTrace.trace)[q]? = some record) :
    (submissions (v.run.toExec v.pre))[(emissions v.pre).length + feedPosition v.run j₀ 0 +
      q]? = some record := by
  obtain ⟨historyB, extB, hemB⟩ := JointRun.prefixHistory_emissions v.pre v.run stepB
  obtain ⟨suffix, framesEq⟩ := extB.settledFrames
  have framesFull : (v.run.toExec v.pre).settledFrames =
      (ConfiguredHistoryTrace.step historyB B.stepTrace.trace).settledFrames ++ suffix :=
    framesEq
  have sendersB :
      (ConfiguredHistoryTrace.step historyB B.stepTrace.trace).NoSenderAt systemAddress :=
    extB.noSenderAt v.senders
  have authoritiesB :
      (ConfiguredHistoryTrace.step historyB B.stepTrace.trace).NoAuthorityAt systemAddress :=
    extB.noAuthorityAt v.authorities
  have avoidB : ∀ root ∈ (ConfiguredHistoryTrace.step historyB B.stepTrace.trace).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress := by
    intro root member hcode
    exact v.avoid root (extB.rawFrames_mem root member) hcode
  have occB : (submissions
      (ConfiguredHistoryTrace.step historyB B.stepTrace.trace)).length ≤ wordOccurrenceCap := by
    have h := v.occurrences
    simp only [submissions, List.length_map, framesFull, List.flatMap_append,
      List.length_append] at h ⊢
    omega
  have queueEq := history_queueAtRequests v.deployment v.admission historyB B.stepTrace.trace
    v.otherInstalled sendersB authoritiesB avoidB occB
  have hfeed : feedPosition v.run j₀ 0 =
      ((v.run.steps.take j₀).flatMap stepWithdrawalRequests).length := rfl
  have hidx : (emissions historyB).length + q =
      (emissions v.pre).length + feedPosition v.run j₀ 0 + q := by
    rw [hemB, hfeed, List.length_append, List.length_map]
  have queuedAt : (submissions
      (ConfiguredHistoryTrace.step historyB B.stepTrace.trace))[(emissions historyB).length + q]? =
      some record := by
    have hqueued := queued
    rw [queueEq] at hqueued
    rwa [List.getElem?_drop] at hqueued
  have subsApp : submissions (v.run.toExec v.pre) =
      submissions (ConfiguredHistoryTrace.step historyB B.stepTrace.trace) ++
        (suffix.flatMap submissionFramePayments).map
          (fun pair => submissionRecord pair.1) := by
    simp only [submissions, framesFull, List.flatMap_append, List.map_append]
  have idxLt : (emissions historyB).length + q <
      (submissions (ConfiguredHistoryTrace.step historyB B.stepTrace.trace)).length := by
    have hq : q < (queueAtRequests B.stepTrace.trace).length :=
      (List.getElem?_eq_some_iff.mp queued).1
    rw [queueEq, List.length_drop] at hq
    omega
  rw [← hidx, subsApp, List.getElem?_append_left idxLt]
  exact queuedAt

/-- **Per-step request cap.** Every joint step carries at most 16 withdrawal requests:
the step's execution block publishes the emitted prefix of its request-boundary model
(`blockWithdrawals_eq_of_request_rep` on the `block_word_fifo` replay), which has length
at most `maxPerBlock = 16` (`emitted_length_le`), and the beacon block carries the same
requests serialized (`blockWithdrawals_step`). -/
theorem ValidJoint.stepWithdrawalRequests_length_le {P : Preset}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls}
    (stepD : v.run.steps[j]? = some D) :
    (stepWithdrawalRequests D).length ≤ 16 := by
  obtain ⟨historyD, extD, -⟩ := JointRun.prefixHistory_emissions v.pre v.run stepD
  have sendersD :
      (ConfiguredHistoryTrace.step historyD D.stepTrace.trace).NoSenderAt systemAddress :=
    extD.noSenderAt v.senders
  have authoritiesD :
      (ConfiguredHistoryTrace.step historyD D.stepTrace.trace).NoAuthorityAt systemAddress :=
    extD.noAuthorityAt v.authorities
  have avoidD : ∀ root ∈ (ConfiguredHistoryTrace.step historyD D.stepTrace.trace).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress := by
    intro root member hcode
    exact v.avoid root (extD.rawFrames_mem root member) hcode
  have occD : (submissions
      (ConfiguredHistoryTrace.step historyD D.stepTrace.trace)).length ≤ wordOccurrenceCap := by
    have h := v.occurrences
    obtain ⟨suffix, framesEq⟩ := extD.settledFrames
    simp only [submissions, List.length_map, framesEq, List.flatMap_append,
      List.length_append] at h ⊢
    omega
  have occFrames : ((ConfiguredHistoryTrace.step historyD D.stepTrace.trace).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap := by
    simpa only [submissions, List.length_map] using occD
  obtain ⟨r, boundary, _, _, _, _, _, _⟩ :=
    (block_word_fifo v.deployment v.admission historyD D.stepTrace.trace v.otherInstalled
      sendersD authoritiesD avoidD occFrames).checkpoint
  have initialized := v.deployment.initialized v.admission
  have hrep := blockWithdrawals_eq_of_request_rep historyD D.stepTrace.trace
    initialized.checkpointCode r.model boundary.represents
  have hstep := blockWithdrawals_step D
  have heq : (stepWithdrawalRequests D).length =
      (Blanc.WithdrawalRequest.emitted r.model).length := by
    have h := hstep.symm.trans hrep
    have hlen := congrArg List.length h
    simpa only [List.length_map] using hlen
  have hle := Blanc.WithdrawalRequest.emitted_length_le r.model
  rw [show Blanc.WithdrawalRequest.maxPerBlock = 16 from rfl] at hle
  rw [heq]
  exact hle

/-- **Per-step request floor on the delivery path.** For `d < q / 16`, step `j₀ + d` carries
at least 16 withdrawal requests: `latency` at `q' := 16 * d + 15` (which satisfies
`q' / 16 = d` and `q' % 16 = 15`, and `q' < q` so its queue position exists) delivers a
request at index 15. -/
theorem ValidJoint.stepWithdrawalRequests_length_ge {P : Preset}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ q : Nat} {B : JointRunStep (P := P) cfg ccfg bls}
    (stepB : v.run.steps[j₀]? = some B)
    {record : Bytes} (queued : (queueAtRequests B.stepTrace.trace)[q]? = some record)
    {d : Nat} (hd : d < q / 16) {Dd : JointRunStep (P := P) cfg ccfg bls}
    (stepDd : v.run.steps[j₀ + d]? = some Dd) :
    16 ≤ (stepWithdrawalRequests Dd).length := by
  have hq'lt : 16 * d + 15 < q := by omega
  have hlenB : 16 * d + 15 < (queueAtRequests B.stepTrace.trace).length := by
    have hq := (List.getElem?_eq_some_iff.mp queued).1
    omega
  obtain ⟨rec', hrec'⟩ :
      ∃ rec', (queueAtRequests B.stepTrace.trace)[16 * d + 15]? = some rec' :=
    ⟨_, List.getElem?_eq_getElem hlenB⟩
  have hdiv : (16 * d + 15) / 16 = d := by omega
  have hmod : (16 * d + 15) % 16 = 15 := by omega
  have stepDd' : v.run.steps[j₀ + (16 * d + 15) / 16]? = some Dd := by
    rw [hdiv]
    exact stepDd
  obtain ⟨requests, hread, hex, -⟩ := v.latency (q := 16 * d + 15) stepB stepDd' hrec'
  rw [hmod] at hex
  obtain ⟨wr, hwr, -⟩ := hex
  have hstep : (stepWithdrawalRequests Dd)[15]? = some wr := by
    rw [stepWithdrawalRequests, hread, Array.getElem?_toList]
    exact hwr
  have hlt := (List.getElem?_eq_some_iff.mp hstep).1
  omega

/-- **P3 occurrence-indexed, delivered.** The occurrence queued at position `q` of step
`j₀`'s boundary is exactly the request `q % 16` of step `j₀ + q / 16`: each step carries
at most 16 requests, and the latency bound forces each step before the delivering one to
carry exactly 16, fixing the feed-position count. -/
theorem ValidJoint.latency_occurrence_delivered {P : Preset}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ q : Nat} {B D : JointRunStep (P := P) cfg ccfg bls}
    (stepB : v.run.steps[j₀]? = some B) (stepD : v.run.steps[j₀ + q / 16]? = some D)
    {record : Bytes} (queued : (queueAtRequests B.stepTrace.trace)[q]? = some record) :
    feedPosition v.run j₀ 0 + q = feedPosition v.run (j₀ + q / 16) (q % 16) := by
  have hlenD : j₀ + q / 16 < v.run.steps.length :=
    (List.getElem?_eq_some_iff.mp stepD).1
  have hsucc : ∀ j, ∀ Dj : JointRunStep (P := P) cfg ccfg bls,
      v.run.steps[j]? = some Dj →
      feedPosition v.run (j + 1) 0 =
        feedPosition v.run j 0 + (stepWithdrawalRequests Dj).length := by
    intro j Dj hDj
    simp only [feedPosition, List.take_add_one, hDj, Option.toList_some,
      List.flatMap_append, List.flatMap_singleton, List.length_append, Nat.add_zero]
  have key : ∀ m, m ≤ q / 16 →
      feedPosition v.run (j₀ + m) 0 = feedPosition v.run j₀ 0 + 16 * m := by
    intro m
    induction m with
    | zero => intro _; simp only [Nat.add_zero, Nat.mul_zero]
    | succ m ih =>
      intro hm
      have hm' : m ≤ q / 16 := by omega
      have ihEq := ih hm'
      have hmlt : m < q / 16 := by omega
      have hlt : j₀ + m < v.run.steps.length := by omega
      obtain ⟨Dm, hDm⟩ : ∃ Dm, v.run.steps[j₀ + m]? = some Dm :=
        ⟨_, List.getElem?_eq_getElem hlt⟩
      have h16 : (stepWithdrawalRequests Dm).length = 16 := by
        have hle := v.stepWithdrawalRequests_length_le hDm
        have hge := v.stepWithdrawalRequests_length_ge stepB queued hmlt hDm
        omega
      have hjm : j₀ + (m + 1) = (j₀ + m) + 1 := by omega
      rw [hjm, hsucc _ _ hDm, ihEq, h16]
      omega
  have hfin := key (q / 16) (Nat.le_refl _)
  have hsplit : feedPosition v.run (j₀ + q / 16) (q % 16) =
      feedPosition v.run (j₀ + q / 16) 0 + q % 16 := rfl
  have hqm : q = 16 * (q / 16) + q % 16 := (Nat.div_add_mod q 16).symm
  omega

/-- **P3, occurrence-indexed end-to-end latency.** Along a valid joint chain, let `record`
sit at index `q` of the stored EIP-7002 queue at the request boundary of joint step `j₀`, and
let the run reach step `j₀ + q / 16`. Then, with `n = E₀ + feedPosition v.run j₀ 0 + q`:
* the queued record is the joint history's committed paid submission occurrence `n`
  (`latency_occurrence`);
* that same occurrence is request `q % 16` of step `j₀ + q / 16`'s beacon block: `n` is the
  feed position `E₀ + feedPosition v.run (j₀ + q / 16) (q % 16)`
  (`latency_occurrence_delivered`), and the run's feed there is a consensus withdrawal request
  `wr` that serializes to `record` (`latency_submission`).
So the delivery is pinned to the occurrence, not only to its bytes: duplicate records are told
apart. -/
theorem ValidJoint.latency_indexed {P : Preset}
    {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {checkpoint : BlockChain}
    {anchor final : JointState P} (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ q : Nat} {B D : JointRunStep (P := P) cfg ccfg bls}
    (stepB : v.run.steps[j₀]? = some B) (stepD : v.run.steps[j₀ + q / 16]? = some D)
    {record : Bytes} (queued : (queueAtRequests B.stepTrace.trace)[q]? = some record) :
    (submissions (v.run.toExec v.pre))[(emissions v.pre).length + feedPosition v.run j₀ 0 + q]? =
      some record ∧
    (emissions v.pre).length + feedPosition v.run j₀ 0 + q =
      (emissions v.pre).length + feedPosition v.run (j₀ + q / 16) (q % 16) ∧
    ∃ wr, (withdrawalFeed v.run)[feedPosition v.run (j₀ + q / 16) (q % 16)]? = some wr ∧
      Ssz.serialize wr = record := by
  obtain ⟨wr, -, -, hfeed, hser⟩ := v.latency_submission stepB stepD queued
  refine ⟨v.latency_occurrence stepB queued, ?_, wr, hfeed, hser⟩
  rw [Nat.add_assoc, v.latency_occurrence_delivered stepB stepD queued]

end Blanc.Lift.WithdrawalRequest
