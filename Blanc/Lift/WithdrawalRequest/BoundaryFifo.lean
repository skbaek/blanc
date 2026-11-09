import Blanc.Lift.WithdrawalRequest.HistoryFifo
import Blanc.Lift.WithdrawalRequest.HeadlineHistory

/-!
# Request-boundary FIFO for EIP-7002

The stored queue at a block's request boundary is the submission suffix that its
earlier history has not emitted yet: the full ordered submissions through the
block, with the history's emissions dropped. The proof reuses the delivery
replay (`block_word_fifo`): boundary conservation gives the model queue as the
unemitted suffix, and the request-boundary storage represents that model.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune ExecutionTrace ExecutionAccountingReplay Blanc.WithdrawalRequest

/-- **Request-boundary FIFO.** The committed submissions through a block are, in order, the
earlier history's emissions followed by the stored queue at the block's request boundary. The
hypotheses are the `history_delivery` ones. -/
theorem history_submissions_at_requests
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions (ConfiguredHistoryTrace.step history block)).length ≤
      wordOccurrenceCap) :
    submissions (ConfiguredHistoryTrace.step history block) =
      emissions history ++ queueAtRequests block := by
  have occFrames : ((ConfiguredHistoryTrace.step history block).settledFrames.flatMap
      submissionFramePayments).length ≤ wordOccurrenceCap := by
    simpa only [submissions, List.length_map] using occurrences
  obtain ⟨r, boundary, emission, afterReset, _, provenance, _, _⟩ :=
    (block_word_fifo deployment admission history block otherInstalled senders authorities avoid
      occFrames).checkpoint
  have queueB : queueAtRequests block = r.model.queue.map outputRecord :=
    storedQueue_eq boundary.represents
  have fullRecords : submissions (ConfiguredHistoryTrace.step history block) =
      (r.frames.map Prod.snd).map outputRecord :=
    submissions_eq_records (ConfiguredHistoryTrace.step history block) r.frames
      provenance.stepFrames provenance.payloads
  have hFifo : HistoryFifo (ConfiguredHistoryTrace.step history block) :=
    history_fifo deployment admission (ConfiguredHistoryTrace.step history block) otherInstalled
      senders authorities avoid occurrences
  have fifoStep : submissions (ConfiguredHistoryTrace.step history block) =
      emissions (ConfiguredHistoryTrace.step history block) ++
        remainingQueue (ConfiguredHistoryTrace.step history block) := hFifo
  have emissionsStep : emissions (ConfiguredHistoryTrace.step history block) =
      emissions history ++ (emitted r.model).map outputRecord := by
    have h : emissions (ConfiguredHistoryTrace.step history block) =
        emissions history ++ withdrawalRequestRecords block.blockOutput.requests := rfl
    rw [h, emission_eq_records emission]
  have remainingStep : remainingQueue (ConfiguredHistoryTrace.step history block) =
      ((Blanc.WithdrawalRequest.system r.model).queue).map outputRecord := by
    have h : remainingQueue (ConfiguredHistoryTrace.step history block) =
        storedQueue (post.state.getStor withdrawalRequestPredeployAddress).get := rfl
    rw [h, storedQueue_eq afterReset.represents]
  have entriesEq : r.frames.map Prod.snd =
      r.outputs ++ (Blanc.WithdrawalRequest.system r.model).queue :=
    provenance.entries
  have outputsEq : r.outputs = r.pastOutputs ++ emitted r.model := rfl
  have pastEmissions : r.pastOutputs.map outputRecord = emissions history := by
    have hA : submissions (ConfiguredHistoryTrace.step history block) =
        (r.pastOutputs.map outputRecord ++ (emitted r.model).map outputRecord) ++
          ((Blanc.WithdrawalRequest.system r.model).queue).map outputRecord := by
      rw [fullRecords, entriesEq, outputsEq, List.map_append, List.map_append]
    have hB : submissions (ConfiguredHistoryTrace.step history block) =
        (emissions history ++ (emitted r.model).map outputRecord) ++
          ((Blanc.WithdrawalRequest.system r.model).queue).map outputRecord := by
      rw [fifoStep, emissionsStep, remainingStep]
    have hEq : (r.pastOutputs.map outputRecord ++ (emitted r.model).map outputRecord) ++
          ((Blanc.WithdrawalRequest.system r.model).queue).map outputRecord =
        (emissions history ++ (emitted r.model).map outputRecord) ++
          ((Blanc.WithdrawalRequest.system r.model).queue).map outputRecord :=
      hA.symm.trans hB
    have cancelOnce : r.pastOutputs.map outputRecord ++ (emitted r.model).map outputRecord =
        emissions history ++ (emitted r.model).map outputRecord :=
      List.append_cancel_right hEq
    exact List.append_cancel_right cancelOnce
  have framesEntries : r.frames.map Prod.snd = r.submissions.map Submission.entry :=
    wordSubmissionFrames_entries (r.past ++ r.transactions)
  have hInit : (initial.queue) = [] := rfl
  have conserved : r.submissions.map Submission.entry = r.pastOutputs ++ r.model.queue := by
    have h := boundary.wordHistory.conservation
    rw [hInit, List.nil_append] at h
    exact h
  have mapped : (r.submissions.map Submission.entry).map outputRecord =
      r.pastOutputs.map outputRecord ++ r.model.queue.map outputRecord := by
    rw [conserved, List.map_append]
  have subsFromFrames : submissions (ConfiguredHistoryTrace.step history block) =
      (r.submissions.map Submission.entry).map outputRecord := by
    rw [fullRecords, framesEntries]
  rw [subsFromFrames, mapped, pastEmissions, ← queueB]

/-- The stored queue at a block's request boundary is the ordered submissions through the
block with the earlier history's emissions dropped (`history_submissions_at_requests`). -/
theorem history_queueAtRequests
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (deployment : DeploymentHistory cfg checkpoint) (admission : deployment.Admission)
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post)
    (otherInstalled : OtherSystemCodeInstalled checkpoint.state)
    (senders : (ConfiguredHistoryTrace.step history block).NoSenderAt systemAddress)
    (authorities : (ConfiguredHistoryTrace.step history block).NoAuthorityAt systemAddress)
    (avoid : ∀ root ∈ (ConfiguredHistoryTrace.step history block).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ systemAddress)
    (occurrences : (submissions (ConfiguredHistoryTrace.step history block)).length ≤
      wordOccurrenceCap) :
    queueAtRequests block =
      (submissions (ConfiguredHistoryTrace.step history block)).drop (emissions history).length := by
  rw [history_submissions_at_requests deployment admission history block otherInstalled senders
    authorities avoid occurrences, List.drop_left]

end Blanc.Lift.WithdrawalRequest
