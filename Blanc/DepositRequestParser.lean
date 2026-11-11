import Jaune.Transaction

/-! # Positive deposit parsing over the actual ordered receipt keys -/

namespace Blanc

open Jaune

private theorem deposit_logs_loop (logs : List Log) (acc : Bytes)
    (accepted : ∀ log ∈ logs.filter (fun log => decide
      (log.address = depositContractAddress ∧
        log.topics[0]? = some depositEventSignatureHash)),
      ∃ record, extractDepositData log.data = .ok record) :
    forIn logs acc (fun log bytes =>
      if log.address = depositContractAddress ∧
          log.topics[0]? = some depositEventSignatureHash then do
        let record ← Except.mapError TransitionError.block (extractDepositData log.data)
        pure (ForInStep.yield (bytes ++ record))
      else pure (ForInStep.yield bytes)) =
      (.ok (acc ++ ((logs.filter (fun log => decide
        (log.address = depositContractAddress ∧
          log.topics[0]? = some depositEventSignatureHash))).filterMap
            (fun log => match extractDepositData log.data with
              | .ok record => some record
              | .error _ => none)).flatten) : Except TransitionError Bytes) := by
  induction logs generalizing acc with
  | nil =>
      simp only [List.forIn_nil, List.filter_nil, List.filterMap_nil, List.flatten_nil,
        List.append_nil]
      rfl
  | cons log logs ih =>
      have tail : ∀ item ∈ logs.filter (fun item => decide
          (item.address = depositContractAddress ∧
            item.topics[0]? = some depositEventSignatureHash)),
          ∃ record, extractDepositData item.data = .ok record := by
        intro item member
        exact accepted item (List.mem_filter.mpr
          ⟨List.mem_cons_of_mem _ (List.mem_filter.mp member).1,
            (List.mem_filter.mp member).2⟩)
      by_cases selected : log.address = depositContractAddress ∧
          log.topics[0]? = some depositEventSignatureHash
      · obtain ⟨record, extracted⟩ := accepted log
          (List.mem_filter.mpr ⟨List.mem_cons_self, by simpa only [decide_eq_true_eq]⟩)
        rw [List.forIn_cons]
        simp only [selected, and_self, ite_true, extracted, Except.mapError, bind, Except.bind,
          pure, Except.pure, List.filter_cons, decide_true, List.filterMap_cons,
          List.flatten_cons]
        simpa only [List.append_assoc, bind, Except.bind, pure, Except.pure,
          Except.mapError] using ih (acc ++ record) tail
      · rw [List.forIn_cons]
        simp only [selected, ite_false, pure, Except.pure, bind, Except.bind,
          List.filter_cons, decide_false]
        exact ih acc tail

/-- Positional receipt lookups and acceptance of precisely the selected logs determine the
actual parser's bytes. Repeated keys or equal receipt values retain their occurrences. -/
theorem parseDepositRequests_of_receipts
    {bout : BlockOutput} (receipts : List (Fin 5 × Receipt))
    (lookups : List.Forall₂
      (fun key receipt => bout.receiptsTrie[key]? = some receipt)
      bout.receiptKeys receipts)
    (accepted : ∀ log ∈ receipts.flatMap (fun receipt =>
      receipt.2.logs.filter (fun log => decide
        (log.address = depositContractAddress ∧
          log.topics[0]? = some depositEventSignatureHash))),
      ∃ record, extractDepositData log.data = .ok record) :
    parseDepositRequests bout = .ok
      (((receipts.flatMap (fun receipt =>
        receipt.2.logs.filter (fun log => decide
          (log.address = depositContractAddress ∧
            log.topics[0]? = some depositEventSignatureHash)))).filterMap
          (fun log => match extractDepositData log.data with
            | .ok record => some record
            | .error _ => none)).flatten) := by
  unfold parseDepositRequests
  dsimp only
  have loop : ∀ (keys : List Bytes) (receipts : List (Fin 5 × Receipt)),
      List.Forall₂ (fun key receipt => bout.receiptsTrie[key]? = some receipt)
        keys receipts →
      (∀ log ∈ receipts.flatMap (fun receipt =>
        receipt.2.logs.filter (fun log => decide
          (log.address = depositContractAddress ∧
            log.topics[0]? = some depositEventSignatureHash))),
        ∃ record, extractDepositData log.data = .ok record) →
      ∀ acc : Bytes,
      forIn keys acc (fun key bytes => do
        let receipt ← bout.receiptsTrie[key]?.toExcept
          (TransitionError.internal (.invariant (.text "receipt not found")))
        let bytes ← forIn receipt.2.logs bytes (fun log bytes =>
          if log.address = depositContractAddress ∧
              log.topics[0]? = some depositEventSignatureHash then do
            let record ← Except.mapError TransitionError.block (extractDepositData log.data)
            pure (ForInStep.yield (bytes ++ record))
          else pure (ForInStep.yield bytes))
        pure (ForInStep.yield bytes)) =
        (.ok (acc ++ ((receipts.flatMap (fun receipt =>
          receipt.2.logs.filter (fun log => decide
            (log.address = depositContractAddress ∧
              log.topics[0]? = some depositEventSignatureHash)))).filterMap
                (fun log => match extractDepositData log.data with
                  | .ok record => some record
                  | .error _ => none)).flatten) : Except TransitionError Bytes) := by
    intro keys receipts related
    induction related with
    | nil =>
        intro _ acc
        simp only [List.forIn_nil, List.flatMap_nil, List.filterMap_nil, List.flatten_nil,
          List.append_nil]
        rfl
    | @cons key receipt keys receipts lookup related ih =>
        intro allAccepted acc
        have headAccepted := fun log member => allAccepted log
          (List.mem_flatMap.mpr ⟨receipt, List.mem_cons_self, member⟩)
        rw [List.forIn_cons, lookup]
        simp only [Option.toExcept, bind, Except.bind]
        have logsRun := deposit_logs_loop receipt.2.logs acc headAccepted
        simp only [bind, Except.bind] at logsRun
        rw [logsRun]
        simp only [pure, Except.pure, List.flatMap_cons,
          List.filterMap_append, List.flatten_append]
        simp only [Option.toExcept, bind, Except.bind, pure, Except.pure] at ih
        rw [ih (fun log member => allAccepted log (by
          rw [List.flatMap_cons]
          exact List.mem_append_right _ member))]
        rw [List.append_assoc]
  rw [loop _ _ lookups accepted []]
  rfl

/-- Arbitrary withdrawals change neither actual receipt keys nor the receipt trie. -/
theorem withdrawalsPass_receipts
    (rules : ForkRules) (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal) :
    (withdrawalsPass rules benv bout wds).2.receiptKeys = bout.receiptKeys ∧
      (withdrawalsPass rules benv bout wds).2.receiptsTrie = bout.receiptsTrie := by
  unfold withdrawalsPass
  split <;> exact ⟨rfl, rfl⟩

/-- The actual request parser is unchanged by the arbitrary withdrawal pass. -/
theorem parseDepositRequests_withdrawalsPass
    (rules : ForkRules) (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal) :
    parseDepositRequests (withdrawalsPass rules benv bout wds).2 =
      parseDepositRequests bout := by
  obtain ⟨keys, trie⟩ := withdrawalsPass_receipts rules benv bout wds
  unfold parseDepositRequests
  rw [keys, trie]

end Blanc
