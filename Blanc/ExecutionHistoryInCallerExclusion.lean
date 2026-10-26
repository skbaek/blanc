import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionSenderOccurrences

/-!
Caller exclusion on selected historical transaction traces. The pre-Prague
specialization derives disabled delegation from the actual history's forks.
Initial empty code and entered-creation avoidance are independent execution
obligations; sender-query exclusion alone does not establish either of them.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Every transaction-entered frame excludes the address as caller when the
actual admitted senders exclude it and its raw entries have empty code with
no entered creation at that address. System frames are outside the conclusion. -/
theorem ConfiguredHistoryTraceIn.txRawFrames_caller_excluded_of_empty
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain} {a : Adr}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (senders : history.NoSenderAt a)
    (empty : ∀ root ∈ history.txRawFrames, root.devm.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a) :
    ∀ root ∈ history.txRawFrames, root.sevm.caller ≠ a := by
  induction history with
  | refl =>
    intro root member
    simp only [ConfiguredHistoryTraceIn.txRawFrames, List.not_mem_nil] at member
  | step prior block ih =>
    have earlier := ih senders.1
      (fun root member => empty root (List.mem_append_left _ member))
      (fun root member => avoid root (List.mem_append_left _ member))
    have inBlock := block.bodyTrace.transactions.caller_excluded_noStateGas
      (capabilities.stateGas_none block.forkIn) senders.2
      (fun root member => empty root (List.mem_append_right _ member))
      (fun root member => avoid root (List.mem_append_right _ (by
        simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, List.mem_append]
        exact Or.inl (Or.inr member))))
    intro root member
    rcases List.mem_append.mp member with before | here
    · exact earlier root before
    · exact inBlock root here

/-- On an actual pre-Prague history, no authorization exclusion is needed:
the selected rules disable delegation. The initial code and creation-avoidance
premises still require their own producers. -/
theorem ConfiguredHistoryTraceIn.txRawFrames_caller_excluded_prePrague
    {cfg : ChainConfig} {checkpoint future : BlockChain} {a : Adr}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (prePrague : history.AllPrePrague) (senders : history.NoSenderAt a)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (initial : checkpoint.state.getCode a = ByteArray.empty) :
    ∀ root ∈ history.txRawFrames, root.sevm.caller ≠ a := by
  have empty := (history.codeAt_empty_prePrague BodyStageCapabilities.historical
    prePrague avoid initial).1
  exact history.txRawFrames_caller_excluded_of_empty BodyStageCapabilities.historical
    senders empty avoid

/-- Use the original full admitted sender-query population, including VM
reverts and repeated queries. This wrapper neither creates a new query scope
nor derives initial emptiness or absence of earlier contract incarnations. -/
theorem ConfiguredHistoryTraceIn.txRawFrames_caller_excluded_prePrague_of_senderQueries
    {cfg : ChainConfig} {checkpoint future : BlockChain} {a : Adr}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (prePrague : history.AllPrePrague)
    (excluded : ∀ query ∈ history.senderQueries, query.recover ≠ .ok a)
    (avoid : ∀ root ∈ history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (initial : checkpoint.state.getCode a = ByteArray.empty) :
    ∀ root ∈ history.txRawFrames, root.sevm.caller ≠ a :=
  history.txRawFrames_caller_excluded_prePrague prePrague
    (history.noSenderAt_of_senderQueries excluded) avoid initial

end Blanc.ExecutionTrace
