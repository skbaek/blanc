import Blanc.HistoricalFork
import Blanc.ExecutionStagedBodyTrace
import Blanc.Ladder
import Blanc.ExecutionHistory
import Blanc.ExecutionHistoryCommittedCell
import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionSettledReceiptLogs
import Blanc.ExecutionHistoryCommittedCuts
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionStagedAdmission
import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionHistoryInAppend
import Blanc.ExecutionHistoryInSystemEnvironment
import Blanc.ExecutionHistoryInSystemOpenings
import Blanc.LadderSem
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionRewardCredits
import Blanc.Lift.CallerProvenance
import Blanc.TransactionForward
import Blanc.ExecutionMessageEffects
import Blanc.Lift.CommittedLogs
import Blanc.RlpConcrete
import Blanc.TransactionForwardSupport
import Blanc.ExecutionMessageGas
import Blanc.ExecutionTraceCalldata
import Blanc.ExecutionTransactionGas
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionCodeAt
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTraceFrameEnv
import Blanc.ExecutionWarmth
import Blanc.ExecutionTraceAdmission
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionTraceWarmth

/-!
# Configured-history, receipt and frame-environment facts

Reachability, committed-cut, append, system-opening, reward-credit, settled-receipt, frame-env
and warmth facts over configured block and history traces.  Each section names the module whose
vocabulary it extends.  Nothing here mentions a contract.
-/

/-! ## From `Blanc/ExecutionHistory.lean` -/

namespace Blanc

open Jaune

namespace ExecutionTrace

end ExecutionTrace

end Blanc

/-! ## From `Blanc/ExecutionHistoryCommittedCuts.lean` -/

namespace Blanc.ExecutionTrace

open Jaune

end Blanc.ExecutionTrace

/-! ## From `Blanc/ExecutionHistoryInAppend.lean` -/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-- The settlement-retained roots of a join are in order. -/
theorem ConfiguredHistoryTraceIn.settledFrames_append {F : Fork → Prop}
    {cfg : ChainConfig} {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) :
    (append first second).settledFrames =
      first.settledFrames ++ second.settledFrames := by
  induction second with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.settledFrames, List.append_nil]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.settledFrames, ih, List.append_assoc]

end ExecutionTrace

end Blanc

/-! ## From `Blanc/ExecutionHistoryInSystemOpenings.lean` -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Pre-Cancun blocks have no opening installation obligations. -/
theorem ConfiguredHistoryTraceIn.systemCodeAtOpenings_of_preCancun
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (forks : trace.ForksSatisfy PreCancun) : trace.SystemCodeAtOpenings := by
  induction trace with
  | refl => trivial
  | step prior block ih =>
      exact ⟨ih forks.1, SystemCodeInstalledAt.of_preCancun _ block.forkIn forks.2⟩

/-- Opening installation producers compose along the same retained append. -/
theorem ConfiguredHistoryTraceIn.SystemCodeAtOpenings_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain}
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c) :
    (left.append right).SystemCodeAtOpenings ↔
      left.SystemCodeAtOpenings ∧ right.SystemCodeAtOpenings := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, SystemCodeAtOpenings, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, SystemCodeAtOpenings, ih, and_assoc]

/-- Fork properties split across the same retained append. -/
theorem ConfiguredHistoryTraceIn.ForksSatisfy_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain} (G : Fork → Prop)
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c) :
    (left.append right).ForksSatisfy G ↔ left.ForksSatisfy G ∧ right.ForksSatisfy G := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, ForksSatisfy, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, ForksSatisfy, ih, and_assoc]

/-- A pre-Prague spine needs no authority exclusion: the gated form holds outright. -/
theorem ConfiguredHistoryTraceIn.pragueNoAuthorityAt_of_prePrague
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (forks : trace.ForksSatisfy PrePrague) (a : Adr) : trace.PragueNoAuthorityAt a := by
  induction trace with
  | refl => trivial
  | step prior block ih => exact ⟨ih forks.1, fun notPre => (notPre forks.2).elim⟩

end Blanc.ExecutionTrace

/-! ## From `Blanc/ExecutionRewardCredits.lean` -/

namespace Blanc

open Jaune

/-! ## Bridge to the historical per-credit reward premise -/

namespace ExecutionTrace

/-- Every block of a retained history funds its reward credits; `stateGas = none`
comes per block from `BodyStageCapabilities F`. -/
theorem ConfiguredHistoryTraceIn.rewardCreditsFunded
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint : BlockChain} :
    {future : BlockChain} → (history : ConfiguredHistoryTraceIn F cfg checkpoint future) →
    BodyStageCapabilities F → history.RewardCreditsFunded
  | _, .refl _ _ _, _ => trivial
  | _, .step prior block, capabilities =>
      ⟨prior.rewardCreditsFunded capabilities,
        block.rewardCreditsFunded (capabilities.stateGas_none block.forkIn)⟩

end ExecutionTrace

end Blanc

/-! ## From `Blanc/ExecutionSettledReceiptLogs.lean` -/

namespace Blanc.ExecutionTrace

open Jaune

/-- For a positive index below 128, actual later indices suffice: encoded-key
separation follows from Jaune's codec, even for arbitrarily large suffix indices. -/
theorem TransactionTrace.receipt_of_settledRoots_after_later_indices
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {txs : List (Nat × Tx)} {finalBenv : Benv} {finalBout : BlockOutput}
    (suffix : ApplyTransactionsTrace txs (benv.withState state) bout' finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (positive : 0 < index) (small : index < 128)
    (later : ∀ item ∈ txs, index < item.1) :
    finalBout.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
      some (makeReceipt tx trace.messageOut.error bout'.cumulativeGasUsed
        (trace.settledRoots.flatMap (fun root => root.post.logs))) := by
  apply trace.receipt_of_settledRoots_after_suffix suffix hsg
  intro item member
  exact RlpConcrete.receipt_key_ne_of_small positive small (by have := later item member; omega)

end Blanc.ExecutionTrace

/-! ## From `Blanc/ExecutionTraceFrameEnv.lean` -/

namespace Blanc

open Jaune

/-! ## Direct children keep the code at an address no CREATE frame targets -/

namespace ExecutionTrace

/-! ## From retained slots to whole histories -/

/-- An address whose installed code has a size no canonical system code has is not a system
address. -/
theorem not_mem_systemTargets_of_size {w : State} {ca : Adr} {c : ByteArray}
    (installed : w.getCode ca = c) (system : SystemCodeInstalled w)
    (size : ∀ p ∈ systemContracts, p.2.size ≠ c.size) :
    ca ∉ systemTargets := by
  intro hmem
  have hsize : ∀ p ∈ systemContracts, p.1 = ca → False := by
    intro p hp hca
    have h := system p hp
    rw [hca, installed] at h
    exact size p hp (congrArg ByteArray.size h).symm
  simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hsize (beaconRootsAddress, beaconRootsCode) (by simp only [systemContracts,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_or]) rfl
  · exact hsize (historyStorageAddress, historyStorageCode) (by simp only [systemContracts,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_or, or_true]) rfl
  · exact hsize (withdrawalRequestPredeployAddress, withdrawalRequestCode)
      (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        true_or, or_true]) rfl
  · exact hsize (consolidationRequestPredeployAddress, consolidationRequestCode)
      (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        or_true]) rfl

/-! ## The raw frames of a history are closed under descent

Every frame a raw frame enters is itself a raw frame of the history.  So a trace-local premise over
`trace.rawFrames` (such as "no CREATE frame targets `a`") covers every frame below a given raw
frame, which is what per-frame consumers like `Exec.childFrames_codeAt_keep` need. -/

end ExecutionTrace

end Blanc

/-! ## From `Blanc/ExecutionTraceWarmth.lean` -/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-! ### The message wrappers -/

/-! ### Transactions -/

theorem TransactionTrace.rawFrames_precompile_warm
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (ha : a ∈ benv.stat.rules.precompiles) :
    ∀ root ∈ trace.rawFrames, a ∈ root.devm.accessedAddresses := by
  have hbenv := prepareMessage_benv trace.prepared
  refine trace.message.rawFrames_warm ?_ (prepareMessage_precompile_accessed trace.prepared ?_)
  · rw [hbenv]
    exact hfork.rules_stateGas_none
  · exact ha

theorem ApplyTransactionsTrace.rawFrames_precompile_warm
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (ha : a ∈ benv.stat.rules.precompiles) :
    ∀ root ∈ trace.rawFrames, a ∈ root.devm.accessedAddresses := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | cons head tail ih =>
      intro root member
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rawFrames_precompile_warm hfork ha root member
      · exact ih hfork ha root member

/-! ### Bodies and histories -/

/-- Every frame of a body is entered by a system message or by a transaction. -/
theorem AppliedBodyTrace.rawFrames_system_or_tx
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout) :
    ∀ root ∈ trace.rawFrames,
      root ∈ trace.systemRawFrames ∨ root ∈ trace.transactions.rawFrames := by
  intro root member
  simp only [AppliedBodyTrace.rawFrames, AppliedBodyTrace.systemRawFrames,
    List.mem_append] at member ⊢
  rcases member with ((member | member) | member) | member
  · exact Or.inl (Or.inl (Or.inl member))
  · exact Or.inl (Or.inl (Or.inr member))
  · exact Or.inr member
  · exact Or.inl (Or.inr member)

/-- The transaction frames of a body start with `a` warm, when `a` is a precompile. -/
theorem AppliedBodyTrace.transactions_rawFrames_warm
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) {a : Adr}
    (ha : a ∈ benv.stat.rules.precompiles) :
    ∀ root ∈ trace.transactions.rawFrames, a ∈ root.devm.accessedAddresses :=
  trace.transactions.rawFrames_precompile_warm hfork ha

/-- Every frame of a configured history is entered by a system message or by a transaction. -/
theorem ConfiguredHistoryTrace.rawFrames_system_or_tx
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, root ∈ trace.systemRawFrames ∨ root ∈ trace.txRawFrames := by
  induction trace with
  | refl => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTrace.rawFrames, ConfiguredHistoryTrace.systemRawFrames,
        ConfiguredHistoryTrace.txRawFrames, List.mem_append] at member ⊢
      rcases member with member | member
      · rcases ih root member with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
      · rcases block.bodyTrace.rawFrames_system_or_tx root member with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

/-- **Every transaction frame of a configured history starts with `a` warm**, whenever `a` is a
precompile of every covered fork. -/
theorem ConfiguredHistoryTrace.txRawFrames_warm
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) {a : Adr}
    (ha : ∀ f, CoveredFork f → a ∈ (Fork.ruleSet f).precompiles) :
    ∀ root ∈ trace.txRawFrames, a ∈ root.devm.accessedAddresses := by
  induction trace with
  | refl => intro root member; simp only [txRawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTrace.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih root member
      · exact block.bodyTrace.transactions_rawFrames_warm block.covered
          (ha _ block.covered) root member

end ExecutionTrace

end Blanc
