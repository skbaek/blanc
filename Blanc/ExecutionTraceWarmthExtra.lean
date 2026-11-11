import Blanc.ExecutionWarmth
import Blanc.ExecutionTraceAdmission
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionTraceWarmth

/-!
# Warmth of the frames a transaction enters

Every transaction pre-warms every precompile of the active rules (EIP-2929), and the accessed set
of a frame only grows (`Blanc/ExecutionWarmth.lean`).  So every frame entered by a transaction's
message, including those of subtrees that later revert, starts with every precompile warm.  A
system message starts with an empty set (`processSystemTransactionMsg`, on the covered forks that
have no state gas), so nothing is claimed of its frames.
-/

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
