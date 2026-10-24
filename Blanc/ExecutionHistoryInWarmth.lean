import Blanc.ExecutionHistory
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionTraceWarmth
import Blanc.ExecutionHistoryInForkFacts
import Blanc.HistoricalFork

/-!
# Warmth of transaction frames along selected-domain (`In`) histories

`In` forms of `ConfiguredHistoryTrace.txRawFrames_warm`
(`Blanc/ExecutionTraceWarmth.lean`): every transaction frame of a retained
`In`-history starts with every active precompile warm. The per-transaction
step needs only `stateGas = none` (the existing
`prepareMessage_precompile_accessed` warms unconditionally, and accessed
sets only grow), so `CoveredFork` is replaced by the history's own
`BodyStageCapabilities` everywhere.

The scope is explicit per fork, as ordered: precompile membership is a
per-fork premise. Warmth holds on every access regime (`prepareMessage`
warms precompiles unconditionally), so there is no access hypothesis.
The `0x02` headline corollary discharges precompile membership on `HistFork`
by decision.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-- The frames of the transactions of a retained `In`-history. -/
def ConfiguredHistoryTraceIn.txRawFrames :
    ConfiguredHistoryTraceIn F cfg checkpoint future → List Exec.Deriv
  | .refl _ _ _ => []
  | .step prior block => prior.txRawFrames ++ block.bodyTrace.transactions.rawFrames

/-- A transaction enters only frames that start with `a` warm, whenever `a`
is a precompile of the active rules. Needs only `stateGas = none`. -/
theorem TransactionTrace.rawFrames_precompile_warmIn
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (ha : a ∈ benv.stat.rules.precompiles) :
    ∀ root ∈ trace.rawFrames, a ∈ root.devm.accessedAddresses := by
  have hbenv := prepareMessage_benv trace.prepared
  refine trace.message.rawFrames_warm ?_ (prepareMessage_precompile_accessed trace.prepared ?_)
  · rw [hbenv]
    exact hsg
  · exact ha

/-- A selected transaction list enters only warm-`a` frames. -/
theorem ApplyTransactionsTrace.rawFrames_precompile_warmIn
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (ha : a ∈ benv.stat.rules.precompiles) :
    ∀ root ∈ trace.rawFrames, a ∈ root.devm.accessedAddresses := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | cons head tail ih =>
      intro root member
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rawFrames_precompile_warmIn hsg ha root member
      · exact ih hsg ha root member

/-- The transaction frames of a staged body start with `a` warm. -/
theorem StagedBodyTrace.transactions_rawFrames_warmIn
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (ha : a ∈ benv.stat.rules.precompiles) :
    ∀ root ∈ trace.transactions.rawFrames, a ∈ root.devm.accessedAddresses :=
  trace.transactions.rawFrames_precompile_warmIn hsg ha

/-- The transaction frames of a retained `In`-block start with `a` warm,
with per-block `stateGas = none` from the history's own capabilities. -/
theorem ConfiguredBlockTraceIn.transactions_rawFrames_warmIn
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    {a : Adr} (ha : ∀ f, F f → a ∈ (Fork.ruleSet f).precompiles) :
    ∀ root ∈ trace.bodyTrace.transactions.rawFrames,
      a ∈ root.devm.accessedAddresses :=
  trace.bodyTrace.transactions_rawFrames_warmIn
    (capabilities.stateGas_none trace.forkIn) (ha _ trace.forkIn)

/-- **Every transaction frame of a retained `In`-history starts with `a`
warm**, whenever `a` is a precompile of every selected fork. -/
theorem ConfiguredHistoryTraceIn.txRawFrames_warmIn
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {a : Adr} (ha : ∀ f, F f → a ∈ (Fork.ruleSet f).precompiles) :
    ∀ root ∈ history.txRawFrames, a ∈ root.devm.accessedAddresses := by
  induction history with
  | refl => intro root member; simp only [txRawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTraceIn.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih root member
      · exact block.transactions_rawFrames_warmIn capabilities ha root member

/-- **The `0x02` precompile is warm in every transaction frame of a
historical `In`-history.** The precompile premise discharges on `HistFork`
by decision; there is no access or Berlin-onwards premise. -/
theorem ConfiguredHistoryTraceIn.txRawFrames_warm_hist
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (capabilities : BodyStageCapabilities HistFork) :
    ∀ root ∈ history.txRawFrames, (2 : Adr) ∈ root.devm.accessedAddresses :=
  history.txRawFrames_warmIn capabilities
    (fun _ hf => hf.two_mem_precompiles)

end ExecutionTrace

end Blanc
