import Blanc.ExecutionHistory
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionStagedAdmission
import Blanc.ExecutionTraceEntry
import Blanc.HistoricalFork
import Blanc.ExecutionTraceFrameEnv
import Blanc.Lift.HistoryGas
import Blanc.ExecutionTraceCalldata

/-!
# Per-raw-frame entry and gas facts for selected-domain (`In`) carriers

`StagedBodyTrace`, `ConfiguredBlockTraceIn` and `ConfiguredHistoryTraceIn`
retain the actual selected fork in `F` instead of a modern `CoveredFork`.
The analogues below carry a fork predicate `F` (entry) or a `stateGas = none`
fact (gas) through exactly the transports the modern carrier proofs use, so
no additional rule fact is needed. Bounds that need a numerical rule value
(`txBase`, `dataNonZero`) are out of reach of `BodyStageCapabilities F` and
are not attempted here.
-/

namespace Blanc

open Jaune

/-- Every fork of the historical domain charges at least 16 gas per nonzero
calldata byte (68 before Istanbul, 16 after). -/
theorem HistFork.dataNonZero_ge {f : Fork} (h : HistFork f) :
    16 ≤ (Fork.ruleSet f).txr.dataNonZero := by
  cases f <;> decide

/-- Every fork of the historical domain has the 21000 base transaction charge. -/
theorem HistFork.txBase_eq {f : Fork} (h : HistFork f) :
    (Fork.ruleSet f).gas.txBase = 21000 := by
  revert h
  cases f <;> decide

namespace ExecutionTrace

/-- An optional beacon stage retains only roots that start at pc zero on a
selected fork. -/
theorem BeaconStageTrace.rootEntryIn {F : Fork → Prop} {rules : ForkRules}
    {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ message _ _ => exact message.rootEntryIn hfork

/-- An optional history stage retains only roots that start at pc zero on a
selected fork. -/
theorem HistoryStageTrace.rootEntryIn {F : Fork → Prop} {rules : ForkRules}
    {benv : Benv} {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ _ _ message _ _ => exact message.rootEntryIn hfork

/-- An optional request stage retains only roots that start at pc zero on a
selected fork. -/
theorem RequestStageTrace.rootEntryIn {F : Fork → Prop} {rules : ForkRules}
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ requests _ => exact requests.rootEntryIn hfork

/-- Every raw frame root a staged body retains starts at pc zero on a
selected fork. -/
theorem StagedBodyTrace.rootEntryIn {F : Fork → Prop} {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  intro root member
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.rootEntryIn hfork root member
  · exact trace.history.rootEntryIn (by simpa only [Benv.withState] using hfork) root member
  · exact trace.transactions.rootEntryIn (by simpa only [Benv.withState] using hfork) root member
  · refine trace.requests.rootEntryIn ?_ root member
    have transactionFork : F trace.transactionBenv.stat.fork := by
      rw [trace.transactions.stat_eq]
      simpa only [Benv.withState] using hfork
    simpa only [Benv.withState] using transactionFork

/-- An optional beacon stage starts its frames below the constant system
grant. -/
theorem BeaconStageTrace.rawFrames_gasMeasure_le {rules : ForkRules}
    {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ systemTransactionGas := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ message _ _ => exact message.rawFrames_gasMeasure_le

/-- An optional history stage starts its frames below the constant system
grant. -/
theorem HistoryStageTrace.rawFrames_gasMeasure_le {rules : ForkRules}
    {benv : Benv} {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ systemTransactionGas := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ _ _ message _ _ => exact message.rawFrames_gasMeasure_le

/-- An optional request stage starts its frames below the constant system
grant. -/
theorem RequestStageTrace.rawFrames_gasMeasure_le {rules : ForkRules}
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure ≤ systemTransactionGas := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ requests _ => exact requests.rawFrames_gasMeasure_le

/-- A staged body's frames start below the block gas limit or the constant
system grant: transactions under the former, system stages under the latter. -/
theorem StagedBodyTrace.rawFrames_gasMeasure_le
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none) :
    ∀ root ∈ trace.rawFrames,
      root.devm.gasMeasure ≤ max benv.stat.blockGasLimit systemTransactionGas := by
  intro root member
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · have h := trace.beacon.rawFrames_gasMeasure_le root member
    exact h.trans (Nat.le_max_right _ _)
  · have h := trace.history.rawFrames_gasMeasure_le root member
    exact h.trans (Nat.le_max_right _ _)
  · have h := trace.transactions.rawFrames_gasMeasure_le_noStateGas hsg root member
    exact h.trans (Nat.le_max_left _ _)
  · have h := trace.requests.rawFrames_gasMeasure_le root member
    exact h.trans (Nat.le_max_right _ _)

/-- Every raw frame root a supplied selected-domain block retains starts at
pc zero on the block's selected fork. -/
theorem ConfiguredBlockTraceIn.rootEntryIn {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  intro root hmem
  simp only [ConfiguredBlockTraceIn.rawFrames] at hmem
  exact trace.bodyTrace.rootEntryIn trace.forkIn root hmem

/-- Every raw frame of a supplied selected-domain block starts with
`gasMeasure < 2 ^ 64`. -/
theorem ConfiguredBlockTraceIn.gas_bound {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 64 := by
  have hsg : (initBenv trace.fork pre trace.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none trace.forkIn
  have hlim : (initBenv trace.fork pre trace.block.header).stat.blockGasLimit < 2 ^ 63 :=
    header_gasLimit_lt_of_transition trace.transition
  have hsys : systemTransactionGas < 2 ^ 64 := by decide
  intro root hmem
  simp only [ConfiguredBlockTraceIn.rawFrames] at hmem
  have h := trace.bodyTrace.rawFrames_gasMeasure_le hsg root hmem
  omega

/-- Every raw frame root a supplied selected-domain history retains starts at
pc zero on its block's selected fork. -/
theorem ConfiguredHistoryTraceIn.rootEntryIn {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  induction trace with
  | refl _ _ _ => intro root hmem; simp only [rawFrames, List.not_mem_nil] at hmem
  | step prior block ih =>
      intro root hmem
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact ih root hmem
      · exact block.rootEntryIn root hmem

/-- Every raw frame of a supplied selected-domain history starts with
`gasMeasure < 2 ^ 64`, with no per-frame premise. -/
theorem ConfiguredHistoryTraceIn.gas_bound {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 64 := by
  induction trace with
  | refl _ _ _ => intro root hmem; simp only [rawFrames, List.not_mem_nil] at hmem
  | step prior block ih =>
      intro root hmem
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact ih root hmem
      · exact block.gas_bound capabilities root hmem

/-- Admission corollary: the per-frame word-gas premise of frame walks follows
from the supplied selected-domain history. -/
theorem ConfiguredHistoryTraceIn.frameAdmitted_gas {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {ca : Adr}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) :
    trace.FrameAdmitted ca (fun _ pre => pre.gasMeasure < 2 ^ 256) := by
  rw [ConfiguredHistoryTraceIn.frameAdmitted_iff_rawFrames]
  intro root member _
  have bound := trace.gas_bound capabilities root member
  omega

/-- Every raw frame of a supplied selected-domain history starts below one
word of gas. -/
theorem ConfiguredHistoryTraceIn.rawFrame_gas {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) :
    ∀ root ∈ trace.rawFrames, root.devm.gasMeasure < 2 ^ 256 := by
  intro root member
  have bound := trace.gas_bound capabilities root member
  omega

/-! ## Selected-domain calldata bounds

The transaction-level fact needs `16 ≤ dataNonZero`, which the capabilities
do not supply: it arrives as an explicit fork-class hypothesis and is
discharged for `HistFork` by `HistFork.dataNonZero_ge`. -/

/-- An optional beacon stage retains only short-calldata frames. -/
theorem BeaconStageTrace.rawFrames_data_bound {rules : ForkRules}
    {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hfork : benv.stat.rules.stateGas = none) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ message _ _ =>
      exact SystemMessageTrace.rawFrames_data_bound_noStateGas message
        (systemData_length_lt (Or.inr ⟨_, rfl⟩)) hfork

/-- An optional history stage retains only short-calldata frames. -/
theorem HistoryStageTrace.rawFrames_data_bound {rules : ForkRules}
    {benv : Benv} {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hfork : benv.stat.rules.stateGas = none) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ _ _ message _ _ =>
      exact SystemMessageTrace.rawFrames_data_bound_noStateGas message
        (systemData_length_lt (Or.inr ⟨_, rfl⟩)) hfork

/-- An optional request stage retains only short-calldata frames. -/
theorem RequestStageTrace.rawFrames_data_bound {rules : ForkRules}
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hfork : benv.stat.rules.stateGas = none) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ requests _ =>
      intro root member
      simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames,
        List.mem_append] at member
      rcases member with member | member
      · exact SystemMessageTrace.rawFrames_data_bound_noStateGas
          requests.withdrawal (systemData_length_lt (Or.inl rfl)) hfork root member
      · exact SystemMessageTrace.rawFrames_data_bound_noStateGas
          requests.consolidation (systemData_length_lt (Or.inl rfl)) hfork root member

/-- A staged body's retained frames all have short calldata. -/
theorem StagedBodyTrace.rawFrames_data_bound
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (hnz : 16 ≤ benv.stat.rules.txr.dataNonZero)
    (hlim : benv.stat.blockGasLimit < 2 ^ 63) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  intro root member
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.rawFrames_data_bound hsg root member
  · exact trace.history.rawFrames_data_bound hsg root member
  · exact ApplyTransactionsTrace.rawFrames_data_bound_noStateGas trace.transactions
      hsg hnz hlim root member
  · have hst := ApplyTransactionsTrace.stat_eq trace.transactions
    have hsg_req : trace.transactionBenv.stat.rules.stateGas = none := by
      rw [hst]
      exact hsg
    exact trace.requests.rawFrames_data_bound hsg_req root member

/-- A staged body's frames enter with gas below the block limit plus the
system grant, under an explicit base-charge hypothesis. -/
theorem StagedBodyTrace.rawFrames_gas_lt
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (hbase : benv.stat.rules.gas.txBase = 21000) :
    ∀ root ∈ trace.rawFrames,
      root.devm.gasMeasure < benv.stat.blockGasLimit + systemTransactionGas + 1 := by
  intro root member
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · have bound := trace.beacon.rawFrames_gasMeasure_le root member
    omega
  · have bound := trace.history.rawFrames_gasMeasure_le root member
    omega
  · have bound := trace.transactions.rawFrames_gas_lt_noStateGas hsg hbase root member
    change root.devm.gasMeasure < benv.stat.blockGasLimit at bound
    omega
  · have bound := trace.requests.rawFrames_gasMeasure_le root member
    omega

/-- Every raw frame of a supplied selected-domain block has short calldata,
under an explicit fork-class nonzero-byte-cost hypothesis. -/
theorem ConfiguredBlockTraceIn.calldata_bound {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  have hsg : (initBenv trace.fork pre trace.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none trace.forkIn
  have hnz' : 16 ≤ (initBenv trace.fork pre trace.block.header).stat.rules.txr.dataNonZero := by
    show 16 ≤ (Fork.ruleSet trace.fork).txr.dataNonZero
    exact hdata trace.fork trace.forkIn
  have hlim : (initBenv trace.fork pre trace.block.header).stat.blockGasLimit < 2 ^ 63 :=
    header_gasLimit_lt_of_transition trace.transition
  intro root hmem
  simp only [ConfiguredBlockTraceIn.rawFrames] at hmem
  exact trace.bodyTrace.rawFrames_data_bound hsg hnz' hlim root hmem

/-- The block-level strict gas bound with an explicit fork-class
base-charge hypothesis. -/
theorem ConfiguredBlockTraceIn.rawFrames_gas_lt {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (hbase : ∀ f, F f → (Fork.ruleSet f).gas.txBase = 21000) :
    ∀ root ∈ trace.rawFrames,
      root.devm.gasMeasure < trace.block.header.gasLimit + systemTransactionGas + 1 := by
  have hsg : (initBenv trace.fork pre trace.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none trace.forkIn
  have hbase' : (initBenv trace.fork pre trace.block.header).stat.rules.gas.txBase
      = 21000 := by
    show (Fork.ruleSet trace.fork).gas.txBase = 21000
    exact hbase trace.fork trace.forkIn
  intro root hmem
  simp only [ConfiguredBlockTraceIn.rawFrames] at hmem
  have h := trace.bodyTrace.rawFrames_gas_lt hsg hbase' root hmem
  show root.devm.gasMeasure < trace.block.header.gasLimit + systemTransactionGas + 1
  exact h

/-- Every raw frame of a supplied selected-domain history has short calldata,
under an explicit fork-class nonzero-byte-cost hypothesis. -/
theorem ConfiguredHistoryTraceIn.calldata_bound {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  induction trace with
  | refl _ _ _ => intro root hmem; simp only [rawFrames, List.not_mem_nil] at hmem
  | step prior block ih =>
      intro root hmem
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact ih root hmem
      · exact block.calldata_bound capabilities hdata root hmem

/-- The history calldata bound on the historical domain. -/
theorem ConfiguredHistoryTraceIn.calldata_bound_hist {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (capabilities : BodyStageCapabilities HistFork) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 :=
  trace.calldata_bound capabilities (fun _ hf => hf.dataNonZero_ge)

/-- The block strict gas bound on the historical domain. -/
theorem ConfiguredBlockTraceIn.rawFrames_gas_lt_hist {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn HistFork cfg pre post)
    (capabilities : BodyStageCapabilities HistFork) :
    ∀ root ∈ trace.rawFrames,
      root.devm.gasMeasure < trace.block.header.gasLimit + systemTransactionGas + 1 :=
  trace.rawFrames_gas_lt capabilities (fun _ hf => hf.txBase_eq)

end ExecutionTrace

end Blanc
