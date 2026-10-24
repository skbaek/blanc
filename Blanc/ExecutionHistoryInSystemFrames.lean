import Blanc.ExecutionHistory
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionTraceSystem
import Blanc.SystemContracts
import Blanc.ExecutionHistoryInForkFacts
import Blanc.ExecutionHistoryInCodeAt
import Blanc.HistoricalFork

/-!
# System frames along selected-domain (`In`) histories, by fork era

`In` forms of the system-frame environment facts
(`Blanc/ExecutionTraceSystemCode.lean`): every system frame of a retained
`In`-history targets an installed system address, with a fork-aware
installed set — nothing installed before Cancun (the disabled-stage
lemmas leave no system frames), only the beacon-roots contract on Cancun,
all four system contracts from Prague.

The frame-target half is complete at block and history level: it needs
only spawn-freedom of the entered code plus the era's disabled-stage
flags, both discharged on `HistFork` by decision. The state-preservation
half is complete before Cancun (the era's installed set is empty, so there
is nothing to preserve) and through every system message
(`installed_keep_noStateGas`, via the neutral message-level code fact);
preservation through transactions on Cancun and later eras goes through
the neutral non-deletion chain
(`Blanc/ExecutionHistoryInNoDel.lean`) and is completed at staged, block,
and history level in `Blanc/ExecutionHistoryInSystemCodeKeep.lean`.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-- The system-message frames of a staged body. -/
def StagedBodyTrace.systemRawFrames
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) : List Exec.Deriv :=
  trace.beacon.rawFrames ++ trace.history.rawFrames ++ trace.requests.rawFrames

/-- The system-message frames of a retained `In`-block. -/
def ConfiguredBlockTraceIn.systemRawFrames
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) : List Exec.Deriv :=
  trace.bodyTrace.systemRawFrames

/-- The system-message frames of a retained `In`-history. -/
def ConfiguredHistoryTraceIn.systemRawFrames :
    ConfiguredHistoryTraceIn F cfg checkpoint future → List Exec.Deriv
  | .refl _ _ _ => []
  | .step prior block => prior.systemRawFrames ++ block.systemRawFrames

/-- The system contracts installed at one fork: none before Cancun, only
the beacon-roots contract on Cancun, all four from Prague on (Amsterdam,
outside the historical domain, keeps all four). -/
def installedAt : Fork → List (Adr × ByteArray)
  | .byzantium => []
  | .constantinople => []
  | .petersburg => []
  | .istanbul => []
  | .muirGlacier => []
  | .berlin => []
  | .london => []
  | .arrowGlacier => []
  | .grayGlacier => []
  | .paris => []
  | .shanghai => []
  | .cancun => [(beaconRootsAddress, beaconRootsCode)]
  | .prague => systemContracts
  | .osaka => systemContracts
  | .bpo1 => systemContracts
  | .bpo2 => systemContracts
  | .amsterdam => systemContracts

/-- The canonical system-contract code installed at one fork is present in
a state. -/
def SystemCodeInstalledAt (f : Fork) (w : State) : Prop :=
  ∀ p ∈ installedAt f, w.getCode p.1 = p.2

/-- Before Cancun nothing is installed. -/
theorem HistFork.installedAt_empty_of_preCancun {f : Fork}
    (h : HistFork f) (hc : PreCancun f) : installedAt f = [] := by
  revert h hc
  cases f <;> decide

/-- On Cancun only the beacon-roots contract is installed. -/
theorem HistFork.installedAt_beacon_of_cancun {f : Fork}
    (h : HistFork f) (hc : f = .cancun) :
    installedAt f = [(beaconRootsAddress, beaconRootsCode)] := by
  revert h hc
  cases f <;> decide

/-- The four system-message targets are exactly the installed addresses
from Prague on. -/
theorem systemTargets_installedAt_of_pragueOnwards {f : Fork}
    (hp : PragueOnwards f) : systemTargets = (installedAt f).map Prod.fst := by
  revert hp
  cases f <;> decide

/-- Every frame of a beacon stage whose entered code is spawn-free targets
the beacon-roots contract. -/
theorem BeaconStageTrace.rawFrames_target_beaconRoots
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (h : ∀ root ∈ trace.rawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = beaconRootsAddress := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ message _ _ =>
      exact message.rawFrames_target_of_spawnFree (fun r m => h r m)

/-- Every frame of a history-storage stage whose entered code is spawn-free
targets the history-storage contract. -/
theorem HistoryStageTrace.rawFrames_target_historyStorage
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (h : ∀ root ∈ trace.rawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = historyStorageAddress := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ _ _ _ message _ _ =>
      exact message.rawFrames_target_of_spawnFree (fun r m => h r m)

/-- Every frame of a request stage whose entered code is spawn-free targets
a request contract. -/
theorem RequestStageTrace.systemRawFrames_target_of_spawnFree
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (h : ∀ root ∈ trace.rawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget ∈
      [withdrawalRequestPredeployAddress, consolidationRequestPredeployAddress] := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called _ requests _ =>
      have hwithdrawal := requests.withdrawal.rawFrames_target_of_spawnFree
        (fun r m => h r (by
          simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append]
          tauto))
      have hconsolidation := requests.consolidation.rawFrames_target_of_spawnFree
        (fun r m => h r (by
          simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append]
          tauto))
      intro root member
      simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases member with member | member
      · exact Or.inl (hwithdrawal root member)
      · exact Or.inr (hconsolidation root member)

/-- Every system frame of a staged body whose entered code is spawn-free
targets a system address. -/
theorem StagedBodyTrace.systemRawFrames_target_of_spawnFree
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (h : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ∈ systemTargets := by
  intro root member
  have hbeacon := trace.beacon.rawFrames_target_beaconRoots
    (fun r m => h r (by simp only [StagedBodyTrace.systemRawFrames, List.mem_append]; tauto))
  have hhistory := trace.history.rawFrames_target_historyStorage
    (fun r m => h r (by simp only [StagedBodyTrace.systemRawFrames, List.mem_append]; tauto))
  have hrequests := trace.requests.systemRawFrames_target_of_spawnFree
    (fun r m => h r (by
      simp only [StagedBodyTrace.systemRawFrames, RequestStageTrace.rawFrames,
        RequestsTrace.rawFrames, List.mem_append]
      tauto))
  simp only [StagedBodyTrace.systemRawFrames, RequestStageTrace.rawFrames,
    RequestsTrace.rawFrames, List.mem_append] at member
  simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false]
  rcases member with (member | member) | member
  · exact Or.inl (hbeacon root member)
  · exact Or.inr (Or.inl (hhistory root member))
  · have hr := hrequests root member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact Or.inr (Or.inr hr)

/-- A system message keeps the canonical code installed when none of the
frames it enters is a CREATE at a system address. Neutral form. -/
theorem SystemMessageTrace.installed_keep_noStateGas
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : SystemCodeInstalled benv.state)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    SystemCodeInstalled state := by
  intro p hp
  obtain ⟨hpost, -⟩ := trace.codeAt_empty_noStateGas hsg (avoid p hp)
  rw [hpost]
  exact installed p hp

/-- **Every system frame of a retained `In`-block targets the block fork's
installed set.** Before Cancun there are no system frames; on Cancun only
the beacon-roots stage can run; from Prague on all four stages target the
four system contracts. -/
theorem ConfiguredBlockTraceIn.systemFrames_target_inEra
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (hHist : HistFork trace.fork)
    (hspawn : ∀ root ∈ trace.systemRawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ trace.systemRawFrames,
      root.sevm.currentTarget ∈ (installedAt trace.fork).map Prod.fst := by
  rcases hHist.preCancun_cancun_pragueOnwards with hpre | hcan | hprague
  · have hbeacon := hHist.sys_beaconRoots_false_of_preCancun hpre
    have hhistory := hHist.sys_historyStorage_false_of_prePrague hpre.toPrePrague
    have hrequests := hHist.header_requestsHash_false_of_prePrague hpre.toPrePrague
    have hempty : trace.systemRawFrames = [] := by
      have hb := BeaconStageTrace.rawFrames_of_disabled trace.bodyTrace.beacon hbeacon
      have hh := HistoryStageTrace.rawFrames_of_disabled trace.bodyTrace.history hhistory
      have hr := RequestStageTrace.rawFrames_of_disabled trace.bodyTrace.requests hrequests
      show trace.bodyTrace.beacon.rawFrames ++ trace.bodyTrace.history.rawFrames ++
        trace.bodyTrace.requests.rawFrames = []
      simp only [hb, hh, hr, List.append_nil]
    intro root member
    rw [hempty] at member
    simp only [List.not_mem_nil] at member
  · have hpreP : PrePrague .cancun := by decide
    have hHistC : HistFork .cancun := by decide
    have hhistory := hHistC.sys_historyStorage_false_of_prePrague hpreP
    have hrequests := hHistC.header_requestsHash_false_of_prePrague hpreP
    have hinit : (initBenv trace.fork pre trace.block.header).stat.rules
        = trace.fork.ruleSet := rfl
    have hhistory' : (initBenv trace.fork pre trace.block.header).stat.rules.sys.historyStorage
        = false := by
      rw [hinit, hcan]
      exact hhistory
    have hrequests' : (initBenv trace.fork pre trace.block.header).stat.rules.header.requestsHash
        = false := by
      rw [hinit, hcan]
      exact hrequests
    have hempty : trace.bodyTrace.history.rawFrames = [] :=
      HistoryStageTrace.rawFrames_of_disabled _ hhistory'
    have hemptyReq : trace.bodyTrace.requests.rawFrames = [] :=
      RequestStageTrace.rawFrames_of_disabled _ hrequests'
    have hchar := HistFork.installedAt_beacon_of_cancun hHist hcan
    intro root member
    simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames,
      hempty, hemptyReq, List.append_nil] at member
    have htarget := trace.bodyTrace.beacon.rawFrames_target_beaconRoots
      (fun r m => hspawn r (by
        simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames,
          hempty, hemptyReq, List.append_nil]
        exact m)) root member
    rw [hchar]
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
    exact htarget
  · have htarget := trace.bodyTrace.systemRawFrames_target_of_spawnFree
      (fun r m => hspawn r (by
        simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames] at m ⊢
        exact m))
    intro root member
    simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames] at member
    have hmem := htarget root member
    rw [← systemTargets_installedAt_of_pragueOnwards hprague]
    exact hmem

/-- **Every system frame of a retained `In`-history targets the installed
set of its own block's fork.** -/
theorem ConfiguredHistoryTraceIn.systemFrames_target_inEra
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (hHist : ∀ f, F f → HistFork f)
    (hspawn : ∀ root ∈ history.systemRawFrames, SpawnFree root.sevm.code) :
    ∀ root ∈ history.systemRawFrames, ∃ f, HistFork f ∧
      root.sevm.currentTarget ∈ (installedAt f).map Prod.fst := by
  induction history with
  | refl => intro root member; simp only [systemRawFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTraceIn.systemRawFrames, List.mem_append] at member
      rcases member with member | member
      · obtain ⟨f, hf, hmem⟩ := ih
          (fun r m => hspawn r (by
            simp only [ConfiguredHistoryTraceIn.systemRawFrames, List.mem_append]
            exact Or.inl m)) root member
        exact ⟨f, hf, hmem⟩
      · exact ⟨block.fork, hHist _ block.forkIn,
          block.systemFrames_target_inEra (hHist _ block.forkIn)
            (fun r m => hspawn r (by
              simp only [ConfiguredHistoryTraceIn.systemRawFrames, List.mem_append]
              exact Or.inr m)) root member⟩

/-- **A pre-Cancun retained `In`-block preserves its (empty) installed
set**: there is nothing installed, so there is nothing to preserve. -/
theorem ConfiguredBlockTraceIn.systemFrames_installed_preCancun
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (hHist : HistFork trace.fork) (hpre : PreCancun trace.fork) :
    SystemCodeInstalledAt trace.fork post.state := by
  unfold SystemCodeInstalledAt
  rw [HistFork.installedAt_empty_of_preCancun hHist hpre]
  intro p hp
  simp only [List.not_mem_nil] at hp

/-- **Every pre-Cancun installed set holds in every state**, vacuously:
there is nothing installed. -/
theorem SystemCodeInstalledAt.of_preCancun {f : Fork} (w : State)
    (hf : HistFork f) (hpf : PreCancun f) : SystemCodeInstalledAt f w := by
  unfold SystemCodeInstalledAt
  rw [HistFork.installedAt_empty_of_preCancun hf hpf]
  intro p hp
  simp only [List.not_mem_nil] at hp

end ExecutionTrace

end Blanc
