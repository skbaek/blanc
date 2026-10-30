import Blanc.ExecutionHistoryInSystemCodeKeep
import Blanc.ExecutionTraceSystemCode

/-! Canonical system-frame environments over selected historical traces.
Only the selected fork's installed set is required at a block opening:
none before Cancun, beacon roots on Cancun, all four from Prague.
Reachable code freedom is used, including for canonical EIP-7002 code. -/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Exactly the selected fork's system codes at this actual block input. -/
def ConfiguredBlockTraceIn.SystemCodeAtOpening
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) : Prop :=
  SystemCodeInstalledAt trace.fork pre.state

/-- Era-aware installation inputs along the actual retained block spine.
A seam composition must produce these inputs from its checkpoint anchors. -/
def ConfiguredHistoryTraceIn.SystemCodeAtOpenings
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.SystemCodeAtOpenings ∧ block.SystemCodeAtOpening

/-- An installed contract with a distinct code size is outside the active system set. -/
theorem not_mem_installedAt_of_size {f : Fork} {w : State} {ca : Adr} {c : ByteArray}
    (hHist : HistFork f) (installed : w.getCode ca = c)
    (system : SystemCodeInstalledAt f w)
    (size : ∀ p ∈ systemContracts, c.size ≠ p.2.size) :
    ca ∉ (installedAt f).map Prod.fst := by
  intro member
  obtain ⟨p, hp, same⟩ := List.mem_map.mp member
  have hcode := system p hp
  rw [same, installed] at hcode
  exact size p (mem_systemContracts_of_mem_installedAt hHist hp)
    (congrArg ByteArray.size hcode)

private theorem BeaconStageTrace.systemCodeFacts
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none) (installed : SystemCodeInstalled benv.state)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    (∀ root ∈ trace.rawFrames, root.sevm.currentTarget = beaconRootsAddress) ∧
      SystemCodeInstalled state := by
  cases trace with
  | skipped => exact ⟨fun root member => by simp only [rawFrames, List.not_mem_nil] at member,
      installed⟩
  | called enabled out message incorporated run =>
      exact ⟨message.rawFrames_target_of_installed beaconRoots_mem_systemContracts installed,
        message.installed_keep_noStateGas hsg installed avoid⟩

private theorem HistoryStageTrace.systemCodeFacts
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder}
    {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none) (installed : SystemCodeInstalled benv.state)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    (∀ root ∈ trace.rawFrames, root.sevm.currentTarget = historyStorageAddress) ∧
      SystemCodeInstalled state := by
  cases trace with
  | skipped => exact ⟨fun root member => by simp only [rawFrames, List.not_mem_nil] at member,
      installed⟩
  | called enabled lastHash lastHashRun out message incorporated run =>
      have mem : (historyStorageAddress, historyStorageCode) ∈ systemContracts := by
        simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
          or_false, true_or, or_true]
      exact ⟨message.rawFrames_target_of_installed mem installed,
        message.installed_keep_noStateGas hsg installed avoid⟩

private theorem BeaconStageTrace.target_of_beaconCode
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (installed : benv.state.getCode beaconRootsAddress = beaconRootsCode) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = beaconRootsAddress := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called enabled out message incorporated run =>
      obtain ⟨reach, nodeleg, -⟩ := systemContracts_facts _ beaconRoots_mem_systemContracts
      exact message.rawFrames_target_of_code (by rw [installed]; exact reach)
        (by rw [installed]; exact nodeleg)

private theorem RequestStageTrace.systemCodeTargets
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget ∈ systemTargets := by
  cases trace with
  | skipped => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | called enabled requests run =>
      exact (requests.systemFrames_of_installed hfork installed avoid).1

/-- The optional staged form of canonical modern system-frame confinement.
All statements concern the supplied retained stages, without re-extracting execution. -/
theorem StagedBodyTrace.systemFrames_of_installedIn
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hfork : CoveredFork benv.stat.fork) (installed : SystemCodeInstalled benv.state)
    (notCreated : ∀ p ∈ systemContracts, p.1 ∉ benv.createdAccounts)
    (hauth : ∀ p ∈ systemContracts, ∀ q ∈ trace.decodedTxs.putIndex, ∀ auth ∈ q.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ p.1)
    (avoid : ∀ p ∈ systemContracts, ∀ root ∈ trace.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ∈ systemTargets := by
  have avoidBeacon : ∀ p ∈ systemContracts, ∀ root ∈ trace.beacon.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inl member)))
  have avoidHistory : ∀ p ∈ systemContracts, ∀ root ∈ trace.history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member)))
  have avoidTx : ∀ p ∈ systemContracts, ∀ root ∈ trace.transactions.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member))
  have avoidRequests : ∀ p ∈ systemContracts, ∀ root ∈ trace.requests.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ p.1 :=
    fun p hp root member => avoid p hp root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inr member)
  obtain ⟨hBeacon, installedBeacon⟩ := trace.beacon.systemCodeFacts hfork.rules_stateGas_none
    installed avoidBeacon
  obtain ⟨hHistory, installedHistory⟩ := trace.history.systemCodeFacts
    hfork.rules_stateGas_none installedBeacon avoidHistory
  have installedTx : SystemCodeInstalled trace.transactionBenv.state := by
    intro p hp
    obtain ⟨-, hnd, hne⟩ := systemContracts_facts p hp
    have hcode : ((benv.withState trace.beaconState).withState trace.historyState).state.getCode
        p.1 = p.2 := installedHistory p hp
    have keep := trace.transactions.codeAt_keep hfork (hauth p hp) (avoidTx p hp)
      (by rw [hcode]; exact hne) (by rw [hcode]; exact hnd) (notCreated p hp)
    rw [keep]
    exact hcode
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have installedWithdrawals : SystemCodeInstalled trace.withdrawalState := by
    intro p hp
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact installedTx p hp
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact installedTx p hp
  have hRequests := trace.requests.systemCodeTargets
    (by change CoveredFork trace.transactionBenv.stat.fork; rw [txStat]; exact hfork)
    installedWithdrawals avoidRequests
  intro root member
  simp only [StagedBodyTrace.systemRawFrames, List.mem_append] at member
  simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false]
  rcases member with (member | member) | member
  · exact Or.inl (hBeacon root member)
  · exact Or.inr (Or.inl (hHistory root member))
  · have target := hRequests root member
    simpa only [systemTargets, List.mem_cons, List.not_mem_nil, or_false] using target

/-- No frame of this block without a code address (at any depth) targets a system
contract that the block's selected fork installs: vacuous before Cancun, beacon roots on
Cancun, all four from Prague. Contracts created inside a span before their activation
are therefore not excluded. -/
def ConfiguredBlockTraceIn.InstalledNoFrame
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) : Prop :=
  ∀ q ∈ installedAt trace.fork, ∀ root ∈ trace.rawFrames,
    root.sevm.codeAddress = none → root.sevm.currentTarget ≠ q.1

/-- `InstalledNoFrame` at every block of a retained `In`-history. -/
def ConfiguredHistoryTraceIn.InstalledNoFrame {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.InstalledNoFrame ∧ block.InstalledNoFrame

/-- No authorization of this block recovers to `a`, required only from Prague on
(EIP-7702 delegation is disabled on every earlier fork). -/
def ConfiguredBlockTraceIn.PragueNoAuthorityAt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} (a : Adr)
    (trace : ConfiguredBlockTraceIn F cfg pre post) : Prop :=
  ¬ PrePrague trace.fork → ∀ q ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ q.2.auths,
    ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a

/-- `PragueNoAuthorityAt` at every block of a retained `In`-history. -/
def ConfiguredHistoryTraceIn.PragueNoAuthorityAt {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} (a : Adr) :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.PragueNoAuthorityAt a ∧ block.PragueNoAuthorityAt a

/-- System confinement at a real selected block: no installed code is needed before Cancun,
only beacon-roots code on Cancun, and the canonical modern table from Prague. Authority and
frame exclusions are needed only from Prague, and only for the installed contracts. -/
theorem ConfiguredBlockTraceIn.systemFrames_target_of_installedAt
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) (hHist : HistFork trace.fork)
    (installed : trace.SystemCodeAtOpening)
    (hauth : ∀ p ∈ systemContracts, trace.PragueNoAuthorityAt p.1)
    (avoid : trace.InstalledNoFrame) :
    ∀ root ∈ trace.systemRawFrames,
      root.sevm.currentTarget ∈ (installedAt trace.fork).map Prod.fst := by
  rcases hHist.preCancun_cancun_pragueOnwards with hpre | hcan | hprague
  · have hb := BeaconStageTrace.rawFrames_of_disabled trace.bodyTrace.beacon
      (hHist.sys_beaconRoots_false_of_preCancun hpre)
    have hh := HistoryStageTrace.rawFrames_of_disabled trace.bodyTrace.history
      (hHist.sys_historyStorage_false_of_prePrague hpre.toPrePrague)
    have hr := RequestStageTrace.rawFrames_of_disabled trace.bodyTrace.requests
      (hHist.header_requestsHash_false_of_prePrague hpre.toPrePrague)
    intro root member
    simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames,
      hb, hh, hr, List.append_nil, List.not_mem_nil] at member
  · have hHistC : HistFork .cancun := by decide
    have hpreP : PrePrague .cancun := by decide
    have hh := HistoryStageTrace.rawFrames_of_disabled trace.bodyTrace.history
      (by change trace.fork.ruleSet.sys.historyStorage = false; rw [hcan]
          exact hHistC.sys_historyStorage_false_of_prePrague hpreP)
    have hr := RequestStageTrace.rawFrames_of_disabled trace.bodyTrace.requests
      (by change trace.fork.ruleSet.header.requestsHash = false; rw [hcan]
          exact hHistC.header_requestsHash_false_of_prePrague hpreP)
    have hcode : pre.state.getCode beaconRootsAddress = beaconRootsCode := by
      exact installed (beaconRootsAddress, beaconRootsCode) (by
        rw [hcan]
        exact List.mem_cons_self)
    have htarget := trace.bodyTrace.beacon.target_of_beaconCode hcode
    intro root member
    simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames,
      hh, hr, List.append_nil] at member
    rw [hcan]
    change root.sevm.currentTarget ∈ [beaconRootsAddress]
    exact List.mem_singleton.mpr (htarget root member)
  · have covered := hHist.pragueOnwards_covered hprague
    have htable : installedAt trace.fork = systemContracts :=
      covered.cases (motive := fun f => installedAt f = systemContracts) rfl rfl rfl rfl
    have full : SystemCodeInstalled pre.state := by
      intro p hp
      exact installed p (htable.symm ▸ hp)
    have notPre : ¬ PrePrague trace.fork := by
      revert hprague
      generalize trace.fork = f
      cases f <;> decide
    have targets := trace.bodyTrace.systemFrames_of_installedIn covered full
      (fun p _ => AdrSet.not_mem_empty) (fun p hp => hauth p hp notPre)
      (fun p hp => avoid p (htable.symm ▸ hp))
    intro root member
    rw [htable]
    change root.sevm.currentTarget ∈ systemTargets
    exact targets root member

/-- Every actual block frame originates in an optional system stage or a transaction. -/
theorem ConfiguredBlockTraceIn.rawFrames_system_or_tx
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) (root : Exec.Deriv)
    (member : root ∈ trace.rawFrames) :
    root ∈ trace.systemRawFrames ∨ root ∈ trace.bodyTrace.transactions.rawFrames := by
  simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, List.mem_append] at member
  simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames, List.mem_append]
  rcases member with ((member | member) | member) | member
  · exact Or.inl (Or.inl (Or.inl member))
  · exact Or.inl (Or.inl (Or.inr member))
  · exact Or.inr member
  · exact Or.inl (Or.inr member)

end ExecutionTrace

end Blanc

