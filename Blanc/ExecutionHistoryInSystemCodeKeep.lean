import Blanc.ExecutionHistory
import Blanc.ExecutionHistoryInCodeAt
import Blanc.ExecutionHistoryInNoDel
import Blanc.ExecutionHistoryInSystemFrames
import Blanc.ExecutionHistoryInForkFacts
import Blanc.SystemContracts
import Blanc.HistoricalFork

/-!
# Installed system code along selected-domain (`In`) histories

`In` forms of installed-code preservation
(`Blanc/ExecutionTraceSystemCode.lean`): a staged body keeps the code at an
address whose canonical code is nonempty and not a delegation designator
(`StagedBodyTrace.codeAt_keep_noStateGas`, via the neutral transaction-list
keep); a retained `In`-block on a Cancun-onwards fork keeps every address of
its fork's installed set (`ConfiguredBlockTraceIn.systemFrames_installed_keep`,
era-split by `HistFork.preCancun_cancunOnwards`: vacuous before Cancun, keep
from Cancun on); and a retained `In`-history whose every block is
Cancun-onwards threads one canonical code end to end, in particular the
beacon-roots code.

Per-address character facts (nonempty, not-delegating) come from the
canonical contract table (`systemContracts_facts`) through installed-set
membership; the block-open created-account fact is discharged afresh per
block (`AdrSet.not_mem_empty`); delegation is cased per fork exactly as in
the empty-code chain (disabled on pre-Prague forks, no-authority premise
later).

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-- The beacon-roots contract heads the canonical table. -/
theorem beaconRoots_mem_systemContracts :
    (beaconRootsAddress, beaconRootsCode) ∈ systemContracts := by
  unfold systemContracts
  rw [List.mem_cons]
  exact Or.inl rfl

/-- Every installed address of a historical fork holds a canonical system
contract code. -/
theorem mem_systemContracts_of_mem_installedAt {f : Fork} {p : Adr × ByteArray}
    (hHist : HistFork f) (hmem : p ∈ installedAt f) :
    p ∈ systemContracts := by
  rcases hHist.preCancun_cancun_pragueOnwards with hpre | rfl | hprague
  · rw [HistFork.installedAt_empty_of_preCancun hHist hpre] at hmem
    simp only [List.not_mem_nil] at hmem
  · rw [HistFork.installedAt_beacon_of_cancun hHist rfl] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    subst hmem
    exact beaconRoots_mem_systemContracts
  · have heq : installedAt f = systemContracts := by
      cases f with
      | prague => rfl
      | osaka => rfl
      | bpo1 => rfl
      | bpo2 => rfl
      | _ => exact absurd hprague (by decide)
    rw [heq] at hmem
    exact hmem

/-- A beacon stage keeps the canonical code at `a`. Neutral form, state
conclusion only. -/
theorem BeaconStageTrace.codeAt_keep_noStateGas
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr} {c : ByteArray}
    (hkeep : benv.state.getCode a = c)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = c := by
  cases trace with
  | skipped => exact hkeep
  | called _ _ message _ _ =>
      obtain ⟨hpost, -⟩ := message.codeAt_empty_noStateGas hsg avoid
      exact hpost.trans hkeep

/-- A history-storage stage keeps the canonical code at `a`. Neutral form,
state conclusion only. -/
theorem HistoryStageTrace.codeAt_keep_noStateGas
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr} {c : ByteArray}
    (hkeep : benv.state.getCode a = c)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = c := by
  cases trace with
  | skipped => exact hkeep
  | called _ _ _ _ message _ _ =>
      obtain ⟨hpost, -⟩ := message.codeAt_empty_noStateGas hsg avoid
      exact hpost.trans hkeep

/-- **A staged body keeps the canonical code at `a`**, when no frame it
enters targets `a`, `a` was not created in the block, and either delegation
is disabled or none of its authorizations recovers to `a`. The canonical
code itself is nonempty and not a delegation designator. -/
theorem StagedBodyTrace.codeAt_keep_noStateGas
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (hflag : benv.stat.rules.settle.selfdestructOnlyCreated = true)
    (hrefund : benv.stat.fork.ruleSet.settle.refundQuotient = 5)
    (hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false)
    {a : Adr} {c : ByteArray}
    (hdis : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hkeep : benv.state.getCode a = c)
    (hc_ne : c.toList ≠ [])
    (hc_nd : ¬ isValidDelegation c)
    (notCreated : a ∉ benv.createdAccounts) :
    state.getCode a = c := by
  have avoidBeacon : ∀ root ∈ trace.beacon.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inl member)))
  have avoidHistory : ∀ root ∈ trace.history.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inl (Or.inr member)))
  have avoidTx : ∀ root ∈ trace.transactions.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member))
  have avoidRequests : ∀ root ∈ trace.requests.rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a :=
    fun root member => avoid root (by
      simp only [StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inr member)
  have hbeacon : trace.beaconState.getCode a = c :=
    trace.beacon.codeAt_keep_noStateGas hsg hkeep avoidBeacon
  have hhistory : trace.historyState.getCode a = c :=
    trace.history.codeAt_keep_noStateGas (benv := benv.withState trace.beaconState)
      hsg hbeacon avoidHistory
  have hstart : ((benv.withState trace.beaconState).withState
      trace.historyState).state.getCode a = c := by
    simpa only [Benv.withState] using hhistory
  have hne : (((benv.withState trace.beaconState).withState
      trace.historyState).state.getCode a).toList ≠ [] := by
    rw [hstart]
    exact hc_ne
  have hnd : ¬ isValidDelegation (((benv.withState trace.beaconState).withState
      trace.historyState).state.getCode a) := by
    rw [hstart]
    exact hc_nd
  have hfinalTx : trace.transactionBenv.state.getCode a = c :=
    (trace.transactions.codeAt_keep_noStateGas (benv :=
        (benv.withState trace.beaconState).withState trace.historyState)
      hsg hflag hrefund hsweep hdis avoidTx hne hnd notCreated).trans hstart
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have hwithdrawal : trace.withdrawalState.getCode a = c := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact hfinalTx
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact hfinalTx
  have hrequest := trace.requests.codeAt_noStateGas
    (benv := trace.transactionBenv.withState trace.withdrawalState)
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    avoidRequests
  have hreqState : trace.requestState.getCode a = c :=
    hrequest.trans hwithdrawal
  rw [trace.finalState_eq, trace.rewardState_eq]
  split
  · exact hreqState
  · rw [payRewards_getCode]
    exact hreqState

/-- **A retained `In`-block on a Cancun-onwards fork keeps the canonical
code at `a`.** The schedule facts come from the fork by decision; the
block-open created-account fact holds afresh. -/
theorem ConfiguredBlockTraceIn.codeAt_keep_of_cancunOnwards
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (hHist : HistFork trace.fork) (hC : CancunOnwards trace.fork)
    {a : Adr} {c : ByteArray}
    (hdis : trace.fork.ruleSet.delegationEnabled = false ∨
      ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
        ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hkeep : pre.state.getCode a = c)
    (hc_ne : c.toList ≠ [])
    (hc_nd : ¬ isValidDelegation c) :
    post.state.getCode a = c := by
  have hstate := trace.bodyTrace.codeAt_keep_noStateGas
    (capabilities.stateGas_none trace.forkIn)
    (HistFork.selfdestructOnlyCreated_of_cancunOnwards hHist hC)
    (HistFork.refundQuotient_five_of_cancunOnwards hHist hC)
    (HistFork.touchedSweep_false_of_cancunOnwards hHist hC)
    hdis avoid hkeep hc_ne hc_nd AdrSet.not_mem_empty
  rw [trace.postEq]
  exact hstate

/-- **A retained `In`-block preserves its fork's installed set**,
era-split: vacuous before Cancun (nothing is installed), keep from Cancun
on (every installed address holds canonical, hence nonempty and
non-delegating, code). -/
theorem ConfiguredBlockTraceIn.systemFrames_installed_keep
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (hHist : HistFork trace.fork)
    (hdeleg : ∀ f, F f → PrePrague f → (Fork.ruleSet f).delegationEnabled = false)
    (hauth : ∀ a, ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ a, ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hpre : SystemCodeInstalledAt trace.fork pre.state) :
    SystemCodeInstalledAt trace.fork post.state := by
  rcases hHist.preCancun_cancunOnwards with hpreC | hC
  · exact SystemCodeInstalledAt.of_preCancun post.state hHist hpreC
  · intro q hq
    have hqmem := mem_systemContracts_of_mem_installedAt hHist hq
    have hqfacts := systemContracts_facts q hqmem
    have hdis : trace.fork.ruleSet.delegationEnabled = false ∨
        ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
          ∀ authority, recoverAuthority auth = .ok authority → authority ≠ q.1 := by
      by_cases hpp : PrePrague trace.fork
      · exact Or.inl (hdeleg _ trace.forkIn hpp)
      · exact Or.inr (hauth _)
    exact trace.codeAt_keep_of_cancunOnwards capabilities hHist hC hdis
      (avoid _) (hpre q hq) hqfacts.2.2 hqfacts.2.1

/-- Every block of a retained `In`-history selects a Cancun-onwards fork. -/
def ConfiguredHistoryTraceIn.AllCancunOnwards {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.AllCancunOnwards ∧ CancunOnwards block.fork

/-- **A retained `In`-history whose every block is Cancun-onwards threads
one canonical code end to end**, when no frame it enters targets its address
and either delegation is disabled per pre-Prague block or no authorization
of the history recovers to it. -/
theorem ConfiguredHistoryTraceIn.codeAt_keep_of_cancunOnwards
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (hdeleg : ∀ f, F f → PrePrague f → (Fork.ruleSet f).delegationEnabled = false)
    (hHist : ∀ f, F f → HistFork f)
    (hC : history.AllCancunOnwards)
    (hauth : history.NoAuthorityAt a)
    (avoid : ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hc_ne : c.toList ≠ []) (hc_nd : ¬ isValidDelegation c)
    (hstart : checkpoint.state.getCode a = c) :
    future.state.getCode a = c := by
  induction history with
  | refl => exact hstart
  | step prior block ih =>
      have hstate := ih hC.1 hauth.1
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inl member))
      have hdis : block.fork.ruleSet.delegationEnabled = false ∨
          ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths,
            ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a := by
        by_cases hpre : PrePrague block.fork
        · exact Or.inl (hdeleg _ block.forkIn hpre)
        · exact Or.inr hauth.2
      exact block.codeAt_keep_of_cancunOnwards capabilities (hHist _ block.forkIn)
        hC.2 hdis
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member))
        hstate hc_ne hc_nd

/-- **The beacon-roots code threads end to end along a Cancun-onwards
retained `In`-history**: it is installed on every Cancun-onwards fork, so
its canonical character facts discharge once and for all. -/
theorem ConfiguredHistoryTraceIn.beaconRootsCode_keep_of_cancunOnwards
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (hdeleg : ∀ f, F f → PrePrague f → (Fork.ruleSet f).delegationEnabled = false)
    (hHist : ∀ f, F f → HistFork f)
    (hC : history.AllCancunOnwards)
    (hauth : history.NoAuthorityAt beaconRootsAddress)
    (avoid : ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ beaconRootsAddress)
    (hstart : checkpoint.state.getCode beaconRootsAddress = beaconRootsCode) :
    future.state.getCode beaconRootsAddress = beaconRootsCode := by
  have hmem : (beaconRootsAddress, beaconRootsCode) ∈ systemContracts :=
    beaconRoots_mem_systemContracts
  have hfacts := systemContracts_facts _ hmem
  exact history.codeAt_keep_of_cancunOnwards capabilities hdeleg hHist hC hauth
    avoid hfacts.2.2 hfacts.2.1 hstart

end ExecutionTrace

end Blanc
