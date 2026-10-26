import Blanc.ExecutionTraceCallerExclusion
import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionHistoryInSystemFrames
import Blanc.ExecutionTraceSystemCode

/-!
Caller exclusion through a Cancun deployment-block suffix and later Cancun blocks.
Checked senders, empty system-address code and CREATE avoidance are environmental
conditions. Canonical beacon code at later block openings is a separate residual
installation condition; EIP-7002 deployment does not establish it.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Withdrawals, request calls and reward credits keep one account's code after
the transaction fold, when the actual request calls avoid CREATE at that account. -/
theorem StagedBodyTrace.afterTransactions_codeAt_noStateGas
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : trace.transactionBenv.stat.rules.stateGas = none) {a : Adr}
    (avoid : ∀ root ∈ trace.requests.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = trace.transactionBenv.state.getCode a := by
  have withdrawal : trace.withdrawalState.getCode a = trace.transactionBenv.state.getCode a := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false => rw [(trace.withdrawals_disabled enabled).1]
    | true =>
      simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
      rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
  have requests := trace.requests.codeAt_noStateGas
    (benv := trace.transactionBenv.withState trace.withdrawalState) hsg avoid
  apply Eq.trans (congrArg (fun world : State => world.getCode a) trace.finalState_eq)
  rw [trace.rewardState_eq]
  split
  · exact requests.trans withdrawal
  · rw [payRewards_getCode]
    exact requests.trans withdrawal

/-- A Cancun block's post-transaction request stage is actually disabled. -/
theorem ConfiguredBlockTraceIn.requests_rawFrames_empty_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (fork : block.fork = .cancun) :
    block.bodyTrace.requests.rawFrames = [] := by
  apply RequestStageTrace.rawFrames_of_disabled
  change block.fork.ruleSet.header.requestsHash = false
  rw [fork]
  rfl

/-- The actual deployment-block suffix excludes the checked senders and keeps
empty code. Cancun delegation and request stages are disabled by the selected fork. -/
theorem ConfiguredBlockTraceIn.tail_callers_and_code_empty_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} {a : Adr}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (fork : block.fork = .cancun)
    (senders : cut.after.NoSenderAt a)
    (avoid : ∀ root ∈ (MidHistoryTraceIn.tail block cut).rawFrames,
      root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a)
    (empty : cut.afterBenv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ (MidHistoryTraceIn.tail block cut).rawFrames, root.sevm.caller ≠ a) ∧
      post.state.getCode a = ByteArray.empty := by
  have requests := block.requests_rawFrames_empty_cancun fork
  simp only [MidHistoryTraceIn.rawFrames, requests, List.append_nil] at avoid ⊢
  have cutSg : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]
    change block.fork.ruleSet.stateGas = none
    rw [fork]
    rfl
  have cutDelegation : cut.afterBenv.stat.rules.delegationEnabled = false := by
    rw [block.txSplit_stat cut]
    change block.fork.ruleSet.delegationEnabled = false
    rw [fork]
    rfl
  obtain ⟨roots, finalTx⟩ := cut.after.codeAt_empty_noStateGas cutSg
    (Or.inl cutDelegation) avoid empty
  refine ⟨cut.after.caller_excluded_noStateGas cutSg senders roots avoid, ?_⟩
  have afterTx := block.bodyTrace.afterTransactions_codeAt_noStateGas
    (a := a) (by
      rw [block.bodyTrace.transactions.stat_eq]
      change block.fork.ruleSet.stateGas = none
      rw [fork]
      rfl) (by intro root member; rw [requests] at member; cases member)
  rw [block.postEq]
  exact afterTx.trans finalTx

/-- The actual code at the beacon-stage target confines its raw frame roots. -/
theorem BeaconStageTrace.rawFrames_target_of_code
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (reach : SpawnFreeReach (benv.state.getCode beaconRootsAddress))
    (ordinary : ¬ isValidDelegation (benv.state.getCode beaconRootsAddress)) :
    ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = beaconRootsAddress := by
  cases trace with
  | skipped => intro root member; cases member
  | called _ _ message _ _ => exact message.rawFrames_target_of_code reach ordinary

/-- In a whole Cancun block, target-restricted caller exclusion combines the
checked transactions with the sole active protocol target, beacon roots. -/
theorem ConfiguredBlockTraceIn.callers_and_code_empty_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} {a ca : Adr}
    (block : ConfiguredBlockTraceIn F cfg pre post) (fork : block.fork = .cancun)
    (senders : block.bodyTrace.transactions.NoSenderAt a)
    (avoid : ∀ root ∈ block.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : pre.state.getCode a = ByteArray.empty)
    (beacon : pre.state.getCode beaconRootsAddress = beaconRootsCode)
    (target : ca ≠ beaconRootsAddress) :
    (∀ root ∈ block.rawFrames, root.sevm.currentTarget = ca → root.sevm.caller ≠ a) ∧
      post.state.getCode a = ByteArray.empty := by
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none := by
    change block.fork.ruleSet.stateGas = none
    rw [fork]
    rfl
  have delegation : (initBenv block.fork pre block.block.header).stat.rules.delegationEnabled =
      false := by
    change block.fork.ruleSet.delegationEnabled = false
    rw [fork]
    rfl
  obtain ⟨roots, final⟩ := block.bodyTrace.codeAt_empty_noStateGas hsg (Or.inl delegation)
    avoid empty
  have callers := block.bodyTrace.transactions.caller_excluded_noStateGas hsg senders roots
    (fun root member => avoid root (by
      simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, List.mem_append]
      exact Or.inl (Or.inr member)))
  have beaconTargets := block.bodyTrace.beacon.rawFrames_target_of_code
    (by change SpawnFreeReach (pre.state.getCode beaconRootsAddress)
        rw [beacon]; exact beaconRootsCode_spawnFreeReach)
    (by change ¬ isValidDelegation (pre.state.getCode beaconRootsAddress)
        rw [beacon]
        exact (systemContracts_facts _ (List.mem_cons_self)).2.1)
  have historyEmpty : block.bodyTrace.history.rawFrames = [] := by
    apply HistoryStageTrace.rawFrames_of_disabled
    change block.fork.ruleSet.sys.historyStorage = false
    rw [fork]
    rfl
  have requestsEmpty := block.requests_rawFrames_empty_cancun fork
  refine ⟨?_, ?_⟩
  · intro root member currentTarget
    simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, historyEmpty,
      requestsEmpty, List.append_nil, List.mem_append] at member
    rcases member with member | member
    · exact False.elim (target (currentTarget.symm.trans (beaconTargets root member)))
    · exact callers root member
  · rw [block.postEq]
    exact final

/-- The checked senders of the remaining deployment-block transactions and later blocks. -/
def MidHistoryTraceIn.NoSenderAt {F : Fork → Prop} {cfg : ChainConfig} (a : Adr) :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail _ cut => cut.after.NoSenderAt a
  | _, _, .step prior block => prior.NoSenderAt a ∧ block.bodyTrace.transactions.NoSenderAt a

/-- Every retained block, including the block containing the cut, actually selects Cancun. -/
def MidHistoryTraceIn.AllCancun {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail block _ => block.fork = .cancun
  | _, _, .step prior block => prior.AllCancun ∧ block.fork = .cancun

/-- A separate environmental installation fact at a whole block's actual opening boundary. -/
def ConfiguredBlockTraceIn.BeaconCodeInstalled
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (_block : ConfiguredBlockTraceIn F cfg pre post) : Prop :=
  pre.state.getCode beaconRootsAddress = beaconRootsCode

/-- Only later whole-block openings require beacon installation: the initial
mid-block tail has no remaining beacon call. This is an explicit residual condition. -/
def MidHistoryTraceIn.BeaconCodeInstalled {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail _ _ => True
  | _, _, .step prior block => prior.BeaconCodeInstalled ∧ block.BeaconCodeInstalled

/-- A Cancun mid history derives target-restricted caller exclusion from checked
senders and actual code/CREATE conditions. Beacon protocol frames cannot reach a
different target; no authority premise or caller conclusion is assumed at child roots. -/
theorem MidHistoryTraceIn.callers_and_code_empty_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain} {a ca : Adr}
    (trace : MidHistoryTraceIn F cfg start future) (forks : trace.AllCancun)
    (senders : trace.NoSenderAt a) (beacon : trace.BeaconCodeInstalled)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : start.state.getCode a = ByteArray.empty) (target : ca ≠ beaconRootsAddress) :
    (∀ root ∈ trace.rawFrames, root.sevm.currentTarget = ca → root.sevm.caller ≠ a) ∧
      future.state.getCode a = ByteArray.empty := by
  induction trace with
  | tail block cut =>
    obtain ⟨callers, final⟩ := block.tail_callers_and_code_empty_cancun cut forks senders avoid empty
    exact ⟨fun root member _ => callers root member, final⟩
  | step prior block ih =>
    obtain ⟨priorCallers, middleEmpty⟩ := ih forks.1 senders.1 beacon.1
      (fun root member => avoid root (List.mem_append_left _ member)) empty
    obtain ⟨blockCallers, final⟩ := block.callers_and_code_empty_cancun forks.2 senders.2
      (fun root member => avoid root (List.mem_append_right _ member)) middleEmpty beacon.2 target
    refine ⟨?_, final⟩
    intro root member currentTarget
    simp only [MidHistoryTraceIn.rawFrames, List.mem_append] at member
    rcases member with member | member
    · exact priorCallers root member currentTarget
    · exact blockCallers root member currentTarget

/-- The derived caller law supplies the trace-local admission consumed by a
contract's historical invariant theorem, including the deployment-block suffix. -/
theorem MidHistoryTraceIn.frameAdmitted_caller_ne_cancun
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain} {a ca : Adr}
    (trace : MidHistoryTraceIn F cfg start future) (forks : trace.AllCancun)
    (senders : trace.NoSenderAt a) (beacon : trace.BeaconCodeInstalled)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (empty : start.state.getCode a = ByteArray.empty) (target : ca ≠ beaconRootsAddress) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.caller ≠ a) :=
  (trace.frameAdmitted_iff_rawFrames ca _).2
    (trace.callers_and_code_empty_cancun forks senders beacon avoid empty target).1

end Blanc.ExecutionTrace
