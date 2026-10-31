import Blanc.ExecutionHistory
import Blanc.ExecutionCodeAt
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionMessageEffects
import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionHistoryInForkFacts
import Blanc.ExecutionHistoryInWarmth
import Blanc.HistoricalFork

/-!
# Empty code at one address along selected-domain (`In`) histories

`In` forms of `ConfiguredHistoryTrace.codeAt_empty` and
`ConfiguredHistoryTrace.NoAuthorityAt`
(`Blanc/ExecutionTraceCodeAt.lean`): a retained `In`-history that starts
with empty code at `a` ends with empty code at `a`, and so does every
transaction frame it enters. The interpreter-level step case is
`ExecutionTrace.Exec.codeAt_avoid_noStateGas` (`Blanc/ExecutionCodeAt.lean`),
of which `Exec.codeAt_avoid` is the covered corollary.

EIP-7702 authority is cased per fork, as ordered: the message-level fact
takes `rules.delegationEnabled = false` as a disjunct beside the usual
no-authority premise, so before Prague — where delegation is disabled —
the fact holds with no authority premise. At history level the disjunct
is supplied from an explicit per-fork disabled-delegation hypothesis
(discharged on `HistFork` by decision) on pre-Prague blocks and from an
`In` no-authority premise on later ones; fully pre-Prague histories get a
corollary with no authority premise at all.

Contract-neutral: no contract name in any statement.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

/-- A system message keeps empty code at `a`, and so does every frame it
enters: its authorization list is empty. -/
theorem SystemMessageTrace.codeAt_empty_noStateGas
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a := by
  have hmsgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    unfold systemTransactionMessage processSystemTransactionMsg Benv.beginTransaction
    exact hsg
  have hca : (systemTransactionMessage benv target data).target.isNone = true →
      (systemTransactionMessage benv target data).codeAddress = none := by
    intro h
    simp only [systemTransactionMessage, processSystemTransactionMsg, Option.isNone_some,
      Bool.false_eq_true] at h
  have hauth : ∀ auth ∈ (systemTransactionMessage benv target data).tenv.stat.auths,
      ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a := by
    intro auth hauth
    simp only [systemTransactionMessage, processSystemTransactionMsg, processSystemTransactionTenv,
      Std.TreeMap.empty_eq_emptyc, List.not_mem_nil] at hauth
  have hdis : (systemTransactionMessage benv target data).benv.stat.rules.delegationEnabled =
      false ∨ ∀ auth ∈ (systemTransactionMessage benv target data).tenv.stat.auths,
        ∀ authority, recoverAuthority auth = .ok authority → authority ≠ a :=
    Or.inr hauth
  exact trace.message.codeAt_noStateGas hmsgSg hca hdis avoid

/-- A beacon stage that starts with empty code at `a` ends with it, and so
does every frame it enters. -/
theorem BeaconStageTrace.codeAt_empty_noStateGas
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hempty : benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = ByteArray.empty ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a := by
  cases trace with
  | skipped => exact ⟨hempty, fun root member => by simp only [rawFrames,
    List.not_mem_nil] at member⟩
  | called _ _ message _ _ =>
      obtain ⟨hpost, hroots⟩ := message.codeAt_empty_noStateGas hsg avoid
      exact ⟨hpost.trans hempty, hroots⟩

/-- A history-storage stage that starts with empty code at `a` ends with
it, and so does every frame it enters. -/
theorem HistoryStageTrace.codeAt_empty_noStateGas
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hempty : benv.state.getCode a = ByteArray.empty)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = ByteArray.empty ∧
      ∀ root ∈ trace.rawFrames, root.devm.getCode a = benv.state.getCode a := by
  cases trace with
  | skipped => exact ⟨hempty, fun root member => by simp only [rawFrames,
    List.not_mem_nil] at member⟩
  | called _ _ _ _ message _ _ =>
      obtain ⟨hpost, hroots⟩ := message.codeAt_empty_noStateGas hsg avoid
      exact ⟨hpost.trans hempty, hroots⟩

/-- A request stage keeps the code at `a`. -/
theorem RequestStageTrace.codeAt_noStateGas
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a) :
    state.getCode a = benv.state.getCode a := by
  cases trace with
  | skipped => rfl
  | called _ requests _ =>
      obtain ⟨hw, -⟩ := requests.withdrawal.codeAt_empty_noStateGas hsg (fun root member =>
        avoid root (by
          simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append]
          exact Or.inl member))
      obtain ⟨hc, -⟩ := requests.consolidation.codeAt_empty_noStateGas
        (benv := benv.withState requests.withdrawalState) hsg (fun root member =>
          avoid root (by
            simp only [RequestStageTrace.rawFrames, RequestsTrace.rawFrames, List.mem_append]
            exact Or.inr member))
      rw [requests.state_eq_consolidationState]
      exact hc.trans hw

/-- **A staged body that starts with empty code at `a` ends with it, and so
does every transaction frame it enters**, when no frame it enters targets
`a`. Either delegation is disabled or no authorization of its transactions
recovers to `a`. -/
theorem StagedBodyTrace.codeAt_empty_noStateGas
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none) {a : Adr}
    (hauth : benv.stat.rules.delegationEnabled = false ∨
      ∀ p ∈ trace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : benv.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.transactions.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      state.getCode a = ByteArray.empty := by
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
  obtain ⟨hbeacon, -⟩ := trace.beacon.codeAt_empty_noStateGas hsg hempty avoidBeacon
  obtain ⟨hhistory, -⟩ := trace.history.codeAt_empty_noStateGas
    (benv := benv.withState trace.beaconState) hsg hbeacon avoidHistory
  have hstart : ((benv.withState trace.beaconState).withState trace.historyState).state.getCode a =
      ByteArray.empty := by
    simpa only [Benv.withState] using hhistory
  obtain ⟨hroots, hfinalTx⟩ := trace.transactions.codeAt_empty_noStateGas
    (benv := (benv.withState trace.beaconState).withState trace.historyState)
    hsg hauth avoidTx hstart
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have hwithdrawal : trace.withdrawalState.getCode a = ByteArray.empty := by
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
  refine ⟨hroots, ?_⟩
  have hreqWithdraw : trace.requestState.getCode a = ByteArray.empty :=
    hrequest.trans hwithdrawal
  rw [trace.finalState_eq, trace.rewardState_eq]
  split
  · exact hreqWithdraw
  · rw [payRewards_getCode]
    exact hreqWithdraw

/-- No authorization of any transaction of a retained `In`-history recovers
to `a`. -/
def ConfiguredHistoryTraceIn.NoAuthorityAt {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} (a : Adr) :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block =>
      prior.NoAuthorityAt a ∧
        ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
          recoverAuthority auth = .ok authority → authority ≠ a

/-- Every block of a retained `In`-history selects a pre-Prague fork. -/
def ConfiguredHistoryTraceIn.AllPrePrague {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.AllPrePrague ∧ PrePrague block.fork

/-- **A retained `In`-block that starts with empty code at `a` ends with
it**, and so does every transaction frame it enters. Delegation is either
disabled at the block's fork (the pre-Prague arm, needing no authority
premise) or no authorization of its transactions recovers to `a`. -/
theorem ConfiguredBlockTraceIn.codeAt_empty_noStateGas
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) {a : Adr}
    (hdis : trace.fork.ruleSet.delegationEnabled = false ∨
      ∀ p ∈ trace.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
        recoverAuthority auth = .ok authority → authority ≠ a)
    (avoid : ∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : pre.state.getCode a = ByteArray.empty) :
    (∀ root ∈ trace.bodyTrace.transactions.rawFrames, root.devm.getCode a = ByteArray.empty) ∧
      post.state.getCode a = ByteArray.empty := by
  obtain ⟨hroots, hstate⟩ := trace.bodyTrace.codeAt_empty_noStateGas
    (capabilities.stateGas_none trace.forkIn) hdis avoid hempty
  refine ⟨hroots, ?_⟩
  rw [trace.postEq]
  exact hstate

/-- **A retained `In`-history that starts with empty code at `a` ends with
empty code at `a`, and so does every transaction frame it enters**, when no
frame it enters targets `a`. Per-block delegation is either disabled on a
pre-Prague fork (from the explicit per-fork hypothesis, needing no
authority premise there) or covered by the history's no-authority premise. -/
theorem ConfiguredHistoryTraceIn.codeAt_empty_noStateGas
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (hdeleg : ∀ f, F f → PrePrague f → (Fork.ruleSet f).delegationEnabled = false)
    (hauth : history.NoAuthorityAt a)
    (avoid : ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : checkpoint.state.getCode a = ByteArray.empty) :
    (∀ root ∈ history.txRawFrames, root.devm.getCode a = ByteArray.empty) ∧
      future.state.getCode a = ByteArray.empty := by
  induction history with
  | refl => exact ⟨fun root member => by simp only [txRawFrames, List.not_mem_nil] at member,
      hempty⟩
  | step prior block ih =>
      obtain ⟨hroots, hstate⟩ := ih hauth.1
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inl member))
      have hdis : block.fork.ruleSet.delegationEnabled = false ∨
          ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a := by
        by_cases hpre : PrePrague block.fork
        · exact Or.inl (hdeleg _ block.forkIn hpre)
        · exact Or.inr hauth.2
      obtain ⟨hroots', hfinal⟩ := block.codeAt_empty_noStateGas capabilities hdis
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ConfiguredHistoryTraceIn.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

/-- **A fully pre-Prague historical `In`-history keeps empty code at `a`
with no authority premise**: delegation is disabled on every block, so no
authorization can install a delegation designator anywhere. -/
theorem ConfiguredHistoryTraceIn.codeAt_empty_prePrague
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (capabilities : BodyStageCapabilities HistFork)
    (hpre : history.AllPrePrague)
    (avoid : ∀ root ∈ history.rawFrames, root.sevm.codeAddress = none →
      root.sevm.currentTarget ≠ a)
    (hempty : checkpoint.state.getCode a = ByteArray.empty) :
    (∀ root ∈ history.txRawFrames, root.devm.getCode a = ByteArray.empty) ∧
      future.state.getCode a = ByteArray.empty := by
  induction history with
  | refl => exact ⟨fun root member => by simp only [txRawFrames, List.not_mem_nil] at member,
      hempty⟩
  | step prior block ih =>
      obtain ⟨hroots, hstate⟩ := ih hpre.1
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inl member))
      have hdis : block.fork.ruleSet.delegationEnabled = false ∨
          ∀ p ∈ block.bodyTrace.decodedTxs.putIndex, ∀ auth ∈ p.2.auths, ∀ authority,
            recoverAuthority auth = .ok authority → authority ≠ a :=
        Or.inl (block.forkIn.delegationDisabled_of_prePrague hpre.2)
      obtain ⟨hroots', hfinal⟩ := block.codeAt_empty_noStateGas capabilities hdis
        (fun root member => avoid root (by
          simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append]
          exact Or.inr member)) hstate
      refine ⟨fun root member => ?_, hfinal⟩
      simp only [ConfiguredHistoryTraceIn.txRawFrames, List.mem_append] at member
      rcases member with member | member
      · exact hroots root member
      · exact hroots' root member

end ExecutionTrace

end Blanc
