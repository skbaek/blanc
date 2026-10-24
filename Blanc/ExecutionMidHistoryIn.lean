import Blanc.ExecutionHistoricalAdmission
import Blanc.ExecutionBodyEffects

/-!
# Selected-domain (`In`) histories that start in the middle of a block

`ApplyTransactionsTrace.TxSplit` cuts a retained transaction fold at one
position `i`: the prefix before it, the actual transaction at `i` as data (its
`TransactionTrace`), and the suffix after it, with raw and settled frame
equations. `splitAt` produces a cut at every in-range position.

`MidHistoryTraceIn` is a selected-domain history whose base is the remainder of
one retained configured block after transaction `i` (suffix transactions,
withdrawals, requests, rewards), followed by whole configured blocks on the
same snoc spine as `ConfiguredHistoryTraceIn`. No `ValidContext` is needed at
the mid-block start. Its raw and settled frames, entry admission and reward
premise mirror the whole-block history's; `append` joins an ordinary
`ConfiguredHistoryTraceIn` after it.

Every block-local side condition at the cut (selected fork, `stateGas = none`,
not-yet-created, withdrawal-inclusive balance bound) is derived from the
retained block (`txSplit_stat`, `txSplit_notCreated`, `txSplit_bound`), so the
only contract premise of the preservation theorems at the start is the
invariant right after transaction `i`.

Contract-neutral: no contract name, no `CoveredFork`, no assumed access mode
or delegation. Premises are the existing `In` ones (`PreservesAdmittedIn F`,
`BodyStageCapabilities F`, `FrameAdmitted`, `RewardCreditsFunded`,
`InstalledCert`), each dischargeable on `HistFork`.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-! ## Transaction-position cut -/

/-- Cut of a retained transaction fold at position `i`: the prefix before it,
the actual transaction at `i` (Type-valued), and the suffix after it. -/
structure ApplyTransactionsTrace.TxSplit
    {txs : List (Nat × Tx)} {startBenv finalBenv : Benv} {startBout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs startBenv startBout finalBenv finalBout) (i : Nat) where
  index : Nat
  tx : Tx
  benv : Benv
  bout : BlockOutput
  txState : State
  txBout : BlockOutput
  at_eq : txs.drop i = (index, tx) :: txs.drop (i + 1)
  before : ApplyTransactionsTrace (txs.take i) startBenv startBout benv bout
  head : TransactionTrace benv bout tx index txState txBout
  after : ApplyTransactionsTrace (txs.drop (i + 1)) (benv.withState txState) txBout
    finalBenv finalBout
  rawFrames_eq : trace.rawFrames = before.rawFrames ++ head.rawFrames ++ after.rawFrames
  settledFrames_eq :
    trace.settledFrames = before.settledFrames ++ head.settledFrames ++ after.settledFrames

/-- The environment right after transaction `i`: the start of the remainder. -/
def ApplyTransactionsTrace.TxSplit.afterBenv
    {txs : List (Nat × Tx)} {startBenv finalBenv : Benv} {startBout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace txs startBenv startBout finalBenv finalBout} {i : Nat}
    (cut : trace.TxSplit i) : Benv :=
  cut.benv.withState cut.txState

/-- Every in-range position has a cut. -/
noncomputable def ApplyTransactionsTrace.splitAt
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) (i : Nat)
    (lt : i < txs.length) : trace.TxSplit i := by
  induction trace generalizing i with
  | nil benv bout => exact absurd lt (Nat.not_lt_zero i)
  | @cons index tx txs benv bout txState txBout finalBenv finalBout head tail ih =>
      cases i with
      | zero =>
          exact ⟨index, tx, benv, bout, txState, txBout, rfl, .nil benv bout, head, tail,
            rfl, rfl⟩
      | succ i =>
          let cut := ih i (Nat.lt_of_succ_lt_succ lt)
          refine ⟨cut.index, cut.tx, cut.benv, cut.bout, cut.txState, cut.txBout, cut.at_eq,
            .cons head cut.before, cut.head, cut.after, ?_, ?_⟩
          · simp only [ApplyTransactionsTrace.rawFrames, List.append_assoc]
            rw [cut.rawFrames_eq]
            simp only [List.append_assoc]
            rfl
          · simp only [ApplyTransactionsTrace.settledFrames, List.append_assoc]
            rw [cut.settledFrames_eq]
            simp only [List.append_assoc]
            rfl

/-- Positions assigned by `putIndex` from offset `k`: an entry found after
dropping `i` carries position `k + i` and the `i`-th element. -/
theorem putIndex_aux_drop_eq_cons {α : Type} :
    ∀ (xs : List α) (k i : Nat) {index : Nat} {x : α} {rest : List (Nat × α)},
      (Jaune.List.putIndex.aux k xs).drop i = (index, x) :: rest →
        index = k + i ∧ xs[i]? = some x
  | [], k, i, index, x, rest, h => by
      simp only [Jaune.List.putIndex.aux, List.drop_nil, reduceCtorEq] at h
  | y :: ys, k, 0, index, x, rest, h => by
      simp only [Jaune.List.putIndex.aux, List.drop_zero, List.cons.injEq,
        Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact ⟨rfl, rfl⟩
  | y :: ys, k, i + 1, index, x, rest, h => by
      simp only [Jaune.List.putIndex.aux, List.drop_succ_cons] at h
      obtain ⟨hindex, hx⟩ := putIndex_aux_drop_eq_cons ys (k + 1) i h
      exact ⟨by omega, by simpa only [List.getElem?_cons_succ] using hx⟩

/-- On a decoded block list the cut's index is its position and its
transaction is the decoded one. -/
theorem ApplyTransactionsTrace.TxSplit.putIndex_eq
    {xs : List Tx} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    {trace : ApplyTransactionsTrace xs.putIndex benv bout finalBenv finalBout} {i : Nat}
    (cut : trace.TxSplit i) : cut.index = i ∧ xs[i]? = some cut.tx := by
  have h := putIndex_aux_drop_eq_cons xs 0 i cut.at_eq
  simpa only [Nat.zero_add] using h

/-! ## Block-local facts at a cut -/

/-- The remainder runs on the block's selected fork. -/
theorem ConfiguredBlockTraceIn.txSplit_stat
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    cut.afterBenv.stat = (initBenv block.fork pre block.block.header).stat :=
  cut.before.stat_eq

/-- No account is in the created set at any transaction boundary of a block. -/
theorem ConfiguredBlockTraceIn.txSplit_notCreated
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) (a : Adr) :
    a ∉ cut.afterBenv.createdAccounts := by
  have eq : cut.afterBenv.createdAccounts =
      (initBenv block.fork pre block.block.header).createdAccounts :=
    cut.before.createdAccounts_eq
  rw [eq]
  exact AdrSet.not_mem_empty

/-- A system message with `stateGas = none` does not raise the balance sum. -/
theorem SystemMessageTrace.sum_le_noStateGas
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  have msgSg : (systemTransactionMessage benv target data).benv.stat.rules.stateGas = none := by
    simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hsg
  simpa only [systemTransactionMessage_benv_state] using
    processMessageCall_sum_le msgSg trace.message.result

/-- An optional beacon stage with `stateGas = none` does not raise the balance sum. -/
theorem BeaconStageTrace.sum_le_noStateGas
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact le_rfl
  | called _ _ message _ _ => exact message.sum_le_noStateGas hsg

/-- An optional history stage with `stateGas = none` does not raise the balance sum. -/
theorem HistoryStageTrace.sum_le_noStateGas
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact le_rfl
  | called _ _ _ _ message _ _ => exact message.sum_le_noStateGas hsg

/-- Withdrawal-inclusive no-wrap bound after transaction `i` (hence `SumNof`). -/
theorem ConfiguredBlockTraceIn.txSplit_bound
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (capabilities : BodyStageCapabilities F) :
    sum cut.afterBenv.state.bal + wdsum block.block.wds < 2 ^ 256 := by
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none block.forkIn
  have beacon := block.bodyTrace.beacon.sum_le_noStateGas hsg
  have history := block.bodyTrace.history.sum_le_noStateGas
    (by simpa only [Benv.withState] using hsg)
  have before := cut.before.sum_le_noStateGas
    (by simpa only [Benv.withState] using hsg)
  have cutSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    simpa only [Benv.withState] using hsg
  have head := processTransaction_sum_le cut.head.result cutSg
  have bound := block.withdrawalsBound
  simp only [Benv.withState] at beacon history before
  change sum cut.txState.bal + wdsum block.block.wds < 2 ^ 256
  change sum pre.state.bal + wdsum block.block.wds < 2 ^ 256 at bound
  change sum block.bodyTrace.beaconState.bal ≤ sum pre.state.bal at beacon
  omega

/-! ## The mid-block history carrier -/

/-- A selected-domain history that starts right after transaction `i` of a
retained block: the remainder of that block (suffix transactions,
withdrawals, requests, rewards) as its base, followed by whole configured
blocks. Same snoc spine as `ConfiguredHistoryTraceIn`, with a different base
constructor. No `ValidContext` is needed at the start. -/
inductive MidHistoryTraceIn (F : Fork → Prop) (cfg : ChainConfig) : Benv → BlockChain → Type
  | tail {boundary completed : BlockChain} {i : Nat}
      (block : ConfiguredBlockTraceIn F cfg boundary completed)
      (cut : block.bodyTrace.transactions.TxSplit i) :
      MidHistoryTraceIn F cfg cut.afterBenv completed
  | step {start : Benv} {current future : BlockChain} :
      MidHistoryTraceIn F cfg start current →
      ConfiguredBlockTraceIn F cfg current future →
      MidHistoryTraceIn F cfg start future

/-- Raw roots: the remainder's suffix transactions and request calls
(withdrawals and rewards are frame-free), then each later block's roots. -/
def MidHistoryTraceIn.rawFrames {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} →
    MidHistoryTraceIn F cfg start future → List Exec.Deriv
  | _, _, .tail block cut => cut.after.rawFrames ++ block.bodyTrace.requests.rawFrames
  | _, _, .step prior block => prior.rawFrames ++ block.rawFrames

/-- Settlement-retained roots in the same order. -/
def MidHistoryTraceIn.settledFrames {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} →
    MidHistoryTraceIn F cfg start future → List Exec.Frame
  | _, _, .tail block cut => cut.after.settledFrames ++ block.bodyTrace.requests.settledFrames
  | _, _, .step prior block => prior.settledFrames ++ block.settledFrames

/-- The mid-history settlement filter never invents a raw invocation root. -/
theorem MidHistoryTraceIn.mem_rawFrames_of_mem_settledFrames
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  induction trace with
  | tail block cut =>
      simp only [MidHistoryTraceIn.settledFrames, List.mem_append] at member
      simp only [MidHistoryTraceIn.rawFrames, List.mem_append]
      rcases member with afterMember | requestMember
      · exact Or.inl (cut.after.mem_rawFrames_of_mem_settledFrames frame afterMember)
      · exact Or.inr
          (block.bodyTrace.requests.mem_rawFrames_of_mem_settledFrames frame requestMember)
  | step prior block ih =>
      simp only [MidHistoryTraceIn.settledFrames, List.mem_append] at member
      simp only [MidHistoryTraceIn.rawFrames, List.mem_append]
      rcases member with priorMember | blockMember
      · exact Or.inl (ih priorMember)
      · exact Or.inr (block.mem_rawFrames_of_mem_settledFrames frame blockMember)

/-- Pointwise entry admission on the remainder and the later blocks. -/
def MidHistoryTraceIn.FrameAdmitted {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} →
    MidHistoryTraceIn F cfg start future → Adr → (Sevm → Devm → Prop) → Prop
  | _, _, .tail block cut, ca, entry =>
      cut.after.FrameAdmitted ca entry ∧ block.bodyTrace.requests.FrameAdmitted ca entry
  | _, _, .step prior block, ca, entry =>
      prior.FrameAdmitted ca entry ∧ block.FrameAdmitted ca entry

/-- Mid-history admission quantifies every raw entry of the trace. -/
theorem MidHistoryTraceIn.frameAdmitted_iff_rawFrames
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) (ca : Adr) (entry : Sevm → Devm → Prop) :
    trace.FrameAdmitted ca entry ↔
      ∀ root ∈ trace.rawFrames, root.sevm.currentTarget = ca → entry root.sevm root.devm := by
  induction trace with
  | tail block cut =>
      simp only [MidHistoryTraceIn.FrameAdmitted, MidHistoryTraceIn.rawFrames,
        cut.after.frameAdmitted_iff_rawFrames ca entry,
        block.bodyTrace.requests.frameAdmitted_iff_rawFrames ca entry,
        List.mem_append, or_imp, forall_and]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.FrameAdmitted, MidHistoryTraceIn.rawFrames, ih,
        block.frameAdmitted_iff_rawFrames ca entry, List.mem_append, or_imp, forall_and]

/-! ## The split lemma, block form -/

/-- Block raw roots = opening calls ++ transactions before `i` ++ transaction
`i` ++ the mid base. -/
theorem ConfiguredBlockTraceIn.rawFrames_txSplit
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    block.rawFrames =
      block.bodyTrace.beacon.rawFrames ++ block.bodyTrace.history.rawFrames ++
        cut.before.rawFrames ++ cut.head.rawFrames ++
        (MidHistoryTraceIn.tail block cut).rawFrames := by
  simp only [ConfiguredBlockTraceIn.rawFrames, StagedBodyTrace.rawFrames, cut.rawFrames_eq,
    MidHistoryTraceIn.rawFrames, List.append_assoc]

/-- Block settled roots split the same way. -/
theorem ConfiguredBlockTraceIn.settledFrames_txSplit
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) :
    block.settledFrames =
      block.bodyTrace.beacon.settledFrames ++ block.bodyTrace.history.settledFrames ++
        cut.before.settledFrames ++ cut.head.settledFrames ++
        (MidHistoryTraceIn.tail block cut).settledFrames := by
  simp only [ConfiguredBlockTraceIn.settledFrames, StagedBodyTrace.settledFrames,
    cut.settledFrames_eq, MidHistoryTraceIn.settledFrames, List.append_assoc]

/-- Whole-block admission restricts to the mid base. -/
theorem ConfiguredBlockTraceIn.FrameAdmitted.tail
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    {block : ConfiguredBlockTraceIn F cfg pre post} {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i) {ca : Adr} {entry : Sevm → Devm → Prop}
    (admitted : block.FrameAdmitted ca entry) :
    (MidHistoryTraceIn.tail block cut).FrameAdmitted ca entry := by
  have whole := (block.frameAdmitted_iff_rawFrames ca entry).1 admitted
  rw [MidHistoryTraceIn.frameAdmitted_iff_rawFrames]
  intro root member
  apply whole root
  rw [block.rawFrames_txSplit cut]
  exact List.mem_append_right _ member

/-- Every raw root of a mid history lies in the raw roots of some retained
configured block, which transports every block-level per-root fact. -/
theorem MidHistoryTraceIn.rawFrames_mem_block
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) :
    ∀ root ∈ trace.rawFrames, ∃ (pre post : BlockChain)
      (block : ConfiguredBlockTraceIn F cfg pre post), root ∈ block.rawFrames := by
  induction trace with
  | tail block cut =>
      intro root member
      refine ⟨_, _, block, ?_⟩
      rw [block.rawFrames_txSplit cut]
      exact List.mem_append_right _ member
  | step prior block ih =>
      intro root member
      simp only [MidHistoryTraceIn.rawFrames, List.mem_append] at member
      rcases member with priorMember | blockMember
      · exact ih root priorMember
      · exact ⟨_, _, block, blockMember⟩

/-! ## Rewards and append -/

/-- The reward-funding premise: the base reuses its block's own premise. -/
def MidHistoryTraceIn.RewardCreditsFunded {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail block _ => block.RewardCreditsFunded
  | _, _, .step prior block => prior.RewardCreditsFunded ∧ block.RewardCreditsFunded

/-- Append a whole-block history after the mid trace, by recursion on the
whole-block history (its `refl` data is dropped). -/
def MidHistoryTraceIn.append {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (history : ConfiguredHistoryTraceIn F cfg current future) :
    MidHistoryTraceIn F cfg start future :=
  match history with
  | .refl _ _ _ => mid
  | .step prior block => .step (mid.append prior) block

/-- Raw roots of an append are in order. -/
theorem MidHistoryTraceIn.append_rawFrames {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (history : ConfiguredHistoryTraceIn F cfg current future) :
    (mid.append history).rawFrames = mid.rawFrames ++ history.rawFrames := by
  induction history with
  | refl =>
      simp only [MidHistoryTraceIn.append, ConfiguredHistoryTraceIn.rawFrames, List.append_nil]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.append, MidHistoryTraceIn.rawFrames,
        ConfiguredHistoryTraceIn.rawFrames, ih, List.append_assoc]

/-- Settlement-retained roots of an append are in order. -/
theorem MidHistoryTraceIn.append_settledFrames {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (history : ConfiguredHistoryTraceIn F cfg current future) :
    (mid.append history).settledFrames = mid.settledFrames ++ history.settledFrames := by
  induction history with
  | refl =>
      simp only [MidHistoryTraceIn.append, ConfiguredHistoryTraceIn.settledFrames,
        List.append_nil]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.append, MidHistoryTraceIn.settledFrames,
        ConfiguredHistoryTraceIn.settledFrames, ih, List.append_assoc]

/-- Entry admission splits across an append. -/
theorem MidHistoryTraceIn.append_frameAdmitted {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (history : ConfiguredHistoryTraceIn F cfg current future) (ca : Adr)
    (entry : Sevm → Devm → Prop) :
    (mid.append history).FrameAdmitted ca entry ↔
      mid.FrameAdmitted ca entry ∧ history.FrameAdmitted ca entry := by
  induction history with
  | refl =>
      simp only [MidHistoryTraceIn.append, ConfiguredHistoryTraceIn.FrameAdmitted, and_true]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.append, MidHistoryTraceIn.FrameAdmitted,
        ConfiguredHistoryTraceIn.FrameAdmitted, ih, and_assoc]

/-- Reward funding splits across an append. -/
theorem MidHistoryTraceIn.append_rewardCreditsFunded {F : Fork → Prop} {cfg : ChainConfig}
    {start : Benv} {current future : BlockChain}
    (mid : MidHistoryTraceIn F cfg start current)
    (history : ConfiguredHistoryTraceIn F cfg current future) :
    (mid.append history).RewardCreditsFunded ↔
      mid.RewardCreditsFunded ∧ history.RewardCreditsFunded := by
  induction history with
  | refl =>
      simp only [MidHistoryTraceIn.append, ConfiguredHistoryTraceIn.RewardCreditsFunded,
        and_true]
  | step prior block ih =>
      simp only [MidHistoryTraceIn.append, MidHistoryTraceIn.RewardCreditsFunded,
        ConfiguredHistoryTraceIn.RewardCreditsFunded, ih, and_assoc]

/-! ## Preservation -/

open ContractSpecSem

/-- The stages after the transaction fold (withdrawals, requests, rewards)
carry the invariant from the fold's end boundary to the body's final state. -/
theorem StagedBodyTrace.afterTransactions_stateInv_admitted_semIn {F : Fork → Prop}
    {C : ByteArray} {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (hF : F benv.stat.fork) (hsg : benv.stat.rules.stateGas = none)
    (admitted : trace.requests.FrameAdmitted ca entry)
    (txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256)
    (rewards : trace.RewardCreditsFunded)
    (txInv : c.BenvInv ca trace.transactionBenv)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca state := by
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have withdrawalInv : c.BenvInv ca (trace.transactionBenv.withState trace.withdrawalState) := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact ⟨txInv.state, by simpa only [Benv.withState] using txInv.ca⟩
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1]
        exact benvInv_processWithdrawalsState_sem txInv txBound
  have requests := trace.requests.stateInv_and_sum_le_admitted_semIn preserves
    (by change F trace.transactionBenv.stat.fork; rw [txStat]; exact hF)
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    admitted withdrawalInv K image
  rw [trace.finalState_eq]
  have rewardEq := trace.rewardState_eq
  cases hpow : benv.stat.rules.pow with
  | none =>
      rw [hpow] at rewardEq
      rw [rewardEq]
      exact requests.1
  | some pow =>
      rw [hpow] at rewardEq
      rw [rewardEq]
      exact StateInv.payRewards (rewards pow hpow) requests.1

/-- Remainder-of-block preservation: suffix transactions, withdrawals,
requests and rewards. Fork membership, `stateGas = none`, not-yet-created and
the withdrawal bound all come from `block`; the only contract premise is the
invariant right after transaction `i`. -/
theorem ConfiguredBlockTraceIn.tail_stateInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : (MidHistoryTraceIn.tail block cut).FrameAdmitted ca entry)
    (rewards : block.RewardCreditsFunded)
    (inv : c.StateInv ca cut.afterBenv.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca post.state := by
  have hsg : (initBenv block.fork pre block.block.header).stat.rules.stateGas = none :=
    capabilities.stateGas_none block.forkIn
  have stat := block.txSplit_stat cut
  have afterF : F cut.afterBenv.stat.fork := by rw [stat]; exact block.forkIn
  have afterSg : cut.afterBenv.stat.rules.stateGas = none := by rw [stat]; exact hsg
  have afterBound : sum cut.txState.bal + wdsum block.block.wds < 2 ^ 256 :=
    block.txSplit_bound cut capabilities
  have afterInv : c.BenvInv ca cut.afterBenv := ⟨inv, block.txSplit_notCreated cut ca⟩
  have afterSum : sum (cut.benv.withState cut.txState).state.bal < 2 ^ 256 := by
    simp only [Benv.withState]
    omega
  have txInv : c.BenvInv ca block.bodyTrace.transactionBenv :=
    cut.after.benvInv_admitted_semIn preserves afterF afterSg admitted.1 afterSum
      afterInv K image
  have txLe : sum block.bodyTrace.transactionBenv.state.bal ≤ sum cut.txState.bal := by
    simpa only [Benv.withState] using cut.after.sum_le_noStateGas afterSg
  have hstate := block.bodyTrace.afterTransactions_stateInv_admitted_semIn preserves
    block.forkIn hsg admitted.2 (by omega) rewards txInv K image
  rw [block.postEq]
  exact hstate

/-- **Mid-history preservation** (`refl` replaced by `tail`). -/
theorem MidHistoryTraceIn.stateInv_admitted_semIn {F : Fork → Prop} {C : ByteArray}
    {c : ContractSpecSem} {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca start.state)
    (K : InstalledCert C) (image : c.sem.image = some C.toList) :
    c.StateInv ca future.state := by
  induction trace with
  | tail block cut =>
      exact block.tail_stateInv_admitted_semIn cut preserves capabilities admitted rewards inv
        K image
  | step prior block ih =>
      exact block.stateInv_admitted_semIn preserves capabilities admitted.2 rewards.2
        (ih admitted.1 rewards.1 inv) K image

end ExecutionTrace

namespace ExecutionTrace

open Jaune

open ContractSpec

/-- `ContractSpec` form of `MidHistoryTraceIn.stateInv_admitted_semIn`. -/
theorem MidHistoryTraceIn.stateInv_admittedIn {F : Fork → Prop} {C : ByteArray}
    {c : ContractSpec} {ca : Adr} {entry : Sevm → Devm → Prop}
    {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future)
    (preserves : c.PreservesAdmittedIn F ca entry)
    (capabilities : BodyStageCapabilities F)
    (admitted : trace.FrameAdmitted ca entry)
    (rewards : trace.RewardCreditsFunded)
    (inv : c.StateInv ca start.state)
    (K : InstalledCert C) (image : Prog.compile c.prog = some C.toList) :
    c.StateInv ca future.state :=
  stateInv_ofSem (trace.stateInv_admitted_semIn (c := c.toSem)
    (preservesAdmittedIn_toSem c ca entry preserves) capabilities admitted rewards
    (stateInv_toSem inv) K image)

end ExecutionTrace

end Blanc
