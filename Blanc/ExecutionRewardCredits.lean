import Blanc.LadderSem
import Blanc.ExecutionStagedBodyTrace
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionHistory
import Blanc.ExecutionHistoricalAdmission

/-!
# Exact balance credits in proof-of-work block rewards

The reward budget is a natural-number sum before any conversion to EVM words.
Beneficiaries may coincide. Every intermediate credit is justified by that same
budget; a bound on the final wrapped balance would not suffice. The same
budget discharges the per-credit `RewardCreditsFunded` premise of the historical
admitted-preservation theorems (`Blanc.ExecutionHistoricalAdmission`).
-/

namespace Blanc

open Jaune

/-- A natural-valued credit fold preserves a credit-stable predicate and mints
exactly the stated sum. No distinct-recipient premise is needed. -/
theorem fold_addBal_nat_preserves {P : State → Prop}
    (credit : ∀ (st : State) (a : Adr) (v : B256),
      sum st.bal + v.toNat < 2 ^ 256 → P st → P (st.addBal a v))
    (credits : List (Adr × Nat)) {st : State}
    (bound : sum st.bal + (credits.map Prod.snd).sum < 2 ^ 256)
    (initial : P st) :
    P (credits.foldl (fun w c => w.addBal c.1 c.2.toB256) st) ∧
      sum (credits.foldl (fun w c => w.addBal c.1 c.2.toB256) st).bal =
        sum st.bal + (credits.map Prod.snd).sum := by
  induction credits generalizing st with
  | nil => exact ⟨initial, by simp only [List.foldl_nil, List.map_nil, List.sum_nil, Nat.add_zero]⟩
  | cons c cs ih =>
      have headBound : c.2 < 2 ^ 256 := by
        simp only [List.map_cons, List.sum_cons] at bound
        omega
      have value : c.2.toB256.toNat = c.2 := B256.toNat_toB256_of_lt headBound
      have creditBound : sum st.bal + c.2.toB256.toNat < 2 ^ 256 := by
        simp only [List.map_cons, List.sum_cons] at bound
        omega
      have total := sum_addBal_eq st c.1 c.2.toB256 creditBound
      have tailBound : sum (st.addBal c.1 c.2.toB256).bal +
          (cs.map Prod.snd).sum < 2 ^ 256 := by
        simp only [List.map_cons, List.sum_cons] at bound
        rw [total, value]
        omega
      obtain ⟨preserved, summed⟩ := ih tailBound (credit st c.1 _ creditBound initial)
      refine ⟨preserved, ?_⟩
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [summed, total, value]
      omega

/-- The actual PoW reward transition preserves any predicate stable under
nonwrapping direct credits and mints exactly `ChainConfig.rewardTotal`. -/
theorem payRewards_preserves_and_sum {P : State → Prop}
    (credit : ∀ (st : State) (a : Adr) (v : B256),
      sum st.bal + v.toNat < 2 ^ 256 → P st → P (st.addBal a v))
    (pow : PowRules) (number : Nat) (coinbase : Adr) (ommers : List Header)
    {st : State}
    (bound : sum st.bal + ChainConfig.rewardTotal pow number ommers < 2 ^ 256)
    (initial : P st) :
    P (payRewards pow number coinbase ommers st) ∧
      sum (payRewards pow number coinbase ommers st).bal =
        sum st.bal + ChainConfig.rewardTotal pow number ommers := by
  let credits : List (Adr × Nat) :=
    (coinbase, pow.blockReward + ommers.length * (pow.blockReward / 32)) ::
      ommers.map (fun o => (o.coinbase, (8 + o.number - number) * pow.blockReward / 8))
  have amount : (credits.map Prod.snd).sum = ChainConfig.rewardTotal pow number ommers := by
    simp only [credits, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
      ChainConfig.rewardTotal]
  have result := fold_addBal_nat_preserves credit credits (by rw [amount]; exact bound) initial
  simpa only [credits, List.foldl_cons, List.foldl_map, amount, payRewards] using result

/-- Exact total mint of real PoW rewards under the natural-number budget. -/
theorem sum_payRewards_eq (pow : PowRules) (number : Nat) (coinbase : Adr)
    (ommers : List Header) {st : State}
    (bound : sum st.bal + ChainConfig.rewardTotal pow number ommers < 2 ^ 256) :
    sum (payRewards pow number coinbase ommers st).bal =
      sum st.bal + ChainConfig.rewardTotal pow number ommers :=
  (payRewards_preserves_and_sum (P := fun _ => True)
    (fun _ _ _ _ _ => trivial) pow number coinbase ommers bound trivial).2

/-- Reward credits preserve a protected account's storage even without a
balance budget. Protection, rather than a historical no-deletion assertion,
excludes normalization of a storage-only account. -/
theorem payRewards_getStor_of_protected (pow : PowRules) (number : Nat)
    (coinbase : Adr) (ommers : List Header) {st : State} {ca : Adr}
    (protection : State.Protected st ca) :
    (payRewards pow number coinbase ommers st).getStor ca = st.getStor ca := by
  have fold : ∀ (xs : List Header) (w : State), State.Protected w ca →
      (xs.foldl (fun acc o => acc.addBal o.coinbase
        ((8 + o.number - number) * pow.blockReward / 8).toB256) w).getStor ca =
        w.getStor ca := by
    intro xs
    induction xs with
    | nil => intro w _; rfl
    | cons o os ih =>
        intro w hp
        rw [List.foldl_cons, ih (w.addBal o.coinbase
          ((8 + o.number - number) * pow.blockReward / 8).toB256) (hp.setBal _ _)]
        exact State.setBal_get_stor_of_protected hp
  unfold payRewards
  dsimp only
  rw [fold ommers (st.addBal coinbase
    (pow.blockReward + ommers.length * (pow.blockReward / 32)).toB256)
    (protection.setBal _ _)]
  exact State.setBal_get_stor_of_protected protection

/-- Each account's natural balance is monotone through the real reward fold.
The pre-credit total budget prevents recipient overflow, including collisions. -/
theorem payRewards_balance_mono (pow : PowRules) (number : Nat)
    (coinbase : Adr) (ommers : List Header) {st : State}
    (bound : sum st.bal + ChainConfig.rewardTotal pow number ommers < 2 ^ 256)
    (ca : Adr) :
    (st.bal ca).toNat ≤ ((payRewards pow number coinbase ommers st).bal ca).toNat := by
  apply (payRewards_preserves_and_sum (P := fun w => (st.bal ca).toNat ≤ (w.bal ca).toNat)
    (fun w a v budget before => ?_) pow number coinbase ommers bound le_rfl).1
  by_cases target : a = ca
  · subst a
    have nof : B256.Nof (w.bal ca) v := by
      unfold B256.Nof
      have current : (w.bal ca).toNat ≤ sum w.bal := le_sum
      omega
    have balance : (w.addBal ca v).bal ca = w.bal ca + v := by
      show ((w.setBal ca (w.bal ca + v)).get ca).bal = _
      rw [State.setBal_get_self, Acct.clearIfEmpty_bal]
      rfl
    rw [balance, B256.toNat_add_eq_of_nof _ _ nof]
    omega
  · have balance : (w.addBal a v).bal ca = w.bal ca := by
      show ((w.setBal a (w.bal a + v)).get ca).bal = _
      rw [State.setBal_get_ne target]
      rfl
    rw [balance]
    exact before

/-! ## Bridge to the historical per-credit reward premise -/

/-- The ommer credits of `payRewards` are each funded, in fold order, by one
opening natural-number bound on their total. -/
theorem OmmerCreditsFunded.of_sum {pow : PowRules} {number : Nat} :
    ∀ (ommers : List Header) {st : State},
      sum st.bal + (ommers.map fun o => (8 + o.number - number) * pow.blockReward / 8).sum <
        2 ^ 256 →
      OmmerCreditsFunded pow number st ommers
  | [], _, _ => trivial
  | o :: os, st, bound => by
      simp only [List.map_cons, List.sum_cons] at bound
      generalize hrest : (os.map fun o => (8 + o.number - number) * pow.blockReward / 8).sum =
        rest at bound
      have value : (ExecutionTrace.stagedOmmerRewardValue pow number o).toNat =
          (8 + o.number - number) * pow.blockReward / 8 :=
        B256.toNat_toB256_of_lt (by omega)
      have credit : sum st.bal + (ExecutionTrace.stagedOmmerRewardValue pow number o).toNat <
          2 ^ 256 := by
        rw [value]
        omega
      refine ⟨credit, OmmerCreditsFunded.of_sum os ?_⟩
      rw [sum_addBal_eq _ _ _ credit, value, hrest]
      omega

/-- The exact reward budget `ChainConfig.rewardTotal` funds every `payRewards`
credit (miner first, then each ommer in fold order) at the state it is applied
to. Beneficiaries may coincide. -/
theorem RewardCreditsFunded.of_rewardTotal {pow : PowRules} {number : Nat} {coinbase : Adr}
    {ommers : List Header} {st : State}
    (bound : sum st.bal + ChainConfig.rewardTotal pow number ommers < 2 ^ 256) :
    RewardCreditsFunded pow number coinbase ommers st := by
  unfold ChainConfig.rewardTotal at bound
  generalize hrest : (ommers.map fun o => (8 + o.number - number) * pow.blockReward / 8).sum =
    rest at bound
  have value : (ExecutionTrace.stagedMinerRewardValue pow ommers).toNat =
      pow.blockReward + ommers.length * (pow.blockReward / 32) :=
    B256.toNat_toB256_of_lt (by omega)
  have credit : sum st.bal + (ExecutionTrace.stagedMinerRewardValue pow ommers).toNat <
      2 ^ 256 := by
    rw [value]
    omega
  refine ⟨credit, OmmerCreditsFunded.of_sum ommers ?_⟩
  rw [sum_addBal_eq _ _ _ credit, value, hrest]
  omega

/-- PoW rewards preserve a semantic contract invariant under the exact mint
budget: the historical per-credit law `StateInv.payRewards` applied to the
credits funded by `RewardCreditsFunded.of_rewardTotal`. -/
theorem ContractSpecSem.StateInv.payRewards_of_rewardTotal {c : ContractSpecSem} {ca : Adr}
    {pow : PowRules} {number : Nat} {coinbase : Adr} {ommers : List Header} {st : State}
    (initial : c.StateInv ca st)
    (bound : sum st.bal + ChainConfig.rewardTotal pow number ommers < 2 ^ 256) :
    c.StateInv ca (Jaune.payRewards pow number coinbase ommers st) :=
  ContractSpecSem.StateInv.payRewards (RewardCreditsFunded.of_rewardTotal bound) initial

namespace ExecutionTrace

/-- Transport through the retained body's actual final reward stage, with
its exact mint. Skipped rewards are an identity; enabled rewards use their
real miner/ommer credits, never an equality to request state. -/
theorem StagedBodyTrace.reward_preserves_and_sum {P : State → Prop}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (credit : ∀ (st : State) (a : Adr) (v : B256),
      sum st.bal + v.toNat < 2 ^ 256 → P st → P (st.addBal a v))
    (initial : P trace.requestState)
    (budget : ∀ pow, benv.stat.rules.pow = some pow →
      sum trace.requestState.bal + ChainConfig.rewardTotal pow benv.stat.number ommers < 2 ^ 256) :
    P state ∧ sum state.bal = sum trace.requestState.bal +
      (match benv.stat.rules.pow with
       | none => 0
       | some pow => ChainConfig.rewardTotal pow benv.stat.number ommers) := by
  have endpoint := trace.state_eq_rewardState.trans trace.rewardState_eq
  cases enabled : benv.stat.rules.pow with
  | none =>
      simp only [enabled] at endpoint
      exact ⟨(congrArg P endpoint).mpr initial,
        (congrArg (fun w : State => sum w.bal) endpoint).trans (Nat.add_zero _).symm⟩
  | some pow =>
      simp only [enabled] at endpoint
      obtain ⟨preserved, summed⟩ := payRewards_preserves_and_sum credit pow benv.stat.number
        benv.stat.coinbase ommers (budget pow enabled) initial
      exact ⟨(congrArg P endpoint).mpr preserved,
        (congrArg (fun w : State => sum w.bal) endpoint).trans summed⟩

/-- A semantic invariant already established at the request endpoint survives
the actual retained reward stage. Earlier interpreter stages remain separate. -/
theorem StagedBodyTrace.stateInv_of_requestState {c : ContractSpecSem} {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (initial : c.StateInv ca trace.requestState)
    (budget : ∀ pow, benv.stat.rules.pow = some pow →
      sum trace.requestState.bal + ChainConfig.rewardTotal pow benv.stat.number ommers < 2 ^ 256) :
    c.StateInv ca state :=
  (trace.reward_preserves_and_sum (fun _ _ _ h inv => inv.addBal h) initial budget).1

/-- Protected storage survives the final retained stage without a balance
budget, including when the selected fork enables actual PoW rewards. -/
theorem StagedBodyTrace.reward_getStor_of_protected {ca : Adr}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (protection : State.Protected trace.requestState ca) :
    state.getStor ca = trace.requestState.getStor ca := by
  have endpoint := trace.state_eq_rewardState.trans trace.rewardState_eq
  cases enabled : benv.stat.rules.pow with
  | none =>
      simp only [enabled] at endpoint
      exact congrArg (fun w => w.getStor ca) endpoint
  | some pow =>
      simp only [enabled] at endpoint
      exact (congrArg (fun w => w.getStor ca) endpoint).trans
        (payRewards_getStor_of_protected pow benv.stat.number benv.stat.coinbase
          ommers protection)

/-- Actual system-message execution cannot increase the total balance under
the selected no-state-gas rule; no modern fork predicate is required. -/
theorem SystemMessageTrace.sum_le_of_stateGas_none
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  have result := processMessageCall_sum_le
    (by simpa only [BenvStat.rules, systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hsg) trace.message.result
  simpa only [systemTransactionMessage, processSystemTransactionMsg,
    Benv.beginTransaction] using result

/-- Called and skipped beacon stages both satisfy the same total bound. -/
theorem BeaconStageTrace.sum_le_of_stateGas_none
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact le_rfl
  | called _ _ message _ _ => exact message.sum_le_of_stateGas_none hsg

/-- The history stage keeps its actual input/output and optional call. -/
theorem HistoryStageTrace.sum_le_of_stateGas_none
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder}
    {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact le_rfl
  | called _ _ _ _ message _ _ => exact message.sum_le_of_stateGas_none hsg

/-- The actual transaction fold is balance-nonincreasing under its selected
rule, including historical gas and settlement behavior. -/
theorem ApplyTransactionsTrace.sum_le_of_stateGas_none
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none) :
    sum finalBenv.state.bal ≤ sum benv.state.bal := by
  induction trace with
  | nil => exact le_rfl
  | cons head tail ih =>
      exact (ih hsg).trans (processTransaction_sum_le head.result hsg)

/-- Both retained checked request calls are real no-state-gas executions. -/
theorem RequestsTrace.sum_le_of_stateGas_none
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  rw [trace.state_eq_consolidationState]
  exact (trace.consolidation.sum_le_of_stateGas_none hsg).trans
    (trace.withdrawal.sum_le_of_stateGas_none hsg)

/-- Disabled requests are an identity; enabled requests use the actual two
retained messages, without asserting equality of their state endpoints. -/
theorem RequestStageTrace.sum_le_of_stateGas_none
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput}
    {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none) :
    sum state.bal ≤ sum benv.state.bal := by
  cases trace with
  | skipped => exact le_rfl
  | called _ requests _ => exact requests.sum_le_of_stateGas_none hsg

/-- The exact natural mint of direct withdrawals, justified before every
word conversion and recipient credit by the opening total bound. -/
theorem sum_processWithdrawalsState_eq {st : State} {wds : List Withdrawal}
    (bound : sum st.bal + wdsum wds < 2 ^ 256) :
    sum (processWithdrawalsState st wds).bal = sum st.bal + wdsum wds := by
  induction wds generalizing st with
  | nil => simp only [processWithdrawalsState, List.foldl_nil, wdsum,
      List.map_nil, List.sum_nil, Nat.add_zero]
  | cons wd wds ih =>
      have bounds := withdrawalCredit_bounds bound
      have amount : wd.amount.toNat * 10 ^ 9 < 2 ^ 256 := by
        simp only [wdsum, List.map_cons, List.sum_cons] at bound
        omega
      have value := withdrawalCredit_toNat (wd := wd) amount
      rw [processWithdrawalsState_cons]
      rw [ih bounds.2, sum_addBal_eq _ _ _ bounds.1, value]
      simp only [wdsum, List.map_cons, List.sum_cons]
      omega

/-- Transport the body-entry total through the actual system prefixes,
transactions, optional direct withdrawals and request messages. -/
theorem StagedBodyTrace.request_sum_le
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256) :
    sum trace.requestState.bal ≤ sum benv.state.bal + wdsum wds := by
  have beacon := trace.beacon.sum_le_of_stateGas_none hsg
  have history := trace.history.sum_le_of_stateGas_none hsg
  have transactions := trace.transactions.sum_le_of_stateGas_none hsg
  have txBound : sum trace.transactionBenv.state.bal + wdsum wds < 2 ^ 256 := by
    dsimp only [Benv.withState] at history transactions
    omega
  have withdrawals : sum trace.withdrawalState.bal ≤
      sum trace.transactionBenv.state.bal + wdsum wds := by
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        omega
    | true =>
        have endpoints := trace.withdrawalsRun
        simp only [withdrawalsPass, enabled, ↓reduceIte, processWithdrawals] at endpoints
        rw [← (Prod.mk.inj endpoints).1, sum_processWithdrawalsState_eq txBound]
  have requestGas : (trace.transactionBenv.withState trace.withdrawalState).stat.rules.stateGas =
      none := by
    change trace.transactionBenv.stat.rules.stateGas = none
    rw [trace.transactions.stat_eq]
    exact hsg
  have requests := trace.requests.sum_le_of_stateGas_none requestGas
  dsimp only [Benv.withState] at history transactions requests
  omega

/-- A future mint's budget is derived from body-entry evidence, never from
an assumed bound on the already-executed request endpoint. -/
theorem StagedBodyTrace.request_budget
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput} {mint : Nat}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (bound : sum benv.state.bal + wdsum wds + mint < 2 ^ 256) :
    sum trace.requestState.bal + mint < 2 ^ 256 := by
  have prior := trace.request_sum_le hsg (by omega)
  omega

/-- The retained configured pre-block withdrawal-plus-reward bound supplies
the exact selected PoW budget at the actual request state. -/
theorem ConfiguredBlockTraceIn.request_reward_budget
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : trace.fork.ruleSet.stateGas = none) (pow : PowRules)
    (enabled : trace.fork.ruleSet.pow = some pow) :
    sum trace.bodyTrace.requestState.bal + ChainConfig.rewardTotal pow
      trace.block.header.number trace.block.ommers < 2 ^ 256 := by
  have reward : cfg.rewardAt trace.block = ChainConfig.rewardTotal pow
      trace.block.header.number trace.block.ommers := by
    simp only [ChainConfig.rewardAt, trace.forkAt, enabled]
  apply trace.bodyTrace.request_budget hsg
  change sum pre.state.bal + wdsum trace.block.wds +
    ChainConfig.rewardTotal pow trace.block.header.number trace.block.ommers < 2 ^ 256
  rw [← reward]
  exact trace.bound

/-- A credit-stable predicate at the actual request stage reaches the
configured post-state, with the selected reward total computed by its schedule.
Only the balance budget is derived here; earlier invariant preservation is a
separate proof obligation. -/
theorem ConfiguredBlockTraceIn.reward_preserves_and_sum
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} {P : State → Prop}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : trace.fork.ruleSet.stateGas = none)
    (credit : ∀ (st : State) (a : Adr) (v : B256),
      sum st.bal + v.toNat < 2 ^ 256 → P st → P (st.addBal a v))
    (initial : P trace.bodyTrace.requestState) :
    P post.state ∧ sum post.state.bal =
      sum trace.bodyTrace.requestState.bal + cfg.rewardAt trace.block := by
  have reward := trace.bodyTrace.reward_preserves_and_sum credit initial
    (fun pow enabled => trace.request_reward_budget hsg pow enabled)
  have mint : (match (initBenv trace.fork pre trace.block.header).stat.rules.pow with
      | none => 0
      | some pow => ChainConfig.rewardTotal pow
          (initBenv trace.fork pre trace.block.header).stat.number trace.block.ommers) =
      cfg.rewardAt trace.block := by
    change (match trace.fork.ruleSet.pow with
      | none => 0
      | some pow => ChainConfig.rewardTotal pow trace.block.header.number trace.block.ommers) = _
    simp only [ChainConfig.rewardAt, trace.forkAt]
    cases trace.fork.ruleSet.pow <;> rfl
  rw [mint] at reward
  rw [show post.state = trace.bodyState from congrArg BlockChain.state trace.postEq]
  exact reward

/-- The whole actual configured body, including its selected PoW rewards,
stays below the opening total plus the retained withdrawal/reward mint. -/
theorem ConfiguredBlockTraceIn.sum_post_le
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : trace.fork.ruleSet.stateGas = none) :
    sum post.state.bal ≤ sum pre.state.bal + wdsum trace.block.wds +
      cfg.rewardAt trace.block := by
  have prior := trace.bodyTrace.request_sum_le hsg trace.withdrawalsBound
  have reward := (trace.reward_preserves_and_sum (P := fun _ => True) hsg
    (fun _ _ _ _ _ => trivial) trivial).2
  rw [reward]
  exact Nat.add_le_add_right prior _

/-- A staged body's request-endpoint reward budget discharges its per-credit
reward premise. -/
theorem StagedBodyTrace.rewardCreditsFunded_of_budget
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (budget : ∀ pow, benv.stat.rules.pow = some pow →
      sum trace.requestState.bal + ChainConfig.rewardTotal pow benv.stat.number ommers < 2 ^ 256) :
    trace.RewardCreditsFunded :=
  fun pow enabled => Blanc.RewardCreditsFunded.of_rewardTotal (budget pow enabled)

/-- A retained configured block funds its own reward credits: the budget comes
from its reward-inclusive pre-block bound, through `request_reward_budget`. -/
theorem ConfiguredBlockTraceIn.rewardCreditsFunded
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (hsg : trace.fork.ruleSet.stateGas = none) :
    trace.RewardCreditsFunded :=
  trace.bodyTrace.rewardCreditsFunded_of_budget
    (fun pow enabled => trace.request_reward_budget hsg pow enabled)

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
