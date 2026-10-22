import Blanc.LadderSem
import Blanc.ExecutionStagedBodyTrace

/-!
# Exact balance credits in proof-of-work block rewards

The reward budget is a natural-number sum before any conversion to EVM words.
Beneficiaries may coincide. Every intermediate credit is justified by that same
budget; a bound on the final wrapped balance would not suffice.
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

/-- PoW rewards preserve a semantic contract invariant under the exact mint
budget. This uses the contract's proved direct-credit law at every recipient. -/
theorem ContractSpecSem.StateInv.payRewards {c : ContractSpecSem} {ca : Adr}
    {pow : PowRules} {number : Nat} {coinbase : Adr} {ommers : List Header} {st : State}
    (initial : c.StateInv ca st)
    (bound : sum st.bal + ChainConfig.rewardTotal pow number ommers < 2 ^ 256) :
    c.StateInv ca (Jaune.payRewards pow number coinbase ommers st) :=
  (payRewards_preserves_and_sum (P := c.StateInv ca)
    (fun _ _ _ h inv => inv.addBal h) pow number coinbase ommers bound initial).1

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

end ExecutionTrace

end Blanc
