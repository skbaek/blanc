import Blanc.Lift.UniswapV2Pair.Properties

/-! Pure oracle laws for the source-level Uniswap V2 Pair model. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

def oracleTimestamp (ctx : Context) : Nat := ctx.timestamp.toNat % 2 ^ 32

def oracleElapsed (st : State) (ctx : Context) : Nat :=
  (oracleTimestamp ctx + 2 ^ 32 - st.blockTimestampLast.toNat) % 2 ^ 32

def oracleIncrement0 (st : State) (ctx : Context) (oldReserve0 oldReserve1 : Nat) : Nat :=
  if oracleElapsed st ctx > 0 ∧ oldReserve0 ≠ 0 ∧ oldReserve1 ≠ 0 then
    (oldReserve1 * 2 ^ 112 / oldReserve0) * oracleElapsed st ctx
  else 0

def oracleIncrement1 (st : State) (ctx : Context) (oldReserve0 oldReserve1 : Nat) : Nat :=
  if oracleElapsed st ctx > 0 ∧ oldReserve0 ≠ 0 ∧ oldReserve1 ≠ 0 then
    (oldReserve0 * 2 ^ 112 / oldReserve1) * oracleElapsed st ctx
  else 0

/-- A successful `_update` has the wrapped timestamp and both modular oracle laws. -/
theorem State.update_oracle_law {st post : State} {ctx : Context}
    {balance0 balance1 : B256} {oldReserve0 oldReserve1 : Nat}
    {event : Event} {update : OracleUpdate}
    (accepted : st.update ctx balance0 balance1 oldReserve0 oldReserve1 =
      .ok (post, event, update)) :
    post.price0CumulativeLast.toNat =
        (st.price0CumulativeLast.toNat + oracleIncrement0 st ctx oldReserve0 oldReserve1) % 2 ^ 256 ∧
      post.price1CumulativeLast.toNat =
        (st.price1CumulativeLast.toNat + oracleIncrement1 st ctx oldReserve0 oldReserve1) % 2 ^ 256 ∧
      post.blockTimestampLast = UInt32.ofNat (oracleTimestamp ctx) ∧
      update.elapsed = oracleElapsed st ctx ∧
      update.increment0 = oracleIncrement0 st ctx oldReserve0 oldReserve1 ∧
      update.increment1 = oracleIncrement1 st ctx oldReserve0 oldReserve1 := by
  rw [State.update] at accepted
  by_cases bound0 : balance0.toNat < 2 ^ 112
  · rw [dite_eq_left bound0] at accepted
    by_cases bound1 : balance1.toNat < 2 ^ 112
    · rw [dite_eq_left bound1] at accepted
      cases (Except.ok.inj accepted)
      simp only [oracleTimestamp, oracleElapsed, oracleIncrement0, oracleIncrement1,
        B256.toNat_add, Nat.lo_eq]
      refine ⟨?_, ?_, True.intro, True.intro, rfl, rfl⟩
      · rw [B256.toNat_toB256, Nat.lo_eq, Nat.add_mod_mod]
        rfl
      · rw [B256.toNat_toB256, Nat.lo_eq, Nat.add_mod_mod]
        rfl
    · rw [dite_eq_right bound1] at accepted
      cases accepted
  · rw [dite_eq_right bound0] at accepted
    cases accepted

def oracleFold0 (initial : B256) : List TaggedOracleUpdate → B256
  | [] => initial
  | tagged :: updates => oracleFold0 (initial + Nat.toB256 tagged.update.increment0) updates

def oracleFold1 (initial : B256) : List TaggedOracleUpdate → B256
  | [] => initial
  | tagged :: updates => oracleFold1 (initial + Nat.toB256 tagged.update.increment1) updates

def oracleSum0 : List TaggedOracleUpdate → Nat
  | [] => 0
  | tagged :: updates => tagged.update.increment0 + oracleSum0 updates

def oracleSum1 : List TaggedOracleUpdate → Nat
  | [] => 0
  | tagged :: updates => tagged.update.increment1 + oracleSum1 updates

/-- Committed update receipts add exactly their increments modulo one B256 word. -/
theorem oracleFold0_law (initial : B256) (updates : List TaggedOracleUpdate) :
    (oracleFold0 initial updates).toNat =
      (initial.toNat + oracleSum0 updates) % 2 ^ 256 := by
  induction updates generalizing initial with
  | nil =>
      rw [oracleFold0, oracleSum0, Nat.add_zero,
        Nat.mod_eq_of_lt (B256.toNat_lt _)]
  | cons tagged updates ih =>
      rw [oracleFold0, oracleSum0, ih]
      rw [B256.toNat_add, Nat.lo_eq, B256.toNat_toB256, Nat.lo_eq]
      rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

/-- The symmetric committed-update fold law for token 1's accumulator. -/
theorem oracleFold1_law (initial : B256) (updates : List TaggedOracleUpdate) :
    (oracleFold1 initial updates).toNat =
      (initial.toNat + oracleSum1 updates) % 2 ^ 256 := by
  induction updates generalizing initial with
  | nil =>
      rw [oracleFold1, oracleSum1, Nat.add_zero,
        Nat.mod_eq_of_lt (B256.toNat_lt _)]
  | cons tagged updates ih =>
      rw [oracleFold1, oracleSum1, ih]
      rw [B256.toNat_add, Nat.lo_eq, B256.toNat_toB256, Nat.lo_eq]
      rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]

theorem oracleFold0_append (initial : B256) (left right : List TaggedOracleUpdate) :
    oracleFold0 initial (left ++ right) = oracleFold0 (oracleFold0 initial left) right := by
  induction left generalizing initial with
  | nil => rfl
  | cons tagged left ih =>
      rw [List.cons_append, oracleFold0, ih, oracleFold0]

theorem oracleFold1_append (initial : B256) (left right : List TaggedOracleUpdate) :
    oracleFold1 initial (left ++ right) = oracleFold1 (oracleFold1 initial left) right := by
  induction left generalizing initial with
  | nil => rfl
  | cons tagged left ih =>
      rw [List.cons_append, oracleFold1, ih, oracleFold1]

def Checkpoint.Accumulates (base0 base1 : B256) (c : Checkpoint) : Prop :=
  c.state.price0CumulativeLast = oracleFold0 base0 c.updates ∧
    c.state.price1CumulativeLast = oracleFold1 base1 c.updates

theorem runTyped_initial_accumulates (st : State) :
    ({ state := st, logs := [], updates := [] } : Checkpoint).Accumulates
      st.price0CumulativeLast st.price1CumulativeLast := by
  constructor <;> rfl

def Frame.Accumulates (base0 base1 : B256) (f : Frame) : Prop :=
  f.checkpoint.Accumulates base0 base1 ∧ f.current.Accumulates base0 base1

def SegmentResult.Accumulates (base0 base1 : B256) (s : SegmentResult) : Prop :=
  s.frame.Accumulates base0 base1

theorem Checkpoint.accumulates_restate {base0 base1 : B256} {c : Checkpoint}
    {post : State} (hc : c.Accumulates base0 base1)
    (h0 : post.price0CumulativeLast = c.state.price0CumulativeLast)
    (h1 : post.price1CumulativeLast = c.state.price1CumulativeLast) :
    ({ c with state := post }).Accumulates base0 base1 := by
  constructor
  · change post.price0CumulativeLast = oracleFold0 base0 c.updates
    rw [h0, hc.1]
  · change post.price1CumulativeLast = oracleFold1 base1 c.updates
    rw [h1, hc.2]

theorem State.economicCore_oracles {st post : State}
    (hcore : post.economicCore = st.economicCore) :
    post.price0CumulativeLast = st.price0CumulativeLast ∧
      post.price1CumulativeLast = st.price1CumulativeLast := by
  have hprices := congrArg (fun core => core.2.2.2.1) hcore
  exact Prod.mk.inj hprices

theorem State.mintLP_oracles {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (accepted : st.mintLP recipient value = .ok (post, events)) :
    post.price0CumulativeLast = st.price0CumulativeLast ∧
      post.price1CumulativeLast = st.price1CumulativeLast := by
  rw [State.mintLP] at accepted
  by_cases supplyBound : st.totalSupply.toNat + value.toNat < 2 ^ 256
  · rw [ite_eq_left supplyBound] at accepted
    by_cases balanceBound : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256
    · rw [ite_eq_left balanceBound] at accepted
      have stateEq := congrArg (fun result : State × List Event => result.1)
        (Except.ok.inj accepted)
      dsimp only at stateEq
      exact ⟨(congrArg (fun state : State => state.price0CumulativeLast) stateEq).symm,
        (congrArg (fun state : State => state.price1CumulativeLast) stateEq).symm⟩
    · rw [ite_eq_right balanceBound] at accepted
      cases accepted
  · rw [ite_eq_right supplyBound] at accepted
    cases accepted

theorem State.burnLP_oracles {st post : State} {source : Adr} {value : B256}
    {events : List Event} (accepted : st.burnLP source value = .ok (post, events)) :
    post.price0CumulativeLast = st.price0CumulativeLast ∧
      post.price1CumulativeLast = st.price1CumulativeLast := by
  rw [State.burnLP] at accepted
  by_cases balanceCovered : value ≤ st.balanceOf source
  · rw [ite_eq_left balanceCovered] at accepted
    by_cases supplyCovered : value ≤ st.totalSupply
    · rw [ite_eq_left supplyCovered] at accepted
      have stateEq := congrArg (fun result : State × List Event => result.1)
        (Except.ok.inj accepted)
      dsimp only at stateEq
      exact ⟨(congrArg (fun state : State => state.price0CumulativeLast) stateEq).symm,
        (congrArg (fun state : State => state.price1CumulativeLast) stateEq).symm⟩
    · rw [ite_eq_right supplyCovered] at accepted
      cases accepted
  · rw [ite_eq_right balanceCovered] at accepted
    cases accepted

theorem mintFee_oracles {st : State} {feeTo : Adr} {reserve0 reserve1 : Nat}
    {fee : FeeResult}
    (accepted : mintFee st feeTo reserve0 reserve1 = .ok fee) :
    fee.state.price0CumulativeLast = st.price0CumulativeLast ∧
      fee.state.price1CumulativeLast = st.price1CumulativeLast := by
  rw [mintFee] at accepted
  by_cases feeOff : feeTo = 0
  · rw [ite_eq_left feeOff] at accepted
    cases (Except.ok.inj accepted)
    exact ⟨rfl, rfl⟩
  · rw [ite_eq_right feeOff] at accepted
    by_cases noLast : st.kLast = 0
    · rw [ite_eq_left noLast] at accepted
      cases (Except.ok.inj accepted)
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right noLast] at accepted
      by_cases growing : Nat.sqrt st.kLast.toNat < Nat.sqrt (reserve0 * reserve1)
      · rw [ite_eq_left growing] at accepted
        by_cases numeratorBound :
            st.totalSupply.toNat * (Nat.sqrt (reserve0 * reserve1) - Nat.sqrt st.kLast.toNat) < 2 ^ 256
        · rw [ite_eq_left numeratorBound] at accepted
          by_cases scaledRootBound : Nat.sqrt (reserve0 * reserve1) * 5 < 2 ^ 256
          · rw [ite_eq_left scaledRootBound] at accepted
            by_cases denominatorBound :
                Nat.sqrt (reserve0 * reserve1) * 5 + Nat.sqrt st.kLast.toNat < 2 ^ 256
            · rw [ite_eq_left denominatorBound] at accepted
              by_cases positiveFee : st.totalSupply.toNat *
                  (Nat.sqrt (reserve0 * reserve1) - Nat.sqrt st.kLast.toNat) /
                  (Nat.sqrt (reserve0 * reserve1) * 5 + Nat.sqrt st.kLast.toNat) > 0
              · rw [ite_eq_left positiveFee] at accepted
                obtain ⟨⟨post, events⟩, minted, feeEq⟩ := Except.bind_eq_ok accepted
                have oracles := State.mintLP_oracles minted
                cases feeEq
                exact oracles
              · rw [ite_eq_right positiveFee] at accepted
                cases (Except.ok.inj accepted)
                exact ⟨rfl, rfl⟩
            · rw [ite_eq_right denominatorBound] at accepted
              cases accepted
          · rw [ite_eq_right scaledRootBound] at accepted
            cases accepted
        · rw [ite_eq_right numeratorBound] at accepted
          cases accepted
      · rw [ite_eq_right growing] at accepted
        cases (Except.ok.inj accepted)
        exact ⟨rfl, rfl⟩

theorem Frame.withEvents_accumulates {base0 base1 : B256} {f : Frame}
    {post : State} {events : List Event}
    (hf : f.Accumulates base0 base1)
    (h0 : post.price0CumulativeLast = f.current.state.price0CumulativeLast)
    (h1 : post.price1CumulativeLast = f.current.state.price1CumulativeLast) :
    (f.withEvents post events).Accumulates base0 base1 := by
  refine ⟨hf.1, ?_⟩
  exact Checkpoint.accumulates_restate hf.2 h0 h1

theorem Frame.withEvents_core_accumulates {base0 base1 : B256} {f : Frame}
    {post : State} {events : List Event}
    (hf : f.Accumulates base0 base1)
    (hcore : post.economicCore = f.current.state.economicCore) :
    (f.withEvents post events).Accumulates base0 base1 := by
  have horacles := State.economicCore_oracles hcore
  exact Frame.withEvents_accumulates hf horacles.1 horacles.2

theorem Frame.fail_accumulates {base0 base1 : B256} {f : Frame} {failure : Failure}
    (hf : f.Accumulates base0 base1) :
    (f.fail failure).frame.Accumulates base0 base1 := by
  exact ⟨hf.1, hf.1⟩

theorem Frame.withUpdate_accumulates {base0 base1 : B256} {f : Frame}
    {post : State} {event : Event} {update : OracleUpdate}
    (hf : f.Accumulates base0 base1)
    (h0 : post.price0CumulativeLast =
      f.current.state.price0CumulativeLast + Nat.toB256 update.increment0)
    (h1 : post.price1CumulativeLast =
      f.current.state.price1CumulativeLast + Nat.toB256 update.increment1) :
    (f.withUpdate post event update).Accumulates base0 base1 := by
  refine ⟨hf.1, ?_⟩
  constructor
  · change post.price0CumulativeLast =
      oracleFold0 base0 (f.current.updates ++ [{ origin := f.origin, update := update }])
    rw [oracleFold0_append, oracleFold0, h0, hf.2.1]
    rfl
  · change post.price1CumulativeLast =
      oracleFold1 base1 (f.current.updates ++ [{ origin := f.origin, update := update }])
    rw [oracleFold1_append, oracleFold1, h1, hf.2.2]
    rfl

theorem Frame.withUpdate_from_update_accumulates {base0 base1 : B256} {f : Frame}
    {ctx : Context} {balance0 balance1 : B256} {oldReserve0 oldReserve1 : Nat}
    {post : State} {event : Event} {update : OracleUpdate}
    (hf : f.Accumulates base0 base1)
    (accepted : f.current.state.update ctx balance0 balance1 oldReserve0 oldReserve1 =
      .ok (post, event, update)) :
    (f.withUpdate post event update).Accumulates base0 base1 := by
  have law := State.update_oracle_law accepted
  have h0 : post.price0CumulativeLast =
      f.current.state.price0CumulativeLast + Nat.toB256 update.increment0 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, Nat.lo_eq, B256.toNat_toB256, Nat.lo_eq,
      law.2.2.2.2.1, Nat.add_mod_mod]
    exact law.1
  have h1 : post.price1CumulativeLast =
      f.current.state.price1CumulativeLast + Nat.toB256 update.increment1 := by
    apply B256.toNat_inj
    rw [B256.toNat_add, Nat.lo_eq, B256.toNat_toB256, Nat.lo_eq,
      law.2.2.2.2.2, Nat.add_mod_mod]
    exact law.2.1
  exact Frame.withUpdate_accumulates hf h0 h1

theorem Frame.finishUpdated_accumulates {base0 base1 : B256} {f : Frame}
    {balance0 balance1 : B256} {reserves : CachedReserves} {feeOn : Bool}
    {lastEvent : Option Event} {returndata : Bytes}
    (hf : f.Accumulates base0 base1) :
    (f.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata).frame.Accumulates
      base0 base1 := by
  rw [Frame.finishUpdated]
  cases accepted : f.current.state.update f.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure => exact Frame.fail_accumulates hf
  | ok result =>
      rcases result with ⟨post, event, update⟩
      have updated := Frame.withUpdate_from_update_accumulates hf accepted
      cases feeOn with
      | false =>
          cases lastEvent with
          | none => exact updated
          | some extra => exact Frame.withEvents_accumulates updated rfl rfl
      | true =>
          cases lastEvent with
          | none => exact Frame.withEvents_accumulates updated rfl rfl
          | some extra => exact Frame.withEvents_accumulates updated rfl rfl

theorem Frame.mintAfterFee_accumulates {base0 base1 : B256} {f : Frame}
    {observed : MintObserved} {fee : FeeResult} {feeTo : Adr}
    (hf : f.Accumulates base0 base1)
    (hfee : mintFee f.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val = .ok fee) :
    (f.mintAfterFee observed fee).frame.Accumulates base0 base1 := by
  have feeOracles := mintFee_oracles hfee
  let chargedFrame := f.withEvents fee.state fee.events
  have charged : chargedFrame.Accumulates base0 base1 :=
    Frame.withEvents_accumulates (events := fee.events) hf feeOracles.1 feeOracles.2
  rw [Frame.mintAfterFee]
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure =>
    simp only [Frame.fail]
    exact Frame.fail_accumulates charged
  | ok liquidity =>
    simp only []
    cases initial : (if fee.state.totalSupply = 0 then
        fee.state.mintLP 0 1000 else .ok (fee.state, [])) with
    | error failure =>
      simp only [Frame.fail]
      exact Frame.fail_accumulates charged
    | ok result =>
      rcases result with ⟨postMinimum, minimumEvents⟩
      simp only []
      have minimum :
          (chargedFrame.withEvents postMinimum minimumEvents).Accumulates base0 base1 := by
        by_cases zero : fee.state.totalSupply = 0
        · rw [ite_eq_left zero] at initial
          cases minted : fee.state.mintLP 0 1000 with
          | error failure =>
            simp only [minted] at initial
            cases initial
          | ok result =>
            rcases result with ⟨post, events⟩
            simp only [minted] at initial
            cases initial
            have hmint := State.mintLP_oracles minted
            exact Frame.withEvents_accumulates charged hmint.1 hmint.2
        · rw [ite_eq_right zero] at initial
          cases initial
          exact Frame.withEvents_accumulates charged rfl rfl
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive]
        cases minted : postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure =>
          simp only [Frame.fail]
          exact Frame.fail_accumulates minimum
        | ok result =>
          rcases result with ⟨post, events⟩
          have hmint := State.mintLP_oracles minted
          have issued := Frame.withEvents_accumulates (events := events) minimum hmint.1 hmint.2
          exact Frame.finishUpdated_accumulates issued
      · rw [ite_eq_right positive]
        exact Frame.fail_accumulates minimum

theorem Frame.burnAfterFee_accumulates {base0 base1 : B256} {f : Frame}
    {observed : BurnObserved} {fee : FeeResult} {feeTo : Adr}
    (hf : f.Accumulates base0 base1)
    (hfee : mintFee f.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val = .ok fee) :
    (f.burnAfterFee observed fee).frame.Accumulates base0 base1 := by
  have feeOracles := mintFee_oracles hfee
  let chargedFrame := f.withEvents fee.state fee.events
  have charged : chargedFrame.Accumulates base0 base1 :=
    Frame.withEvents_accumulates (events := fee.events) hf feeOracles.1 feeOracles.2
  rw [Frame.burnAfterFee]
  cases priced : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply with
  | error failure =>
    simp only [Frame.fail]
    exact Frame.fail_accumulates charged
  | ok amounts =>
    rcases amounts with ⟨amount0, amount1⟩
    simp only []
    by_cases positive : amount0 > 0 ∧ amount1 > 0
    · rw [ite_eq_left positive]
      cases burned : fee.state.burnLP f.context.pair observed.liquidity with
      | error failure =>
        simp only [Frame.fail]
        exact Frame.fail_accumulates charged
      | ok result =>
        rcases result with ⟨post, events⟩
        have hburn := State.burnLP_oracles burned
        change (chargedFrame.withEvents post events).Accumulates base0 base1
        exact Frame.withEvents_accumulates (events := events) charged hburn.1 hburn.2
    · rw [ite_eq_right positive]
      exact Frame.fail_accumulates charged

theorem segment_if_accumulates {base0 base1 : B256} {p : Prop} [Decidable p]
    {thenBranch elseBranch : SegmentResult}
    (ht : thenBranch.Accumulates base0 base1)
    (he : elseBranch.Accumulates base0 base1) :
    (if p then thenBranch else elseBranch).Accumulates base0 base1 := by
  by_cases h : p <;> simp only [h] <;> assumption

theorem mintFee_segment_accumulates {base0 base1 : B256} {f : Frame}
    {observed : MintObserved} {feeTo : Adr} (hf : f.Accumulates base0 base1) :
    (match mintFee f.current.state feeTo observed.reserves.reserve0.val
        observed.reserves.reserve1.val with
      | .error failure => f.fail failure
      | .ok fee => f.mintAfterFee observed fee).Accumulates base0 base1 := by
  cases accepted : mintFee f.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val with
  | error failure =>
      exact Frame.fail_accumulates hf
  | ok fee =>
      exact Frame.mintAfterFee_accumulates hf accepted

theorem burnFee_segment_accumulates {base0 base1 : B256} {f : Frame}
    {observed : BurnObserved} {feeTo : Adr} (hf : f.Accumulates base0 base1) :
    (match mintFee f.current.state feeTo observed.locals.reserves.reserve0.val
        observed.locals.reserves.reserve1.val with
      | .error failure => f.fail failure
      | .ok fee => f.burnAfterFee observed fee).Accumulates base0 base1 := by
  cases accepted : mintFee f.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val with
  | error failure =>
      exact Frame.fail_accumulates hf
  | ok fee =>
      exact Frame.burnAfterFee_accumulates hf accepted

theorem swapCheck_segment_accumulates {base0 base1 : B256} {f : Frame}
    {locals : SwapLocals} {balance0 balance1 : B256} (hf : f.Accumulates base0 base1) :
    (match swapCheck balance0 balance1
        (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
          locals.reserves.reserve0.val locals.reserves.reserve1.val).1
        (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
          locals.reserves.reserve0.val locals.reserves.reserve1.val).2
        locals.reserves.reserve0.val locals.reserves.reserve1.val with
      | .error failure => f.fail failure
      | .ok _ => f.finishUpdated balance0 balance1 locals.reserves false
          (some (.swap f.context.sender
            (Nat.toB256 (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
              locals.reserves.reserve0.val locals.reserves.reserve1.val).1)
            (Nat.toB256 (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
              locals.reserves.reserve0.val locals.reserves.reserve1.val).2)
            locals.amount0Out locals.amount1Out locals.recipient)) []).Accumulates base0 base1 := by
  cases checked : swapCheck balance0 balance1
      (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).1
      (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).2
      locals.reserves.reserve0.val locals.reserves.reserve1.val with
  | error failure =>
      exact Frame.fail_accumulates hf
  | ok _unit =>
      exact Frame.finishUpdated_accumulates hf

theorem permitRecovery_segment_accumulates {base0 base1 : B256} {f : Frame}
    {owner spender : Adr} {value : B256} {recovered : Adr}
    (hf : f.Accumulates base0 base1) :
    (if recovered ≠ 0 ∧ recovered = owner then
        match f.current.state.approveLP f.context owner spender value with
        | .error failure => f.fail failure
        | .ok (post, events) => (f.withEvents post events).finish []
      else f.fail (.sourceGuard "UniswapV2: INVALID_SIGNATURE")).Accumulates base0 base1 := by
  by_cases valid : recovered ≠ 0 ∧ recovered = owner
  · rw [ite_eq_left valid]
    cases accepted : f.current.state.approveLP f.context owner spender value with
    | error failure =>
        exact Frame.fail_accumulates hf
    | ok result =>
        rcases result with ⟨post, events⟩
        change (f.withEvents post events).Accumulates base0 base1
        have core := State.approveLP_core accepted
        exact Frame.withEvents_core_accumulates hf core
  · rw [ite_eq_right valid]
    exact Frame.fail_accumulates hf

theorem Frame.afterSwapTransfer1_accumulates {base0 base1 : B256} {f : Frame}
    {locals : SwapLocals} (hf : f.Accumulates base0 base1) :
    (f.afterSwapTransfer1 locals).Accumulates base0 base1 := by
  rw [Frame.afterSwapTransfer1]
  by_cases hasData : locals.data.length > 0
  · rw [ite_eq_left hasData]
    exact hf
  · rw [ite_eq_right hasData]
    exact hf

theorem Frame.afterSwapTransfer0_accumulates {base0 base1 : B256} {f : Frame}
    {locals : SwapLocals} (hf : f.Accumulates base0 base1) :
    (f.afterSwapTransfer0 locals).Accumulates base0 base1 := by
  rw [Frame.afterSwapTransfer0]
  by_cases hasOutput : locals.amount1Out > 0
  · rw [ite_eq_left hasOutput]
    exact hf
  · rw [ite_eq_right hasOutput]
    exact Frame.afterSwapTransfer1_accumulates hf

theorem resumeSegment_accumulates {base0 base1 : B256} {prior : Frame}
    {request : Request} {continuation : Continuation} {result : ExternalResult}
    (hf : prior.Accumulates base0 base1) :
    (resumeSegment prior request continuation result).Accumulates base0 base1 := by
  have hframe : (prior.beginResume request).Accumulates base0 base1 := hf
  rw [resumeSegment]
  cases decoded : decodeExternal request result with
  | error failure =>
      exact Frame.fail_accumulates hframe
  | ok decodedResult =>
      cases continuation <;> cases decodedResult
      case mintFee.address => exact mintFee_segment_accumulates hframe
      case burnFee.address => exact burnFee_segment_accumulates hframe
      case swapBalance1.word => exact swapCheck_segment_accumulates hframe
      case permitRecovery.address => exact permitRecovery_segment_accumulates hframe
      case swapTransfer0.unit => exact Frame.afterSwapTransfer0_accumulates hframe
      case swapTransfer1.unit => exact Frame.afterSwapTransfer1_accumulates hframe
      all_goals
        try simp only [Frame.fail, Frame.suspend, Frame.finish, Frame.finishLocked]
        first
        | apply segment_if_accumulates
          · exact hframe
          · exact Frame.fail_accumulates hframe
        | exact ⟨hframe.1, hframe.1⟩
        | exact Frame.finishUpdated_accumulates hframe
        | change (prior.beginResume request).Accumulates base0 base1
          exact hframe

theorem Frame.finish_updates {f : Frame} {returndata : Bytes} :
    (f.finish returndata).frame.checkpoint = f.checkpoint ∧
      (f.finish returndata).frame.current.updates = f.current.updates := by
  constructor <;> rfl

theorem Frame.fail_updates {f : Frame} {failure : Failure} :
    (f.fail failure).frame.checkpoint = f.checkpoint ∧
      (f.fail failure).frame.current.updates = f.checkpoint.updates := by
  constructor <;> rfl

theorem Frame.finishLP_updates {f : Frame}
    {result : Except Failure (State × List Event)} {returndata : Bytes} :
    f.checkpoint.updates = f.current.updates →
    (f.finishLP result returndata).frame.checkpoint = f.checkpoint ∧
      (f.finishLP result returndata).frame.current.updates = f.current.updates := by
  intro checkpointUpdates
  cases result with
  | error failure => exact ⟨rfl, checkpointUpdates⟩
  | ok result => constructor <;> rfl

theorem startImmediate_updates {current : Checkpoint} {ctx : Context} {entry : Entry}
    {result : SegmentResult}
    (immediate : startImmediate current ctx entry = some result) :
    result.frame.checkpoint = current ∧ result.frame.current.updates = current.updates := by
  rw [startImmediate] at immediate
  by_cases paid : ctx.value ≠ 0
  · rw [ite_eq_left paid] at immediate
    rw [← Option.some.inj immediate]
    exact Frame.fail_updates
  · rw [ite_eq_right paid] at immediate
    cases getter : getterResult current.state entry with
    | some returndata =>
      rw [getter] at immediate
      rw [← Option.some.inj immediate]
      exact Frame.finish_updates
    | none =>
      rw [getter] at immediate
      cases entry
      case approve spender value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_updates rfl
      case transfer recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_updates rfl
      case transferFrom source recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_updates rfl
      case «initialize» token0 token1 =>
        dsimp only at immediate
        by_cases authorized : ctx.sender = current.state.factory
        · rw [ite_eq_left authorized] at immediate
          cases staticContext : ctx.isStatic with
          | true =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact Frame.fail_updates
          | false =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact Frame.finish_updates
        · rw [ite_eq_right authorized] at immediate
          rw [← Option.some.inj immediate]
          exact Frame.fail_updates
      all_goals cases immediate

theorem startImmediate_accumulates {base0 base1 : B256} {current : Checkpoint}
    {ctx : Context} {entry : Entry} {result : SegmentResult}
    (hc : current.Accumulates base0 base1)
    (immediate : startImmediate current ctx entry = some result) :
    result.Accumulates base0 base1 := by
  change result.frame.Accumulates base0 base1
  have frameFields := startImmediate_updates immediate
  have core := (startImmediate_core entry immediate).2
  have horacles := State.economicCore_oracles core
  refine ⟨?_, ?_⟩
  · rw [frameFields.1]
    exact hc
  · constructor
    · rw [horacles.1, hc.1, frameFields.2]
    · rw [horacles.2, hc.2, frameFields.2]

theorem Frame.enter_accumulates {base0 base1 : B256} {current : Checkpoint}
    {ctx : Context} {entry : Entry} (hc : current.Accumulates base0 base1) :
    (Frame.enter current ctx entry).Accumulates base0 base1 := by
  exact ⟨hc, hc⟩

theorem Frame.lock_accumulates {base0 base1 : B256} {current : Checkpoint} {locked : Frame}
    {ctx : Context} {entry : Entry} (hc : current.Accumulates base0 base1)
    (opened : (Frame.enter current ctx entry).lock = .ok locked) :
    (Frame.enter current ctx entry).checkpoint.Accumulates base0 base1 ∧
      locked.Accumulates base0 base1 := by
  have entered := Frame.enter_accumulates (ctx := ctx) (entry := entry) hc
  refine ⟨entered.1, ?_⟩
  rw [Frame.lock] at opened
  by_cases unlocked : (Frame.enter current ctx entry).current.state.unlocked = 1
  · rw [ite_eq_left unlocked] at opened
    cases staticContext : (Frame.enter current ctx entry).context.isStatic with
    | false =>
      rw [staticContext] at opened
      cases opened
      exact ⟨entered.1, Checkpoint.accumulates_restate entered.2 rfl rfl⟩
    | true =>
      rw [staticContext] at opened
      cases opened
  · rw [ite_eq_right unlocked] at opened
    cases opened

theorem startTyped_accumulates {base0 base1 : B256} {current : Checkpoint}
    {ctx : Context} {entry : Entry} (hc : current.Accumulates base0 base1) :
    (startTyped current ctx entry).Accumulates base0 base1 := by
  cases immediate : startImmediate current ctx entry with
  | some result =>
    rw [startTyped, immediate]
    exact startImmediate_accumulates hc immediate
  | none =>
    have entered := Frame.enter_accumulates (ctx := ctx) (entry := entry) hc
    cases entry
    case permit owner spender value deadline v r s =>
      simp only [startTyped, immediate, SegmentResult.Accumulates]
      by_cases timely : ctx.timestamp ≤ deadline
      · rw [ite_eq_left timely]
        cases staticContext : ctx.isStatic with
        | true =>
          simp only [ite_true, Frame.fail]
          exact Frame.fail_accumulates entered
        | false =>
          change ((Frame.enter current ctx (Entry.permit owner spender value deadline v r s)).withEvents
            (Frame.enter current ctx (Entry.permit owner spender value deadline v r s)).current.state
            []).Accumulates base0 base1
          exact Frame.withEvents_accumulates entered rfl rfl
      · rw [ite_eq_right timely]
        exact Frame.fail_accumulates entered
    all_goals
      simp only [startTyped, immediate, SegmentResult.Accumulates]
      cases opened : (Frame.enter current ctx _).lock with
      | error failure =>
        simp only [Frame.fail]
        exact Frame.fail_accumulates entered
      | ok locked =>
        have lockedAccum := Frame.lock_accumulates hc opened
        simp only [Frame.suspend]
        repeat' first | split
        all_goals first
          | exact lockedAccum.2
          | exact Frame.fail_accumulates lockedAccum.2

mutual

theorem drive_accumulates (fuel : Nat) {base0 base1 : B256}
    {segment : SegmentResult} {transcript : Transcript}
    (hs : segment.Accumulates base0 base1) :
    (drive fuel segment transcript).frame.Accumulates base0 base1 := by
  cases fuel with
  | zero => exact hs
  | succ fuel =>
    cases segment with
    | finished frame returndata => exact hs
    | failed frame failure => cases failure <;> exact hs
    | suspended frame request continuation =>
      cases transcript with
      | done => exact hs
      | foreignLog emitter topics data tail => exact hs
      | invoke sender value isStatic entry child tail => exact hs
      | next result turns tail =>
        rw [drive]
        cases missing : request.requiresCode && !result.codeExists with
        | true =>
          exact drive_accumulates fuel (resumeSegment_accumulates hs)
        | false =>
          have turnsAccum := driveTurns_accumulates fuel frame request 0 turns hs
          cases complete : (driveTurns fuel frame request 0 turns).complete with
          | false =>
            simp only [Bool.false_eq_true, complete, ite_false]
            exact turnsAccum
          | true =>
            have settledAccum :
                (frame.settleExternal fuel request result turns).Accumulates base0 base1 := by
              rw [Frame.settleExternal]
              cases successful : result.success with
              | true =>
                simp only [ite_true]
                exact turnsAccum
              | false =>
                exact ⟨turnsAccum.1, hs.2⟩
            have resumed := drive_accumulates fuel
              (segment := resumeSegment (frame.settleExternal fuel request result turns)
                request continuation result) (transcript := tail)
              (resumeSegment_accumulates (prior := frame.settleExternal fuel request result turns)
                (request := request) (continuation := continuation) (result := result) settledAccum)
            simpa only [missing, Bool.false_eq_true, complete, ite_true, ite_false,
              Frame.settleExternal] using resumed

theorem driveTurns_accumulates (fuel : Nat) {base0 base1 : B256}
    (frame : Frame) (request : Request) (turn : Nat) (turns : Transcript)
    (hf : frame.Accumulates base0 base1) :
    (driveTurns fuel frame request turn turns).frame.Accumulates base0 base1 := by
  cases fuel with
  | zero => exact hf
  | succ fuel =>
    cases turns with
    | done => exact hf
    | next result children tail => exact hf
    | foreignLog emitter topics data tail =>
      rw [driveTurns]
      cases staticExternal : externalStatic frame request with
      | true =>
        simp only [ite_true]
        exact hf
      | false =>
        let logged : Frame := { frame with current :=
          { frame.current with logs := frame.current.logs ++
            [.foreign { invocation := frame.context.invocation, site := request.site, turn := turn }
              emitter topics data] } }
        have loggedAccum : logged.Accumulates base0 base1 := by
          exact ⟨hf.1, hf.2⟩
        exact driveTurns_accumulates fuel logged request (turn + 1) tail loggedAccum
    | invoke sender value isStatic entry transcript tail =>
      let context := childContext frame request turn sender value isStatic
      have childAccum := drive_accumulates fuel
        (segment := startTyped frame.current context entry) (transcript := transcript)
        (startTyped_accumulates (current := frame.current) (ctx := context) (entry := entry)
          hf.2)
      let child := drive fuel (startTyped frame.current context entry) transcript
      let settled : Frame := { frame with current := child.frame.current }
      have settledAccum : settled.Accumulates base0 base1 := by
        exact ⟨hf.1, childAccum.2⟩
      have tailAccum := driveTurns_accumulates fuel settled request (turn + 1) tail settledAccum
      rw [driveTurns]
      cases childStatus : (drive fuel (startTyped frame.current context entry) transcript).status with
      | incomplete => exact hf
      | success returndata =>
        simpa only [childStatus, settled, child, context] using tailAccum
      | failed failure =>
        simpa only [childStatus, settled, child, context] using tailAccum

end

theorem runTyped_oracle_accumulates {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript} :
    (runTyped st ctx entry transcript).frame.current.state.price0CumulativeLast =
        oracleFold0 st.price0CumulativeLast
          (runTyped st ctx entry transcript).frame.current.updates ∧
      (runTyped st ctx entry transcript).frame.current.state.price1CumulativeLast =
        oracleFold1 st.price1CumulativeLast
          (runTyped st ctx entry transcript).frame.current.updates := by
  have initial :
      ({ state := st, logs := [], updates := [] } : Checkpoint).Accumulates
        st.price0CumulativeLast st.price1CumulativeLast :=
    runTyped_initial_accumulates st
  have started := startTyped_accumulates (current :=
      ({ state := st, logs := [], updates := [] } : Checkpoint))
    (ctx := ctx) (entry := entry) initial
  have driven := drive_accumulates (transcript.work + 2)
    (segment := startTyped ({ state := st, logs := [], updates := [] } : Checkpoint) ctx entry)
    (transcript := transcript) started
  simpa only [Checkpoint.Accumulates, runTyped] using driven.2

end Blanc.Lift.UniswapV2Pair
