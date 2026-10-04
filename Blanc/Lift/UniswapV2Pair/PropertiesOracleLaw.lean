import Blanc.Lift.UniswapV2Pair.PropertiesOracle

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Logical correctness of an `OracleUpdate`'s timing and accumulator increments. -/
def OracleUpdate.Lawful (u : OracleUpdate) : Prop :=
  u.elapsed = (u.timestamp.toNat % 2 ^ 32 + 2 ^ 32 - u.oldTimestamp.toNat) % 2 ^ 32 ∧
  u.increment0 =
    (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
      (u.oldReserve1 * 2 ^ 112 / u.oldReserve0) * u.elapsed
    else 0) ∧
  u.increment1 =
    (if u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0 then
      (u.oldReserve0 * 2 ^ 112 / u.oldReserve1) * u.elapsed
    else 0)

/-- Every oracle update emitted by a successful `State.update` is lawful. -/
theorem State.update_oracle_lawful {st post : State} {ctx : Context}
    {balance0 balance1 : B256} {oldReserve0 oldReserve1 : Nat}
    {event : Event} {update : OracleUpdate}
    (accepted : st.update ctx balance0 balance1 oldReserve0 oldReserve1 =
      .ok (post, event, update)) :
    update.Lawful := by
  rw [State.update] at accepted
  by_cases bound0 : balance0.toNat < 2 ^ 112
  · rw [dite_eq_left bound0] at accepted
    by_cases bound1 : balance1.toNat < 2 ^ 112
    · rw [dite_eq_left bound1] at accepted
      cases (Except.ok.inj accepted)
      exact ⟨rfl, rfl, rfl⟩
    · rw [dite_eq_right bound1] at accepted
      cases accepted
  · rw [dite_eq_right bound0] at accepted
    cases accepted

theorem State.update_blockTimestampLast {st post : State} {ctx : Context}
    {balance0 balance1 : B256} {oldReserve0 oldReserve1 : Nat}
    {event : Event} {update : OracleUpdate}
    (accepted : st.update ctx balance0 balance1 oldReserve0 oldReserve1 =
      .ok (post, event, update)) :
    post.blockTimestampLast = UInt32.ofNat (update.timestamp.toNat % 2 ^ 32) ∧
      update.oldTimestamp = st.blockTimestampLast := by
  rw [State.update] at accepted
  by_cases bound0 : balance0.toNat < 2 ^ 112
  · rw [dite_eq_left bound0] at accepted
    by_cases bound1 : balance1.toNat < 2 ^ 112
    · rw [dite_eq_left bound1] at accepted
      cases (Except.ok.inj accepted)
      exact ⟨rfl, rfl⟩
    · rw [dite_eq_right bound1] at accepted
      cases accepted
  · rw [dite_eq_right bound0] at accepted
    cases accepted

/-- A chronological chain of oracle updates from an initial timestamp to a final timestamp. -/
def OracleTimestampChain (start finish : UInt32) : List TaggedOracleUpdate → Prop
  | [] => finish = start
  | tagged :: updates =>
      tagged.update.oldTimestamp = start ∧
        OracleTimestampChain (UInt32.ofNat (tagged.update.timestamp.toNat % 2 ^ 32)) finish updates

theorem OracleTimestampChain_append (start mid finish : UInt32)
    (left right : List TaggedOracleUpdate)
    (hleft : OracleTimestampChain start mid left)
    (hright : OracleTimestampChain mid finish right) :
    OracleTimestampChain start finish (left ++ right) := by
  induction left generalizing start with
  | nil =>
      change mid = start at hleft
      rw [← hleft]
      exact hright
  | cons tagged tail ih =>
      change tagged.update.oldTimestamp = start ∧
        OracleTimestampChain (UInt32.ofNat (tagged.update.timestamp.toNat % 2 ^ 32)) mid tail at hleft
      change tagged.update.oldTimestamp = start ∧
        OracleTimestampChain (UInt32.ofNat (tagged.update.timestamp.toNat % 2 ^ 32)) finish (tail ++ right)
      exact ⟨hleft.1, ih _ hleft.2⟩

theorem OracleTimestampChain_snoc (start mid finish : UInt32)
    (left : List TaggedOracleUpdate) (tagged : TaggedOracleUpdate)
    (hleft : OracleTimestampChain start mid left)
    (hstep : tagged.update.oldTimestamp = mid)
    (hend : finish = UInt32.ofNat (tagged.update.timestamp.toNat % 2 ^ 32)) :
    OracleTimestampChain start finish (left ++ [tagged]) :=
  OracleTimestampChain_append start mid finish left [tagged] hleft ⟨hstep, hend⟩

theorem lawful_updates_snoc {left : List TaggedOracleUpdate} {tagged : TaggedOracleUpdate}
    (hleft : ∀ u ∈ left, OracleUpdate.Lawful u.update)
    (htagged : OracleUpdate.Lawful tagged.update) :
    ∀ u ∈ left ++ [tagged], OracleUpdate.Lawful u.update := by
  intro u hu
  rw [List.mem_append] at hu
  cases hu with
  | inl hl => exact hleft u hl
  | inr hr =>
      rw [List.mem_singleton] at hr
      subst hr
      exact htagged

def Checkpoint.Lawful (baseTimestamp : UInt32) (c : Checkpoint) : Prop :=
  (∀ u ∈ c.updates, u.update.Lawful) ∧
    OracleTimestampChain baseTimestamp c.state.blockTimestampLast c.updates

def Frame.Lawful (baseTimestamp : UInt32) (f : Frame) : Prop :=
  f.checkpoint.Lawful baseTimestamp ∧ f.current.Lawful baseTimestamp

def SegmentResult.Lawful (baseTimestamp : UInt32) (s : SegmentResult) : Prop :=
  s.frame.Lawful baseTimestamp

theorem Checkpoint.lawful_restate {baseTimestamp : UInt32} {c : Checkpoint}
    {post : State} (hc : c.Lawful baseTimestamp)
    (hts : post.blockTimestampLast = c.state.blockTimestampLast) :
    ({ c with state := post }).Lawful baseTimestamp :=
  ⟨hc.1, by change OracleTimestampChain baseTimestamp post.blockTimestampLast c.updates; rw [hts]; exact hc.2⟩

theorem State.economicCore_blockTimestampLast {st post : State}
    (hcore : post.economicCore = st.economicCore) :
    post.blockTimestampLast = st.blockTimestampLast :=
  congrArg (fun core => core.2.2.1) hcore

theorem State.mintLP_blockTimestampLast {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (accepted : st.mintLP recipient value = .ok (post, events)) :
    post.blockTimestampLast = st.blockTimestampLast := by
  rw [State.mintLP] at accepted
  by_cases supplyBound : st.totalSupply.toNat + value.toNat < 2 ^ 256
  · rw [ite_eq_left supplyBound] at accepted
    by_cases balanceBound : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256
    · rw [ite_eq_left balanceBound] at accepted
      have stateEq := congrArg (fun result : State × List Event => result.1)
        (Except.ok.inj accepted)
      dsimp only at stateEq
      exact (congrArg (fun state : State => state.blockTimestampLast) stateEq).symm
    · rw [ite_eq_right balanceBound] at accepted
      cases accepted
  · rw [ite_eq_right supplyBound] at accepted
    cases accepted

theorem State.burnLP_blockTimestampLast {st post : State} {source : Adr} {value : B256}
    {events : List Event} (accepted : st.burnLP source value = .ok (post, events)) :
    post.blockTimestampLast = st.blockTimestampLast := by
  rw [State.burnLP] at accepted
  by_cases balanceCovered : value ≤ st.balanceOf source
  · rw [ite_eq_left balanceCovered] at accepted
    by_cases supplyCovered : value ≤ st.totalSupply
    · rw [ite_eq_left supplyCovered] at accepted
      have stateEq := congrArg (fun result : State × List Event => result.1)
        (Except.ok.inj accepted)
      dsimp only at stateEq
      exact (congrArg (fun state : State => state.blockTimestampLast) stateEq).symm
    · rw [ite_eq_right supplyCovered] at accepted
      cases accepted
  · rw [ite_eq_right balanceCovered] at accepted
    cases accepted

theorem mintFee_blockTimestampLast {st : State} {feeTo : Adr} {reserve0 reserve1 : Nat}
    {fee : FeeResult}
    (accepted : mintFee st feeTo reserve0 reserve1 = .ok fee) :
    fee.state.blockTimestampLast = st.blockTimestampLast := by
  rw [mintFee] at accepted
  by_cases feeOff : feeTo = 0
  · rw [ite_eq_left feeOff] at accepted
    cases (Except.ok.inj accepted)
    rfl
  · rw [ite_eq_right feeOff] at accepted
    by_cases noLast : st.kLast = 0
    · rw [ite_eq_left noLast] at accepted
      cases (Except.ok.inj accepted)
      rfl
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
                have hts := State.mintLP_blockTimestampLast minted
                cases feeEq
                exact hts
              · rw [ite_eq_right positiveFee] at accepted
                cases (Except.ok.inj accepted)
                rfl
            · rw [ite_eq_right denominatorBound] at accepted
              cases accepted
          · rw [ite_eq_right scaledRootBound] at accepted
            cases accepted
        · rw [ite_eq_right numeratorBound] at accepted
          cases accepted
      · rw [ite_eq_right growing] at accepted
        cases (Except.ok.inj accepted)
        rfl

theorem Frame.withEvents_lawful {baseTimestamp : UInt32} {f : Frame}
    {post : State} {events : List Event} (hf : f.Lawful baseTimestamp)
    (hts : post.blockTimestampLast = f.current.state.blockTimestampLast) :
    (f.withEvents post events).Lawful baseTimestamp :=
  ⟨hf.1, Checkpoint.lawful_restate hf.2 hts⟩

theorem Frame.withEvents_core_lawful {baseTimestamp : UInt32} {f : Frame}
    {post : State} {events : List Event} (hf : f.Lawful baseTimestamp)
    (hcore : post.economicCore = f.current.state.economicCore) :
    (f.withEvents post events).Lawful baseTimestamp :=
  Frame.withEvents_lawful hf (State.economicCore_blockTimestampLast hcore)

theorem Frame.fail_lawful {baseTimestamp : UInt32} {f : Frame} {failure : Failure}
    (hf : f.Lawful baseTimestamp) :
    (f.fail failure).frame.Lawful baseTimestamp :=
  ⟨hf.1, hf.1⟩

theorem Frame.withUpdate_lawful {baseTimestamp : UInt32} {f : Frame}
    {post : State} {event : Event} {update : OracleUpdate}
    (hf : f.Lawful baseTimestamp)
    (hlawful : update.Lawful)
    (hold : update.oldTimestamp = f.current.state.blockTimestampLast)
    (hend : post.blockTimestampLast = UInt32.ofNat (update.timestamp.toNat % 2 ^ 32)) :
    (f.withUpdate post event update).Lawful baseTimestamp := by
  refine ⟨hf.1, ?_⟩
  constructor
  · change ∀ u ∈ f.current.updates ++ [{ origin := f.origin, update := update }], u.update.Lawful
    exact lawful_updates_snoc hf.2.1 hlawful
  · change OracleTimestampChain baseTimestamp post.blockTimestampLast
      (f.current.updates ++ [{ origin := f.origin, update := update }])
    exact OracleTimestampChain_snoc baseTimestamp f.current.state.blockTimestampLast
      post.blockTimestampLast f.current.updates { origin := f.origin, update := update }
      hf.2.2 hold hend

theorem Frame.withUpdate_from_update_lawful {baseTimestamp : UInt32} {f : Frame}
    {ctx : Context} {balance0 balance1 : B256} {oldReserve0 oldReserve1 : Nat}
    {post : State} {event : Event} {update : OracleUpdate}
    (hf : f.Lawful baseTimestamp)
    (accepted : f.current.state.update ctx balance0 balance1 oldReserve0 oldReserve1 =
      .ok (post, event, update)) :
    (f.withUpdate post event update).Lawful baseTimestamp := by
  have hlaw := State.update_oracle_lawful accepted
  have hts := State.update_blockTimestampLast accepted
  exact Frame.withUpdate_lawful hf hlaw hts.2 hts.1

theorem Frame.finishUpdated_lawful {baseTimestamp : UInt32} {f : Frame}
    {balance0 balance1 : B256} {reserves : CachedReserves} {feeOn : Bool}
    {lastEvent : Option Event} {returndata : Bytes}
    (hf : f.Lawful baseTimestamp) :
    (f.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata).frame.Lawful
      baseTimestamp := by
  rw [Frame.finishUpdated]
  cases accepted : f.current.state.update f.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure => exact Frame.fail_lawful hf
  | ok result =>
      rcases result with ⟨post, event, update⟩
      have updated := Frame.withUpdate_from_update_lawful hf accepted
      cases feeOn with
      | false =>
          cases lastEvent with
          | none => exact updated
          | some extra => exact Frame.withEvents_lawful updated rfl
      | true =>
          cases lastEvent with
          | none => exact Frame.withEvents_lawful updated rfl
          | some extra => exact Frame.withEvents_lawful updated rfl

theorem Frame.mintAfterFee_lawful {baseTimestamp : UInt32} {f : Frame}
    {observed : MintObserved} {fee : FeeResult} {feeTo : Adr}
    (hf : f.Lawful baseTimestamp)
    (hfee : mintFee f.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val = .ok fee) :
    (f.mintAfterFee observed fee).frame.Lawful baseTimestamp := by
  have feeTs := mintFee_blockTimestampLast hfee
  let chargedFrame := f.withEvents fee.state fee.events
  have charged : chargedFrame.Lawful baseTimestamp :=
    Frame.withEvents_lawful (events := fee.events) hf feeTs
  rw [Frame.mintAfterFee]
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure =>
    simp only [Frame.fail]
    exact Frame.fail_lawful charged
  | ok liquidity =>
    simp only []
    cases initial : (if fee.state.totalSupply = 0 then
        fee.state.mintLP 0 1000 else .ok (fee.state, [])) with
    | error failure =>
      simp only [Frame.fail]
      exact Frame.fail_lawful charged
    | ok result =>
      rcases result with ⟨postMinimum, minimumEvents⟩
      simp only []
      have minimum :
          (chargedFrame.withEvents postMinimum minimumEvents).Lawful baseTimestamp := by
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
            have hmint := State.mintLP_blockTimestampLast minted
            exact Frame.withEvents_lawful charged hmint
        · rw [ite_eq_right zero] at initial
          cases initial
          exact Frame.withEvents_lawful charged rfl
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive]
        cases minted : postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure =>
          simp only [Frame.fail]
          exact Frame.fail_lawful minimum
        | ok result =>
          rcases result with ⟨post, events⟩
          have hmint := State.mintLP_blockTimestampLast minted
          have issued := Frame.withEvents_lawful (events := events) minimum hmint
          exact Frame.finishUpdated_lawful issued
      · rw [ite_eq_right positive]
        exact Frame.fail_lawful minimum

theorem Frame.burnAfterFee_lawful {baseTimestamp : UInt32} {f : Frame}
    {observed : BurnObserved} {fee : FeeResult} {feeTo : Adr}
    (hf : f.Lawful baseTimestamp)
    (hfee : mintFee f.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val = .ok fee) :
    (f.burnAfterFee observed fee).frame.Lawful baseTimestamp := by
  have feeTs := mintFee_blockTimestampLast hfee
  let chargedFrame := f.withEvents fee.state fee.events
  have charged : chargedFrame.Lawful baseTimestamp :=
    Frame.withEvents_lawful (events := fee.events) hf feeTs
  rw [Frame.burnAfterFee]
  cases priced : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply with
  | error failure =>
    simp only [Frame.fail]
    exact Frame.fail_lawful charged
  | ok amounts =>
    rcases amounts with ⟨amount0, amount1⟩
    simp only []
    by_cases positive : amount0 > 0 ∧ amount1 > 0
    · rw [ite_eq_left positive]
      cases burned : fee.state.burnLP f.context.pair observed.liquidity with
      | error failure =>
        simp only [Frame.fail]
        exact Frame.fail_lawful charged
      | ok result =>
        rcases result with ⟨post, events⟩
        have hburn := State.burnLP_blockTimestampLast burned
        change (chargedFrame.withEvents post events).Lawful baseTimestamp
        exact Frame.withEvents_lawful (events := events) charged hburn
    · rw [ite_eq_right positive]
      exact Frame.fail_lawful charged

theorem segment_if_lawful {baseTimestamp : UInt32} {p : Prop} [Decidable p]
    {thenBranch elseBranch : SegmentResult}
    (ht : thenBranch.Lawful baseTimestamp) (he : elseBranch.Lawful baseTimestamp) :
    (if p then thenBranch else elseBranch).Lawful baseTimestamp := by
  by_cases h : p <;> simp only [h, ite_true, ite_false] <;> assumption

theorem mintFee_segment_lawful {baseTimestamp : UInt32} {f : Frame}
    {observed : MintObserved} {feeTo : Adr} (hf : f.Lawful baseTimestamp) :
    (match mintFee f.current.state feeTo observed.reserves.reserve0.val
        observed.reserves.reserve1.val with
      | .error failure => f.fail failure
      | .ok fee => f.mintAfterFee observed fee).Lawful baseTimestamp := by
  cases accepted : mintFee f.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val with
  | error failure => exact Frame.fail_lawful hf
  | ok fee => exact Frame.mintAfterFee_lawful hf accepted

theorem burnFee_segment_lawful {baseTimestamp : UInt32} {f : Frame}
    {observed : BurnObserved} {feeTo : Adr} (hf : f.Lawful baseTimestamp) :
    (match mintFee f.current.state feeTo observed.locals.reserves.reserve0.val
        observed.locals.reserves.reserve1.val with
      | .error failure => f.fail failure
      | .ok fee => f.burnAfterFee observed fee).Lawful baseTimestamp := by
  cases accepted : mintFee f.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val with
  | error failure => exact Frame.fail_lawful hf
  | ok fee => exact Frame.burnAfterFee_lawful hf accepted

theorem swapCheck_segment_lawful {baseTimestamp : UInt32} {f : Frame}
    {locals : SwapLocals} {balance0 balance1 : B256} (hf : f.Lawful baseTimestamp) :
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
            locals.amount0Out locals.amount1Out locals.recipient)) []).Lawful baseTimestamp := by
  cases checked : swapCheck balance0 balance1
      (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).1
      (swapInputs balance0 balance1 locals.amount0Out locals.amount1Out
        locals.reserves.reserve0.val locals.reserves.reserve1.val).2
      locals.reserves.reserve0.val locals.reserves.reserve1.val with
  | error failure => exact Frame.fail_lawful hf
  | ok _unit => exact Frame.finishUpdated_lawful hf

theorem permitRecovery_segment_lawful {baseTimestamp : UInt32} {f : Frame}
    {owner spender : Adr} {value : B256} {recovered : Adr}
    (hf : f.Lawful baseTimestamp) :
    (if recovered ≠ 0 ∧ recovered = owner then
        match f.current.state.approveLP f.context owner spender value with
        | .error failure => f.fail failure
        | .ok (post, events) => (f.withEvents post events).finish []
      else f.fail (.sourceGuard "UniswapV2: INVALID_SIGNATURE")).Lawful baseTimestamp := by
  by_cases valid : recovered ≠ 0 ∧ recovered = owner
  · rw [ite_eq_left valid]
    cases accepted : f.current.state.approveLP f.context owner spender value with
    | error failure => exact Frame.fail_lawful hf
    | ok result =>
        rcases result with ⟨post, events⟩
        change (f.withEvents post events).Lawful baseTimestamp
        have core := State.approveLP_core accepted
        exact Frame.withEvents_core_lawful hf core
  · rw [ite_eq_right valid]
    exact Frame.fail_lawful hf

theorem Frame.afterSwapTransfer1_lawful {baseTimestamp : UInt32} {f : Frame}
    {locals : SwapLocals} (hf : f.Lawful baseTimestamp) :
    (f.afterSwapTransfer1 locals).Lawful baseTimestamp := by
  rw [Frame.afterSwapTransfer1]
  by_cases hasData : locals.data.length > 0 <;> simp only [hasData, ite_true, ite_false] <;> exact hf

theorem Frame.afterSwapTransfer0_lawful {baseTimestamp : UInt32} {f : Frame}
    {locals : SwapLocals} (hf : f.Lawful baseTimestamp) :
    (f.afterSwapTransfer0 locals).Lawful baseTimestamp := by
  rw [Frame.afterSwapTransfer0]
  by_cases hasOutput : locals.amount1Out > 0
  · rw [ite_eq_left hasOutput]
    exact hf
  · rw [ite_eq_right hasOutput]
    exact Frame.afterSwapTransfer1_lawful hf

theorem resumeSegment_lawful {baseTimestamp : UInt32} {prior : Frame}
    {request : Request} {continuation : Continuation} {result : ExternalResult}
    (hf : prior.Lawful baseTimestamp) :
    (resumeSegment prior request continuation result).Lawful baseTimestamp := by
  have hframe : (prior.beginResume request).Lawful baseTimestamp := hf
  rw [resumeSegment]
  cases decoded : decodeExternal request result with
  | error failure => exact Frame.fail_lawful hframe
  | ok decodedResult =>
      cases continuation <;> cases decodedResult
      case mintFee.address => exact mintFee_segment_lawful hframe
      case burnFee.address => exact burnFee_segment_lawful hframe
      case swapBalance1.word => exact swapCheck_segment_lawful hframe
      case permitRecovery.address => exact permitRecovery_segment_lawful hframe
      case swapTransfer0.unit => exact Frame.afterSwapTransfer0_lawful hframe
      case swapTransfer1.unit => exact Frame.afterSwapTransfer1_lawful hframe
      all_goals
        try simp only [Frame.fail, Frame.suspend, Frame.finish, Frame.finishLocked]
        first
        | apply segment_if_lawful
          · exact hframe
          · exact Frame.fail_lawful hframe
        | exact ⟨hframe.1, hframe.1⟩
        | exact Frame.finishUpdated_lawful hframe
        | change (prior.beginResume request).Lawful baseTimestamp
          exact hframe

theorem startImmediate_lawful {baseTimestamp : UInt32} {current : Checkpoint}
    {ctx : Context} {entry : Entry} {result : SegmentResult}
    (hc : current.Lawful baseTimestamp)
    (immediate : startImmediate current ctx entry = some result) :
    result.Lawful baseTimestamp := by
  change result.frame.Lawful baseTimestamp
  have frameFields := startImmediate_updates immediate
  have core := (startImmediate_core entry immediate).2
  have hts := State.economicCore_blockTimestampLast core
  refine ⟨?_, ?_⟩
  · rw [frameFields.1]
    exact hc
  · constructor
    · rw [frameFields.2]
      exact hc.1
    · rw [hts, frameFields.2]
      exact hc.2

theorem Frame.enter_lawful {baseTimestamp : UInt32} {current : Checkpoint}
    {ctx : Context} {entry : Entry} (hc : current.Lawful baseTimestamp) :
    (Frame.enter current ctx entry).Lawful baseTimestamp :=
  ⟨hc, hc⟩

theorem Frame.lock_lawful {baseTimestamp : UInt32} {current : Checkpoint} {locked : Frame}
    {ctx : Context} {entry : Entry} (hc : current.Lawful baseTimestamp)
    (opened : (Frame.enter current ctx entry).lock = .ok locked) :
    (Frame.enter current ctx entry).checkpoint.Lawful baseTimestamp ∧
      locked.Lawful baseTimestamp := by
  have entered := Frame.enter_lawful (ctx := ctx) (entry := entry) hc
  refine ⟨entered.1, ?_⟩
  rw [Frame.lock] at opened
  by_cases unlocked : (Frame.enter current ctx entry).current.state.unlocked = 1
  · rw [ite_eq_left unlocked] at opened
    cases staticContext : (Frame.enter current ctx entry).context.isStatic with
    | false =>
      rw [staticContext] at opened
      cases opened
      exact ⟨entered.1, Checkpoint.lawful_restate entered.2 rfl⟩
    | true =>
      rw [staticContext] at opened
      cases opened
  · rw [ite_eq_right unlocked] at opened
    cases opened

theorem startTyped_lawful {baseTimestamp : UInt32} {current : Checkpoint}
    {ctx : Context} {entry : Entry} (hc : current.Lawful baseTimestamp) :
    (startTyped current ctx entry).Lawful baseTimestamp := by
  cases immediate : startImmediate current ctx entry with
  | some result =>
    rw [startTyped, immediate]
    exact startImmediate_lawful hc immediate
  | none =>
    have entered := Frame.enter_lawful (ctx := ctx) (entry := entry) hc
    cases entry
    case permit owner spender value deadline v r s =>
      simp only [startTyped, immediate, SegmentResult.Lawful]
      by_cases timely : ctx.timestamp ≤ deadline
      · rw [ite_eq_left timely]
        cases staticContext : ctx.isStatic with
        | true =>
          simp only [ite_true, Frame.fail]
          exact Frame.fail_lawful entered
        | false =>
          change ((Frame.enter current ctx (Entry.permit owner spender value deadline v r s)).withEvents
            (Frame.enter current ctx (Entry.permit owner spender value deadline v r s)).current.state
            []).Lawful baseTimestamp
          exact Frame.withEvents_lawful entered rfl
      · rw [ite_eq_right timely]
        exact Frame.fail_lawful entered
    all_goals
      simp only [startTyped, immediate, SegmentResult.Lawful]
      cases opened : (Frame.enter current ctx _).lock with
      | error failure =>
        simp only [Frame.fail]
        exact Frame.fail_lawful entered
      | ok locked =>
        have lockedLaw := Frame.lock_lawful hc opened
        simp only [Frame.suspend]
        repeat' first | split
        all_goals first
          | exact lockedLaw.2
          | exact Frame.fail_lawful lockedLaw.2

mutual

theorem drive_lawful (fuel : Nat) {baseTimestamp : UInt32}
    {segment : SegmentResult} {transcript : Transcript}
    (hs : segment.Lawful baseTimestamp) :
    (drive fuel segment transcript).frame.Lawful baseTimestamp := by
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
          exact drive_lawful fuel (resumeSegment_lawful hs)
        | false =>
          have turnsLaw := driveTurns_lawful fuel frame request 0 turns hs
          cases complete : (driveTurns fuel frame request 0 turns).complete with
          | false =>
            simp only [Bool.false_eq_true, complete, ite_false]
            exact turnsLaw
          | true =>
            have settledLaw :
                (frame.settleExternal fuel request result turns).Lawful baseTimestamp := by
              rw [Frame.settleExternal]
              cases successful : result.success with
              | true =>
                simp only [ite_true]
                exact turnsLaw
              | false =>
                exact ⟨turnsLaw.1, hs.2⟩
            have resumed := drive_lawful fuel
              (segment := resumeSegment (frame.settleExternal fuel request result turns)
                request continuation result) (transcript := tail)
              (resumeSegment_lawful (prior := frame.settleExternal fuel request result turns)
                (request := request) (continuation := continuation) (result := result) settledLaw)
            simpa only [missing, Bool.false_eq_true, complete, ite_true, ite_false,
              Frame.settleExternal] using resumed

theorem driveTurns_lawful (fuel : Nat) {baseTimestamp : UInt32}
    (frame : Frame) (request : Request) (turn : Nat) (turns : Transcript)
    (hf : frame.Lawful baseTimestamp) :
    (driveTurns fuel frame request turn turns).frame.Lawful baseTimestamp := by
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
        have loggedLaw : logged.Lawful baseTimestamp := by
          exact ⟨hf.1, hf.2⟩
        exact driveTurns_lawful fuel logged request (turn + 1) tail loggedLaw
    | invoke sender value isStatic entry transcript tail =>
      let context := childContext frame request turn sender value isStatic
      have childLaw := drive_lawful fuel
        (segment := startTyped frame.current context entry) (transcript := transcript)
        (startTyped_lawful (current := frame.current) (ctx := context) (entry := entry)
          hf.2)
      let child := drive fuel (startTyped frame.current context entry) transcript
      let settled : Frame := { frame with current := child.frame.current }
      have settledLaw : settled.Lawful baseTimestamp := by
        exact ⟨hf.1, childLaw.2⟩
      have tailLaw := driveTurns_lawful fuel settled request (turn + 1) tail settledLaw
      rw [driveTurns]
      cases childStatus : (drive fuel (startTyped frame.current context entry) transcript).status with
      | incomplete => exact hf
      | success returndata =>
        simpa only [childStatus, settled, child, context] using tailLaw
      | failed failure =>
        simpa only [childStatus, settled, child, context] using tailLaw

end

theorem runTyped_initial_lawful (st : State) :
    ({ state := st, logs := [], updates := [] } : Checkpoint).Lawful st.blockTimestampLast := by
  refine ⟨?_, rfl⟩
  intro u hu
  cases hu

/-- Headline: typed execution guarantees lawful oracle increments, chaining timestamps, and accumulators. -/
theorem runTyped_oracle_law {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript} :
    (∀ u ∈ (runTyped st ctx entry transcript).frame.current.updates, u.update.Lawful) ∧
      OracleTimestampChain st.blockTimestampLast
        (runTyped st ctx entry transcript).frame.current.state.blockTimestampLast
        (runTyped st ctx entry transcript).frame.current.updates ∧
      (runTyped st ctx entry transcript).frame.current.state.price0CumulativeLast =
        oracleFold0 st.price0CumulativeLast
          (runTyped st ctx entry transcript).frame.current.updates ∧
      (runTyped st ctx entry transcript).frame.current.state.price1CumulativeLast =
        oracleFold1 st.price1CumulativeLast
          (runTyped st ctx entry transcript).frame.current.updates := by
  have initial :
      ({ state := st, logs := [], updates := [] } : Checkpoint).Lawful st.blockTimestampLast :=
    runTyped_initial_lawful st
  have started := startTyped_lawful (current :=
      ({ state := st, logs := [], updates := [] } : Checkpoint))
    (ctx := ctx) (entry := entry) initial
  have driven := drive_lawful (transcript.work + 2)
    (segment := startTyped ({ state := st, logs := [], updates := [] } : Checkpoint) ctx entry)
    (transcript := transcript) started
  have accumulates := @runTyped_oracle_accumulates st ctx entry transcript
  exact ⟨driven.2.1, driven.2.2, accumulates.1, accumulates.2⟩

