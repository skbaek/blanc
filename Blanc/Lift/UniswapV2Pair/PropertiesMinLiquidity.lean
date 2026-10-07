import Blanc.Lift.UniswapV2Pair.SourceReplay

/-!
# The `MINIMUM_LIQUIDITY` supply floor, model side

The first mint locks `MINIMUM_LIQUIDITY = 1000` LP at address zero (`Frame.mintAfterFee`). Address
zero's balance can only fall by a `transfer` whose caller is zero, a `transferFrom` whose owner is
zero (which needs an allowance address zero granted, by an `approve` whose caller is zero: `permit`
already refuses a zero recovered owner), or a `burn` of the Pair's own balance when the Pair is
address zero. So, with no zero caller and a nonzero Pair, the supply never returns below 1000 once
positive.

* `State.SupplyFloor`: the supply is zero or address zero holds at least 1000 LP, and address zero has
  granted no allowance (with the ledger, `balanceOf 0 ≤ totalSupply` turns it into
  `1000 ≤ totalSupply` whenever the supply is positive);
* `Transcript.CallersNonzero`, `SourceInvocation.CallersNonzero`: no invocation and no nested
  re-entered child invocation (`Transcript.invoke`) of the transcript has caller zero;
* `runTyped_supplyFloor`: every `runTyped` result keeps the floor through every owned segment, every
  nested committed child and every rollback; with the lock held at entry it keeps the lock;
* `SourceReplay.supplyFloor`: along a replay from a floored state, every outermost boundary is floored,
  and an invocation entered with positive supply leaves at least 1000.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-! ## The invariant -/

/-- `MINIMUM_LIQUIDITY` is held at address zero. -/
def State.MinimumLocked (st : State) : Prop :=
  1000 ≤ (st.balanceOf 0).toNat

/-- Address zero has granted no allowance. -/
def State.ZeroAllowances (st : State) : Prop :=
  ∀ spender, st.allowance 0 spender = 0

/-- **The supply floor.**  The supply is zero or `MINIMUM_LIQUIDITY` is held at address zero, and
address zero has granted no allowance. -/
def State.SupplyFloor (st : State) : Prop :=
  (st.totalSupply.toNat = 0 ∨ st.MinimumLocked) ∧ st.ZeroAllowances

private structure FloorOn (locked : Prop) (supply zeroBalance : B256)
    (zeroAllowance : Adr → B256) : Prop where
  floor : supply.toNat = 0 ∨ 1000 ≤ zeroBalance.toNat
  zero : ∀ spender, zeroAllowance spender = 0
  held : locked → 1000 ≤ zeroBalance.toNat

/-- The carried form: the floor, and the lock whenever `locked` holds at entry.  It reads only the
supply, address zero's balance and address zero's allowance row. -/
private def State.FloorAt (locked : Prop) (st : State) : Prop :=
  FloorOn locked st.totalSupply (st.balanceOf 0) (st.allowance 0)

private theorem State.FloorAt.of_locked {locked : Prop} {st : State} (held : st.MinimumLocked)
    (zero : st.ZeroAllowances) : st.FloorAt locked :=
  ⟨Or.inr held, zero, fun _ => held⟩

private theorem B256.eq_zero_of_toNat {x : B256} (h : x.toNat = 0) : x = 0 :=
  B256.toNat_inj _ _ (by rw [h, B256.toNat_zero])

private theorem B256.eq_zero_of_le_zero {x y : B256} (zero : y = 0) (h : x ≤ y) : x = 0 := by
  have := B256.toNat_le_toNat h
  rw [zero, B256.toNat_zero] at this
  exact B256.eq_zero_of_toNat (Nat.le_zero.mp this)

/-! ## State-level steps -/

/-- The floor depends only on the supply, address zero's balance and address zero's allowances. -/
private theorem State.FloorAt.transport {locked : Prop} {st post : State}
    (supply : post.totalSupply = st.totalSupply)
    (balance : (st.balanceOf 0).toNat ≤ (post.balanceOf 0).toNat)
    (allowance : post.allowance 0 = st.allowance 0) (floor : st.FloorAt locked) :
    post.FloorAt locked := by
  refine ⟨?_, fun x => ?_, fun h => ?_⟩
  · rw [supply]
    exact floor.1.imp id fun held => le_trans held balance
  · show post.allowance 0 x = 0
    rw [allowance]
    exact floor.2 x
  · exact le_trans (floor.3 h) balance

private theorem State.mintLP_fields {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (accepted : st.mintLP recipient value = .ok (post, events)) :
    post.balanceOf = Blanc.ledgerCredit st.balanceOf recipient value ∧
      post.allowance = st.allowance ∧ B256.Nof (st.balanceOf recipient) value := by
  rw [State.mintLP] at accepted
  by_cases supplyBound : st.totalSupply.toNat + value.toNat < 2 ^ 256
  · rw [ite_eq_left supplyBound] at accepted
    by_cases balanceBound : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256
    · rw [ite_eq_left balanceBound] at accepted
      rw [← (Prod.mk.inj (Except.ok.inj accepted)).1]
      exact ⟨rfl, rfl, balanceBound⟩
    · rw [ite_eq_right balanceBound] at accepted
      cases accepted
  · rw [ite_eq_right supplyBound] at accepted
    cases accepted

/-- A checked mint keeps the lock, or establishes it when it mints at least 1000 to address zero. -/
private theorem State.mintLP_locked {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (held : st.MinimumLocked ∨ (recipient = 0 ∧ 1000 ≤ value.toNat))
    (zero : st.ZeroAllowances) (accepted : st.mintLP recipient value = .ok (post, events)) :
    post.MinimumLocked ∧ post.ZeroAllowances := by
  obtain ⟨balances, allowances, nof⟩ := State.mintLP_fields accepted
  refine ⟨?_, fun x => ?_⟩
  · show 1000 ≤ (post.balanceOf 0).toNat
    rw [balances]
    by_cases toZero : recipient = 0
    · subst toZero
      rw [Blanc.ledgerCredit_self, B256.toNat_add_eq_of_nof _ _ nof]
      have : 1000 ≤ (st.balanceOf 0).toNat ∨ 1000 ≤ value.toNat := held.imp id And.right
      omega
    · rw [Blanc.ledgerCredit_ne value (Ne.symm toZero)]
      exact held.resolve_right fun h => toZero h.1
  · show post.allowance 0 x = 0
    rw [allowances]
    exact zero x

private theorem State.burnLP_floor {locked : Prop} {st post : State} {source : Adr} {value : B256}
    {events : List Event} (floor : st.FloorAt locked) (nonzero : source ≠ 0)
    (accepted : st.burnLP source value = .ok (post, events)) : post.FloorAt locked := by
  have supply := (State.burnLP_supply accepted).2
  rw [State.burnLP] at accepted
  by_cases covered : value ≤ st.balanceOf source
  · rw [ite_eq_left covered] at accepted
    by_cases supplyCovered : value ≤ st.totalSupply
    · rw [ite_eq_left supplyCovered] at accepted
      have postEq := (Prod.mk.inj (Except.ok.inj accepted)).1
      have balance : post.balanceOf 0 = st.balanceOf 0 := by
        rw [← postEq]
        exact Blanc.ledgerDebit_ne value (Ne.symm nonzero)
      have allowance : post.allowance = st.allowance := by rw [← postEq]
      refine ⟨?_, fun x => ?_, fun h => ?_⟩
      · rcases floor.1 with zeroSupply | held
        · left
          omega
        · right
          show 1000 ≤ (post.balanceOf 0).toNat
          rw [balance]
          exact held
      · show post.allowance 0 x = 0
        rw [allowance]
        exact floor.2 x
      · show 1000 ≤ (post.balanceOf 0).toNat
        rw [balance]
        exact floor.3 h
    · rw [ite_eq_right supplyCovered] at accepted
      cases accepted
  · rw [ite_eq_right covered] at accepted
    cases accepted

private theorem State.transferLP_floor {locked : Prop} {st : State} {ctx : Context}
    {source recipient : Adr} {value : B256} {post : State} {events : List Event}
    (floor : st.FloorAt locked) (guard : source ≠ 0 ∨ value = 0)
    (accepted : st.transferLP ctx source recipient value = .ok (post, events)) :
    post.FloorAt locked := by
  rw [State.transferLP] at accepted
  by_cases covered : value ≤ st.balanceOf source
  · rw [ite_eq_left covered] at accepted
    cases staticContext : ctx.isStatic with
    | true =>
      rw [staticContext] at accepted
      cases accepted
    | false =>
      rw [staticContext] at accepted
      dsimp only at accepted
      by_cases credit :
          (Blanc.ledgerDebit st.balanceOf source value recipient).toNat + value.toNat < 2 ^ 256
      · rw [ite_eq_left credit] at accepted
        have postEq := (Prod.mk.inj (Except.ok.inj accepted)).1
        have debited : (st.balanceOf 0).toNat ≤
            (Blanc.ledgerDebit st.balanceOf source value 0).toNat := by
          by_cases fromZero : source = 0
          · subst fromZero
            have zero := guard.resolve_left (fun h => h rfl)
            subst zero
            rw [Blanc.ledgerDebit_self, B256.toNat_sub_eq_of_le _ _ covered, B256.toNat_zero]
            omega
          · rw [Blanc.ledgerDebit_ne value (Ne.symm fromZero)]
        have credited : (Blanc.ledgerDebit st.balanceOf source value 0).toNat ≤
            (Blanc.ledgerCredit (Blanc.ledgerDebit st.balanceOf source value) recipient value
              0).toNat := by
          by_cases toZero : recipient = 0
          · subst toZero
            rw [Blanc.ledgerCredit_self, B256.toNat_add_eq_of_nof _ _ credit]
            omega
          · rw [Blanc.ledgerCredit_ne value (Ne.symm toZero)]
        refine State.FloorAt.transport (by rw [← postEq]) ?_ (by rw [← postEq]) floor
        rw [← postEq]
        exact le_trans debited credited
      · rw [ite_eq_right credit] at accepted
        cases accepted
  · rw [ite_eq_right covered] at accepted
    cases accepted

private theorem State.transferFromLP_floor {locked : Prop} {st : State} {ctx : Context}
    {source recipient : Adr} {value : B256} {post : State} {events : List Event}
    (floor : st.FloorAt locked)
    (accepted : st.transferFromLP ctx source recipient value = .ok (post, events)) :
    post.FloorAt locked := by
  rw [State.transferFromLP] at accepted
  by_cases unlimited : st.allowance source ctx.sender = B256.max
  · rw [ite_eq_left unlimited] at accepted
    refine State.transferLP_floor floor (Or.inl ?_) accepted
    rintro rfl
    rw [floor.2 ctx.sender] at unlimited
    exact absurd unlimited (by decide)
  · rw [ite_eq_right unlimited] at accepted
    by_cases covered : value ≤ st.allowance source ctx.sender
    · rw [ite_eq_left covered] at accepted
      cases staticContext : ctx.isStatic with
      | true =>
        rw [staticContext] at accepted
        cases accepted
      | false =>
        rw [staticContext] at accepted
        let reduced : State := { st with allowance := Function.update st.allowance source (Function.update (st.allowance source) ctx.sender (st.allowance source ctx.sender - value)) }
        have zeroRow : reduced.allowance 0 = st.allowance 0 ∨ value = 0 ∧ source = 0 := by
          by_cases fromZero : source = 0
          · right
            exact ⟨B256.eq_zero_of_le_zero (fromZero ▸ floor.2 ctx.sender) covered, fromZero⟩
          · left
            show Function.update st.allowance source _ 0 = st.allowance 0
            rw [Function.update_of_ne (Ne.symm fromZero)]
        have reducedFloor : reduced.FloorAt locked := by
          refine ⟨floor.1, fun x => ?_, floor.3⟩
          rcases zeroRow with same | ⟨rfl, rfl⟩
          · show reduced.allowance 0 x = 0
            rw [same]
            exact floor.2 x
          · show Function.update st.allowance 0 (Function.update (st.allowance 0) ctx.sender
              (st.allowance 0 ctx.sender - 0)) 0 x = 0
            rw [Function.update_self]
            by_cases spender : x = ctx.sender
            · subst spender
              rw [Function.update_self]
              apply B256.eq_zero_of_toNat
              rw [B256.toNat_sub_eq_of_le _ _ covered, floor.2 ctx.sender, B256.toNat_zero]
            · rw [Function.update_of_ne spender]
              exact floor.2 x
        have guard : source ≠ 0 ∨ value = 0 := by
          by_cases fromZero : source = 0
          · exact Or.inr (B256.eq_zero_of_le_zero (fromZero ▸ floor.2 ctx.sender) covered)
          · exact Or.inl fromZero
        exact State.transferLP_floor (st := reduced) reducedFloor guard accepted
    · rw [ite_eq_right covered] at accepted
      cases accepted

private theorem State.approveLP_floor {locked : Prop} {st : State} {ctx : Context}
    {owner spender : Adr} {value : B256} {post : State} {events : List Event}
    (floor : st.FloorAt locked) (nonzero : owner ≠ 0)
    (accepted : st.approveLP ctx owner spender value = .ok (post, events)) :
    post.FloorAt locked := by
  rw [State.approveLP] at accepted
  cases staticContext : ctx.isStatic with
  | true =>
    rw [staticContext] at accepted
    cases accepted
  | false =>
    rw [staticContext] at accepted
    have postEq := (Prod.mk.inj (Except.ok.inj accepted)).1
    refine State.FloorAt.transport (by rw [← postEq]) (by rw [← postEq]) ?_ floor
    rw [← postEq]
    exact Function.update_of_ne (Ne.symm nonzero) _ _

private theorem State.update_floor {locked : Prop} {st post : State} {ctx : Context}
    {balance0 balance1 : B256} {reserve0 reserve1 : Nat} {event : Event} {update : OracleUpdate}
    (floor : st.FloorAt locked)
    (accepted : st.update ctx balance0 balance1 reserve0 reserve1 = .ok (post, event, update)) :
    post.FloorAt locked := by
  have balances := State.update_ledger accepted
  have supply := (State.update_supply_reserves accepted).1
  have allowance : post.allowance = st.allowance := by
    rw [State.update] at accepted
    by_cases bound0 : balance0.toNat < 2 ^ 112
    · rw [dite_eq_left bound0] at accepted
      by_cases bound1 : balance1.toNat < 2 ^ 112
      · rw [dite_eq_left bound1] at accepted
        rw [← (Prod.mk.inj (Except.ok.inj accepted)).1]
      · rw [dite_eq_right bound1] at accepted
        cases accepted
    · rw [dite_eq_right bound0] at accepted
      cases accepted
  exact State.FloorAt.transport supply (by rw [balances]) (by rw [allowance]) floor

/-- The protocol-fee mint keeps the floor: it mints only from a positive supply. -/
private theorem mintFee_floor {locked : Prop} {st : State} {feeTo : Adr}
    {reserve0 reserve1 : Nat} {fee : FeeResult} (floor : st.FloorAt locked)
    (accepted : mintFee st feeTo reserve0 reserve1 = .ok fee) : fee.state.FloorAt locked := by
  rw [mintFee] at accepted
  by_cases feeOff : feeTo = 0
  · rw [ite_eq_left feeOff] at accepted
    rw [← Except.ok.inj accepted]
    exact floor
  · rw [ite_eq_right feeOff] at accepted
    by_cases noLast : st.kLast = 0
    · rw [ite_eq_left noLast] at accepted
      rw [← Except.ok.inj accepted]
      exact floor
    · rw [ite_eq_right noLast] at accepted
      by_cases growing : Nat.sqrt st.kLast.toNat < Nat.sqrt (reserve0 * reserve1)
      · rw [ite_eq_left growing] at accepted
        by_cases numeratorBound :
            st.totalSupply.toNat * (Nat.sqrt (reserve0 * reserve1) - Nat.sqrt st.kLast.toNat) <
              2 ^ 256
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
                rw [← Except.ok.inj feeEq]
                have supplyPositive : st.totalSupply.toNat ≠ 0 := by
                  intro zero
                  rw [zero, Nat.zero_mul, Nat.zero_div] at positiveFee
                  exact absurd positiveFee (lt_irrefl 0)
                have held : st.MinimumLocked := floor.1.resolve_left supplyPositive
                have postHeld := State.mintLP_locked (Or.inl held) floor.2 minted
                exact State.FloorAt.of_locked postHeld.1 postHeld.2
              · rw [ite_eq_right positiveFee] at accepted
                rw [← Except.ok.inj accepted]
                exact floor
            · rw [ite_eq_right denominatorBound] at accepted
              cases accepted
          · rw [ite_eq_right scaledRootBound] at accepted
            cases accepted
        · rw [ite_eq_right numeratorBound] at accepted
          cases accepted
      · rw [ite_eq_right growing] at accepted
        rw [← Except.ok.inj accepted]
        exact floor


/-! ## Owned segments -/

/-- The invariant on a frame: a nonzero Pair, and the floor on its rollback checkpoint and its
current state. -/
private def Frame.FloorAt (locked : Prop) (frame : Frame) : Prop :=
  frame.context.pair ≠ 0 ∧ frame.checkpoint.state.FloorAt locked ∧
    frame.current.state.FloorAt locked

private theorem Frame.fail_floor {locked : Prop} {frame : Frame} (floor : frame.FloorAt locked)
    (failure : Failure) : (frame.fail failure).frame.FloorAt locked :=
  ⟨floor.1, floor.2.1, floor.2.1⟩

private theorem Frame.withEvents_floor {locked : Prop} {frame : Frame} {post : State}
    {events : List Event} (floor : frame.FloorAt locked) (postFloor : post.FloorAt locked) :
    (frame.withEvents post events).FloorAt locked :=
  ⟨floor.1, floor.2.1, postFloor⟩

private theorem Frame.finishLP_floor {locked : Prop} {frame : Frame} (floor : frame.FloorAt locked)
    {result : Except Failure (State × List Event)} (returndata : Bytes)
    (successful : ∀ post events, result = .ok (post, events) → post.FloorAt locked) :
    (frame.finishLP result returndata).frame.FloorAt locked := by
  cases result with
  | error failure => exact Frame.fail_floor floor failure
  | ok postEvents =>
    rcases postEvents with ⟨post, events⟩
    exact ⟨floor.1, floor.2.1, successful post events rfl⟩

private theorem Frame.finishUpdated_floor {locked : Prop} {frame : Frame}
    (floor : frame.FloorAt locked) (balance0 balance1 : B256) (reserves : CachedReserves)
    (feeOn : Bool) (lastEvent : Option Event) (returndata : Bytes) :
    (frame.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata).frame.FloorAt
      locked := by
  rw [Frame.finishUpdated]
  cases updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure => exact Frame.fail_floor floor failure
  | ok result =>
    rcases result with ⟨post, event, update⟩
    have postFloor := State.update_floor floor.2.2 updated
    cases feeOn <;> cases lastEvent <;> exact ⟨floor.1, floor.2.1, postFloor⟩

/-- The mint's `MINIMUM_LIQUIDITY` lock at address zero establishes the floor for the recipient mint. -/
private theorem Frame.mintAfterFee_floor {locked : Prop} {frame : Frame}
    (floor : frame.FloorAt locked) (observed : MintObserved) {fee : FeeResult}
    (feeFloor : fee.state.FloorAt locked) :
    (frame.mintAfterFee observed fee).frame.FloorAt locked := by
  have charged : (frame.withEvents fee.state fee.events).FloorAt locked :=
    Frame.withEvents_floor floor feeFloor
  rw [Frame.mintAfterFee]
  cases amount : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure => exact Frame.fail_floor charged failure
  | ok liquidity =>
    dsimp only
    have initialFloor : ∀ post events,
        (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000 else .ok (fee.state, [])) =
          .ok (post, events) → post.MinimumLocked ∧ post.ZeroAllowances := by
      intro post events initial
      by_cases zero : fee.state.totalSupply = 0
      · rw [ite_eq_left zero] at initial
        exact State.mintLP_locked (Or.inr ⟨rfl, by decide⟩) feeFloor.2 initial
      · rw [ite_eq_right zero] at initial
        rw [← (Prod.mk.inj (Except.ok.inj initial)).1]
        refine ⟨feeFloor.1.resolve_left fun natZero => zero ?_, feeFloor.2⟩
        exact B256.eq_zero_of_toNat natZero
    generalize (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000
      else Except.ok (fee.state, [])) = initial at initialFloor ⊢
    cases initial with
    | error failure => exact Frame.fail_floor charged failure
    | ok postEvents =>
      rcases postEvents with ⟨postMinimum, minimumEvents⟩
      have minimumHeld := initialFloor postMinimum minimumEvents rfl
      have minimum : (((frame.withEvents fee.state fee.events).withEvents postMinimum
          minimumEvents)).FloorAt locked :=
        Frame.withEvents_floor charged (State.FloorAt.of_locked minimumHeld.1 minimumHeld.2)
      dsimp only
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive]
        cases minted : postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure => exact Frame.fail_floor minimum failure
        | ok postEvents =>
          rcases postEvents with ⟨post, events⟩
          dsimp only
          have postHeld := State.mintLP_locked (Or.inl minimumHeld.1) minimumHeld.2 minted
          exact Frame.finishUpdated_floor
            (Frame.withEvents_floor minimum (State.FloorAt.of_locked postHeld.1 postHeld.2))
            _ _ _ _ _ _
      · rw [ite_eq_right positive]
        exact Frame.fail_floor minimum _

/-- The burn debits the Pair's own balance, never address zero's. -/
private theorem Frame.burnAfterFee_floor {locked : Prop} {frame : Frame}
    (floor : frame.FloorAt locked) (observed : BurnObserved) {fee : FeeResult}
    (feeFloor : fee.state.FloorAt locked) :
    (frame.burnAfterFee observed fee).frame.FloorAt locked := by
  have charged : (frame.withEvents fee.state fee.events).FloorAt locked :=
    Frame.withEvents_floor floor feeFloor
  rw [Frame.burnAfterFee]
  split
  · exact Frame.fail_floor charged _
  · split
    · split
      · exact Frame.fail_floor charged _
      · rename_i post events burned
        exact ⟨floor.1, floor.2.1, State.burnLP_floor feeFloor floor.1 burned⟩
    · exact Frame.fail_floor charged _

/-- The immediate entries keep the invariant: `approve` and `transfer` act for a nonzero caller. -/
private theorem startImmediate_floor {locked : Prop} {current : Checkpoint}
    (floor : current.state.FloorAt locked) {ctx : Context} (sender : ctx.sender ≠ 0)
    (pair : ctx.pair ≠ 0) (entry : Entry) {result : SegmentResult}
    (immediate : startImmediate current ctx entry = some result) :
    result.frame.FloorAt locked := by
  have entered : (Frame.enter current ctx entry).FloorAt locked := ⟨pair, floor, floor⟩
  rw [startImmediate] at immediate
  by_cases paid : ctx.value ≠ 0
  · rw [ite_eq_left paid] at immediate
    rw [← Option.some.inj immediate]
    exact Frame.fail_floor entered _
  · rw [ite_eq_right paid] at immediate
    cases getter : getterResult current.state entry with
    | some returndata =>
      rw [getter] at immediate
      rw [← Option.some.inj immediate]
      exact entered
    | none =>
      rw [getter] at immediate
      cases entry
      case approve spender value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_floor entered _ fun _ _ accepted =>
          State.approveLP_floor floor sender accepted
      case transfer recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_floor entered _ fun _ _ accepted =>
          State.transferLP_floor floor (Or.inl sender) accepted
      case transferFrom source recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_floor entered _ fun _ _ accepted =>
          State.transferFromLP_floor floor accepted
      case «initialize» token0 token1 =>
        dsimp only at immediate
        by_cases authorized : ctx.sender = current.state.factory
        · rw [ite_eq_left authorized] at immediate
          cases staticContext : ctx.isStatic with
          | true =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact Frame.fail_floor entered _
          | false =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact entered
        · rw [ite_eq_right authorized] at immediate
          rw [← Option.some.inj immediate]
          exact Frame.fail_floor entered _
      all_goals cases immediate

private theorem Frame.lock_floor {locked : Prop} {frame lockedFrame : Frame}
    (floor : frame.FloorAt locked) (locking : frame.lock = .ok lockedFrame) :
    lockedFrame.FloorAt locked := by
  rw [Frame.lock] at locking
  by_cases unlocked : frame.current.state.unlocked = 1
  · rw [ite_eq_left unlocked] at locking
    cases staticContext : frame.context.isStatic with
    | true =>
      rw [staticContext] at locking
      cases locking
    | false =>
      rw [staticContext] at locking
      rw [← Except.ok.inj locking]
      exact floor
  · rw [ite_eq_right unlocked] at locking
    cases locking

/-- Every first owned segment of all 27 entries keeps the invariant. -/
private theorem startTyped_floor {locked : Prop} {current : Checkpoint}
    (floor : current.state.FloorAt locked) {ctx : Context} (sender : ctx.sender ≠ 0)
    (pair : ctx.pair ≠ 0) (entry : Entry) : (startTyped current ctx entry).frame.FloorAt locked := by
  have entered : (Frame.enter current ctx entry).FloorAt locked := ⟨pair, floor, floor⟩
  cases immediate : startImmediate current ctx entry with
  | some result =>
    rw [startTyped, immediate]
    exact startImmediate_floor floor sender pair entry immediate
  | none =>
    rw [startTyped, immediate]
    cases entry
    case permit owner spender value deadline v r s =>
      dsimp only
      by_cases timely : ctx.timestamp ≤ deadline
      · rw [ite_eq_left timely]
        cases staticContext : ctx.isStatic with
        | true => exact Frame.fail_floor entered _
        | false => exact entered
      · rw [ite_eq_right timely]
        exact Frame.fail_floor entered _
    all_goals
      dsimp only
      split
      · exact Frame.fail_floor entered _
      · rename_i lockedFrame locking
        have lockedFloor := Frame.lock_floor entered locking
        repeat' split
        all_goals first
          | exact lockedFloor
          | exact Frame.fail_floor lockedFloor _

private theorem Frame.afterSwapTransfer1_floor {locked : Prop} {frame : Frame}
    (floor : frame.FloorAt locked) (locals : SwapLocals) :
    (frame.afterSwapTransfer1 locals).frame.FloorAt locked := by
  rw [Frame.afterSwapTransfer1]
  split
  · exact floor
  · exact floor

private theorem Frame.afterSwapTransfer0_floor {locked : Prop} {frame : Frame}
    (floor : frame.FloorAt locked) (locals : SwapLocals) :
    (frame.afterSwapTransfer0 locals).frame.FloorAt locked := by
  rw [Frame.afterSwapTransfer0]
  split
  · exact floor
  · exact Frame.afterSwapTransfer1_floor floor locals

/-- Every resumed owned segment keeps the invariant; the permit approval is guarded by a nonzero
recovered owner. -/
private theorem resumeSegment_floor {locked : Prop} {prior : Frame} (floor : prior.FloorAt locked)
    (request : Request) (continuation : Continuation) (result : ExternalResult) :
    (resumeSegment prior request continuation result).frame.FloorAt locked := by
  have resumed : (prior.beginResume request).FloorAt locked := floor
  rw [resumeSegment]
  cases decodeExternal request result with
  | error failure => exact Frame.fail_floor resumed failure
  | ok decoded =>
    dsimp only
    cases continuation <;> cases decoded
    all_goals
      try dsimp only
      repeat' split
    all_goals first
      | exact resumed
      | exact Frame.fail_floor resumed _
      | exact Frame.afterSwapTransfer0_floor resumed _
      | exact Frame.afterSwapTransfer1_floor resumed _
      | exact Frame.finishUpdated_floor resumed _ _ _ _ _ _
      | (rename_i guard
         exact Frame.finishLP_floor resumed _ fun _ _ accepted =>
          State.approveLP_floor resumed.2.2 (guard.2 ▸ guard.1) accepted)
      | (rename_i fee accepted
         first
          | exact Frame.mintAfterFee_floor resumed _ (mintFee_floor resumed.2.2 accepted)
          | exact Frame.burnAfterFee_floor resumed _ (mintFee_floor resumed.2.2 accepted))

/-! ## The driver -/

/-- **No zero caller in a transcript.**  Every nested re-entered child invocation
(`Transcript.invoke`), at every depth, has a nonzero caller. -/
def Transcript.CallersNonzero : Transcript → Prop
  | .done => True
  | .next _ turns tail => turns.CallersNonzero ∧ tail.CallersNonzero
  | .foreignLog _ _ _ tail => tail.CallersNonzero
  | .invoke sender _ _ _ transcript tail =>
    sender ≠ 0 ∧ transcript.CallersNonzero ∧ tail.CallersNonzero

/-- **No zero caller in an invocation**: neither the invocation itself nor any nested re-entered
child of its transcript has caller zero. -/
def SourceInvocation.CallersNonzero (inv : SourceInvocation) : Prop :=
  inv.context.sender ≠ 0 ∧ inv.transcript.CallersNonzero

/-- The finite driver keeps the invariant, jointly for `drive` and `driveTurns`, through every
nested committed child (started with its transcript's nonzero caller) and every rollback. -/
private theorem drive_floor {locked : Prop} (fuel : Nat) :
    (∀ segment transcript, transcript.CallersNonzero → segment.frame.FloorAt locked →
      (drive fuel segment transcript).frame.FloorAt locked) ∧
      ∀ frame request turn turns, turns.CallersNonzero → frame.FloorAt locked →
        (driveTurns fuel frame request turn turns).frame.FloorAt locked := by
  induction fuel with
  | zero =>
    refine ⟨fun segment transcript _ floor => ?_, fun frame request turn turns _ floor => ?_⟩
    · rw [drive]
      exact floor
    · rw [driveTurns]
      exact floor
  | succ fuel ih =>
    refine ⟨fun segment transcript callers floor => ?_,
      fun frame request turn turns callers floor => ?_⟩
    · cases segment with
      | finished frame returndata => exact floor
      | failed frame failure => cases failure <;> exact floor
      | suspended frame request continuation =>
        cases transcript with
        | done => exact floor
        | foreignLog emitter topics data tail => exact floor
        | invoke sender value isStatic entry child tail => exact floor
        | next result turns tail =>
          obtain ⟨turnsCallers, tailCallers⟩ := callers
          rw [drive]
          dsimp only
          have executed := ih.2 frame request 0 turns turnsCallers floor
          split
          · exact ih.1 _ tail tailCallers (resumeSegment_floor floor request continuation result)
          · split
            · let executedFrame := (driveTurns fuel frame request 0 turns).frame
              have settled : (if result.success = true then executedFrame
                  else { executedFrame with current := frame.current }).FloorAt locked := by
                split
                · exact executed
                · exact ⟨executed.1, executed.2.1, floor.2.2⟩
              exact ih.1 _ tail tailCallers
                (resumeSegment_floor settled request continuation result)
            · exact executed
    · cases turns with
      | done =>
        rw [driveTurns]
        exact floor
      | next result children tail =>
        rw [driveTurns]
        exact floor
      | foreignLog emitter topics data tail =>
        rw [driveTurns]
        dsimp only
        split
        · exact floor
        · exact ih.2 _ request (turn + 1) tail callers floor
      | invoke sender value isStatic entry transcript tail =>
        obtain ⟨senderNonzero, childCallers, tailCallers⟩ := callers
        rw [driveTurns]
        dsimp only
        have child := ih.1 (startTyped frame.current
          (childContext frame request turn sender value isStatic) entry) transcript childCallers
          (startTyped_floor (ctx := childContext frame request turn sender value isStatic)
            floor.2.2 senderNonzero floor.1 entry)
        split
        · exact floor
        · exact ih.2 _ request (turn + 1) tail tailCallers ⟨floor.1, floor.2.1, child.2.2⟩

private theorem runTyped_floorAt {locked : Prop} {st : State} (floor : st.FloorAt locked)
    {ctx : Context} {entry : Entry} {transcript : Transcript} (sender : ctx.sender ≠ 0)
    (pair : ctx.pair ≠ 0) (callers : transcript.CallersNonzero) :
    (runTyped st ctx entry transcript).frame.current.state.FloorAt locked :=
  ((drive_floor _).1 _ transcript callers
    (startTyped_floor (current := { state := st, logs := [], updates := [] }) floor sender pair
      entry)).2.2

/-- **The supply floor through one invocation (model).**  For every entry and every finite
transcript, with a nonzero Pair and no zero caller at any depth, every `runTyped` result keeps the
floor, and keeps `MINIMUM_LIQUIDITY` at address zero whenever it was held at entry. -/
theorem runTyped_supplyFloor {st : State} {ctx : Context} {entry : Entry}
    {transcript : Transcript} (floor : st.SupplyFloor) (sender : ctx.sender ≠ 0)
    (pair : ctx.pair ≠ 0) (callers : transcript.CallersNonzero) :
    (runTyped st ctx entry transcript).frame.current.state.SupplyFloor ∧
      (st.MinimumLocked → (runTyped st ctx entry transcript).frame.current.state.MinimumLocked) := by
  have kept := runTyped_floorAt (locked := False) (entry := entry) ⟨floor.1, floor.2, False.elim⟩
    sender pair callers
  refine ⟨⟨kept.1, kept.2⟩, fun held => ?_⟩
  exact (runTyped_floorAt (locked := True) ⟨floor.1, floor.2, fun _ => held⟩ sender pair
    callers).3 trivial

/-! ## The replay -/

/-- **The supply floor along a replay (model).**  From a floored state with the ledger, if every
invocation has a nonzero Pair and no zero caller at any depth, the final state and both ends of every
outermost replay boundary are floored, and an invocation entered with positive supply leaves at least
`MINIMUM_LIQUIDITY` of supply. -/
theorem SourceReplay.supplyFloor {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) (floor : st.SupplyFloor) (ledger : st.Ledger)
    (pairs : ∀ inv ∈ invs, inv.context.pair ≠ 0)
    (callers : ∀ inv ∈ invs, inv.CallersNonzero) :
    finish.SupplyFloor ∧
      ∀ before after, (before, after) ∈ sourceReplayEdges st invs →
        before.SupplyFloor ∧ after.SupplyFloor ∧
          (0 < before.totalSupply.toNat → 1000 ≤ after.totalSupply.toNat) := by
  induction replay with
  | nil st =>
    exact ⟨floor, fun _ _ member => by cases member⟩
  | @cons st finish inv rest out bytes consumed successful tail ih =>
    have runEq : inv.run st = out := (runTyped_of_exact consumed).1
    have here := callers inv List.mem_cons_self
    have step := runTyped_supplyFloor (entry := inv.entry) floor here.1
      (pairs inv List.mem_cons_self) here.2
    have stepLedger := (runTyped_ledger ledger inv.context inv.entry inv.transcript).2
    change (inv.run st).frame.current.state.SupplyFloor ∧
      (st.MinimumLocked → (inv.run st).frame.current.state.MinimumLocked) at step
    change (inv.run st).frame.current.state.Ledger at stepLedger
    rw [runEq] at step stepLedger
    obtain ⟨finishFloor, edges⟩ := ih step.1 stepLedger
      (fun inv' member => pairs inv' (List.mem_cons_of_mem _ member))
      (fun inv' member => callers inv' (List.mem_cons_of_mem _ member))
    refine ⟨finishFloor, fun before after member => ?_⟩
    rw [sourceReplayEdges, runEq, List.mem_cons] at member
    rcases member with same | later
    · cases same
      refine ⟨floor, step.1, fun positive => ?_⟩
      have held : st.MinimumLocked := floor.1.resolve_left (Nat.pos_iff_ne_zero.mp positive)
      rw [← stepLedger.sum_eq]
      exact le_trans (step.2 held) Blanc.le_sum
    · exact edges before after later

end Blanc.Lift.UniswapV2Pair
