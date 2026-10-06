import Blanc.Lift.UniswapV2Pair.Properties
import Blanc.Lift.UniswapV2Pair.Consumption
import Blanc.Lift.LedgerFootprint

/-!
# U7: the LP-token ledger, model side

`State.LedgerOn keys st` is the ledger invariant over a finite key footprint: `keys` is
duplicate-free, names every account with a nonzero `balanceOf` (address 0 and `feeTo` included
whenever they hold LP tokens), and `Σ_{k ∈ keys} balanceOf k = totalSupply`.  Because a
duplicate-free covering footprint carries the full address sum (`Blanc.footprintSum_eq_sum`), the
invariant is transported as the footprint-free `State.Ledger` (`sum balanceOf = totalSupply`) and
read back over any covering footprint (`State.Ledger.on`), in particular over the entry footprint
extended by the keys a step touches (`State.LedgerOn.extend`).

* `State.initialized_ledgerOn`: the empty footprint after `initialize`;
* `startTyped_ledger`, `resumeSegment_ledger`: every owned segment of all 27 entries, including
  mint's `MINIMUM_LIQUIDITY` lock at address 0 and the protocol-fee mint to `feeTo`, keeps the
  invariant on both its checkpoint and its current state;
* `drive_ledger`: the finite driver, through nested committed children (`Transcript.invoke`) and the
  rollback of failed calls and segments;
* `runTyped_ledger`, `runTyped_ledgerOn`: the headline for every `runTyped` result;
* `ExactConsumes.ledger`: the same through the relational exact consumption (`Consumption.lean`)
  that the history lift consumes;
* `footprintSum_dup_breaks_ledger`: the statement control, a duplicated key breaks the equation.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-! ## The invariant -/

/-- Footprint-free transport form: the full address sum of the LP ledger is the supply. -/
def State.Ledger (st : State) : Prop :=
  Blanc.SumBacked st.balanceOf st.totalSupply

theorem State.Ledger.sum_eq {st : State} (ledger : st.Ledger) :
    Blanc.sum st.balanceOf = st.totalSupply.toNat :=
  Blanc.SumBacked.eq ledger

theorem State.Ledger.intro {st : State} (backed : Blanc.sum st.balanceOf = st.totalSupply.toNat) :
    st.Ledger :=
  Blanc.SumBacked.mk backed

/-- **The U7 ledger invariant over a finite key footprint.** -/
structure State.LedgerOn (keys : List Adr) (st : State) : Prop where
  nodup : keys.Nodup
  covers : Blanc.FootprintCovers keys st.balanceOf
  backed : Blanc.footprintSum keys st.balanceOf = st.totalSupply.toNat

theorem State.LedgerOn.ledger {keys : List Adr} {st : State} (on : st.LedgerOn keys) :
    st.Ledger :=
  State.Ledger.intro ((Blanc.footprintSum_eq_sum on.nodup on.covers).symm.trans on.backed)

/-- The transported invariant is read over any duplicate-free covering footprint. -/
theorem State.Ledger.on {keys : List Adr} {st : State} (ledger : st.Ledger) (nodup : keys.Nodup)
    (covers : Blanc.FootprintCovers keys st.balanceOf) : st.LedgerOn keys :=
  ⟨nodup, covers, (Blanc.footprintSum_eq_sum nodup covers).trans ledger.sum_eq⟩

/-- **Footprint extension.**  A step that keeps the ledger and moves only rows in `touched`
keeps the invariant over the entry footprint extended by `touched`. -/
theorem State.LedgerOn.extend {keys touched : List Adr} {pre post : State}
    (on : pre.LedgerOn keys) (ledger : post.Ledger)
    (frame : ∀ account, account ∉ touched → post.balanceOf account = pre.balanceOf account) :
    post.LedgerOn (keys ++ touched).dedup :=
  ledger.on (List.nodup_dedup _) (on.covers.extend frame)

/-- After `initialize` (`initializedState`, `Creation/DeployInit.lean`, unfolds to this state). -/
theorem State.initialized_ledgerOn (factory : Adr) (domain : B256) (token0 token1 : Adr) :
    ({ State.empty factory domain with token0 := token0, token1 := token1 } : State).LedgerOn [] :=
  ⟨List.nodup_nil, fun _ nonzero => absurd rfl nonzero, B256.toNat_zero.symm⟩

/-- **Control (U7).**  With one nonzero key duplicated in the footprint, the footprint sum no
longer equals the supply. -/
theorem footprintSum_dup_breaks_ledger {keys : List Adr} {st : State} {key : Adr}
    (on : st.LedgerOn keys) (nonzero : st.balanceOf key ≠ 0) :
    Blanc.footprintSum (key :: keys) st.balanceOf ≠ st.totalSupply.toNat := by
  rw [← on.ledger.sum_eq]
  exact Blanc.footprintSum_dup_ne_sum on.nodup on.covers nonzero

/-! ## State-level steps -/

theorem State.mintLP_preserves {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (ledger : st.Ledger)
    (accepted : st.mintLP recipient value = .ok (post, events)) : post.Ledger := by
  have nof : B256.Nof (st.balanceOf recipient) value := by
    rw [State.mintLP] at accepted
    by_cases supplyBound : st.totalSupply.toNat + value.toNat < 2 ^ 256
    · rw [ite_eq_left supplyBound] at accepted
      by_cases balanceBound : (st.balanceOf recipient).toNat + value.toNat < 2 ^ 256
      · exact balanceBound
      · rw [ite_eq_right balanceBound] at accepted
        cases accepted
    · rw [ite_eq_right supplyBound] at accepted
      cases accepted
  apply State.Ledger.intro
  rw [(State.mintLP_ledger accepted).1, Blanc.sum_ledgerCredit nof, State.mintLP_supply accepted,
    ledger.sum_eq]

theorem State.burnLP_preserves {st post : State} {source : Adr} {value : B256}
    {events : List Event} (ledger : st.Ledger)
    (accepted : st.burnLP source value = .ok (post, events)) : post.Ledger := by
  have supply := (State.burnLP_supply accepted).2
  rw [State.burnLP] at accepted
  by_cases covered : value ≤ st.balanceOf source
  · rw [ite_eq_left covered] at accepted
    by_cases supplyCovered : value ≤ st.totalSupply
    · rw [ite_eq_left supplyCovered] at accepted
      have balances := congrArg (fun result : State × List Event => result.1.balanceOf)
        (Except.ok.inj accepted)
      dsimp only at balances
      apply State.Ledger.intro
      rw [← balances, Blanc.sum_ledgerDebit covered, supply, ledger.sum_eq]
    · rw [ite_eq_right supplyCovered] at accepted
      cases accepted
  · rw [ite_eq_right covered] at accepted
    cases accepted

theorem State.transferLP_preserves {st : State} {ctx : Context} {source recipient : Adr}
    {value : B256} {post : State} {events : List Event} (ledger : st.Ledger)
    (accepted : st.transferLP ctx source recipient value = .ok (post, events)) : post.Ledger := by
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
        have postState := congrArg Prod.fst (Except.ok.inj accepted)
        dsimp only at postState
        rw [← postState]
        have nof : Blanc.SumNof st.balanceOf := by
          unfold Blanc.SumNof
          rw [ledger.sum_eq]
          exact B256.toNat_lt _
        apply State.Ledger.intro
        dsimp only
        rw [Blanc.sum_ledgerDebit_credit nof covered]
        exact ledger.sum_eq
      · rw [ite_eq_right credit] at accepted
        cases accepted
  · rw [ite_eq_right covered] at accepted
    cases accepted

theorem State.transferFromLP_preserves {st : State} {ctx : Context} {source recipient : Adr}
    {value : B256} {post : State} {events : List Event} (ledger : st.Ledger)
    (accepted : st.transferFromLP ctx source recipient value = .ok (post, events)) :
    post.Ledger := by
  rw [State.transferFromLP] at accepted
  by_cases unlimited : st.allowance source ctx.sender = B256.max
  · rw [ite_eq_left unlimited] at accepted
    exact State.transferLP_preserves ledger accepted
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
        exact State.transferLP_preserves (st := reduced) ledger accepted
    · rw [ite_eq_right covered] at accepted
      cases accepted

theorem State.approveLP_preserves {st : State} {ctx : Context} {owner spender : Adr}
    {value : B256} {post : State} {events : List Event} (ledger : st.Ledger)
    (accepted : st.approveLP ctx owner spender value = .ok (post, events)) : post.Ledger := by
  rw [State.approveLP] at accepted
  cases staticContext : ctx.isStatic with
  | true =>
    rw [staticContext] at accepted
    cases accepted
  | false =>
    rw [staticContext] at accepted
    have postState := congrArg Prod.fst (Except.ok.inj accepted)
    dsimp only at postState
    rw [← postState]
    exact ledger

theorem State.update_preserves {st post : State} {ctx : Context} {balance0 balance1 : B256}
    {reserve0 reserve1 : Nat} {event : Event} {update : OracleUpdate} (ledger : st.Ledger)
    (accepted : st.update ctx balance0 balance1 reserve0 reserve1 = .ok (post, event, update)) :
    post.Ledger := by
  apply State.Ledger.intro
  rw [State.update_ledger accepted, (State.update_supply_reserves accepted).1]
  exact ledger.sum_eq

/-- The protocol-fee mint to `feeTo` keeps the ledger. -/
theorem mintFee_preserves {st : State} {feeTo : Adr} {reserve0 reserve1 : Nat}
    {fee : FeeResult} (ledger : st.Ledger)
    (accepted : mintFee st feeTo reserve0 reserve1 = .ok fee) : fee.state.Ledger := by
  rw [mintFee] at accepted
  by_cases feeOff : feeTo = 0
  · rw [ite_eq_left feeOff] at accepted
    rw [← Except.ok.inj accepted]
    exact ledger
  · rw [ite_eq_right feeOff] at accepted
    by_cases noLast : st.kLast = 0
    · rw [ite_eq_left noLast] at accepted
      rw [← Except.ok.inj accepted]
      exact ledger
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
                exact State.mintLP_preserves ledger minted
              · rw [ite_eq_right positiveFee] at accepted
                rw [← Except.ok.inj accepted]
                exact ledger
            · rw [ite_eq_right denominatorBound] at accepted
              cases accepted
          · rw [ite_eq_right scaledRootBound] at accepted
            cases accepted
        · rw [ite_eq_right numeratorBound] at accepted
          cases accepted
      · rw [ite_eq_right growing] at accepted
        rw [← Except.ok.inj accepted]
        exact ledger

/-! ## Owned segments -/

/-- The invariant on a frame: its rollback checkpoint and its current state. -/
def Frame.Ledger (frame : Frame) : Prop :=
  frame.checkpoint.state.Ledger ∧ frame.current.state.Ledger

theorem Frame.fail_ledger {frame : Frame} (checkpoint : frame.checkpoint.state.Ledger)
    (failure : Failure) : (frame.fail failure).frame.Ledger :=
  ⟨checkpoint, checkpoint⟩

theorem Frame.withEvents_ledger {frame : Frame} {post : State} {events : List Event}
    (checkpoint : frame.checkpoint.state.Ledger) (postLedger : post.Ledger) :
    (frame.withEvents post events).Ledger :=
  ⟨checkpoint, postLedger⟩

theorem Frame.finishLP_ledger {frame : Frame} (ledger : frame.Ledger)
    {result : Except Failure (State × List Event)} (returndata : Bytes)
    (successful : ∀ post events, result = .ok (post, events) → post.Ledger) :
    (frame.finishLP result returndata).frame.Ledger := by
  cases result with
  | error failure => exact Frame.fail_ledger ledger.1 failure
  | ok postEvents =>
    rcases postEvents with ⟨post, events⟩
    exact ⟨ledger.1, successful post events rfl⟩

theorem Frame.finishUpdated_ledger {frame : Frame} (ledger : frame.Ledger)
    (balance0 balance1 : B256) (reserves : CachedReserves) (feeOn : Bool)
    (lastEvent : Option Event) (returndata : Bytes) :
    (frame.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata).frame.Ledger := by
  rw [Frame.finishUpdated]
  cases updated : frame.current.state.update frame.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure => exact Frame.fail_ledger ledger.1 failure
  | ok result =>
    rcases result with ⟨post, event, update⟩
    have postLedger := State.update_preserves ledger.2 updated
    cases feeOn <;> cases lastEvent <;> exact ⟨ledger.1, postLedger⟩

theorem Frame.mintAfterFee_ledger {frame : Frame} (ledger : frame.Ledger) (observed : MintObserved)
    {fee : FeeResult} (feeLedger : fee.state.Ledger) :
    (frame.mintAfterFee observed fee).frame.Ledger := by
  rw [Frame.mintAfterFee]
  cases amount : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure => exact Frame.fail_ledger ledger.1 failure
  | ok liquidity =>
    dsimp only
    have initialLedger : ∀ post events,
        (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000 else .ok (fee.state, [])) =
          .ok (post, events) → post.Ledger := by
      intro post events initial
      by_cases zero : fee.state.totalSupply = 0
      · rw [ite_eq_left zero] at initial
        exact State.mintLP_preserves feeLedger initial
      · rw [ite_eq_right zero] at initial
        rw [← (Prod.mk.inj (Except.ok.inj initial)).1]
        exact feeLedger
    generalize (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000
      else Except.ok (fee.state, [])) = initial at initialLedger ⊢
    cases initial with
    | error failure => exact Frame.fail_ledger ledger.1 failure
    | ok postEvents =>
      rcases postEvents with ⟨postMinimum, minimumEvents⟩
      have minimumLedger := initialLedger postMinimum minimumEvents rfl
      dsimp only
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive]
        cases minted : postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure => exact Frame.fail_ledger ledger.1 failure
        | ok postEvents =>
          rcases postEvents with ⟨post, events⟩
          dsimp only
          have postLedger : (((frame.withEvents fee.state fee.events).withEvents postMinimum
              minimumEvents).withEvents post events).Ledger :=
            Frame.withEvents_ledger ledger.1 (State.mintLP_preserves minimumLedger minted)
          exact Frame.finishUpdated_ledger postLedger _ _ _ _ _ _
      · rw [ite_eq_right positive]
        exact Frame.fail_ledger ledger.1 _

theorem Frame.burnAfterFee_ledger {frame : Frame} (ledger : frame.Ledger) (observed : BurnObserved)
    {fee : FeeResult} (feeLedger : fee.state.Ledger) :
    (frame.burnAfterFee observed fee).frame.Ledger := by
  rw [Frame.burnAfterFee]
  split
  · exact Frame.fail_ledger ledger.1 _
  · split
    · split
      · exact Frame.fail_ledger ledger.1 _
      · rename_i post events burned
        exact ⟨ledger.1, State.burnLP_preserves feeLedger burned⟩
    · exact Frame.fail_ledger ledger.1 _

/-- The immediate entries (getters, approve, transfer, transferFrom, initialize, and every
paid call) keep the invariant. -/
theorem startImmediate_ledger {current : Checkpoint} (ledger : current.state.Ledger)
    {ctx : Context} (entry : Entry) {result : SegmentResult}
    (immediate : startImmediate current ctx entry = some result) : result.frame.Ledger := by
  have entered : (Frame.enter current ctx entry).Ledger := ⟨ledger, ledger⟩
  rw [startImmediate] at immediate
  by_cases paid : ctx.value ≠ 0
  · rw [ite_eq_left paid] at immediate
    rw [← Option.some.inj immediate]
    exact Frame.fail_ledger ledger _
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
        exact Frame.finishLP_ledger entered _ fun _ _ accepted =>
          State.approveLP_preserves ledger accepted
      case transfer recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_ledger entered _ fun _ _ accepted =>
          State.transferLP_preserves ledger accepted
      case transferFrom source recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_ledger entered _ fun _ _ accepted =>
          State.transferFromLP_preserves ledger accepted
      case «initialize» token0 token1 =>
        dsimp only at immediate
        by_cases authorized : ctx.sender = current.state.factory
        · rw [ite_eq_left authorized] at immediate
          cases staticContext : ctx.isStatic with
          | true =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact Frame.fail_ledger ledger _
          | false =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact entered
        · rw [ite_eq_right authorized] at immediate
          rw [← Option.some.inj immediate]
          exact Frame.fail_ledger ledger _
      all_goals cases immediate

theorem Frame.lock_ledger {frame locked : Frame} (ledger : frame.Ledger)
    (locking : frame.lock = .ok locked) : locked.Ledger := by
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
      exact ledger
  · rw [ite_eq_right unlocked] at locking
    cases locking

/-- **Every first owned segment of all 27 entries keeps the invariant.** -/
theorem startTyped_ledger {current : Checkpoint} (ledger : current.state.Ledger) (ctx : Context)
    (entry : Entry) : (startTyped current ctx entry).frame.Ledger := by
  have entered : (Frame.enter current ctx entry).Ledger := ⟨ledger, ledger⟩
  cases immediate : startImmediate current ctx entry with
  | some result =>
    rw [startTyped, immediate]
    exact startImmediate_ledger ledger entry immediate
  | none =>
    rw [startTyped, immediate]
    cases entry
    case permit owner spender value deadline v r s =>
      dsimp only
      by_cases timely : ctx.timestamp ≤ deadline
      · rw [ite_eq_left timely]
        cases staticContext : ctx.isStatic with
        | true => exact Frame.fail_ledger ledger _
        | false => exact entered
      · rw [ite_eq_right timely]
        exact Frame.fail_ledger ledger _
    all_goals
      dsimp only
      split
      · exact Frame.fail_ledger ledger _
      · rename_i locked locking
        have lockedLedger := Frame.lock_ledger entered locking
        repeat' split
        all_goals first
          | exact lockedLedger
          | exact Frame.fail_ledger lockedLedger.1 _

theorem Frame.afterSwapTransfer1_ledger {frame : Frame} (ledger : frame.Ledger)
    (locals : SwapLocals) : (frame.afterSwapTransfer1 locals).frame.Ledger := by
  rw [Frame.afterSwapTransfer1]
  split
  · exact ledger
  · exact ledger

theorem Frame.afterSwapTransfer0_ledger {frame : Frame} (ledger : frame.Ledger)
    (locals : SwapLocals) : (frame.afterSwapTransfer0 locals).frame.Ledger := by
  rw [Frame.afterSwapTransfer0]
  split
  · exact ledger
  · exact Frame.afterSwapTransfer1_ledger ledger locals

/-- **Every resumed owned segment keeps the invariant**: the fee mint to `feeTo`, mint's
`MINIMUM_LIQUIDITY` lock at address 0 and its recipient mint, the burn, every reserve update and
the permit approval; every failure restores the invocation checkpoint. -/
theorem resumeSegment_ledger {prior : Frame} (ledger : prior.Ledger) (request : Request)
    (continuation : Continuation) (result : ExternalResult) :
    (resumeSegment prior request continuation result).frame.Ledger := by
  have resumed : (prior.beginResume request).Ledger := ledger
  rw [resumeSegment]
  cases decodeExternal request result with
  | error failure => exact Frame.fail_ledger resumed.1 failure
  | ok decoded =>
    dsimp only
    cases continuation <;> cases decoded
    all_goals
      try dsimp only
      repeat' split
    all_goals first
      | exact resumed
      | exact Frame.fail_ledger resumed.1 _
      | exact Frame.afterSwapTransfer0_ledger resumed _
      | exact Frame.afterSwapTransfer1_ledger resumed _
      | exact Frame.finishUpdated_ledger resumed _ _ _ _ _ _
      | exact Frame.finishLP_ledger resumed _ fun _ _ accepted =>
          State.approveLP_preserves resumed.2 accepted
      | (rename_i fee accepted
         first
          | exact Frame.mintAfterFee_ledger resumed _ (mintFee_preserves resumed.2 accepted)
          | exact Frame.burnAfterFee_ledger resumed _ (mintFee_preserves resumed.2 accepted))

/-! ## The driver -/

/-- **The finite driver keeps the invariant**, jointly for `drive` and `driveTurns`: through
every resumed segment, every nested committed child (`Transcript.invoke`, started at the parent's
current state and settled into it), every foreign log, the rollback of a failed external call to
the parent's pre-call state, and the rollback of a failed segment to its invocation checkpoint. -/
theorem drive_ledger (fuel : Nat) :
    (∀ segment transcript, segment.frame.Ledger → (drive fuel segment transcript).frame.Ledger) ∧
      ∀ frame request turn turns, frame.Ledger →
        (driveTurns fuel frame request turn turns).frame.Ledger := by
  induction fuel with
  | zero =>
    refine ⟨fun segment transcript ledger => ?_, fun frame request turn turns ledger => ?_⟩
    · rw [drive]
      exact ledger
    · rw [driveTurns]
      exact ledger
  | succ fuel ih =>
    refine ⟨fun segment transcript ledger => ?_, fun frame request turn turns ledger => ?_⟩
    · cases segment with
      | finished frame returndata => exact ledger
      | failed frame failure => cases failure <;> exact ledger
      | suspended frame request continuation =>
        cases transcript with
        | done => exact ledger
        | foreignLog emitter topics data tail => exact ledger
        | invoke sender value isStatic entry child tail => exact ledger
        | next result turns tail =>
          rw [drive]
          dsimp only
          have executed := ih.2 frame request 0 turns ledger
          split
          · exact ih.1 _ tail (resumeSegment_ledger ledger request continuation result)
          · split
            · let executedFrame := (driveTurns fuel frame request 0 turns).frame
              have settled : (if result.success = true then executedFrame
                  else { executedFrame with current := frame.current }).Ledger := by
                split
                · exact executed
                · exact ⟨executed.1, ledger.2⟩
              exact ih.1 _ tail (resumeSegment_ledger settled request continuation result)
            · exact executed
    · cases turns with
      | done =>
        rw [driveTurns]
        exact ledger
      | next result children tail =>
        rw [driveTurns]
        exact ledger
      | foreignLog emitter topics data tail =>
        rw [driveTurns]
        dsimp only
        split
        · exact ledger
        · exact ih.2 _ request (turn + 1) tail ledger
      | invoke sender value isStatic entry transcript tail =>
        rw [driveTurns]
        dsimp only
        have child := ih.1 (startTyped frame.current
          (childContext frame request turn sender value isStatic) entry) transcript
          (startTyped_ledger ledger.2 _ entry)
        split
        · exact ledger
        · exact ih.2 _ request (turn + 1) tail ⟨ledger.1, child.2⟩

/-- **U7 headline (model).**  Every `runTyped` result, of every entry and every finite transcript,
keeps the ledger on both its checkpoint and its final state. -/
theorem runTyped_ledger {st : State} (ledger : st.Ledger) (ctx : Context) (entry : Entry)
    (transcript : Transcript) : (runTyped st ctx entry transcript).frame.Ledger :=
  (drive_ledger _).1 _ transcript
    (startTyped_ledger (current := { state := st, logs := [], updates := [] }) ledger ctx entry)

/-- **U7 headline over a finite footprint.**  From the invariant over `keys` at entry, the final
state of every `runTyped` result holds the invariant over the entry footprint extended by every
account whose LP balance the run moved. -/
theorem runTyped_ledgerOn {keys touched : List Adr} {st : State} (on : st.LedgerOn keys)
    (ctx : Context) (entry : Entry) (transcript : Transcript)
    (frame : ∀ account, account ∉ touched →
      (runTyped st ctx entry transcript).frame.current.state.balanceOf account = st.balanceOf account) :
    (runTyped st ctx entry transcript).frame.current.state.LedgerOn (keys ++ touched).dedup :=
  on.extend (runTyped_ledger on.ledger ctx entry transcript).2 frame

/-- **The relational driver keeps the invariant**: an exact consumption (`ExactConsumes`,
`Consumption.lean`) from a frame holding the ledger ends in one, through every nested committed
child of its turn queues (`ExactTurns.invoke`) and every failed-call rollback. -/
theorem ExactConsumes.ledger {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (consumed : ExactConsumes segment transcript out) (ledger : segment.frame.Ledger) :
    out.frame.Ledger := by
  refine ExactConsumes.rec
    (motive_1 := fun segment _ out _ => segment.frame.Ledger → out.frame.Ledger)
    (motive_2 := fun frame _ _ _ out _ => frame.Ledger → out.frame.Ledger)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed ledger
  · intro frame bytes ledger
    exact ledger
  · intro frame failure genuine ledger
    exact ledger
  · intro frame request continuation result tail out missing rest ih ledger
    exact ih (resumeSegment_ledger ledger request continuation result)
  · intro frame request continuation result turns tail executed out present noCodeTurns during rest
      ihTurns ihRest ledger
    have executedLedger := ihTurns ledger
    apply ihRest
    apply resumeSegment_ledger
    split
    · exact executedLedger
    · exact ⟨executedLedger.1, ledger.2⟩
  · intro frame request turn ledger
    exact ledger
  · intro frame request turn emitter topics data tail out mutable rest ih ledger
    exact ih ledger
  · intro frame request turn sender value isStatic entry transcript tail child out selected rest
      ihSelected ihRest ledger
    exact ihRest ⟨ledger.1, (ihSelected (startTyped_ledger ledger.2 _ entry)).2⟩

end Blanc.Lift.UniswapV2Pair
