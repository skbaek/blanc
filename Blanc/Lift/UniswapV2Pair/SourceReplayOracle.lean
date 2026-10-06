import Blanc.Lift.UniswapV2Pair.SourceReplay
import Blanc.Lift.UniswapV2Pair.PropertiesOracleLaw

/-! Oracle receipts of an ordered source replay: every receipt is lawful, the receipts chain the
stored `blockTimestampLast` from the replay's initial state to its final state, and every receipt's
timestamp is the timestamp of the invocation that produced it (nested re-entered frames inherit their
parent's context, so their receipts carry the same block timestamp). -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem State.update_timestamp {st post : State} {ctx : Context}
    {balance0 balance1 : B256} {oldReserve0 oldReserve1 : Nat}
    {event : Event} {update : OracleUpdate}
    (accepted : st.update ctx balance0 balance1 oldReserve0 oldReserve1 =
      .ok (post, event, update)) :
    update.timestamp = ctx.timestamp := by
  rw [State.update] at accepted
  by_cases bound0 : balance0.toNat < 2 ^ 112
  · rw [dite_eq_left bound0] at accepted
    by_cases bound1 : balance1.toNat < 2 ^ 112
    · rw [dite_eq_left bound1] at accepted
      cases (Except.ok.inj accepted)
      rfl
    · rw [dite_eq_right bound1] at accepted
      cases accepted
  · rw [dite_eq_right bound0] at accepted
    cases accepted

/-- Every receipt of a checkpoint carries the timestamp `ts`. -/
def Checkpoint.Stamped (ts : B256) (c : Checkpoint) : Prop :=
  ∀ u ∈ c.updates, u.update.timestamp = ts

/-- A frame at timestamp `ts` whose checkpoint and current receipts all carry `ts`. -/
def Frame.Stamped (ts : B256) (f : Frame) : Prop :=
  f.context.timestamp = ts ∧ f.checkpoint.Stamped ts ∧ f.current.Stamped ts

def SegmentResult.Stamped (ts : B256) (s : SegmentResult) : Prop :=
  s.frame.Stamped ts

theorem Frame.withEvents_stamped {ts : B256} {f : Frame} {post : State} {events : List Event}
    (hf : f.Stamped ts) : (f.withEvents post events).Stamped ts := hf

theorem Frame.fail_stamped {ts : B256} {f : Frame} {failure : Failure}
    (hf : f.Stamped ts) : (f.fail failure).Stamped ts := ⟨hf.1, hf.2.1, hf.2.1⟩

theorem Frame.finish_stamped {ts : B256} {f : Frame} {returndata : Bytes}
    (hf : f.Stamped ts) : (f.finish returndata).Stamped ts := hf

theorem Frame.suspend_stamped {ts : B256} {f : Frame} {site : CallSite} {target : Adr}
    {operation : ExternalOperation} {continuation : Continuation}
    (hf : f.Stamped ts) : (f.suspend site target operation continuation).Stamped ts := hf

theorem Frame.finishLocked_stamped {ts : B256} {f : Frame} {returndata : Bytes}
    (hf : f.Stamped ts) : (f.finishLocked returndata).Stamped ts := hf

theorem Frame.finishLP_stamped {ts : B256} {f : Frame}
    {result : Except Failure (State × List Event)} {returndata : Bytes}
    (hf : f.Stamped ts) : (f.finishLP result returndata).Stamped ts := by
  cases result with
  | error failure => exact Frame.fail_stamped hf
  | ok result =>
    rcases result with ⟨post, events⟩
    exact hf

theorem Frame.withUpdate_stamped {ts : B256} {f : Frame} {post : State} {event : Event}
    {update : OracleUpdate} (hf : f.Stamped ts) (hu : update.timestamp = ts) :
    (f.withUpdate post event update).Stamped ts := by
  refine ⟨hf.1, hf.2.1, ?_⟩
  intro u member
  change u ∈ f.current.updates ++ [{ origin := f.origin, update := update }] at member
  rcases List.mem_append.mp member with old | new
  · exact hf.2.2 u old
  · rw [List.mem_singleton] at new
    rw [new]
    exact hu

theorem Frame.finishUpdated_stamped {ts : B256} {f : Frame}
    {balance0 balance1 : B256} {reserves : CachedReserves} {feeOn : Bool}
    {lastEvent : Option Event} {returndata : Bytes} (hf : f.Stamped ts) :
    (f.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata).Stamped ts := by
  rw [Frame.finishUpdated]
  cases accepted : f.current.state.update f.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure => exact Frame.fail_stamped hf
  | ok result =>
      rcases result with ⟨post, event, update⟩
      have hu : update.timestamp = ts := (State.update_timestamp accepted).trans hf.1
      have updated : (f.withUpdate (if feeOn then
          { post with kLast := Nat.toB256 (post.reserve0.val * post.reserve1.val) } else post)
          event update).Stamped ts := Frame.withUpdate_stamped hf hu
      cases lastEvent with
      | none => exact updated
      | some extra => exact updated

theorem Frame.mintAfterFee_stamped {ts : B256} {f : Frame} {observed : MintObserved}
    {fee : FeeResult} (hf : f.Stamped ts) : (f.mintAfterFee observed fee).Stamped ts := by
  have charged : (f.withEvents fee.state fee.events).Stamped ts := hf
  rw [Frame.mintAfterFee]
  cases mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure => exact Frame.fail_stamped charged
  | ok liquidity =>
    simp only []
    cases (if fee.state.totalSupply = 0 then fee.state.mintLP 0 1000
        else .ok (fee.state, [])) with
    | error failure => exact Frame.fail_stamped charged
    | ok result =>
      rcases result with ⟨postMinimum, minimumEvents⟩
      simp only []
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive]
        cases postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure => exact Frame.fail_stamped charged
        | ok result =>
          rcases result with ⟨post, events⟩
          exact Frame.finishUpdated_stamped charged
      · rw [ite_eq_right positive]
        exact Frame.fail_stamped charged

theorem Frame.burnAfterFee_stamped {ts : B256} {f : Frame} {observed : BurnObserved}
    {fee : FeeResult} (hf : f.Stamped ts) : (f.burnAfterFee observed fee).Stamped ts := by
  have charged : (f.withEvents fee.state fee.events).Stamped ts := hf
  rw [Frame.burnAfterFee]
  cases burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply with
  | error failure => exact Frame.fail_stamped charged
  | ok amounts =>
    rcases amounts with ⟨amount0, amount1⟩
    simp only []
    by_cases positive : amount0 > 0 ∧ amount1 > 0
    · rw [ite_eq_left positive]
      cases fee.state.burnLP f.context.pair observed.liquidity with
      | error failure => exact Frame.fail_stamped charged
      | ok result =>
        rcases result with ⟨post, events⟩
        exact charged
    · rw [ite_eq_right positive]
      exact Frame.fail_stamped charged

theorem Frame.afterSwapTransfer0_stamped {ts : B256} {f : Frame} {locals : SwapLocals}
    (hf : f.Stamped ts) : (f.afterSwapTransfer0 locals).Stamped ts := by
  rw [Frame.afterSwapTransfer0, Frame.afterSwapTransfer1]
  repeat' split
  all_goals exact hf

theorem Frame.afterSwapTransfer1_stamped {ts : B256} {f : Frame} {locals : SwapLocals}
    (hf : f.Stamped ts) : (f.afterSwapTransfer1 locals).Stamped ts := by
  rw [Frame.afterSwapTransfer1]
  repeat' split
  all_goals exact hf

theorem resumeSegment_stamped {ts : B256} {prior : Frame} {request : Request}
    {continuation : Continuation} {result : ExternalResult} (hf : prior.Stamped ts) :
    (resumeSegment prior request continuation result).Stamped ts := by
  have hframe : (prior.beginResume request).Stamped ts := hf
  rw [resumeSegment]
  cases decodeExternal request result with
  | error failure => exact Frame.fail_stamped hframe
  | ok decoded =>
      dsimp only
      repeat' split
      all_goals first
        | exact Frame.fail_stamped hframe
        | exact Frame.finishUpdated_stamped hframe
        | exact Frame.mintAfterFee_stamped hframe
        | exact Frame.burnAfterFee_stamped hframe
        | exact Frame.afterSwapTransfer0_stamped hframe
        | exact Frame.afterSwapTransfer1_stamped hframe
        | exact Frame.finishLP_stamped hframe
        | exact hframe

theorem startImmediate_stamped {current : Checkpoint} {ctx : Context} {entry : Entry}
    {result : SegmentResult} (hc : current.Stamped ctx.timestamp)
    (immediate : startImmediate current ctx entry = some result) :
    result.Stamped ctx.timestamp := by
  have entered : (Frame.enter current ctx entry).Stamped ctx.timestamp := ⟨rfl, hc, hc⟩
  rw [startImmediate] at immediate
  by_cases paid : ctx.value ≠ 0
  · rw [ite_eq_left paid] at immediate
    rw [← Option.some.inj immediate]
    exact Frame.fail_stamped entered
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
        exact Frame.finishLP_stamped entered
      case transfer recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_stamped entered
      case transferFrom source recipient value =>
        rw [← Option.some.inj immediate]
        exact Frame.finishLP_stamped entered
      case «initialize» token0 token1 =>
        dsimp only at immediate
        by_cases authorized : ctx.sender = current.state.factory
        · rw [ite_eq_left authorized] at immediate
          cases staticContext : ctx.isStatic with
          | true =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact Frame.fail_stamped entered
          | false =>
            rw [staticContext] at immediate
            rw [← Option.some.inj immediate]
            exact entered
        · rw [ite_eq_right authorized] at immediate
          rw [← Option.some.inj immediate]
          exact Frame.fail_stamped entered
      all_goals cases immediate

theorem Frame.lock_stamped {ts : B256} {f locked : Frame} (hf : f.Stamped ts)
    (opened : f.lock = .ok locked) : locked.Stamped ts := by
  rw [Frame.lock] at opened
  by_cases unlocked : f.current.state.unlocked = 1
  · rw [ite_eq_left unlocked] at opened
    cases staticContext : f.context.isStatic with
    | false =>
      rw [staticContext] at opened
      cases opened
      exact hf
    | true =>
      rw [staticContext] at opened
      cases opened
  · rw [ite_eq_right unlocked] at opened
    cases opened

theorem startTyped_stamped {current : Checkpoint} {ctx : Context} {entry : Entry}
    (hc : current.Stamped ctx.timestamp) :
    (startTyped current ctx entry).Stamped ctx.timestamp := by
  have entered : (Frame.enter current ctx entry).Stamped ctx.timestamp := ⟨rfl, hc, hc⟩
  cases immediate : startImmediate current ctx entry with
  | some result =>
    rw [startTyped, immediate]
    exact startImmediate_stamped hc immediate
  | none =>
    cases entry
    case permit owner spender value deadline v r s =>
      simp only [startTyped, immediate]
      repeat' split
      all_goals first
        | exact Frame.fail_stamped entered
        | exact entered
    all_goals
      simp only [startTyped, immediate]
      split
      next => exact Frame.fail_stamped entered
      next locked opened =>
        have lockedStamped := Frame.lock_stamped entered opened
        repeat' split
        all_goals first
          | exact lockedStamped
          | exact Frame.fail_stamped lockedStamped

mutual

theorem drive_stamped (fuel : Nat) {ts : B256} {segment : SegmentResult}
    {transcript : Transcript} (hs : segment.Stamped ts) :
    (drive fuel segment transcript).frame.Stamped ts := by
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
        | true => exact drive_stamped fuel (resumeSegment_stamped hs)
        | false =>
          have turnsStamped := driveTurns_stamped fuel frame request 0 turns hs
          cases complete : (driveTurns fuel frame request 0 turns).complete with
          | false =>
            simp only [Bool.false_eq_true, complete, ite_false]
            exact turnsStamped
          | true =>
            have settled :
                (if result.success then (driveTurns fuel frame request 0 turns).frame
                  else { (driveTurns fuel frame request 0 turns).frame with
                    current := frame.current }).Stamped ts := by
              cases result.success with
              | true => exact turnsStamped
              | false => exact ⟨turnsStamped.1, turnsStamped.2.1, hs.2.2⟩
            have resumed := drive_stamped fuel (transcript := tail)
              (resumeSegment_stamped (request := request) (continuation := continuation)
                (result := result) settled)
            simpa only [missing, Bool.false_eq_true, complete, ite_true, ite_false] using resumed

theorem driveTurns_stamped (fuel : Nat) {ts : B256} (frame : Frame) (request : Request)
    (turn : Nat) (turns : Transcript) (hf : frame.Stamped ts) :
    (driveTurns fuel frame request turn turns).frame.Stamped ts := by
  cases fuel with
  | zero => exact hf
  | succ fuel =>
    cases turns with
    | done => exact hf
    | next result children tail => exact hf
    | foreignLog emitter topics data tail =>
      rw [driveTurns]
      cases externalStatic frame request with
      | true => exact hf
      | false =>
        exact driveTurns_stamped fuel _ request (turn + 1) tail ⟨hf.1, hf.2.1, hf.2.2⟩
    | invoke sender value isStatic entry transcript tail =>
      let context := childContext frame request turn sender value isStatic
      have contextTs : context.timestamp = ts := hf.1
      have started : (startTyped frame.current context entry).Stamped context.timestamp :=
        startTyped_stamped (fun u member => (hf.2.2 u member).trans contextTs.symm)
      have childStamped := drive_stamped fuel (transcript := transcript) started
      let child := drive fuel (startTyped frame.current context entry) transcript
      let settled : Frame := { frame with current := child.frame.current }
      have settledStamped : settled.Stamped ts :=
        ⟨hf.1, hf.2.1, fun u member => (childStamped.2.2 u member).trans contextTs⟩
      have tailStamped := driveTurns_stamped fuel settled request (turn + 1) tail settledStamped
      rw [driveTurns]
      cases childStatus : (drive fuel (startTyped frame.current context entry) transcript).status with
      | incomplete => exact hf
      | success returndata =>
        simpa only [childStatus, settled, child, context] using tailStamped
      | failed failure =>
        simpa only [childStatus, settled, child, context] using tailStamped

end

/-- Every receipt of one typed run carries the run's context timestamp, re-entered frames included. -/
theorem runTyped_stamped {st : State} {ctx : Context} {entry : Entry} {transcript : Transcript} :
    ∀ u ∈ (runTyped st ctx entry transcript).frame.current.updates,
      u.update.timestamp = ctx.timestamp :=
  (drive_stamped (transcript.work + 2) (transcript := transcript)
    (startTyped_stamped (current := { state := st, logs := [], updates := [] })
      (entry := entry) (fun _ member => (nomatch member)))).2.2

/-- One invocation's receipts with the invocation that produced them, in replay order. -/
def sourceReplayReceipts : State → List SourceInvocation →
    List (SourceInvocation × List TaggedOracleUpdate)
  | _, [] => []
  | st, inv :: rest =>
    (inv, (inv.run st).frame.current.updates) ::
      sourceReplayReceipts (inv.run st).frame.current.state rest

theorem sourceReplayUpdates_eq_receipts (st : State) (invs : List SourceInvocation) :
    sourceReplayUpdates st invs = (sourceReplayReceipts st invs).flatMap Prod.snd := by
  induction invs generalizing st with
  | nil => rfl
  | cons inv rest ih =>
    rw [sourceReplayUpdates, sourceReplayReceipts, List.flatMap_cons, ih]

/-- **Oracle receipts of a replay.**  Every update receipt of the replay is lawful
(`Δt = (ts mod 2^32 − last) mod 2^32`, increments `⌊r1·2^112/r0⌋·Δt` and `⌊r0·2^112/r1⌋·Δt` when `Δt`
and both reserves are nonzero), the receipts chain `last` from the initial state's
`blockTimestampLast` through each receipt's `ts mod 2^32` to the final state's, and each receipt's
`ts` is the context timestamp of the invocation that produced it. -/
theorem SourceReplay.oracle_receipts {st finish : State} {invs : List SourceInvocation}
    (replay : SourceReplay st invs finish) :
    (∀ u ∈ sourceReplayUpdates st invs, u.update.Lawful) ∧
      OracleTimestampChain st.blockTimestampLast finish.blockTimestampLast
        (sourceReplayUpdates st invs) ∧
      ∀ inv receipts, (inv, receipts) ∈ sourceReplayReceipts st invs →
        inv ∈ invs ∧ ∀ u ∈ receipts, u.update.timestamp = inv.context.timestamp := by
  induction replay with
  | nil st =>
    exact ⟨fun _ member => (nomatch member), rfl, fun _ _ member => (nomatch member)⟩
  | @cons st finish inv rest out bytes consumed successful tail ih =>
    have runEq : inv.run st = out := (runTyped_of_exact consumed).1
    have law := runTyped_oracle_law (st := st) (ctx := inv.context) (entry := inv.entry)
      (transcript := inv.transcript)
    have stamped := runTyped_stamped (st := st) (ctx := inv.context) (entry := inv.entry)
      (transcript := inv.transcript)
    change (∀ u ∈ (inv.run st).frame.current.updates, u.update.Lawful) ∧
      OracleTimestampChain st.blockTimestampLast (inv.run st).frame.current.state.blockTimestampLast
        (inv.run st).frame.current.updates ∧ _ ∧ _ at law
    change ∀ u ∈ (inv.run st).frame.current.updates, u.update.timestamp = inv.context.timestamp
      at stamped
    rw [runEq] at law stamped
    obtain ⟨restLawful, restChain, restStamped⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro u member
      rw [sourceReplayUpdates, runEq, List.mem_append] at member
      rcases member with here | later
      · exact law.1 u here
      · exact restLawful u later
    · rw [sourceReplayUpdates, runEq]
      exact OracleTimestampChain_append _ _ _ _ _ law.2.1 restChain
    · intro inv' receipts member
      rw [sourceReplayReceipts, runEq, List.mem_cons] at member
      rcases member with same | later
      · cases same
        exact ⟨List.mem_cons_self .., stamped⟩
      · obtain ⟨mem, hts⟩ := restStamped inv' receipts later
        exact ⟨List.mem_cons_of_mem _ mem, hts⟩

end Blanc.Lift.UniswapV2Pair
