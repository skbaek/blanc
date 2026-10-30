import Blanc.Lift.UniswapV2Pair.PropertiesOracleLaw
import Blanc.Lift.UniswapV2Pair.SourceReplayOracle

/-!
# The oracle receipts of one Pair invocation

One typed run (`runTyped`) of the Pair model may emit several oracle receipts (re-entered
invocations included), but they collapse to a single `(Δ, increment)`:

* the first receipt was taken at the run's *entry* reserves (`Frame.FirstAt`, carried through the
  driver: reserves change only by `_update`, which appends a receipt, and rollbacks restore a
  checkpoint that satisfies the same invariant);
* every receipt carries the run's timestamp (`runTyped_stamped`), so by the timestamp chain
  (`OracleTimestampChain`) every receipt after the first has `Δ = 0` and, being lawful
  (`OracleUpdate.Lawful`), zero increments.

`runTyped_oracle_call` states the result over the entry and exit states: each accumulator advances
by `twapIncrement` of the entry reserves over the stored-timestamp advance `wrapElapsed`, modulo
`2 ^ 256`, and the stored timestamp stays or becomes the run's timestamp modulo `2 ^ 32`.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-! ## Statement vocabulary -/

/-- The Uniswap V2 TWAP increment of one accumulator: `⌊r1 · 2^112 / r0⌋ · Δ` when `Δ` and both
reserves are nonzero, zero otherwise (`price0`: `twapIncrement r0 r1`; `price1`:
`twapIncrement r1 r0`). -/
def twapIncrement (r0 r1 elapsed : Nat) : Nat :=
  if elapsed > 0 ∧ r0 ≠ 0 ∧ r1 ≠ 0 then r1 * 2 ^ 112 / r0 * elapsed else 0

/-- The advance of a `uint32` timestamp from `last` to `last'`, modulo `2 ^ 32`. -/
def wrapElapsed (last last' : Nat) : Nat := (last' + 2 ^ 32 - last) % 2 ^ 32

/-! ## Reserve-preservation of the non-oracle state operations -/

theorem State.mintLP_cached {st post : State} {recipient : Adr} {value : B256}
    {events : List Event} (h : st.mintLP recipient value = .ok (post, events)) :
    post.cachedReserves = st.cachedReserves := by
  unfold State.mintLP at h
  split_ifs at h
  all_goals obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl

theorem State.burnLP_cached {st post : State} {source : Adr} {value : B256}
    {events : List Event} (h : st.burnLP source value = .ok (post, events)) :
    post.cachedReserves = st.cachedReserves := by
  unfold State.burnLP at h
  split_ifs at h
  all_goals obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); rfl

theorem State.approveLP_cached {st post : State} {ctx : Context} {owner spender : Adr}
    {value : B256} {events : List Event}
    (h : st.approveLP ctx owner spender value = .ok (post, events)) :
    post.cachedReserves = st.cachedReserves := by
  have core := congrArg (fun c => c.2.1) (State.approveLP_core h)
  simp only [State.economicCore, Prod.mk.injEq] at core
  rw [State.cachedReserves, State.cachedReserves, core.1, core.2]

theorem mintFee_cached {st : State} {feeTo : Adr} {r0 r1 : Nat} {fee : FeeResult}
    (h : mintFee st feeTo r0 r1 = .ok fee) : fee.state.cachedReserves = st.cachedReserves := by
  simp only [mintFee] at h
  split_ifs at h
  all_goals try (cases Except.ok.inj h; rfl)
  cases hm : st.mintLP feeTo (Nat.toB256 ((st.totalSupply.toNat * ((r0 * r1).sqrt -
      st.kLast.toNat.sqrt)) / ((r0 * r1).sqrt * 5 + st.kLast.toNat.sqrt))) with
  | error e =>
    rw [hm] at h
    cases h
  | ok r =>
    obtain ⟨post, events⟩ := r
    rw [hm] at h
    cases Except.ok.inj h
    exact State.mintLP_cached hm

theorem State.update_oldReserves {st post : State} {ctx : Context} {balance0 balance1 : B256}
    {r0 r1 : Nat} {event : Event} {update : OracleUpdate}
    (h : st.update ctx balance0 balance1 r0 r1 = .ok (post, event, update)) :
    update.oldReserve0 = r0 ∧ update.oldReserve1 = r1 := by
  unfold State.update at h
  split_ifs at h
  all_goals cases Except.ok.inj h; exact ⟨rfl, rfl⟩

/-! ## The first-receipt invariant -/

/-- The first receipt of a checkpoint was taken at reserves `r`; before any receipt the reserves
are still `r`. -/
def Checkpoint.FirstAt (r : CachedReserves) (c : Checkpoint) : Prop :=
  (c.updates = [] → c.state.cachedReserves = r) ∧
    ∀ u, c.updates.head? = some u →
      u.update.oldReserve0 = r.reserve0.val ∧ u.update.oldReserve1 = r.reserve1.val

/-- Both checkpoints of a frame satisfy `Checkpoint.FirstAt`, and receipts are never lost: the
frame's checkpoint has one if the run's start (`K`) had, and its current state has one if its
checkpoint has. -/
def Frame.FirstAt (r : CachedReserves) (K : List TaggedOracleUpdate) (f : Frame) : Prop :=
  f.checkpoint.FirstAt r ∧ f.current.FirstAt r ∧ (K ≠ [] → f.checkpoint.updates ≠ []) ∧
    (f.checkpoint.updates ≠ [] → f.current.updates ≠ [])

/-- A suspended continuation's cached reserves are `r` while the frame has no receipt. -/
def Continuation.cached : Continuation → Option CachedReserves
  | .mintBalance0 _ reserves => some reserves
  | .mintBalance1 _ reserves _ => some reserves
  | .mintFee observed => some observed.reserves
  | .burnInitialBalance0 locals => some locals.reserves
  | .burnInitialBalance1 locals _ => some locals.reserves
  | .burnFee observed => some observed.locals.reserves
  | .burnTransfer0 priced => some priced.observed.locals.reserves
  | .burnTransfer1 priced => some priced.observed.locals.reserves
  | .burnFinalBalance0 priced => some priced.observed.locals.reserves
  | .burnFinalBalance1 priced _ => some priced.observed.locals.reserves
  | .swapTransfer0 locals => some locals.reserves
  | .swapTransfer1 locals => some locals.reserves
  | .swapCallback locals => some locals.reserves
  | .swapBalance0 locals => some locals.reserves
  | .swapBalance1 locals _ => some locals.reserves
  | .syncBalance0 reserves => some reserves
  | .syncBalance1 reserves _ => some reserves
  | _ => none

def ContAt (r : CachedReserves) (f : Frame) (continuation : Continuation) : Prop :=
  ∀ c, continuation.cached = some c → f.current.updates = [] → c = r

def SegmentResult.FirstAt (r : CachedReserves) (K : List TaggedOracleUpdate) :
    SegmentResult → Prop
  | .finished f _ => f.FirstAt r K
  | .failed f _ => f.FirstAt r K
  | .suspended f _ continuation => f.FirstAt r K ∧ ContAt r f continuation

/-! ### Frame operations -/

section
variable {r : CachedReserves} {K : List TaggedOracleUpdate}

theorem Frame.fail_firstAt {f : Frame} {failure : Failure} (hf : f.FirstAt r K) :
    (f.fail failure).FirstAt r K :=
  ⟨hf.1, hf.1, hf.2.2.1, id⟩

theorem Frame.withEvents_firstAt {f : Frame} {post : State} {events : List Event}
    (hf : f.FirstAt r K)
    (same : f.current.updates = [] → post.cachedReserves = f.current.state.cachedReserves) :
    (f.withEvents post events).FirstAt r K :=
  ⟨hf.1, ⟨fun h => (same h).trans (hf.2.1.1 h), hf.2.1.2⟩, hf.2.2.1, hf.2.2.2⟩

theorem Frame.withUpdate_updates_ne_nil {f : Frame} {post : State} {event : Event}
    {update : OracleUpdate} : (f.withUpdate post event update).current.updates ≠ [] :=
  List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)

theorem Frame.withUpdate_firstAt {f : Frame} {post : State} {event : Event}
    {update : OracleUpdate} (hf : f.FirstAt r K)
    (first : f.current.updates = [] →
      update.oldReserve0 = r.reserve0.val ∧ update.oldReserve1 = r.reserve1.val) :
    (f.withUpdate post event update).FirstAt r K := by
  refine ⟨hf.1, ⟨fun h => absurd h Frame.withUpdate_updates_ne_nil, ?_⟩, hf.2.2.1,
    fun _ => Frame.withUpdate_updates_ne_nil⟩
  intro u hu
  change (f.current.updates ++ [({ origin := f.origin, update := update } : TaggedOracleUpdate)]).head?
    = some u at hu
  cases hcur : f.current.updates with
  | nil =>
    rw [hcur] at hu
    cases hu
    exact first hcur
  | cons v rest =>
    rw [hcur] at hu
    exact hf.2.1.2 u (by rw [hcur]; exact hu)

theorem Frame.finishLocked_firstAt {f : Frame} {bytes : Bytes} (hf : f.FirstAt r K) :
    (f.finishLocked bytes).FirstAt r K :=
  Frame.withEvents_firstAt hf (fun _ => rfl)

theorem Frame.finishUpdated_firstAt {f : Frame} {balance0 balance1 : B256}
    {reserves : CachedReserves} {feeOn : Bool} {lastEvent : Option Event} {returndata : Bytes}
    (hf : f.FirstAt r K) (cached : f.current.updates = [] → reserves = r) :
    (f.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata).FirstAt r K := by
  rw [Frame.finishUpdated]
  cases accepted : f.current.state.update f.context balance0 balance1
      reserves.reserve0.val reserves.reserve1.val with
  | error failure => exact Frame.fail_firstAt hf
  | ok result =>
    rcases result with ⟨post, event, update⟩
    have old := State.update_oldReserves accepted
    have updated := Frame.withUpdate_firstAt (post := if feeOn = true then
        { post with kLast := Nat.toB256 (post.reserve0.val * post.reserve1.val) } else post)
      (event := event) hf (fun h => by rw [old.1, old.2, cached h]; exact ⟨rfl, rfl⟩)
    have nonempty : (f.withUpdate (if feeOn = true then
        { post with kLast := Nat.toB256 (post.reserve0.val * post.reserve1.val) } else post)
        event update).current.updates ≠ [] := Frame.withUpdate_updates_ne_nil
    cases lastEvent with
    | none => exact Frame.finishLocked_firstAt updated
    | some extra =>
      exact Frame.finishLocked_firstAt
        (Frame.withEvents_firstAt updated (fun h => absurd h nonempty))

theorem Frame.mintAfterFee_firstAt {f : Frame} {observed : MintObserved} {fee : FeeResult}
    {feeTo : Adr} (hf : f.FirstAt r K) (cont : f.current.updates = [] → observed.reserves = r)
    (hfee : mintFee f.current.state feeTo observed.reserves.reserve0.val
      observed.reserves.reserve1.val = .ok fee) :
    (f.mintAfterFee observed fee).FirstAt r K := by
  have charged : (f.withEvents fee.state fee.events).FirstAt r K :=
    Frame.withEvents_firstAt hf (fun _ => mintFee_cached hfee)
  rw [Frame.mintAfterFee]
  cases priced : mintAmount observed.amount0 observed.amount1 fee.state.totalSupply
      observed.reserves.reserve0.val observed.reserves.reserve1.val with
  | error failure => exact Frame.fail_firstAt charged
  | ok liquidity =>
    simp only []
    cases initial : (if fee.state.totalSupply = 0 then
        fee.state.mintLP 0 1000 else .ok (fee.state, [])) with
    | error failure => exact Frame.fail_firstAt charged
    | ok result =>
      rcases result with ⟨postMinimum, minimumEvents⟩
      simp only []
      have minimumCached : postMinimum.cachedReserves = fee.state.cachedReserves := by
        by_cases zero : fee.state.totalSupply = 0
        · rw [ite_eq_left zero] at initial
          exact State.mintLP_cached initial
        · rw [ite_eq_right zero] at initial
          cases initial
          rfl
      have minimum := Frame.withEvents_firstAt (events := minimumEvents) charged
        (fun _ => minimumCached)
      by_cases positive : liquidity > 0
      · rw [ite_eq_left positive]
        cases minted : postMinimum.mintLP observed.recipient (Nat.toB256 liquidity) with
        | error failure => exact Frame.fail_firstAt minimum
        | ok result =>
          rcases result with ⟨post, events⟩
          have issued := Frame.withEvents_firstAt (events := events) minimum
            (fun _ => State.mintLP_cached minted)
          exact Frame.finishUpdated_firstAt issued cont
      · rw [ite_eq_right positive]
        exact Frame.fail_firstAt minimum

theorem Frame.burnAfterFee_firstAt {f : Frame} {observed : BurnObserved} {fee : FeeResult}
    {feeTo : Adr} (hf : f.FirstAt r K)
    (cont : f.current.updates = [] → observed.locals.reserves = r)
    (hfee : mintFee f.current.state feeTo observed.locals.reserves.reserve0.val
      observed.locals.reserves.reserve1.val = .ok fee) :
    (f.burnAfterFee observed fee).FirstAt r K := by
  have charged : (f.withEvents fee.state fee.events).FirstAt r K :=
    Frame.withEvents_firstAt hf (fun _ => mintFee_cached hfee)
  rw [Frame.burnAfterFee]
  cases amounts : burnAmounts observed.liquidity observed.balance0 observed.balance1
      fee.state.totalSupply with
  | error failure => exact Frame.fail_firstAt charged
  | ok pair =>
    rcases pair with ⟨amount0, amount1⟩
    simp only []
    by_cases positive : amount0 > 0 ∧ amount1 > 0
    · rw [ite_eq_left positive]
      cases burned : fee.state.burnLP f.context.pair observed.liquidity with
      | error failure => exact Frame.fail_firstAt charged
      | ok result =>
        rcases result with ⟨post, events⟩
        exact ⟨Frame.withEvents_firstAt charged (fun _ => State.burnLP_cached burned),
          fun c hc h => by cases hc; exact cont h⟩
    · rw [ite_eq_right positive]
      exact Frame.fail_firstAt charged

theorem Frame.suspend_firstAt {f : Frame} {site : CallSite} {target : Adr}
    {operation : ExternalOperation} {continuation : Continuation} (hf : f.FirstAt r K)
    (hc : ContAt r f continuation) :
    (f.suspend site target operation continuation).FirstAt r K :=
  ⟨hf, hc⟩

theorem Frame.finishLP_firstAt {f : Frame} {result : Except Failure (State × List Event)}
    {returndata : Bytes} (hf : f.FirstAt r K)
    (same : ∀ post events, result = .ok (post, events) →
      post.cachedReserves = f.current.state.cachedReserves) :
    (f.finishLP result returndata).FirstAt r K := by
  cases result with
  | error failure => exact Frame.fail_firstAt hf
  | ok pe =>
    rcases pe with ⟨post, events⟩
    exact Frame.withEvents_firstAt hf (fun _ => same post events rfl)

theorem resumeSegment_firstAt {prior : Frame} {request : Request}
    {continuation : Continuation} {result : ExternalResult}
    (hf : prior.FirstAt r K) (hcont : ContAt r prior continuation) :
    (resumeSegment prior request continuation result).FirstAt r K := by
  have hframe : (prior.beginResume request).FirstAt r K := hf
  have hc : ContAt r (prior.beginResume request) continuation := hcont
  rw [resumeSegment]
  cases decoded : decodeExternal request result with
  | error failure => exact Frame.fail_firstAt hframe
  | ok decodedResult =>
    cases continuation <;> cases decodedResult
    case mintFee.address observed feeTo =>
      simp only []
      cases accepted : mintFee (prior.beginResume request).current.state feeTo
          observed.reserves.reserve0.val observed.reserves.reserve1.val with
      | error failure => exact Frame.fail_firstAt hframe
      | ok fee => exact Frame.mintAfterFee_firstAt hframe (hc _ rfl) accepted
    case burnFee.address observed feeTo =>
      simp only []
      cases accepted : mintFee (prior.beginResume request).current.state feeTo
          observed.locals.reserves.reserve0.val observed.locals.reserves.reserve1.val with
      | error failure => exact Frame.fail_firstAt hframe
      | ok fee => exact Frame.burnAfterFee_firstAt hframe (hc _ rfl) accepted
    case swapTransfer0.unit locals =>
      simp only [Frame.afterSwapTransfer0, Frame.afterSwapTransfer1]
      repeat' split
      all_goals exact Frame.suspend_firstAt hframe (fun c h => by cases h; exact hc _ rfl)
    case swapTransfer1.unit locals =>
      simp only [Frame.afterSwapTransfer1]
      repeat' split
      all_goals exact Frame.suspend_firstAt hframe (fun c h => by cases h; exact hc _ rfl)
    case swapBalance1.word locals balance0 balance1 =>
      simp only []
      split
      · exact Frame.fail_firstAt hframe
      · exact Frame.finishUpdated_firstAt hframe (hc _ rfl)
    case permitRecovery.address owner spender value recovered =>
      simp only []
      split
      · exact Frame.finishLP_firstAt hframe
          (fun _ _ h => State.approveLP_cached h)
      · exact Frame.fail_firstAt hframe
    all_goals
      simp only []
      first
      | exact Frame.fail_firstAt hframe
      | exact Frame.finishLocked_firstAt hframe
      | exact Frame.finishUpdated_firstAt hframe (hc _ rfl)
      | exact Frame.suspend_firstAt hframe (fun c h => by cases h; exact hc _ rfl)
      | exact Frame.suspend_firstAt hframe (fun c h => by cases h)
      | (split
         · first
           | exact Frame.suspend_firstAt hframe (fun c h => by cases h; exact hc _ rfl)
           | exact Frame.suspend_firstAt hframe (fun c h => by cases h)
         · exact Frame.fail_firstAt hframe)

theorem Checkpoint.firstAt_initial (st : State) :
    ({ state := st, logs := [], updates := [] } : Checkpoint).FirstAt st.cachedReserves :=
  ⟨fun _ => rfl, fun _ h => by cases h⟩

theorem startTyped_firstAt {current : Checkpoint} {ctx : Context} {entry : Entry}
    (hc : current.FirstAt r) : (startTyped current ctx entry).FirstAt r current.updates := by
  have entered : (Frame.enter current ctx entry).FirstAt r current.updates :=
    ⟨hc, hc, id, id⟩
  cases immediate : startImmediate current ctx entry with
  | some result =>
    rw [startTyped, immediate]
    have fields := startImmediate_updates immediate
    have core := congrArg (fun c => c.2.1) (startImmediate_core entry immediate).2
    simp only [State.economicCore, Prod.mk.injEq] at core
    have cached : result.frame.current.state.cachedReserves = current.state.cachedReserves := by
      rw [State.cachedReserves, State.cachedReserves, core.1, core.2]
    have frameAt : result.frame.FirstAt r current.updates := by
      refine ⟨by rw [fields.1]; exact hc, ⟨fun h => ?_, fun u h => ?_⟩, fun h => ?_, fun h => ?_⟩
      · rw [cached]; exact hc.1 (fields.2 ▸ h)
      · exact hc.2 u (fields.2 ▸ h)
      · rw [fields.1]; exact h
      · rw [fields.2]; rw [fields.1] at h; exact h
    have terminal := (startImmediate_core entry immediate).1
    cases result with
    | finished f _ => exact frameAt
    | failed f _ => exact frameAt
    | suspended f _ _ => exact terminal.elim
  | none =>
    cases entry
    case permit owner spender value deadline v r' s =>
      simp only [startTyped, immediate]
      split
      · split
        · exact Frame.fail_firstAt entered
        · exact Frame.suspend_firstAt (Frame.withEvents_firstAt entered (fun _ => rfl))
            (fun c h => by cases h)
      · exact Frame.fail_firstAt entered
    all_goals
      simp only [startTyped, immediate]
      cases opened : (Frame.enter current ctx _).lock with
      | error failure => exact Frame.fail_firstAt entered
      | ok locked =>
        have lockedEq := opened
        rw [Frame.lock] at lockedEq
        split_ifs at lockedEq
        cases lockedEq
        have lockedAt : ({ Frame.enter current ctx _ with current :=
            { (Frame.enter current ctx _).current with state :=
              { (Frame.enter current ctx _).current.state with unlocked := 0 } } } : Frame).FirstAt
              r current.updates :=
          Frame.withEvents_firstAt (events := []) entered (fun _ => rfl)
        simp only []
        repeat' split
        all_goals first
          | exact Frame.fail_firstAt lockedAt
          | exact Frame.suspend_firstAt lockedAt (fun c h hu => by cases h; exact hc.1 hu)
          | exact Frame.suspend_firstAt lockedAt (fun c h => by cases h)

mutual

theorem drive_firstAt (fuel : Nat) {L : List TaggedOracleUpdate} {segment : SegmentResult}
    {transcript : Transcript}
    (hs : segment.FirstAt r L) : (drive fuel segment transcript).frame.FirstAt r L := by
  cases fuel with
  | zero => cases segment <;> first | exact hs | exact hs.1
  | succ fuel =>
    cases segment with
    | finished frame returndata => exact hs
    | failed frame failure => cases failure <;> exact hs
    | suspended frame request continuation =>
      cases transcript with
      | done => exact hs.1
      | foreignLog emitter topics data tail => exact hs.1
      | invoke sender value isStatic entry child tail => exact hs.1
      | next result turns tail =>
        rw [drive]
        cases missing : request.requiresCode && !result.codeExists with
        | true => exact drive_firstAt fuel (resumeSegment_firstAt hs.1 hs.2)
        | false =>
          have turnsAt := driveTurns_firstAt fuel frame request 0 turns hs.1
          cases complete : (driveTurns fuel frame request 0 turns).complete with
          | false =>
            simp only [Bool.false_eq_true, complete, ite_false]
            exact turnsAt.1
          | true =>
            have settledAt : (frame.settleExternal fuel request result turns).FirstAt r L ∧
                ContAt r (frame.settleExternal fuel request result turns) continuation := by
              rw [Frame.settleExternal]
              cases successful : result.success with
              | true =>
                simp only [ite_true]
                refine ⟨turnsAt.1, fun c h hu => hs.2 c h ?_⟩
                by_contra ne
                exact turnsAt.2.1 ne hu
              | false =>
                simp only [Bool.false_eq_true, ite_false]
                refine ⟨⟨turnsAt.1.1, hs.1.2.1, turnsAt.1.2.2.1, ?_⟩, hs.2⟩
                change (driveTurns fuel frame request 0 turns).frame.checkpoint.updates ≠ [] → _
                rw [turnsAt.2.2]
                exact hs.1.2.2.2
            have resumed := drive_firstAt fuel (transcript := tail)
              (resumeSegment_firstAt (request := request) (result := result)
                settledAt.1 settledAt.2)
            simpa only [Bool.false_eq_true, complete, ite_true, ite_false, Frame.settleExternal]
              using resumed

theorem driveTurns_firstAt (fuel : Nat) {L : List TaggedOracleUpdate} (frame : Frame)
    (request : Request) (turn : Nat) (turns : Transcript) (hf : frame.FirstAt r L) :
    (driveTurns fuel frame request turn turns).frame.FirstAt r L ∧
      (frame.current.updates ≠ [] →
        (driveTurns fuel frame request turn turns).frame.current.updates ≠ []) ∧
      (driveTurns fuel frame request turn turns).frame.checkpoint = frame.checkpoint := by
  cases fuel with
  | zero => exact ⟨hf, id, rfl⟩
  | succ fuel =>
    cases turns with
    | done => exact ⟨hf, id, rfl⟩
    | next result children tail => exact ⟨hf, id, rfl⟩
    | foreignLog emitter topics data tail =>
      rw [driveTurns]
      cases staticExternal : externalStatic frame request with
      | true =>
        simp only [ite_true]
        exact ⟨hf, id, by trivial⟩
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact driveTurns_firstAt fuel _ request (turn + 1) tail
          ⟨hf.1, ⟨hf.2.1.1, hf.2.1.2⟩, hf.2.2.1, hf.2.2.2⟩
    | invoke sender value isStatic entry transcript tail =>
      let context := childContext frame request turn sender value isStatic
      have childAt := drive_firstAt fuel (transcript := transcript)
        (startTyped_firstAt (ctx := context) (entry := entry) hf.2.1)
      let child := drive fuel (startTyped frame.current context entry) transcript
      have grow : frame.current.updates ≠ [] → child.frame.current.updates ≠ [] :=
        fun h => childAt.2.2.2 (childAt.2.2.1 h)
      let settled : Frame := { frame with current := child.frame.current }
      have settledAt : settled.FirstAt r L :=
        ⟨hf.1, childAt.2.1, hf.2.2.1, fun h => grow (hf.2.2.2 h)⟩
      have tailAt := driveTurns_firstAt fuel settled request (turn + 1) tail settledAt
      rw [driveTurns]
      cases childStatus : (drive fuel (startTyped frame.current context entry) transcript).status with
      | incomplete => exact ⟨hf, id, rfl⟩
      | success returndata =>
        simpa only [childStatus, settled, child, context] using
          (⟨tailAt.1, fun h => tailAt.2.1 (grow h), tailAt.2.2⟩ : _ ∧ _ ∧ _)
      | failed failure =>
        simpa only [childStatus, settled, child, context] using
          (⟨tailAt.1, fun h => tailAt.2.1 (grow h), tailAt.2.2⟩ : _ ∧ _ ∧ _)

end

end

/-! ## One run: the receipts collapse to one `(Δ, increment)` -/

/-- The first receipt of a run was taken at the run's entry reserves. -/
theorem runTyped_firstAt (st : State) (ctx : Context) (entry : Entry) (transcript : Transcript) :
    (runTyped st ctx entry transcript).frame.current.FirstAt st.cachedReserves :=
  (drive_firstAt (transcript.work + 2) (startTyped_firstAt (ctx := ctx) (entry := entry)
    (Checkpoint.firstAt_initial st))).2.1

theorem uint32_ofNat_mod_toNat (n : Nat) : (UInt32.ofNat (n % 2 ^ 32)).toNat = n % 2 ^ 32 := by
  rw [UInt32.toNat_ofNat', Nat.mod_mod]

theorem wrapElapsed_self (n : Nat) : wrapElapsed n n = 0 := by
  rw [wrapElapsed, Nat.add_sub_cancel_left, Nat.mod_self]

/-- A timestamp chain whose receipts all carry `ts`, started at `ts mod 2^32`, stays there: every
receipt's old timestamp and the final timestamp are `ts mod 2^32`. -/
theorem OracleTimestampChain.stamped {ts : B256} :
    ∀ {fin : UInt32} {rest : List TaggedOracleUpdate},
      (∀ v ∈ rest, v.update.timestamp = ts) →
      OracleTimestampChain (UInt32.ofNat (ts.toNat % 2 ^ 32)) fin rest →
      fin = UInt32.ofNat (ts.toNat % 2 ^ 32) ∧
        ∀ v ∈ rest, v.update.oldTimestamp = UInt32.ofNat (ts.toNat % 2 ^ 32)
  | _, [], _, chain => ⟨chain, fun _ h => nomatch h⟩
  | _, v :: rest, stamped, chain => by
    obtain ⟨old, tail⟩ := chain
    rw [stamped v List.mem_cons_self] at tail
    obtain ⟨finEq, olds⟩ := OracleTimestampChain.stamped
      (fun w h => stamped w (List.mem_cons_of_mem _ h)) tail
    refine ⟨finEq, fun w h => ?_⟩
    rcases List.mem_cons.mp h with rfl | h
    · exact old
    · exact olds w h

/-- A lawful receipt with no elapsed time has zero increments. -/
theorem OracleUpdate.Lawful.increments_zero {u : OracleUpdate} (lawful : u.Lawful)
    (still : u.oldTimestamp = UInt32.ofNat (u.timestamp.toNat % 2 ^ 32)) :
    u.increment0 = 0 ∧ u.increment1 = 0 := by
  have elapsed : u.elapsed = 0 := by
    rw [lawful.1, still, uint32_ofNat_mod_toNat]
    exact wrapElapsed_self _
  have inactive : ¬ (u.elapsed > 0 ∧ u.oldReserve0 ≠ 0 ∧ u.oldReserve1 ≠ 0) := by
    rw [elapsed]
    exact fun h => absurd h.1 (Nat.lt_irrefl 0)
  exact ⟨by rw [lawful.2.1, ite_eq_right inactive], by rw [lawful.2.2, ite_eq_right inactive]⟩

theorem oracleSum_zero : ∀ {rest : List TaggedOracleUpdate},
    (∀ v ∈ rest, v.update.increment0 = 0 ∧ v.update.increment1 = 0) →
      oracleSum0 rest = 0 ∧ oracleSum1 rest = 0
  | [], _ => ⟨rfl, rfl⟩
  | v :: rest, zero => by
    have tail := oracleSum_zero (fun w h => zero w (List.mem_cons_of_mem _ h))
    have here := zero v List.mem_cons_self
    rw [oracleSum0, oracleSum1, here.1, here.2, tail.1, tail.2]
    exact ⟨rfl, rfl⟩

/-- **The oracle receipts of one invocation collapse to one `(Δ, increment)`.**  Either the run
emitted no receipt, or its first receipt was taken at the entry reserves and the entry timestamp,
carries the run's timestamp, and every later receipt has zero increments. -/
theorem runTyped_receipts_collapse (st : State) (ctx : Context) (entry : Entry)
    (transcript : Transcript) :
    (runTyped st ctx entry transcript).frame.current.updates = [] ∨
      ∃ u rest, (runTyped st ctx entry transcript).frame.current.updates = u :: rest ∧
        u.update.Lawful ∧
        u.update.oldReserve0 = st.reserve0.val ∧ u.update.oldReserve1 = st.reserve1.val ∧
        u.update.oldTimestamp = st.blockTimestampLast ∧ u.update.timestamp = ctx.timestamp ∧
        (runTyped st ctx entry transcript).frame.current.state.blockTimestampLast =
          UInt32.ofNat (ctx.timestamp.toNat % 2 ^ 32) ∧
        ∀ v ∈ rest, v.update.increment0 = 0 ∧ v.update.increment1 = 0 := by
  obtain ⟨lawful, chain, -, -⟩ :=
    runTyped_oracle_law (st := st) (ctx := ctx) (entry := entry) (transcript := transcript)
  have stamped := runTyped_stamped (st := st) (ctx := ctx) (entry := entry)
    (transcript := transcript)
  have first := runTyped_firstAt st ctx entry transcript
  revert lawful chain stamped first
  generalize (runTyped st ctx entry transcript).frame.current = c
  intro lawful chain stamped first
  rcases c with ⟨post, logs, updates⟩
  dsimp only at lawful chain stamped first ⊢
  cases updates with
  | nil => exact Or.inl rfl
  | cons u rest =>
    refine Or.inr ⟨u, rest, rfl, lawful u List.mem_cons_self, ?_⟩
    obtain ⟨old, tail⟩ := chain
    have uTs := stamped u List.mem_cons_self
    rw [uTs] at tail
    obtain ⟨finEq, olds⟩ := OracleTimestampChain.stamped
      (fun w h => stamped w (List.mem_cons_of_mem _ h)) tail
    have reserves := first.2 u rfl
    refine ⟨reserves.1, reserves.2, old, uTs, finEq, fun v h => ?_⟩
    refine (lawful v (List.mem_cons_of_mem _ h)).increments_zero ?_
    rw [olds v h, stamped v (List.mem_cons_of_mem _ h)]

/-- **One invocation's oracle effect.**  Each accumulator advances by the TWAP increment of the
entry reserves over the stored-timestamp advance (`wrapElapsed`, modulo `2 ^ 32`), modulo
`2 ^ 256`; the stored timestamp stays or becomes the run's timestamp modulo `2 ^ 32`. -/
theorem runTyped_oracle_call (st : State) (ctx : Context) (entry : Entry)
    (transcript : Transcript) :
    (runTyped st ctx entry transcript).frame.current.state.price0CumulativeLast.toNat =
        (st.price0CumulativeLast.toNat + twapIncrement st.reserve0.val st.reserve1.val
          (wrapElapsed st.blockTimestampLast.toNat
            (runTyped st ctx entry transcript).frame.current.state.blockTimestampLast.toNat)) %
          2 ^ 256 ∧
      (runTyped st ctx entry transcript).frame.current.state.price1CumulativeLast.toNat =
        (st.price1CumulativeLast.toNat + twapIncrement st.reserve1.val st.reserve0.val
          (wrapElapsed st.blockTimestampLast.toNat
            (runTyped st ctx entry transcript).frame.current.state.blockTimestampLast.toNat)) %
          2 ^ 256 ∧
      ((runTyped st ctx entry transcript).frame.current.state.blockTimestampLast =
          st.blockTimestampLast ∨
        (runTyped st ctx entry transcript).frame.current.state.blockTimestampLast.toNat =
          ctx.timestamp.toNat % 2 ^ 32) := by
  obtain ⟨-, chain, acc0, acc1⟩ :=
    runTyped_oracle_law (st := st) (ctx := ctx) (entry := entry) (transcript := transcript)
  have collapse := runTyped_receipts_collapse st ctx entry transcript
  rw [acc0, acc1, oracleFold0_law, oracleFold1_law]
  revert chain collapse
  generalize (runTyped st ctx entry transcript).frame.current = c
  intro chain collapse
  rcases collapse with none | ⟨u, rest, hU, lawful, old0, old1, oldTs, uTs, finEq, later⟩
  · rw [none] at chain ⊢
    change c.state.blockTimestampLast = st.blockTimestampLast at chain
    rw [chain, wrapElapsed_self, twapIncrement, twapIncrement, ite_eq_right (fun h => absurd h.1
      (Nat.lt_irrefl 0)), ite_eq_right (fun h => absurd h.1 (Nat.lt_irrefl 0))]
    exact ⟨rfl, rfl, Or.inl rfl⟩
  · have rest0 := oracleSum_zero later
    have elapsed : u.update.elapsed =
        wrapElapsed st.blockTimestampLast.toNat c.state.blockTimestampLast.toNat := by
      rw [lawful.1, finEq, uint32_ofNat_mod_toNat, uTs, oldTs, wrapElapsed]
    rw [hU, oracleSum0, oracleSum1, rest0.1, rest0.2, Nat.add_zero, Nat.add_zero,
      lawful.2.1, lawful.2.2, elapsed, old0, old1]
    refine ⟨rfl, ?_, Or.inr (by rw [finEq, uint32_ofNat_mod_toNat])⟩
    unfold twapIncrement
    by_cases active : wrapElapsed st.blockTimestampLast.toNat c.state.blockTimestampLast.toNat > 0 ∧
        st.reserve0.val ≠ 0 ∧ st.reserve1.val ≠ 0
    · rw [ite_eq_left active, ite_eq_left ⟨active.1, active.2.2, active.2.1⟩]
    · rw [ite_eq_right active, ite_eq_right (fun h => active ⟨h.1, h.2.2, h.2.1⟩)]

end Blanc.Lift.UniswapV2Pair
