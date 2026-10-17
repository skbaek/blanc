import Blanc.Lift.UniswapV2Pair.Properties
import Blanc.Lift.UniswapV2Pair.PropertiesSides

/-!
# The model ghost of an outer Pair step (C3, U6c2)

Pure facts about the typed Pair model, consumed by the per-step lemma
(`PairTokenStepModel.lean`).  Along one outer step the Pair's booked balance `b` of the side's
token `T` moves only at the step's own external calls; `CallBal` records what one call does to it
(the model-side abstraction of `StepOracle`).  At every suspension the ghost `ContGhost` relates
the continuation's carried words and the frame's reserves to `b`, and `ContObl` states what the
remaining transcript answers (only `sync` and `burn` carry an obligation: their
`EntryNoShrinkSide` premise).

* `resumeSegment_ghost`: a resumption keeps the ghost, and a non-failed resumption whose remaining
  obligation holds discharges the obligation of the call it resumes from;
* `startTyped_ghost`: an outer entry at an unlocked state whose side reserve is at most `b` starts
  with the ghost.
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-- A proposition per token side. -/
abbrev OnSide (side : TokenSide) (p0 p1 : Prop) : Prop :=
  match side with
  | .zero => p0
  | .one => p1

/-- What one observed call does to the Pair's booked balance `b` of the side's token `T`
(`b'` after the call's retained subtree), as the model consumes it. -/
structure CallBal (T pair : Adr) (fr : UniswapV2Pair.Frame) (request : Request) (reply : ExternalResult)
    (b b' : Nat) : Prop where
  static : externalStatic fr request = true → b' = b
  read : request.target = T → request.calldata = (ExternalOperation.balanceOf pair).encode →
    reply.success = true → (Bytes.toB256 (reply.returndata.take 32)).toNat = b
  transfer : ∀ {recipient : Adr} {value : B256}, request.target = T →
    request.calldata = (ExternalOperation.transfer recipient value).encode →
    externalStatic fr request = false → b ≤ b' + value.toNat
  other : request.target ≠ T → externalStatic fr request = false → b ≤ b'

/-- The ghost at a suspension of an outer step, against the booked balance `b`. -/
def ContGhost (side : TokenSide) (t0 t1 : Adr) (b : Nat) (fr : UniswapV2Pair.Frame) (request : Request) :
    Continuation → Prop
  | .mintBalance0 _ _ =>
      request = requestFor .mintBalance0 t0 (.balanceOf fr.context.pair) ∧
        fr.current.state.token1 = t1
  | .mintBalance1 _ _ balance0 =>
      request = requestFor .mintBalance1 t1 (.balanceOf fr.context.pair) ∧
        OnSide side (balance0.toNat ≤ b) True
  | .mintFee observed => (∃ t, request = requestFor .mintFeeTo t .feeTo) ∧
      OnSide side (observed.balance0.toNat ≤ b) (observed.balance1.toNat ≤ b)
  | .burnInitialBalance0 locals =>
      request = requestFor .burnInitialBalance0 t0 (.balanceOf fr.context.pair) ∧
        locals.token0 = t0 ∧ locals.token1 = t1 ∧
        OnSide side (locals.reserves.reserve0.val ≤ b) (locals.reserves.reserve1.val ≤ b)
  | .burnInitialBalance1 locals balance0 =>
      request = requestFor .burnInitialBalance1 t1 (.balanceOf fr.context.pair) ∧
        locals.token0 = t0 ∧ locals.token1 = t1 ∧
        OnSide side (locals.reserves.reserve0.val ≤ balance0.toNat ∧ balance0.toNat ≤ b)
          (locals.reserves.reserve1.val ≤ b)
  | .burnFee observed => (∃ t, request = requestFor .burnFeeTo t .feeTo) ∧
      observed.locals.token0 = t0 ∧ observed.locals.token1 = t1 ∧
      OnSide side
        (observed.locals.reserves.reserve0.val ≤ observed.balance0.toNat ∧
          observed.balance0.toNat ≤ b)
        (observed.locals.reserves.reserve1.val ≤ observed.balance1.toNat ∧
          observed.balance1.toNat ≤ b)
  | .burnTransfer0 p =>
      request = requestFor .burnTransfer0 t0 (.transfer p.observed.locals.recipient p.amount0) ∧
        p.observed.locals.token0 = t0 ∧ p.observed.locals.token1 = t1 ∧
        OnSide side (p.observed.balance0.toNat ≤ b) (p.observed.balance1.toNat ≤ b)
  | .burnTransfer1 p =>
      request = requestFor .burnTransfer1 t1 (.transfer p.observed.locals.recipient p.amount1) ∧
        p.observed.locals.token0 = t0 ∧ p.observed.locals.token1 = t1 ∧
        OnSide side (p.observed.balance0.toNat ≤ b + p.amount0.toNat)
          (p.observed.balance1.toNat ≤ b)
  | .burnFinalBalance0 p =>
      request = requestFor .burnFinalBalance0 t0 (.balanceOf fr.context.pair) ∧
        p.observed.locals.token1 = t1 ∧
        OnSide side (p.observed.balance0.toNat ≤ b + p.amount0.toNat)
          (p.observed.balance1.toNat ≤ b + p.amount1.toNat)
  | .burnFinalBalance1 p balance0 =>
      request = requestFor .burnFinalBalance1 t1 (.balanceOf fr.context.pair) ∧
        OnSide side (balance0.toNat ≤ b) (p.observed.balance1.toNat ≤ b + p.amount1.toNat)
  | .swapTransfer0 l =>
      request = requestFor .swapTransfer0 t0 (.transfer l.recipient l.amount0Out) ∧
        l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .swapTransfer1 l =>
      request = requestFor .swapTransfer1 t1 (.transfer l.recipient l.amount1Out) ∧
        l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .swapCallback l =>
      request = requestFor .swapCallback l.recipient
          (.callback fr.context.sender l.amount0Out l.amount1Out l.data) ∧
        l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .swapBalance0 l =>
      request = requestFor .swapBalance0 t0 (.balanceOf fr.context.pair) ∧ l.token1 = t1
  | .swapBalance1 _ balance0 =>
      request = requestFor .swapBalance1 t1 (.balanceOf fr.context.pair) ∧
        OnSide side (balance0.toNat ≤ b) True
  | .skimBalance0 l =>
      request = requestFor .skimBalance0 t0 (.balanceOf fr.context.pair) ∧
        l.token0 = t0 ∧ l.token1 = t1 ∧ fr.current.state.reserveOn side ≤ b ∧
        fr.current.state.unlocked = 0
  | .skimTransfer0 l =>
      (∃ v, request = requestFor .skimTransfer0 t0 (.transfer l.recipient v) ∧
        OnSide side (fr.current.state.reserve0.val + v.toNat ≤ b)
          (fr.current.state.reserve1.val ≤ b)) ∧
        l.token1 = t1 ∧ fr.current.state.unlocked = 0
  | .skimBalance1 l =>
      request = requestFor .skimBalance1 t1 (.balanceOf fr.context.pair) ∧
        l.token1 = t1 ∧ fr.current.state.reserveOn side ≤ b ∧ fr.current.state.unlocked = 0
  | .skimTransfer1 l =>
      (∃ v, request = requestFor .skimTransfer1 t1 (.transfer l.recipient v) ∧
        OnSide side (fr.current.state.reserve0.val ≤ b)
          (fr.current.state.reserve1.val + v.toNat ≤ b)) ∧
        fr.current.state.unlocked = 0
  | .syncBalance0 reserves =>
      request = requestFor .syncBalance0 t0 (.balanceOf fr.context.pair) ∧
        fr.current.state.token1 = t1 ∧
        OnSide side (reserves.reserve0.val ≤ b) (reserves.reserve1.val ≤ b)
  | .syncBalance1 reserves balance0 =>
      request = requestFor .syncBalance1 t1 (.balanceOf fr.context.pair) ∧
        OnSide side (balance0.toNat ≤ b) (reserves.reserve1.val ≤ b)
  | .permitRecovery _ _ _ =>
      (∃ digest v r s, request = requestFor .permitRecovery 1 (.recover digest v r s)) ∧
        fr.current.state.reserveOn side ≤ b

/-- The ghost of a segment: a finished outer step has its side reserve at most `b`. -/
def SegGhost (side : TokenSide) (t0 t1 : Adr) (b : Nat) : SegmentResult → Prop
  | .finished fr _ => fr.current.state.reserveOn side ≤ b
  | .failed _ _ => True
  | .suspended fr request cont => ContGhost side t0 t1 b fr request cont

/-- What the remaining transcript answers from a suspension (`sync` and `burn` only). -/
def ContObl (side : TokenSide) (fr : UniswapV2Pair.Frame) (transcript : Transcript) : Continuation → Prop
  | .syncBalance0 reserves =>
      OnSide side (reserves.reserve0.val ≤ transcript.firstWord.toNat)
        (reserves.reserve1.val ≤ transcript.ownTail.firstWord.toNat)
  | .syncBalance1 reserves _ =>
      OnSide side True (reserves.reserve1.val ≤ transcript.firstWord.toNat)
  | .burnInitialBalance0 locals =>
      BurnFeeNoShrinkSide side fr.current.state
        { locals := locals, balance0 := transcript.firstWord,
          balance1 := transcript.ownTail.firstWord,
          liquidity := fr.current.state.balanceOf fr.context.pair } transcript.ownTail.ownTail
  | .burnInitialBalance1 locals balance0 =>
      BurnFeeNoShrinkSide side fr.current.state
        { locals := locals, balance0 := balance0, balance1 := transcript.firstWord,
          liquidity := fr.current.state.balanceOf fr.context.pair } transcript.ownTail
  | .burnFee observed => BurnFeeNoShrinkSide side fr.current.state observed transcript
  | .burnTransfer0 p =>
      OnSide side
        (p.observed.balance0.toNat ≤ transcript.ownTail.ownTail.firstWord.toNat + p.amount0.toNat)
        (p.observed.balance1.toNat ≤
          transcript.ownTail.ownTail.ownTail.firstWord.toNat + p.amount1.toNat)
  | .burnTransfer1 p =>
      OnSide side (p.observed.balance0.toNat ≤ transcript.ownTail.firstWord.toNat + p.amount0.toNat)
        (p.observed.balance1.toNat ≤ transcript.ownTail.ownTail.firstWord.toNat + p.amount1.toNat)
  | .burnFinalBalance0 p =>
      OnSide side (p.observed.balance0.toNat ≤ transcript.firstWord.toNat + p.amount0.toNat)
        (p.observed.balance1.toNat ≤ transcript.ownTail.firstWord.toNat + p.amount1.toNat)
  | .burnFinalBalance1 p _ =>
      OnSide side True (p.observed.balance1.toNat ≤ transcript.firstWord.toNat + p.amount1.toNat)
  | _ => True

/-- The obligation of a segment. -/
def SegObl (side : TokenSide) (transcript : Transcript) : SegmentResult → Prop
  | .suspended fr _ cont => ContObl side fr transcript cont
  | _ => True

/-- A segment that is not a failure. -/
def NotFailed : SegmentResult → Prop
  | .failed _ _ => False
  | _ => True

/-- The prior frame a resumption starts from, against the suspended frame. -/
structure PriorOk (fr prior : UniswapV2Pair.Frame) (request : Request) : Prop where
  context : prior.context = fr.context
  static : externalStatic fr request = true → prior.current = fr.current
  core : fr.current.state.unlocked = 0 →
    prior.current.state.economicCore = fr.current.state.economicCore

/-- What a resumption from `.suspended fr _ cont` with `reply` delivers. -/
def Resumed (side : TokenSide) (t0 t1 : Adr) (b' : Nat) (fr : UniswapV2Pair.Frame) (cont : Continuation)
    (reply : ExternalResult) (turns tail : Transcript) (seg : SegmentResult) : Prop :=
  SegGhost side t0 t1 b' seg ∧
    (NotFailed seg → SegObl side tail seg → ContObl side fr (.next reply turns tail) cont)

/-! ## Decoding -/

theorem decode_read {site : CallSite} {t owner : Adr} {reply : ExternalResult}
    {d : DecodedResult} (h : decodeExternal (requestFor site t (.balanceOf owner)) reply = .ok d) :
    reply.success = true ∧ d = .word (Bytes.toB256 (reply.returndata.take 32)) := by
  simp only [decodeExternal, requestFor] at h
  cases hc : reply.codeExists <;> cases hs : reply.success <;>
    simp only [hc, hs, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h
  split_ifs at h
  cases h
  exact ⟨rfl, rfl⟩

theorem decode_feeTo {site : CallSite} {t : Adr} {reply : ExternalResult} {d : DecodedResult}
    (h : decodeExternal (requestFor site t .feeTo) reply = .ok d) :
    d = .address (Bytes.toB256 (reply.returndata.take 32)).toAdr := by
  simp only [decodeExternal, requestFor] at h
  cases hc : reply.codeExists <;> cases hs : reply.success <;>
    simp only [hc, hs, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h
  split_ifs at h
  cases h
  rfl

theorem decode_transfer {site : CallSite} {t recipient : Adr} {value : B256}
    {reply : ExternalResult} {d : DecodedResult}
    (h : decodeExternal (requestFor site t (.transfer recipient value)) reply = .ok d) :
    d = .unit := by
  simp only [decodeExternal, requestFor] at h
  cases hc : reply.codeExists <;> cases hs : reply.success <;>
    simp only [hc, hs, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h <;>
    (split_ifs at h <;> cases h) <;> rfl

theorem finishUpdated_ghost {side : TokenSide} {t0 t1 : Adr} {b : Nat} {fr : UniswapV2Pair.Frame}
    {balance0 balance1 : B256} {reserves : CachedReserves} {feeOn : Bool}
    {lastEvent : Option Event} {returndata : Bytes}
    (held : OnSide side (balance0.toNat ≤ b) (balance1.toNat ≤ b)) :
    SegGhost side t0 t1 b (fr.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata) := by
  have terminal := Frame.finishUpdated_terminal fr balance0 balance1 reserves feeOn lastEvent returndata
  cases h : fr.finishUpdated balance0 balance1 reserves feeOn lastEvent returndata with
  | finished final output =>
    obtain ⟨-, r0, r1⟩ := Frame.finishUpdated_supply_reserves h
    cases side
    · change final.current.state.reserve0.val ≤ b
      rw [r0]
      exact held
    · change final.current.state.reserve1.val ≤ b
      rw [r1]
      exact held
  | failed final failure => exact trivial
  | suspended final request cont =>
    rw [h] at terminal
    exact terminal.elim

theorem mintAfterFee_ghost {side : TokenSide} {t0 t1 : Adr} {b : Nat} {fr : UniswapV2Pair.Frame}
    {observed : MintObserved} {fee : FeeResult}
    (held : OnSide side (observed.balance0.toNat ≤ b) (observed.balance1.toNat ≤ b)) :
    SegGhost side t0 t1 b (fr.mintAfterFee observed fee) := by
  unfold Frame.mintAfterFee
  dsimp only
  split
  · exact trivial
  · split
    · exact trivial
    · split_ifs
      · split
        · exact trivial
        · exact finishUpdated_ghost held
      · exact trivial

theorem skim_value {w : B256} {r : Nat} (bound : r < 2 ^ 112) (covered : r ≤ w.toNat) :
    (w - Nat.toB256 r).toNat = w.toNat - r := by
  have lt : r < 2 ^ 256 := Nat.lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) (by decide))
  rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by
    rw [B256.toNat_toB256_of_lt lt]
    exact covered)), B256.toNat_toB256_of_lt lt]

theorem CallBal.transferAt {T pair : Adr} {fr : UniswapV2Pair.Frame} {site : CallSite}
    {t recipient : Adr} {value : B256} {reply : ExternalResult} {b b' : Nat}
    (bal : CallBal T pair fr (requestFor site t (.transfer recipient value)) reply b b') :
    (t = T → b ≤ b' + value.toNat) ∧ (t ≠ T → b ≤ b') := by
  cases mutable : externalStatic fr (requestFor site t (.transfer recipient value))
  · exact ⟨fun target => bal.transfer target rfl mutable, fun apart => bal.other apart mutable⟩
  · have same := bal.static mutable
    subst same
    exact ⟨fun _ => Nat.le_add_right _ _, fun _ => Nat.le_refl _⟩

theorem burnFinalAnswerOn_zero_eq {t : Transcript} {w : B256}
    (h : burnFinalAnswerOn .zero t = some w) : w = t.ownTail.ownTail.firstWord := by
  rcases t with _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _⟩ | _ | _⟩ | _ | _⟩ | _ | _⟩ | _ | _
  all_goals first
    | exact (Option.some.inj h).symm
    | simp only [burnFinalAnswerOn, reduceCtorEq] at h

theorem burnFinalAnswerOn_one_eq {t : Transcript} {w : B256}
    (h : burnFinalAnswerOn .one t = some w) : w = t.ownTail.ownTail.ownTail.firstWord := by
  rcases t with _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _ | ⟨_, _, _⟩ | _ | _⟩ | _ | _⟩ | _ | _⟩ | _ | _
  all_goals first
    | exact (Option.some.inj h).symm
    | simp only [burnFinalAnswerOn, reduceCtorEq] at h

/-! ## Resumption, per continuation -/

theorem externalStatic_read {fr : UniswapV2Pair.Frame} {site : CallSite} {t owner : Adr} :
    externalStatic fr (requestFor site t (.balanceOf owner)) = true := by
  simp only [externalStatic, requestFor, beq_self_eq_true, Bool.or_true]

theorem CallBal.readAt {T pair : Adr} {fr : UniswapV2Pair.Frame} {site : CallSite}
    {t owner : Adr} {reply : ExternalResult} {b b' : Nat}
    (bal : CallBal T pair fr (requestFor site t (.balanceOf owner)) reply b b') (target : t = T)
    (owner_eq : owner = pair) (success : reply.success = true) :
    (Bytes.toB256 (reply.returndata.take 32)).toNat = b :=
  bal.read target (by rw [owner_eq]; rfl) success

theorem resume_syncBalance0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {reserves : CachedReserves}
    (ghost : ContGhost side t0 t1 b fr request (.syncBalance0 reserves))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.syncBalance0 reserves) reply turns tail
      (resumeSegment prior request (.syncBalance0 reserves) reply) := by
  obtain ⟨rfl, token1, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .syncBalance0 t0 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    simp only [resumeSegment, decoded, Frame.suspend, Frame.beginResume]
    subst same
    rw [current, priorOk.context, token1]
    refine ⟨⟨rfl, ?_⟩, fun _ obligation => ?_⟩
    · cases side
      · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)
      · exact held
    · cases side
      · change reserves.reserve0.val ≤ (Bytes.toB256 (reply.returndata.take 32)).toNat
        rw [bal.readAt hT.symm pairEq success]
        exact held
      · exact obligation

theorem resume_syncBalance1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {reserves : CachedReserves} {balance0 : B256}
    (ghost : ContGhost side t0 t1 b fr request (.syncBalance1 reserves balance0))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.syncBalance1 reserves balance0) reply turns tail
      (resumeSegment prior request (.syncBalance1 reserves balance0) reply) := by
  obtain ⟨rfl, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .syncBalance1 t1 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded]
    refine ⟨finishUpdated_ghost ?_, fun _ _ => ?_⟩
    · cases side
      · exact held
      · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)
    · cases side
      · trivial
      · change reserves.reserve1.val ≤ (Bytes.toB256 (reply.returndata.take 32)).toNat
        rw [bal.readAt hT.symm pairEq success]
        exact held

theorem resume_mintBalance0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {recipient : Adr} {reserves : CachedReserves}
    (ghost : ContGhost side t0 t1 b fr request (.mintBalance0 recipient reserves))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.mintBalance0 recipient reserves) reply turns tail
      (resumeSegment prior request (.mintBalance0 recipient reserves) reply) := by
  obtain ⟨rfl, token1⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .mintBalance0 t0 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded, Frame.suspend, Frame.beginResume]
    rw [current, priorOk.context, token1]
    refine ⟨⟨rfl, ?_⟩, fun _ _ => trivial⟩
    cases side
    · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)
    · trivial

theorem resume_mintBalance1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {recipient : Adr} {reserves : CachedReserves} {balance0 : B256}
    (ghost : ContGhost side t0 t1 b fr request (.mintBalance1 recipient reserves balance0))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.mintBalance1 recipient reserves balance0) reply turns tail
      (resumeSegment prior request (.mintBalance1 recipient reserves balance0) reply) := by
  obtain ⟨rfl, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .mintBalance1 t1 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded]
    split_ifs
    · simp only [Frame.suspend, Frame.beginResume]
      refine ⟨⟨⟨_, rfl⟩, ?_⟩, fun _ _ => trivial⟩
      cases side
      · exact held
      · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)
    · exact ⟨trivial, fun notFailed => notFailed.elim⟩

theorem resume_mintFee {side : TokenSide} {t0 t1 T pair : Adr}
    (_hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {observed : MintObserved}
    (ghost : ContGhost side t0 t1 b fr request (.mintFee observed))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.mintFee observed) reply turns tail
      (resumeSegment prior request (.mintFee observed) reply) := by
  obtain ⟨⟨t, rfl⟩, held⟩ := ghost
  have stat : externalStatic fr (requestFor .mintFeeTo t .feeTo) = true := by
    simp only [externalStatic, requestFor, beq_self_eq_true, Bool.or_true]
  have same := bal.static stat
  subst same
  cases decoded : decodeExternal (requestFor .mintFeeTo t .feeTo) reply with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    rw [decode_feeTo decoded] at decoded
    simp only [resumeSegment, decoded]
    split
    · exact ⟨trivial, fun notFailed => notFailed.elim⟩
    · exact ⟨mintAfterFee_ghost held, fun _ _ => trivial⟩

theorem burnAfterFee_cases (frame : UniswapV2Pair.Frame) (observed : BurnObserved)
    (fee : FeeResult) :
    (∃ fr' failure, frame.burnAfterFee observed fee = .failed fr' failure) ∨
    ∃ (fr' : UniswapV2Pair.Frame) (amount0 amount1 : Nat),
      burnAmounts observed.liquidity observed.balance0 observed.balance1 fee.state.totalSupply =
        .ok (amount0, amount1) ∧
      frame.burnAfterFee observed fee = .suspended fr'
        (requestFor .burnTransfer0 observed.locals.token0
          (.transfer observed.locals.recipient (Nat.toB256 amount0)))
        (.burnTransfer0 (BurnPriced.mk observed fee.feeOn fee.minted fee.state.totalSupply
          (Nat.toB256 amount0) (Nat.toB256 amount1))) := by
  unfold Frame.burnAfterFee
  dsimp only
  split
  · exact Or.inl ⟨_, _, rfl⟩
  · rename_i amount0 amount1 priced
    split_ifs
    · split
      · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inr ⟨_, amount0, amount1, priced, rfl⟩
    · exact Or.inl ⟨_, _, rfl⟩

theorem resume_burnInitialBalance0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {locals : BurnLocals}
    (ghost : ContGhost side t0 t1 b fr request (.burnInitialBalance0 locals))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.burnInitialBalance0 locals) reply turns tail
      (resumeSegment prior request (.burnInitialBalance0 locals) reply) := by
  obtain ⟨rfl, token0, token1, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .burnInitialBalance0 t0 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded, Frame.suspend, Frame.beginResume]
    rw [current, priorOk.context, token1]
    refine ⟨⟨rfl, token0, token1, ?_⟩, fun _ obligation => obligation⟩
    cases side
    · rw [bal.readAt hT.symm pairEq success]
      exact ⟨held, Nat.le_refl _⟩
    · exact held

theorem resume_burnInitialBalance1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {locals : BurnLocals} {balance0 : B256}
    (ghost : ContGhost side t0 t1 b fr request (.burnInitialBalance1 locals balance0))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.burnInitialBalance1 locals balance0) reply turns tail
      (resumeSegment prior request (.burnInitialBalance1 locals balance0) reply) := by
  obtain ⟨rfl, token0, token1, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .burnInitialBalance1 t1 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded, Frame.suspend, Frame.beginResume]
    rw [current, priorOk.context]
    refine ⟨⟨⟨_, rfl⟩, token0, token1, ?_⟩, fun _ obligation => obligation⟩
    cases side
    · exact held
    · rw [bal.readAt hT.symm pairEq success]
      exact ⟨held, Nat.le_refl _⟩

theorem resume_burnFee {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {observed : BurnObserved}
    (ghost : ContGhost side t0 t1 b fr request (.burnFee observed))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.burnFee observed) reply turns tail
      (resumeSegment prior request (.burnFee observed) reply) := by
  obtain ⟨⟨t, rfl⟩, token0, token1, held⟩ := ghost
  have stat : externalStatic fr (requestFor .burnFeeTo t .feeTo) = true := by
    simp only [externalStatic, requestFor, beq_self_eq_true, Bool.or_true]
  have same := bal.static stat
  have current := priorOk.static stat
  subst same
  cases decoded : decodeExternal (requestFor .burnFeeTo t .feeTo) reply with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    rw [decode_feeTo decoded] at decoded
    simp only [resumeSegment, decoded]
    have resumed : (prior.beginResume (requestFor .burnFeeTo t .feeTo)).current = fr.current :=
      current
    rw [resumed]
    split
    · exact ⟨trivial, fun notFailed => notFailed.elim⟩
    · rename_i fee feeEq
      have feeSpec := mintFee_spec feeEq
      rcases burnAfterFee_cases (prior.beginResume (requestFor .burnFeeTo t .feeTo)) observed fee
        with ⟨fr', failure, h⟩ | ⟨fr', amount0, amount1, amounts, h⟩
      · rw [h]
        exact ⟨trivial, fun notFailed => notFailed.elim⟩
      · rw [h]
        have spec := burnAmounts_spec amounts
        refine ⟨⟨by rw [token0], token0, token1, ?_⟩, fun _ obligation => ?_⟩
        · cases side
          · exact held.2
          · exact held.2
        · cases side
          · refine ⟨held.1, fun final0 answer => ?_⟩
            rw [burnFinalAnswerOn_zero_eq answer]
            have bound : observed.balance0.toNat ≤ tail.ownTail.ownTail.firstWord.toNat +
                (Nat.toB256 amount0).toNat := obligation
            rw [spec.1, feeSpec.1, feeSpec.2.2] at bound
            exact bound
          · refine ⟨held.1, fun final1 answer => ?_⟩
            rw [burnFinalAnswerOn_one_eq answer]
            have bound : observed.balance1.toNat ≤ tail.ownTail.ownTail.ownTail.firstWord.toNat +
                (Nat.toB256 amount1).toNat := obligation
            rw [spec.2.1, feeSpec.1, feeSpec.2.2] at bound
            exact bound

theorem resume_burnTransfer0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {p : BurnPriced}
    (ghost : ContGhost side t0 t1 b fr request (.burnTransfer0 p))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.burnTransfer0 p) reply turns tail
      (resumeSegment prior request (.burnTransfer0 p) reply) := by
  obtain ⟨rfl, token0, token1, held⟩ := ghost
  have moved := bal.transferAt
  cases d : decodeExternal (requestFor .burnTransfer0 t0 (.transfer p.observed.locals.recipient p.amount0)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    rw [decode_transfer d] at d
    simp only [resumeSegment, d]
    simp only [Frame.suspend]
    rw [token1]
    refine ⟨⟨rfl, token0, token1, ?_⟩, fun _ obligation => obligation⟩
    cases side
    · exact Nat.le_trans held (moved.1 (hT : T = t0).symm)
    · exact Nat.le_trans held (moved.2 fun e => distinct (e.trans (hT : T = t1)))

theorem resume_burnTransfer1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {p : BurnPriced}
    (ghost : ContGhost side t0 t1 b fr request (.burnTransfer1 p))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.burnTransfer1 p) reply turns tail
      (resumeSegment prior request (.burnTransfer1 p) reply) := by
  obtain ⟨rfl, token0, token1, held⟩ := ghost
  have moved := bal.transferAt
  cases d : decodeExternal (requestFor .burnTransfer1 t1 (.transfer p.observed.locals.recipient p.amount1)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    rw [decode_transfer d] at d
    simp only [resumeSegment, d]
    simp only [Frame.suspend, Frame.beginResume]
    rw [token0, priorOk.context]
    refine ⟨⟨rfl, token1, ?_⟩, fun _ obligation => obligation⟩
    cases side
    · exact Nat.le_trans held
        (Nat.add_le_add_right (moved.2 fun e => distinct (e.trans (hT : T = t0)).symm) _)
    · exact Nat.le_trans held (moved.1 (hT : T = t1).symm)

theorem resume_burnFinalBalance0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {p : BurnPriced}
    (ghost : ContGhost side t0 t1 b fr request (.burnFinalBalance0 p))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.burnFinalBalance0 p) reply turns tail
      (resumeSegment prior request (.burnFinalBalance0 p) reply) := by
  obtain ⟨rfl, token1, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .burnFinalBalance0 t0 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded, Frame.suspend, Frame.beginResume]
    rw [current, priorOk.context, token1]
    refine ⟨⟨rfl, ?_⟩, fun _ obligation => ?_⟩
    · cases side
      · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)
      · exact held
    · cases side
      · change p.observed.balance0.toNat ≤
          (Bytes.toB256 (reply.returndata.take 32)).toNat + p.amount0.toNat
        rw [bal.readAt hT.symm pairEq success]
        exact held
      · exact obligation

theorem resume_burnFinalBalance1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {p : BurnPriced} {balance0 : B256}
    (ghost : ContGhost side t0 t1 b fr request (.burnFinalBalance1 p balance0))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.burnFinalBalance1 p balance0) reply turns tail
      (resumeSegment prior request (.burnFinalBalance1 p balance0) reply) := by
  obtain ⟨rfl, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .burnFinalBalance1 t1 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded]
    refine ⟨finishUpdated_ghost ?_, fun _ _ => ?_⟩
    · cases side
      · exact held
      · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)
    · cases side
      · trivial
      · change p.observed.balance1.toNat ≤
          (Bytes.toB256 (reply.returndata.take 32)).toNat + p.amount1.toNat
        rw [bal.readAt hT.symm pairEq success]
        exact held

theorem decode_callback {site : CallSite} {t sender : Adr} {amount0 amount1 : B256} {data : Bytes}
    {reply : ExternalResult} {d : DecodedResult}
    (h : decodeExternal (requestFor site t (.callback sender amount0 amount1 data)) reply = .ok d) :
    d = .unit := by
  simp only [decodeExternal, requestFor] at h
  cases hc : reply.codeExists <;> cases hs : reply.success <;>
    simp only [hc, hs, Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true,
      Bool.false_eq_true, ite_false, ite_true, reduceCtorEq] at h
  cases h
  rfl

theorem economicCore_reserves {st st' : UniswapV2Pair.State} (h : st'.economicCore = st.economicCore) :
    st'.reserve0 = st.reserve0 ∧ st'.reserve1 = st.reserve1 ∧ st'.unlocked = st.unlocked := by
  simp only [State.economicCore, Prod.mk.injEq] at h
  exact ⟨h.2.1.1, h.2.1.2, h.2.2.2.2.2⟩

theorem resume_swapTransfer0 {side : TokenSide} {t0 t1 T pair : Adr}
    (_hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SwapLocals}
    (ghost : ContGhost side t0 t1 b fr request (.swapTransfer0 l))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.swapTransfer0 l) reply turns tail
      (resumeSegment prior request (.swapTransfer0 l) reply) := by
  obtain ⟨rfl, token0, token1, apart0, apart1⟩ := ghost
  have moved := bal.transferAt
  cases d : decodeExternal (requestFor .swapTransfer0 t0 (.transfer l.recipient l.amount0Out)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    rw [decode_transfer d] at d
    simp only [resumeSegment, d]
    simp only [Frame.afterSwapTransfer0, Frame.afterSwapTransfer1]
    split_ifs
    · exact ⟨⟨by rw [token1], token0, token1, apart0, apart1⟩, fun _ _ => trivial⟩
    · exact ⟨⟨rfl, token0, token1, apart0, apart1⟩, fun _ _ => trivial⟩
    · exact ⟨⟨by rw [token0], token1⟩, fun _ _ => trivial⟩

theorem resume_swapTransfer1 {side : TokenSide} {t0 t1 T pair : Adr}
    (_hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SwapLocals}
    (ghost : ContGhost side t0 t1 b fr request (.swapTransfer1 l))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.swapTransfer1 l) reply turns tail
      (resumeSegment prior request (.swapTransfer1 l) reply) := by
  obtain ⟨rfl, token0, token1, apart0, apart1⟩ := ghost
  have moved := bal.transferAt
  cases d : decodeExternal (requestFor .swapTransfer1 t1 (.transfer l.recipient l.amount1Out)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    rw [decode_transfer d] at d
    simp only [resumeSegment, d]
    simp only [Frame.afterSwapTransfer1]
    split_ifs
    · exact ⟨⟨rfl, token0, token1, apart0, apart1⟩, fun _ _ => trivial⟩
    · exact ⟨⟨by rw [token0], token1⟩, fun _ _ => trivial⟩

theorem resume_swapCallback {side : TokenSide} {t0 t1 T pair : Adr}
    (_hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SwapLocals}
    (ghost : ContGhost side t0 t1 b fr request (.swapCallback l))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.swapCallback l) reply turns tail
      (resumeSegment prior request (.swapCallback l) reply) := by
  obtain ⟨rfl, token0, token1, -, -⟩ := ghost
  cases d : decodeExternal (requestFor .swapCallback l.recipient
      (.callback fr.context.sender l.amount0Out l.amount1Out l.data)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    rw [decode_callback d] at d
    simp only [resumeSegment, d]
    exact ⟨⟨by rw [token0], token1⟩, fun _ _ => trivial⟩

theorem resume_swapBalance0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SwapLocals}
    (ghost : ContGhost side t0 t1 b fr request (.swapBalance0 l))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.swapBalance0 l) reply turns tail
      (resumeSegment prior request (.swapBalance0 l) reply) := by
  obtain ⟨rfl, token1⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .swapBalance0 t0 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded]
    refine ⟨⟨by rw [token1], ?_⟩, fun _ _ => trivial⟩
    cases side
    · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)
    · trivial

theorem resume_swapBalance1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SwapLocals} {balance0 : B256}
    (ghost : ContGhost side t0 t1 b fr request (.swapBalance1 l balance0))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.swapBalance1 l balance0) reply turns tail
      (resumeSegment prior request (.swapBalance1 l balance0) reply) := by
  obtain ⟨rfl, held⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .swapBalance1 t1 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded]
    split
    · exact ⟨trivial, fun notFailed => notFailed.elim⟩
    · refine ⟨finishUpdated_ghost ?_, fun _ _ => trivial⟩
      cases side
      · exact held
      · exact Nat.le_of_eq (bal.readAt hT.symm pairEq success)

theorem resume_skimBalance0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SkimLocals}
    (ghost : ContGhost side t0 t1 b fr request (.skimBalance0 l))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.skimBalance0 l) reply turns tail
      (resumeSegment prior request (.skimBalance0 l) reply) := by
  obtain ⟨rfl, token0, token1, held, locked⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .skimBalance0 t0 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded, Frame.beginResume, current]
    split_ifs with covered
    · refine ⟨⟨⟨_, by rw [token0], ?_⟩, token1, locked⟩, fun _ _ => trivial⟩
      cases side
      · have read := bal.readAt hT.symm pairEq success
        simp only [OnSide]
        rw [skim_value fr.current.state.reserve0.isLt covered]
        omega
      · exact held
    · exact ⟨trivial, fun notFailed => notFailed.elim⟩

theorem resume_skimTransfer0 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SkimLocals}
    (ghost : ContGhost side t0 t1 b fr request (.skimTransfer0 l))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.skimTransfer0 l) reply turns tail
      (resumeSegment prior request (.skimTransfer0 l) reply) := by
  obtain ⟨⟨v, rfl, held⟩, token1, locked⟩ := ghost
  have moved := bal.transferAt
  cases d : decodeExternal (requestFor .skimTransfer0 t0 (.transfer l.recipient v)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    rw [decode_transfer d] at d
    simp only [resumeSegment, d]
    obtain ⟨r0, r1, unlocked⟩ := economicCore_reserves (priorOk.core locked)
    simp only [Frame.suspend, Frame.beginResume]
    refine ⟨⟨by rw [token1], token1, ?_, unlocked.trans locked⟩, fun _ _ => trivial⟩
    cases side
    · have h := moved.1 (hT : T = t0).symm
      simp only [OnSide] at held
      change prior.current.state.reserve0.val ≤ b'
      rw [r0]
      omega
    · have h := moved.2 fun e => distinct (e.trans (hT : T = t1))
      simp only [OnSide] at held
      change prior.current.state.reserve1.val ≤ b'
      rw [r1]
      omega

theorem resume_skimBalance1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SkimLocals}
    (ghost : ContGhost side t0 t1 b fr request (.skimBalance1 l))
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.skimBalance1 l) reply turns tail
      (resumeSegment prior request (.skimBalance1 l) reply) := by
  obtain ⟨rfl, token1, held, locked⟩ := ghost
  have same := bal.static externalStatic_read
  have current := priorOk.static externalStatic_read
  cases decoded : decodeExternal (requestFor .skimBalance1 t1 (.balanceOf fr.context.pair)) reply
    with
  | error failure =>
    simp only [resumeSegment, decoded, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok d =>
    obtain ⟨success, rfl⟩ := decode_read decoded
    subst same
    simp only [resumeSegment, decoded, Frame.beginResume, current]
    split_ifs with covered
    · refine ⟨⟨⟨_, by rw [token1], ?_⟩, locked⟩, fun _ _ => trivial⟩
      cases side
      · exact held
      · have read := bal.readAt hT.symm pairEq success
        simp only [OnSide]
        rw [skim_value fr.current.state.reserve1.isLt covered]
        omega
    · exact ⟨trivial, fun notFailed => notFailed.elim⟩

theorem resume_skimTransfer1 {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {l : SkimLocals}
    (ghost : ContGhost side t0 t1 b fr request (.skimTransfer1 l))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.skimTransfer1 l) reply turns tail
      (resumeSegment prior request (.skimTransfer1 l) reply) := by
  obtain ⟨⟨v, rfl, held⟩, locked⟩ := ghost
  have moved := bal.transferAt
  cases d : decodeExternal (requestFor .skimTransfer1 t1 (.transfer l.recipient v)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    rw [decode_transfer d] at d
    simp only [resumeSegment, d]
    obtain ⟨r0, r1, -⟩ := economicCore_reserves (priorOk.core locked)
    simp only [Frame.finishLocked, Frame.withEvents, Frame.finish, Frame.beginResume]
    refine ⟨?_, fun _ _ => trivial⟩
    cases side
    · have h := moved.2 fun e => distinct (e.trans (hT : T = t0)).symm
      simp only [OnSide] at held
      change prior.current.state.reserve0.val ≤ b'
      rw [r0]
      omega
    · have h := moved.1 (hT : T = t1).symm
      simp only [OnSide] at held
      change prior.current.state.reserve1.val ≤ b'
      rw [r1]
      omega

theorem resume_permitRecovery {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (_distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {b b' : Nat} {turns tail : Transcript}
    {owner spender : Adr} {value : B256}
    (ghost : ContGhost side t0 t1 b fr request (.permitRecovery owner spender value))
    (_pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr (.permitRecovery owner spender value) reply turns tail
      (resumeSegment prior request (.permitRecovery owner spender value) reply) := by
  obtain ⟨⟨digest, v, r, s, rfl⟩, held⟩ := ghost
  have stat : externalStatic fr (requestFor .permitRecovery 1 (.recover digest v r s)) = true := by
    simp only [externalStatic, requestFor, beq_self_eq_true, Bool.or_true]
  have same := bal.static stat
  have current := priorOk.static stat
  subst same
  cases d : decodeExternal (requestFor .permitRecovery 1 (.recover digest v r s)) reply with
  | error failure =>
    simp only [resumeSegment, d, Frame.fail]
    exact ⟨trivial, fun notFailed => notFailed.elim⟩
  | ok decoded =>
    cases decoded with
    | word w =>
      simp only [resumeSegment, d, Frame.fail]
      exact ⟨trivial, fun notFailed => notFailed.elim⟩
    | unit =>
      simp only [resumeSegment, d, Frame.fail]
      exact ⟨trivial, fun notFailed => notFailed.elim⟩
    | address recovered =>
      simp only [resumeSegment, d, Frame.beginResume]
      rw [current]
      split_ifs
      · cases approved : fr.current.state.approveLP prior.context owner spender value with
        | error failure =>
          simp only [Frame.finishLP, Frame.fail]
          exact ⟨trivial, fun notFailed => notFailed.elim⟩
        | ok result =>
          obtain ⟨post, events⟩ := result
          obtain ⟨r0, r1, -⟩ := economicCore_reserves (State.approveLP_core approved)
          simp only [Frame.finishLP, Frame.withEvents, Frame.finish]
          refine ⟨?_, fun _ _ => trivial⟩
          cases side
          · change post.reserve0.val ≤ b'
            rw [r0]
            exact held
          · change post.reserve1.val ≤ b'
            rw [r1]
            exact held
      · exact ⟨trivial, fun notFailed => notFailed.elim⟩

end Blanc.Composition.PairTokenJoint
