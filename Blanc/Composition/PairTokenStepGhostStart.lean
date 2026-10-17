import Blanc.Composition.PairTokenStepGhost
import Blanc.Lift.UniswapV2Pair.PairModelFix

/-!
# The model ghost of an outer Pair step: entry, resumption, request shape

* `resumeSegment_ghost`: every resumption keeps the ghost (dispatch over the continuations);
* `ContGhost.toT`: a mutable request to a token is a `transfer`;
* `startTyped_ghost`: an outer entry at an unlocked state whose side reserve is at most `b` starts
  with the ghost;
* `entryNoShrinkSide_of_obl`: the obligation of the entry segment is `EntryNoShrinkSide`.
-/

namespace Blanc.Composition.PairTokenJoint

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

/-- **A resumption keeps the ghost**, and discharges the obligation of the call it resumes from. -/
theorem resumeSegment_ghost {side : TokenSide} {t0 t1 T pair : Adr}
    (hT : OnSide side (T = t0) (T = t1)) (distinct : t0 ≠ t1) {fr prior : UniswapV2Pair.Frame}
    {request : Request} {cont : Continuation} {reply : ExternalResult} {b b' : Nat}
    {turns tail : Transcript}
    (ghost : ContGhost side t0 t1 b fr request cont)
    (pairEq : fr.context.pair = pair) (bal : CallBal T pair fr request reply b b')
    (priorOk : PriorOk fr prior request) :
    Resumed side t0 t1 b' fr cont reply turns tail (resumeSegment prior request cont reply) := by
  cases cont with
  | mintBalance0 => exact resume_mintBalance0 hT distinct ghost pairEq bal priorOk
  | mintBalance1 => exact resume_mintBalance1 hT distinct ghost pairEq bal priorOk
  | mintFee => exact resume_mintFee hT distinct ghost pairEq bal priorOk
  | burnInitialBalance0 => exact resume_burnInitialBalance0 hT distinct ghost pairEq bal priorOk
  | burnInitialBalance1 => exact resume_burnInitialBalance1 hT distinct ghost pairEq bal priorOk
  | burnFee => exact resume_burnFee hT distinct ghost pairEq bal priorOk
  | burnTransfer0 => exact resume_burnTransfer0 hT distinct ghost pairEq bal priorOk
  | burnTransfer1 => exact resume_burnTransfer1 hT distinct ghost pairEq bal priorOk
  | burnFinalBalance0 => exact resume_burnFinalBalance0 hT distinct ghost pairEq bal priorOk
  | burnFinalBalance1 => exact resume_burnFinalBalance1 hT distinct ghost pairEq bal priorOk
  | swapTransfer0 => exact resume_swapTransfer0 hT distinct ghost pairEq bal priorOk
  | swapTransfer1 => exact resume_swapTransfer1 hT distinct ghost pairEq bal priorOk
  | swapCallback => exact resume_swapCallback hT distinct ghost pairEq bal priorOk
  | swapBalance0 => exact resume_swapBalance0 hT distinct ghost pairEq bal priorOk
  | swapBalance1 => exact resume_swapBalance1 hT distinct ghost pairEq bal priorOk
  | skimBalance0 => exact resume_skimBalance0 hT distinct ghost pairEq bal priorOk
  | skimTransfer0 => exact resume_skimTransfer0 hT distinct ghost pairEq bal priorOk
  | skimBalance1 => exact resume_skimBalance1 hT distinct ghost pairEq bal priorOk
  | skimTransfer1 => exact resume_skimTransfer1 hT distinct ghost pairEq bal priorOk
  | syncBalance0 => exact resume_syncBalance0 hT distinct ghost pairEq bal priorOk
  | syncBalance1 => exact resume_syncBalance1 hT distinct ghost pairEq bal priorOk
  | permitRecovery => exact resume_permitRecovery hT distinct ghost pairEq bal priorOk

theorem externalStatic_feeTo {fr : UniswapV2Pair.Frame} {site : CallSite} {t : Adr} :
    externalStatic fr (requestFor site t .feeTo) = true := by
  simp only [externalStatic, requestFor, beq_self_eq_true, Bool.or_true]

theorem externalStatic_recover {fr : UniswapV2Pair.Frame} {site : CallSite} {t : Adr}
    {digest : B256} {v : UInt8} {r s : B256} :
    externalStatic fr (requestFor site t (.recover digest v r s)) = true := by
  simp only [externalStatic, requestFor, beq_self_eq_true, Bool.or_true]

/-- **A mutable request of a ghosted suspension to the side's token is a `transfer`.** -/
theorem ContGhost.toT {side : TokenSide} {t0 t1 T : Adr} {b : Nat} {fr : UniswapV2Pair.Frame}
    {request : Request} {cont : Continuation} (hT : OnSide side (T = t0) (T = t1))
    (ghost : ContGhost side t0 t1 b fr request cont) :
    request.target = T → externalStatic fr request = false →
      ∃ recipient value, request.calldata = (ExternalOperation.transfer recipient value).encode := by
  have read : ∀ {site t owner}, request = requestFor site t (.balanceOf owner) →
      externalStatic fr request = false → False := by
    intro site t owner eq mutable
    rw [eq, externalStatic_read] at mutable
    cases mutable
  have transfer : ∀ {site t recipient value},
      request = requestFor site t (.transfer recipient value) →
      ∃ recipient value, request.calldata = (ExternalOperation.transfer recipient value).encode :=
    fun {_ _ recipient value} eq => ⟨recipient, value, by rw [eq]; rfl⟩
  intro target mutable
  cases cont with
  | mintBalance0 => exact (read ghost.1 mutable).elim
  | mintBalance1 => exact (read ghost.1 mutable).elim
  | mintFee =>
    obtain ⟨⟨t, eq⟩, -⟩ := ghost
    rw [eq, externalStatic_feeTo] at mutable
    cases mutable
  | burnInitialBalance0 => exact (read ghost.1 mutable).elim
  | burnInitialBalance1 => exact (read ghost.1 mutable).elim
  | burnFee =>
    obtain ⟨⟨t, eq⟩, -⟩ := ghost
    rw [eq, externalStatic_feeTo] at mutable
    cases mutable
  | burnTransfer0 => exact transfer ghost.1
  | burnTransfer1 => exact transfer ghost.1
  | burnFinalBalance0 => exact (read ghost.1 mutable).elim
  | burnFinalBalance1 => exact (read ghost.1 mutable).elim
  | swapTransfer0 => exact transfer ghost.1
  | swapTransfer1 => exact transfer ghost.1
  | swapCallback l =>
    obtain ⟨eq, -, -, apart0, apart1⟩ := ghost
    rw [eq] at target
    cases side
    · exact (apart0 (target.trans hT)).elim
    · exact (apart1 (target.trans hT)).elim
  | swapBalance0 => exact (read ghost.1 mutable).elim
  | swapBalance1 => exact (read ghost.1 mutable).elim
  | skimBalance0 => exact (read ghost.1 mutable).elim
  | skimTransfer0 =>
    obtain ⟨⟨v, eq, -⟩, -⟩ := ghost
    exact transfer eq
  | skimBalance1 => exact (read ghost.1 mutable).elim
  | skimTransfer1 =>
    obtain ⟨⟨v, eq, -⟩, -⟩ := ghost
    exact transfer eq
  | syncBalance0 => exact (read ghost.1 mutable).elim
  | syncBalance1 => exact (read ghost.1 mutable).elim
  | permitRecovery =>
    obtain ⟨⟨digest, v, r, s, eq⟩, -⟩ := ghost
    rw [eq, externalStatic_recover] at mutable
    cases mutable

/-- An immediate entry keeps the reserves. -/
theorem startImmediate_ghost {side : TokenSide} {t0 t1 : Adr} {b : Nat} {current : Checkpoint}
    {ctx : Context} {entry : Entry} {result : SegmentResult}
    (immediate : startImmediate current ctx entry = some result)
    (held : current.state.reserveOn side ≤ b) : SegGhost side t0 t1 b result := by
  obtain ⟨terminal, core⟩ := startImmediate_core entry immediate
  cases result with
  | finished fr output =>
    obtain ⟨r0, r1, -⟩ := economicCore_reserves (st' := fr.current.state) core
    cases side
    · change fr.current.state.reserve0.val ≤ b
      rw [r0]
      exact held
    · change fr.current.state.reserve1.val ≤ b
      rw [r1]
      exact held
  | failed fr failure => exact trivial
  | suspended fr request cont => exact terminal.elim

/-- **An outer entry starts with the ghost.** -/
theorem startTyped_ghost {side : TokenSide} {t0 t1 : Adr} {b : Nat} {current : Checkpoint}
    {ctx : Context} {entry : Entry} (token0 : current.state.token0 = t0)
    (token1 : current.state.token1 = t1) (held : current.state.reserveOn side ≤ b) :
    SegGhost side t0 t1 b (startTyped current ctx entry) := by
  subst token0 token1
  unfold startTyped
  cases immediate : startImmediate current ctx entry with
  | some result => exact startImmediate_ghost immediate held
  | none =>
    dsimp only
    split
    · split_ifs
      · exact trivial
      · exact ⟨⟨_, _, _, _, rfl⟩, held⟩
      · exact trivial
    · cases locking : (Frame.enter current ctx entry).lock with
      | error failure => exact trivial
      | ok locked =>
        obtain ⟨-, -, rfl⟩ := Frame.lock_ok locking
        dsimp only
        split
        · exact ⟨rfl, rfl⟩
        · refine ⟨rfl, rfl, rfl, ?_⟩
          cases side
          · exact held
          · exact held
        · split_ifs with positive bounded apart
          · exact ⟨rfl, rfl, rfl, apart.1, apart.2⟩
          · exact ⟨rfl, rfl, rfl, apart.1, apart.2⟩
          · exact ⟨rfl, rfl, rfl, apart.1, apart.2⟩
          · exact ⟨rfl, rfl⟩
          all_goals exact trivial
        · exact ⟨rfl, rfl, rfl, held, rfl⟩
        · refine ⟨rfl, rfl, ?_⟩
          cases side
          · exact held
          · exact held
        · exact trivial

/-- **The entry segment's obligation is the side's token premise** (`EntryNoShrinkSide`). -/
theorem entryNoShrinkSide_of_obl {side : TokenSide} {current : Checkpoint} {ctx : Context}
    {entry : Entry} {transcript : Transcript}
    (notFailed : NotFailed (startTyped current ctx entry))
    (obligation : SegObl side transcript (startTyped current ctx entry)) :
    EntryNoShrinkSide side current.state ctx entry transcript := by
  cases entry
  case burn recipient =>
    simp only [startTyped, startImmediate, getterResult] at notFailed obligation
    split_ifs at notFailed obligation
    · exact notFailed.elim
    · cases locking : (Frame.enter current ctx (.burn recipient)).lock with
      | error failure =>
        simp only [locking, Frame.fail] at notFailed
        exact notFailed.elim
      | ok locked =>
        obtain ⟨-, -, rfl⟩ := Frame.lock_ok locking
        simp only [locking, Frame.suspend] at obligation
        exact obligation
  case sync =>
    simp only [startTyped, startImmediate, getterResult] at notFailed obligation
    split_ifs at notFailed obligation
    · exact notFailed.elim
    · cases locking : (Frame.enter current ctx .sync).lock with
      | error failure =>
        simp only [locking, Frame.fail] at notFailed
        exact notFailed.elim
      | ok locked =>
        obtain ⟨-, -, rfl⟩ := Frame.lock_ok locking
        simp only [locking, Frame.suspend] at obligation
        cases side
        · exact obligation
        · exact obligation
  all_goals exact trivial

end Blanc.Composition.PairTokenJoint
