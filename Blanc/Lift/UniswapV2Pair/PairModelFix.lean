import Blanc.Lift.UniswapV2Pair.Execution

/-!
# Pair model invariants: fixed tokens, the lock, and the shape of mutable requests

Pure facts about the typed Pair model (`startTyped`, `resumeSegment`), consumed by the joint
invariant (C3):

* every state operation but `initialize` keeps the token addresses, the factory and the lock word
  (`State.Same`);
* `SegInv`: a segment invariant in two modes.  In the *outer* mode (an entry at an unlocked state)
  every mutable request is a `transfer` to one of the two tokens or a callback to a non-token
  address, and the step ends unlocked.  In the *nested* mode (an entry at a locked state) every
  request is static and the lock stays closed;
* `startTyped_segInv_outer` / `startTyped_segInv_nested` establish it and `resumeSegment_segInv`
  preserves it.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Token addresses and factory of a model state. -/
def TokensFix (t0 t1 f : Adr) (st : State) : Prop :=
  st.token0 = t0 ∧ st.token1 = t1 ∧ st.factory = f

/-- Two states agree on the token addresses, the factory and the lock word. -/
def State.Same (st post : State) : Prop :=
  post.token0 = st.token0 ∧ post.token1 = st.token1 ∧ post.factory = st.factory ∧
    post.unlocked = st.unlocked

theorem State.Same.refl (st : State) : st.Same st := ⟨rfl, rfl, rfl, rfl⟩

theorem State.Same.trans {a b c : State} (ab : a.Same b) (bc : b.Same c) : a.Same c :=
  ⟨bc.1.trans ab.1, bc.2.1.trans ab.2.1, bc.2.2.1.trans ab.2.2.1, bc.2.2.2.trans ab.2.2.2⟩

theorem TokensFix.of_same {t0 t1 f : Adr} {st post : State} (fix : TokensFix t0 t1 f st)
    (same : st.Same post) : TokensFix t0 t1 f post :=
  ⟨same.1.trans fix.1, same.2.1.trans fix.2.1, same.2.2.1.trans fix.2.2⟩

theorem State.mintLP_same {st post : State} {recipient : Adr} {value : B256} {events : List Event}
    (h : st.mintLP recipient value = .ok (post, events)) : st.Same post := by
  unfold State.mintLP at h
  split_ifs at h
  all_goals obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨rfl, rfl, rfl, rfl⟩

theorem State.burnLP_same {st post : State} {source : Adr} {value : B256} {events : List Event}
    (h : st.burnLP source value = .ok (post, events)) : st.Same post := by
  unfold State.burnLP at h
  split_ifs at h
  all_goals obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨rfl, rfl, rfl, rfl⟩

theorem State.transferLP_same {st post : State} {ctx : Context} {source recipient : Adr}
    {value : B256} {events : List Event}
    (h : st.transferLP ctx source recipient value = .ok (post, events)) : st.Same post := by
  simp only [State.transferLP] at h
  split_ifs at h
  all_goals obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨rfl, rfl, rfl, rfl⟩

theorem State.approveLP_same {st post : State} {ctx : Context} {owner spender : Adr}
    {value : B256} {events : List Event}
    (h : st.approveLP ctx owner spender value = .ok (post, events)) : st.Same post := by
  unfold State.approveLP at h
  split_ifs at h
  all_goals obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨rfl, rfl, rfl, rfl⟩

theorem State.transferFromLP_same {st post : State} {ctx : Context} {source recipient : Adr}
    {value : B256} {events : List Event}
    (h : st.transferFromLP ctx source recipient value = .ok (post, events)) : st.Same post := by
  rw [State.transferFromLP] at h
  by_cases hmax : st.allowance source ctx.sender = B256.max
  · simp only [hmax, ↓reduceIte] at h
    exact State.transferLP_same h
  · simp only [hmax, ↓reduceIte] at h
    by_cases hle : value ≤ st.allowance source ctx.sender
    · simp only [hle, ↓reduceIte] at h
      by_cases hs : ctx.isStatic = true
      · simp only [hs, ↓reduceIte] at h
        cases h
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
        have same := State.transferLP_same h
        exact State.Same.trans ⟨rfl, rfl, rfl, rfl⟩ same
    · simp only [hle, ↓reduceIte] at h
      cases h

theorem State.update_same {st post : State} {ctx : Context} {balance0 balance1 : B256}
    {r0 r1 : Nat} {event : Event} {update : OracleUpdate}
    (h : st.update ctx balance0 balance1 r0 r1 = .ok (post, event, update)) : st.Same post := by
  unfold State.update at h
  split_ifs at h
  all_goals obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h); exact ⟨rfl, rfl, rfl, rfl⟩

theorem mintFee_same {st : State} {feeTo : Adr} {r0 r1 : Nat} {fee : FeeResult}
    (h : mintFee st feeTo r0 r1 = .ok fee) : st.Same fee.state := by
  simp only [mintFee] at h
  split_ifs at h
  all_goals try (cases Except.ok.inj h; exact ⟨rfl, rfl, rfl, rfl⟩)
  cases hm : st.mintLP feeTo (Nat.toB256 ((st.totalSupply.toNat * ((r0 * r1).sqrt -
      st.kLast.toNat.sqrt)) / ((r0 * r1).sqrt * 5 + st.kLast.toNat.sqrt))) with
  | error e =>
    rw [hm] at h
    cases h
  | ok r =>
    obtain ⟨post, events⟩ := r
    rw [hm] at h
    cases Except.ok.inj h
    exact State.mintLP_same hm

/-! ## The segment invariant -/

/-- What a continuation carries about the tokens and the swap recipient. -/
def ContFix (t0 t1 : Adr) : Continuation → Prop
  | .burnInitialBalance0 l => l.token0 = t0 ∧ l.token1 = t1
  | .burnInitialBalance1 l _ => l.token0 = t0 ∧ l.token1 = t1
  | .burnFee o => o.locals.token0 = t0 ∧ o.locals.token1 = t1
  | .burnTransfer0 p => p.observed.locals.token0 = t0 ∧ p.observed.locals.token1 = t1
  | .burnTransfer1 p => p.observed.locals.token0 = t0 ∧ p.observed.locals.token1 = t1
  | .burnFinalBalance0 p => p.observed.locals.token0 = t0 ∧ p.observed.locals.token1 = t1
  | .burnFinalBalance1 p _ => p.observed.locals.token0 = t0 ∧ p.observed.locals.token1 = t1
  | .swapTransfer0 l => l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .swapTransfer1 l => l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .swapCallback l => l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .swapBalance0 l => l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .swapBalance1 l _ => l.token0 = t0 ∧ l.token1 = t1 ∧ l.recipient ≠ t0 ∧ l.recipient ≠ t1
  | .skimBalance0 l => l.token0 = t0 ∧ l.token1 = t1
  | .skimTransfer0 l => l.token0 = t0 ∧ l.token1 = t1
  | .skimBalance1 l => l.token0 = t0 ∧ l.token1 = t1
  | .skimTransfer1 l => l.token0 = t0 ∧ l.token1 = t1
  | _ => True

/-- The `permit` continuation: the only suspension before (or without) the lock. -/
def Continuation.IsPermit : Continuation → Prop
  | .permitRecovery _ _ _ => True
  | _ => False

/-- A mutable request: a `transfer` to one of the two tokens, or a callback to a non-token. -/
def ReqShape (t0 t1 : Adr) (request : Request) : Prop :=
  (∃ site recipient value, request = requestFor site t0 (.transfer recipient value) ∨
      request = requestFor site t1 (.transfer recipient value)) ∨
    ∃ site target sender amount0 amount1 data,
      request = requestFor site target (.callback sender amount0 amount1 data) ∧
        target ≠ t0 ∧ target ≠ t1

theorem b256_zero_ne_one : (0 : B256) ≠ 1 := by decide

/-- Fixed tokens and factory on both checkpoints; the lock word by mode (`nested`: closed
throughout; outer: open at the entry checkpoint). -/
def FrameFix (nested : Bool) (t0 t1 f : Adr) (fr : Frame) : Prop :=
  TokensFix t0 t1 f fr.current.state ∧ TokensFix t0 t1 f fr.checkpoint.state ∧
    (nested = true → fr.current.state.unlocked ≠ 1 ∧ fr.checkpoint.state.unlocked ≠ 1) ∧
    (nested = false → fr.checkpoint.state.unlocked = 1)

/-- **The segment invariant.**  Outer mode (`nested = false`): a finished segment is unlocked, and a
suspension is either `permit`'s static recovery at the open lock or a request after the lock whose
mutable form has the shape `ReqShape`.  Nested mode: only `permit`'s static recovery suspends. -/
def SegInv (nested : Bool) (t0 t1 f : Adr) : SegmentResult → Prop
  | .finished fr _ => FrameFix nested t0 t1 f fr ∧ (nested = false → fr.current.state.unlocked = 1)
  | .failed fr _ => FrameFix nested t0 t1 f fr
  | .suspended fr request cont => FrameFix nested t0 t1 f fr ∧ ContFix t0 t1 cont ∧
      (externalStatic fr request = false → nested = false ∧ ReqShape t0 t1 request) ∧
      (cont.IsPermit → externalStatic fr request = true ∧
        (nested = false → fr.current.state.unlocked = 1)) ∧
      (¬ cont.IsPermit → nested = false ∧ fr.current.state.unlocked ≠ 1)

theorem Frame.lock_ok {fr locked : Frame} (h : fr.lock = .ok locked) :
    fr.current.state.unlocked = 1 ∧ fr.context.isStatic = false ∧
      locked = { fr with current :=
        { fr.current with state := { fr.current.state with unlocked := 0 } } } := by
  unfold Frame.lock at h
  split_ifs at h with hu hs
  cases Except.ok.inj h
  exact ⟨hu, by simpa only [Bool.not_eq_true] using hs, rfl⟩

theorem Frame.finishLP_same {fr : Frame} {result : Except Failure (State × List Event)}
    {bytes : Bytes} (same : ∀ post events, result = .ok (post, events) → fr.current.state.Same post) :
    (∃ e, fr.finishLP result bytes = .failed { fr with current := fr.checkpoint } e) ∨
      ∃ post events, fr.current.state.Same post ∧
        fr.finishLP result bytes = .finished (fr.withEvents post events) bytes := by
  cases result with
  | error e => exact Or.inl ⟨e, rfl⟩
  | ok r =>
    obtain ⟨post, events⟩ := r
    exact Or.inr ⟨post, events, same post events rfl, rfl⟩

/-- An immediate entry is terminal; its frame keeps the entry checkpoint and, unless it is a
non-static `initialize` from the factory, the tokens, factory and lock word. -/
theorem startImmediate_same {current : Checkpoint} {ctx : Context} {entry : Entry}
    {result : SegmentResult} (h : startImmediate current ctx entry = some result)
    (quiet : ctx.isStatic = false → ctx.sender ≠ current.state.factory) :
    ∃ fr : Frame, fr.checkpoint = current ∧ current.state.Same fr.current.state ∧
      ((∃ bytes, result = .finished fr bytes) ∨ ∃ failure, result = .failed fr failure) := by
  unfold startImmediate at h
  by_cases hv : ctx.value ≠ 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv)] at h
    cases Option.some.inj h
    exact ⟨_, rfl, State.Same.refl _, Or.inr ⟨_, rfl⟩⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false hv)] at h
  split at h
  · cases Option.some.inj h
    exact ⟨_, rfl, State.Same.refl _, Or.inl ⟨_, rfl⟩⟩
  split at h
  · cases Option.some.inj h
    rcases Frame.finishLP_same (fr := Frame.enter current ctx _) (bytes := encodeWords [1])
        (result := current.state.approveLP ctx ctx.sender _ _)
        (fun _ _ hr => State.approveLP_same hr) with ⟨e, he⟩ | ⟨post, events, same, he⟩
    · exact ⟨_, rfl, State.Same.refl _, Or.inr ⟨e, he⟩⟩
    · exact ⟨Frame.withEvents (Frame.enter current ctx _) post events, rfl, same, Or.inl ⟨_, he⟩⟩
  · cases Option.some.inj h
    rcases Frame.finishLP_same (fr := Frame.enter current ctx _) (bytes := encodeWords [1])
        (result := current.state.transferLP ctx ctx.sender _ _)
        (fun _ _ hr => State.transferLP_same hr) with ⟨e, he⟩ | ⟨post, events, same, he⟩
    · exact ⟨_, rfl, State.Same.refl _, Or.inr ⟨e, he⟩⟩
    · exact ⟨Frame.withEvents (Frame.enter current ctx _) post events, rfl, same, Or.inl ⟨_, he⟩⟩
  · cases Option.some.inj h
    rcases Frame.finishLP_same (fr := Frame.enter current ctx _) (bytes := encodeWords [1])
        (result := current.state.transferFromLP ctx _ _ _)
        (fun _ _ hr => State.transferFromLP_same hr) with ⟨e, he⟩ | ⟨post, events, same, he⟩
    · exact ⟨_, rfl, State.Same.refl _, Or.inr ⟨e, he⟩⟩
    · exact ⟨Frame.withEvents (Frame.enter current ctx _) post events, rfl, same, Or.inl ⟨_, he⟩⟩
  · dsimp only at h
    by_cases hsender : ctx.sender = current.state.factory
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hsender)] at h
      by_cases hstatic : ctx.isStatic = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hstatic)] at h
        cases Option.some.inj h
        exact ⟨_, rfl, State.Same.refl _, Or.inr ⟨_, rfl⟩⟩
      · exact absurd hsender (quiet (by simpa only [Bool.not_eq_true] using hstatic))
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hsender)] at h
      cases Option.some.inj h
      exact ⟨_, rfl, State.Same.refl _, Or.inr ⟨_, rfl⟩⟩
  · cases h

theorem segInv_terminal {nested : Bool} {t0 t1 f : Adr} {current : Checkpoint} {fr : Frame}
    {result : SegmentResult} (fix : TokensFix t0 t1 f current.state)
    (lockWord : (nested = true → current.state.unlocked ≠ 1) ∧
      (nested = false → current.state.unlocked = 1))
    (checkpoint : fr.checkpoint = current) (same : current.state.Same fr.current.state)
    (terminal : (∃ bytes, result = .finished fr bytes) ∨ ∃ failure, result = .failed fr failure) :
    SegInv nested t0 t1 f result := by
  have frameFix : FrameFix nested t0 t1 f fr := by
    rw [FrameFix, checkpoint, same.2.2.2]
    exact ⟨fix.of_same same, fix, fun h => ⟨lockWord.1 h, lockWord.1 h⟩, lockWord.2⟩
  rcases terminal with ⟨bytes, rfl⟩ | ⟨failure, rfl⟩
  · exact ⟨frameFix, fun h => same.2.2.2.trans (lockWord.2 h)⟩
  · exact frameFix

theorem startTyped_segInv_outer {current : Checkpoint} {ctx : Context} {entry : Entry}
    {t0 t1 f : Adr} (fix : TokensFix t0 t1 f current.state) (opened : current.state.unlocked = 1)
    (quiet : ctx.isStatic = false → ctx.sender ≠ f) :
    SegInv false t0 t1 f (startTyped current ctx entry) := by
  have lockWord : (false = true → current.state.unlocked ≠ 1) ∧
      (false = false → current.state.unlocked = 1) :=
    ⟨fun h => absurd h Bool.false_ne_true, fun _ => opened⟩
  unfold startTyped
  cases himm : startImmediate current ctx entry with
  | some r =>
    obtain ⟨fr, chk, same, terminal⟩ := startImmediate_same himm (fix.2.2 ▸ quiet)
    exact segInv_terminal fix lockWord chk same terminal
  | none =>
    obtain ⟨h0, h1, hf⟩ := fix
    dsimp only
    split
    · split_ifs
      all_goals simp only [SegInv, FrameFix, TokensFix, Frame.suspend, Frame.withEvents, Frame.enter,
        Frame.fail, requestFor, externalStatic, ContFix, Continuation.IsPermit, h0, h1, hf, opened,
        Bool.or_true, Bool.true_eq_false, false_implies, true_and, and_self, implies_true,
        not_true_eq_false, beq_self_eq_true, Bool.false_eq_true]
    · rename_i notPermit
      cases hl : (Frame.enter current ctx entry).lock with
      | error e =>
        simp only [SegInv, FrameFix, TokensFix, Frame.fail, Frame.enter, h0, h1, hf, opened,
          Bool.false_eq_true, false_implies, and_self, implies_true]
      | ok locked =>
        obtain ⟨-, -, rfl⟩ := Frame.lock_ok hl
        dsimp only [Frame.enter]
        simp only [h0, h1]
        split
        all_goals try split_ifs
        all_goals simp only [SegInv, FrameFix, TokensFix, Frame.suspend, Frame.fail, requestFor,
          externalStatic, ContFix, Continuation.IsPermit, ReqShape, h0, h1, hf, opened, Bool.or_true,
          false_implies, true_and, and_self, implies_true, beq_self_eq_true, Bool.false_eq_true,
          not_false_eq_true, Bool.true_eq_false, true_implies]
        all_goals first
          | exact b256_zero_ne_one
          | exact ⟨by assumption, b256_zero_ne_one⟩
          | exact ⟨by assumption, fun _ => Or.inl ⟨_, _, _, Or.inl rfl⟩, b256_zero_ne_one⟩
          | exact ⟨by assumption, fun _ => Or.inl ⟨_, _, _, Or.inr rfl⟩, b256_zero_ne_one⟩
          | (rename_i hrec _ _ _
             exact ⟨hrec, fun _ => Or.inr ⟨_, _, _, _, _, _, rfl, hrec.1, hrec.2⟩, b256_zero_ne_one⟩)

theorem Frame.lock_locked {fr : Frame} (locked : fr.current.state.unlocked ≠ 1) :
    ∃ e, fr.lock = .error e := by
  unfold Frame.lock
  rw [ite_eq_right_of_eq_false _ _ (eq_false locked)]
  exact ⟨_, rfl⟩

/-- **A re-entered entry at a closed lock** keeps the segment invariant in nested mode: it is
immediate, fails at the lock, or is `permit`'s static recovery. -/
theorem startTyped_segInv_nested {current : Checkpoint} {ctx : Context} {entry : Entry}
    {t0 t1 f : Adr} (fix : TokensFix t0 t1 f current.state) (locked : current.state.unlocked ≠ 1)
    (quiet : ctx.isStatic = false → ctx.sender ≠ f) :
    SegInv true t0 t1 f (startTyped current ctx entry) := by
  have lockWord : (true = true → current.state.unlocked ≠ 1) ∧
      (true = false → current.state.unlocked = 1) :=
    ⟨fun _ => locked, fun h => Bool.noConfusion h⟩
  unfold startTyped
  cases himm : startImmediate current ctx entry with
  | some r =>
    obtain ⟨fr, chk, same, terminal⟩ := startImmediate_same himm (fix.2.2 ▸ quiet)
    exact segInv_terminal fix lockWord chk same terminal
  | none =>
    obtain ⟨h0, h1, hf⟩ := fix
    dsimp only
    split
    · split_ifs
      all_goals simp only [SegInv, FrameFix, TokensFix, Frame.suspend, Frame.withEvents, Frame.enter,
        Frame.fail, requestFor, externalStatic, ContFix, Continuation.IsPermit, h0, h1, hf, ne_eq,
        locked, Bool.or_true, Bool.true_eq_false, false_implies, and_self,
        not_true_eq_false, beq_self_eq_true, not_false_eq_true, true_implies]
    · obtain ⟨e, he⟩ := Frame.lock_locked (fr := Frame.enter current ctx entry) locked
      rw [he]
      simp only [SegInv, FrameFix, TokensFix, Frame.fail, Frame.enter, h0, h1, hf, ne_eq, locked,
        Bool.true_eq_false, false_implies, and_self, not_false_eq_true, true_implies]

/-! ## Resumption -/

section Resume

variable {nested : Bool} {t0 t1 f : Adr}

theorem FrameFix.step {fr fr' : Frame} (fix : FrameFix nested t0 t1 f fr)
    (checkpoint : fr'.checkpoint = fr.checkpoint) (same : fr.current.state.Same fr'.current.state) :
    FrameFix nested t0 t1 f fr' := by
  obtain ⟨cur, chk, lockedFix, openFix⟩ := fix
  refine ⟨cur.of_same same, checkpoint ▸ chk, fun h => ?_, fun h => checkpoint ▸ openFix h⟩
  rw [same.2.2.2, checkpoint]
  exact lockedFix h

theorem segInv_fail {fr : Frame} {failure : Failure} (fix : FrameFix nested t0 t1 f fr) :
    SegInv nested t0 t1 f (fr.fail failure) := by
  obtain ⟨cur, chk, lockedFix, openFix⟩ := fix
  exact ⟨chk, chk, fun h => ⟨(lockedFix h).2, (lockedFix h).2⟩, openFix⟩

/-- A request after the lock: a static read, or a mutable request of the shape. -/
theorem segInv_suspend {fr : Frame} {site : CallSite} {target : Adr}
    {operation : ExternalOperation} {cont : Continuation} (fix : FrameFix false t0 t1 f fr)
    (contFix : ContFix t0 t1 cont) (notPermit : ¬ cont.IsPermit)
    (locked : fr.current.state.unlocked ≠ 1)
    (shape : externalStatic fr (requestFor site target operation) = false →
      ReqShape t0 t1 (requestFor site target operation)) :
    SegInv false t0 t1 f (fr.suspend site target operation cont) :=
  ⟨fix, contFix, fun h => ⟨rfl, shape h⟩, fun h => absurd h notPermit, fun _ => ⟨rfl, locked⟩⟩

theorem segInv_suspend_read {fr : Frame} {site : CallSite} {target owner : Adr}
    {cont : Continuation} (fix : FrameFix false t0 t1 f fr) (contFix : ContFix t0 t1 cont)
    (notPermit : ¬ cont.IsPermit) (locked : fr.current.state.unlocked ≠ 1) :
    SegInv false t0 t1 f (fr.suspend site target (.balanceOf owner) cont) :=
  segInv_suspend fix contFix notPermit locked fun h => by
    simp only [externalStatic, requestFor, Bool.or_eq_false_iff, beq_self_eq_true,
      Bool.true_eq_false, and_false] at h

theorem segInv_suspend_feeTo {fr : Frame} {site : CallSite} {target : Adr}
    {cont : Continuation} (fix : FrameFix false t0 t1 f fr) (contFix : ContFix t0 t1 cont)
    (notPermit : ¬ cont.IsPermit) (locked : fr.current.state.unlocked ≠ 1) :
    SegInv false t0 t1 f (fr.suspend site target .feeTo cont) :=
  segInv_suspend fix contFix notPermit locked fun h => by
    simp only [externalStatic, requestFor, Bool.or_eq_false_iff, beq_self_eq_true,
      Bool.true_eq_false, and_false] at h

theorem segInv_suspend_transfer {fr : Frame} {site : CallSite} {target recipient : Adr}
    {value : B256} {cont : Continuation} (fix : FrameFix false t0 t1 f fr)
    (contFix : ContFix t0 t1 cont) (notPermit : ¬ cont.IsPermit)
    (locked : fr.current.state.unlocked ≠ 1) (token : target = t0 ∨ target = t1) :
    SegInv false t0 t1 f (fr.suspend site target (.transfer recipient value) cont) :=
  segInv_suspend fix contFix notPermit locked fun _ => by
    rcases token with rfl | rfl
    · exact Or.inl ⟨_, _, _, Or.inl rfl⟩
    · exact Or.inl ⟨_, _, _, Or.inr rfl⟩

theorem segInv_suspend_callback {fr : Frame} {site : CallSite} {target sender : Adr}
    {amount0 amount1 : B256} {data : Bytes} {cont : Continuation} (fix : FrameFix false t0 t1 f fr)
    (contFix : ContFix t0 t1 cont) (notPermit : ¬ cont.IsPermit)
    (locked : fr.current.state.unlocked ≠ 1) (apart0 : target ≠ t0) (apart1 : target ≠ t1) :
    SegInv false t0 t1 f (fr.suspend site target (.callback sender amount0 amount1 data) cont) :=
  segInv_suspend fix contFix notPermit locked fun _ =>
    Or.inr ⟨_, _, _, _, _, _, rfl, apart0, apart1⟩

theorem segInv_finishLocked {fr : Frame} {bytes : Bytes} (fix : FrameFix false t0 t1 f fr) :
    SegInv false t0 t1 f (fr.finishLocked bytes) := by
  obtain ⟨cur, chk, -, openFix⟩ := fix
  exact ⟨⟨cur, chk, fun h => Bool.noConfusion h, openFix⟩, fun _ => rfl⟩

theorem segInv_finishUpdated {fr : Frame} {balance0 balance1 : B256} {reserves : CachedReserves}
    {feeOn : Bool} {lastEvent : Option Event} {bytes : Bytes} (fix : FrameFix false t0 t1 f fr) :
    SegInv false t0 t1 f (fr.finishUpdated balance0 balance1 reserves feeOn lastEvent bytes) := by
  unfold Frame.finishUpdated
  split
  · exact segInv_fail fix
  · rename_i post event update hupdate
    have same := State.update_same hupdate
    dsimp only
    split <;> split <;>
      exact segInv_finishLocked (fix.step rfl (same.trans ⟨rfl, rfl, rfl, rfl⟩))

theorem segInv_mintAfterFee {fr : Frame} {observed : MintObserved} {fee : FeeResult}
    (fix : FrameFix false t0 t1 f fr) (same : fr.current.state.Same fee.state) :
    SegInv false t0 t1 f (fr.mintAfterFee observed fee) := by
  have charged : FrameFix false t0 t1 f (fr.withEvents fee.state fee.events) := fix.step rfl same
  unfold Frame.mintAfterFee
  dsimp only
  split
  · exact segInv_fail charged
  · rename_i liquidity _
    split
    · exact segInv_fail charged
    · rename_i postMinimum minimumEvents hinitial
      have minimumSame : fee.state.Same postMinimum := by
        split_ifs at hinitial
        · exact State.mintLP_same hinitial
        · obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj hinitial)
          exact State.Same.refl _
      have minimum : FrameFix false t0 t1 f (fr.withEvents fee.state fee.events |>.withEvents
          postMinimum minimumEvents) := charged.step rfl minimumSame
      split_ifs
      · split
        · exact segInv_fail minimum
        · rename_i post events hmint
          exact segInv_finishUpdated (minimum.step rfl (State.mintLP_same hmint))
      · exact segInv_fail minimum

theorem segInv_burnAfterFee {fr : Frame} {observed : BurnObserved} {fee : FeeResult}
    (fix : FrameFix false t0 t1 f fr) (same : fr.current.state.Same fee.state)
    (locked : fr.current.state.unlocked ≠ 1)
    (tokens : observed.locals.token0 = t0 ∧ observed.locals.token1 = t1) :
    SegInv false t0 t1 f (fr.burnAfterFee observed fee) := by
  have charged : FrameFix false t0 t1 f (fr.withEvents fee.state fee.events) := fix.step rfl same
  unfold Frame.burnAfterFee
  dsimp only
  split
  · exact segInv_fail charged
  · split_ifs
    · split
      · exact segInv_fail charged
      · rename_i post events hburn
        have burnSame := same.trans (State.burnLP_same hburn)
        refine segInv_suspend_transfer (charged.step rfl (State.burnLP_same hburn)) tokens
          (fun h => h) ?_ (Or.inl tokens.1)
        change post.unlocked ≠ 1
        rw [burnSame.2.2.2]
        exact locked
    · exact segInv_fail charged

/-- **Resumption keeps the segment invariant.** -/
theorem resumeSegment_segInv {prior : Frame} {request : Request} {cont : Continuation}
    {reply : ExternalResult} (fix : FrameFix nested t0 t1 f prior) (contFix : ContFix t0 t1 cont)
    (permitOpen : cont.IsPermit → nested = false → prior.current.state.unlocked = 1)
    (postLock : ¬ cont.IsPermit → nested = false ∧ prior.current.state.unlocked ≠ 1) :
    SegInv nested t0 t1 f (resumeSegment prior request cont reply) := by
  have begun : FrameFix nested t0 t1 f (prior.beginResume request) := fix
  unfold resumeSegment
  dsimp only
  split
  · exact segInv_fail begun
  split
  -- mintBalance0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun trivial (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- mintBalance1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    split_ifs
    · exact segInv_suspend_feeTo begun trivial (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
    · exact segInv_fail begun
  -- mintFee
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    split
    · exact segInv_fail begun
    · rename_i fee hfee
      exact segInv_mintAfterFee begun (mintFee_same hfee)
  -- burnInitialBalance0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- burnInitialBalance1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_feeTo begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- burnFee
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    split
    · exact segInv_fail begun
    · rename_i fee hfee
      exact segInv_burnAfterFee begun (mintFee_same hfee) locked contFix
  -- burnTransfer0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_transfer begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked (Or.inr contFix.2)
  -- burnTransfer1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- burnFinalBalance0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- burnFinalBalance1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_finishUpdated begun
  -- swapTransfer0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    unfold Frame.afterSwapTransfer0 Frame.afterSwapTransfer1
    split_ifs
    · exact segInv_suspend_transfer begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked (Or.inr contFix.2.1)
    · exact segInv_suspend_callback begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked contFix.2.2.1 contFix.2.2.2
    · exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- swapTransfer1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    unfold Frame.afterSwapTransfer1
    split_ifs
    · exact segInv_suspend_callback begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked contFix.2.2.1 contFix.2.2.2
    · exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- swapCallback
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- swapBalance0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- swapBalance1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    split
    · exact segInv_fail begun
    · exact segInv_finishUpdated begun
  -- skimBalance0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    split_ifs
    · exact segInv_suspend_transfer begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked (Or.inl contFix.1)
    · exact segInv_fail begun
  -- skimTransfer0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- skimBalance1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    split_ifs
    · exact segInv_suspend_transfer begun contFix (by simp only [Continuation.IsPermit, not_false_eq_true]) locked (Or.inr contFix.2)
    · exact segInv_fail begun
  -- skimTransfer1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_finishLocked begun
  -- syncBalance0
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_suspend_read begun trivial (by simp only [Continuation.IsPermit, not_false_eq_true]) locked
  -- syncBalance1
  · obtain ⟨rfl, locked⟩ := postLock (by simp only [Continuation.IsPermit, not_false_eq_true])
    exact segInv_finishUpdated begun
  -- permitRecovery
  · have opened := permitOpen trivial
    split_ifs
    · rcases Frame.finishLP_same (fr := prior.beginResume request) (bytes := [])
          (result := (prior.beginResume request).current.state.approveLP
            (prior.beginResume request).context _ _ _)
          (fun _ _ hr => State.approveLP_same hr) with ⟨e, he⟩ | ⟨post, events, same, he⟩
      · rw [he]
        exact segInv_fail begun
      · rw [he]
        exact ⟨begun.step rfl same, fun h => same.2.2.2.trans (opened h)⟩
    · exact segInv_fail begun
  -- incomplete
  · exact segInv_fail begun

end Resume

end Blanc.Lift.UniswapV2Pair
