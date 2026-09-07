import Blanc.LidoCircuitBreakerObservation
import Blanc.TransientInvariance

/-!
# What a successful pause commits

The observation cut ends its accepting arm at an arbitrary `pauseSuccess`
entry.  This module classifies the walk from that boundary through its two
events, expiry write, transient lock clear, and terminal `STOP`.

The boundary is deliberately post-callback.  `pauseSuccess` reads the caller's
assignment count and heartbeat interval only after arbitrary target code has
run.  The core result therefore names both words at that state and concludes
in their terms.  `PauseSuccessNoninterference` is the separate, explicit
assumption needed only when a consumer wants to replace those words by their
values at `pauseAfterSet` entry.

Two facts need no such assumption.  The target and duration are frame-local
words staged at offsets 512 and 736, beyond the observation's return window;
they are transported into this boundary.  Conversely memory word zero is not
preserved: `pauseSuccess` re-stages both event data words there before logging
them.

Nothing here claims the accepted answer is true, that any outcome is live, or
that a callee cannot interfere.  The differential rows
`overflow-pause-post-callback-count-positive` and
`overflow-pause-post-callback-interval-change` are measured witnesses that the
two noninterference equalities below can fail.  The assumptions are not
derived here; discharging them would require a no-write result over arbitrary
callee code, which Blanc and Jaune do not currently have.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune
open scoped LogOutputHinv

/-! ## Public result vocabulary -/

/-- The exact first record emitted by `pauseSuccess`.  Its three topics are the
event signature, staged target, and caller; its data is the staged duration
word. -/
def pauseTriggeredLog (sevm : Sevm) (target duration : B256) : Log :=
  ⟨sevm.currentTarget,
    [pauseTriggeredEvent, target, sevm.caller.toB256], duration.toBytes⟩

/-- The exact second record emitted by a committing `pauseSuccess`.  The data
word is parameterized once so the result can bind it to the same word as the
expiry `SSTORE`. -/
def heartbeatUpdatedLog (sevm : Sevm) (value : B256) : Log :=
  ⟨sevm.currentTarget, [heartbeatUpdatedEvent, sevm.caller.toB256],
    value.toBytes⟩

/-- Facts read at the actual post-callback `pauseSuccess` entry.

The two memory words are transported facts, not noninterference assumptions.
The count and interval are deliberately bound to `pre`, not to an earlier
pause state.  No output fact belongs here: the event prefix is universal over
the incoming output, and terminal `STOP` preserves it. -/
def PauseSuccessInputs (sevm : Sevm) (pre : Devm)
    (target duration count interval : B256) : Prop :=
  MemWordAt pre (targetWord * 32).toNat target ∧
  MemWordAt pre (durationWord * 32).toNat duration ∧
  pre.getStorVal sevm.currentTarget (countSlot sevm.caller.toB256) = count ∧
  pre.getStorVal sevm.currentTarget heartbeatIntervalSlot = interval

/-- **Assumed, not derived:** the only two post-callback storage reads used by
the success classification agree with their values at `pauseAfterSet` entry.

Arbitrary target code can re-enter the CircuitBreaker and make either equality
false; the two `overflow-pause-post-callback-*` differential rows cited in the
module header exercise exactly those failures.  A no-write theorem for the
relevant calls, or a stronger authorization invariant excluding the writes,
would derive these equalities.  Neither exists here. -/
def PauseSuccessNoninterference (sevm : Sevm)
    (entry postCallback : Devm) : Prop :=
  postCallback.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) =
    entry.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) ∧
  postCallback.getStorVal sevm.currentTarget heartbeatIntervalSlot =
    entry.getStorVal sevm.currentTarget heartbeatIntervalSlot

/-! ## Trace-linked success and panic routes -/

/-- The literal expiry-write, heartbeat-log, lock-clear, and `STOP` suffix.

Every named state is joined to the next by the instruction that actually
executes.  In particular the `TSTORE` operand equation is not a detached
witness: `lockPre` is reached by the two source pushes and is the state on
which that very `TSTORE` runs. -/
def PauseSuccessFinishTrace (fs : List Func) (sevm : Sevm)
    (pre post : Devm) (value : B256) : Prop :=
  ∃ storePost zeroPost lockPre lockPost : Devm, ∃ tail : List B256,
    value :: tail <<+ pre.stack ∧
    Line.Run sevm pre storeHeartbeatExpiryFromStack storePost ∧
    Ninst.RunCompiled sevm storePost (Ninst.pushB256 0) zeroPost ∧
    Ninst.RunCompiled sevm zeroPost (Ninst.pushB256 lockKey) lockPre ∧
    Ninst.RunCompiled sevm lockPre Ninst.tstore lockPost ∧
    Func.RunCompiledTo fs sevm lockPost Func.stop (.ok post)

/-- A committing route through `pauseSuccess`, with both count arms retained.

The first disjunct is the nonzero-count checked-addition arm; its zero branch
word is the proof that the sum did not wrap.  The second is the zero-count arm;
the branch word is the canonical `1` produced by `ISZERO`.  Both feed the same
trace-linked finishing suffix. -/
def PauseSuccessCommitTrace (fs : List Func) (sevm : Sevm)
    (pre post : Devm) (target duration value : B256) : Prop :=
  ∃ eventPost countPost finishPre : Devm,
    Line.Run sevm pre pauseSuccessEventLine eventPost ∧
    eventPost.logs = pre.logs ++ [pauseTriggeredLog sevm target duration] ∧
    Line.Run sevm eventPost heartbeatCountTest countPost ∧
    ((∃ checkedPre checkedPost : Devm,
        countPost.stack = 0 :: checkedPre.stack ∧
        Devm.PopBurnBy [0] (gVerylow + gHigh) countPost checkedPre ∧
        Line.Run sevm checkedPre checkedHeartbeatExpiryTest checkedPost ∧
        checkedPost.stack = 0 :: finishPre.stack ∧
        Devm.PopBurnBy [0] (gVerylow + gHigh) checkedPost finishPre) ∨
      (∃ zeroPre : Devm,
        countPost.stack = 1 :: zeroPre.stack ∧
        Devm.PopBurnBy [1] (gVerylow + gHigh + gJumpdest) countPost zeroPre ∧
        Ninst.RunCompiled sevm zeroPre (Ninst.pushB256 0) finishPre)) ∧
    PauseSuccessFinishTrace fs sevm finishPre post value

/-- The trace-linked checked-addition overflow route.  The function-table
lookup is intentionally not part of this structural relation: it is an
explicit premise of the exact panic result, where it prevents a generic table
from being mistaken for the production `Panic(0x11)` body. -/
def PauseSuccessPanicTrace (fs : List Func) (sevm : Sevm)
    (pre : Devm) (target duration : B256) (ex : Execution) : Prop :=
  ∃ eventPost countPost checkedPre checkedPost panicPre : Devm,
    Line.Run sevm pre pauseSuccessEventLine eventPost ∧
    eventPost.logs = pre.logs ++ [pauseTriggeredLog sevm target duration] ∧
    Line.Run sevm eventPost heartbeatCountTest countPost ∧
    countPost.stack = 0 :: checkedPre.stack ∧
    Devm.PopBurnBy [0] (gVerylow + gHigh) countPost checkedPre ∧
    Line.Run sevm checkedPre checkedHeartbeatExpiryTest checkedPost ∧
    checkedPost.stack = 1 :: panicPre.stack ∧
    Devm.PopBurnBy [1] (gVerylow + gHigh + gJumpdest) checkedPost panicPre ∧
    Func.RunCompiledTo fs sevm panicPre (Func.call arithmeticPanicSlot) ex

/-- The complete committing result of the post-callback `pauseSuccess` walk.

The log equation is a whole-walk exact delta: precisely `PauseTriggered` and
then `HeartbeatUpdated`, with no intervening or trailing record.  `value` is
also the binder used by `PauseExpiryWrite`, so the heartbeat log cannot drift
from the word stored.  Persistent storage changes at exactly the caller's
expiry cell and at no cell of any other account.  Transient storage changes at
exactly the lock cell.  The final existential exposes the literal
`TSTORE lockKey 0; STOP` suffix and its operands. -/
def PauseSuccessCommit (fs : List Func) (sevm : Sevm) (pre post : Devm)
    (target duration count interval value : B256) : Prop :=
  PauseSuccessInputs sevm pre target duration count interval ∧
  Func.RunCompiledTo fs sevm pre pauseSuccess (.ok post) ∧
  PauseSuccessCommitTrace fs sevm pre post target duration value ∧
  PauseExpiryWrite sevm pre sevm.currentTarget value ∧
  PauseExpiryValue sevm.benvStat.time interval count value ∧
  post.logs =
    pre.logs ++
      [pauseTriggeredLog sevm target duration,
        heartbeatUpdatedLog sevm value] ∧
  (∀ owner,
    Devm.getStor post owner =
      if owner = sevm.currentTarget then
        (Devm.getStor pre owner).set
          (expirySlot sevm.caller.toB256) value
      else Devm.getStor pre owner) ∧
  post.getTransVal sevm.currentTarget lockKey = 0 ∧
  (∀ owner key,
    (owner, key) ≠ (sevm.currentTarget, lockKey) →
      post.getTransVal owner key = pre.getTransVal owner key) ∧
  post.output = pre.output

/-- The checked-addition overflow arm.

The first record has already been emitted, but no persistent or transient
write has occurred when control reaches the production `Panic(0x11)` body.
The final disjunction keeps the body's own terminal out-of-gas leg explicit;
on either terminal result the same storage, transient storage, and sole log
remain. -/
def PauseSuccessPanic (fs : List Func) (sevm : Sevm) (pre : Devm)
    (target duration count interval : B256) (ex : Execution) : Prop :=
  PauseSuccessInputs sevm pre target duration count interval ∧
  Func.RunCompiledTo fs sevm pre pauseSuccess ex ∧
  fs[arithmeticPanicSlot]? =
    some (Func.revertData heartbeatArithmeticPanicData) ∧
  PauseSuccessPanicTrace fs sevm pre target duration ex ∧
  count ≠ 0 ∧
  ¬ B256.Nof sevm.benvStat.time interval ∧
  ((∃ d,
      ex = .error (.halt (.outOfGas .none), d) ∧
      Devm.getStor d = Devm.getStor pre ∧
      d.transientStorage = pre.transientStorage ∧
      d.logs = pre.logs ++ [pauseTriggeredLog sevm target duration]) ∨
    (∃ post,
      ex = .error (.revert, post) ∧
      post.output = heartbeatArithmeticPanicData ∧
      Devm.getStor post = Devm.getStor pre ∧
      post.transientStorage = pre.transientStorage ∧
      post.logs = pre.logs ++ [pauseTriggeredLog sevm target duration]))

/-- Every reached `pauseSuccess` walk either commits its exact result or takes
the storage-silent arithmetic-panic arm. -/
def PauseSuccessOutcome (fs : List Func) (sevm : Sevm) (pre : Devm)
    (target duration count interval : B256) (ex : Execution) : Prop :=
  (∃ post value,
    ex = .ok post ∧
    PauseSuccessCommit fs sevm pre post
      target duration count interval value) ∨
  PauseSuccessPanic fs sevm pre target duration count interval ex

/-- `STOP` preserves `Devm.output` in Jaune's active-frame semantics.  Thus
the source-level empty-return claim needs, and consumes, the honest enclosing
frame fact that the incoming output is empty; it is not a fact about callee
behaviour and is not part of storage noninterference. -/
theorem PauseSuccessCommit.output_empty
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {target duration count interval value : B256}
    (commit : PauseSuccessCommit fs sevm pre post
      target duration count interval value)
    (hpre : pre.output = []) :
    post.output = [] := by
  rcases commit with ⟨-, -, -, -, -, -, -, -, -, houtput⟩
  rw [houtput, hpre]

/-! ## Exact one-instruction effects used by the walk -/

/-- `loadWord` is log-silent.  `MLOAD` deliberately has no global log
invariance instance; exposing the two-instruction fact privately keeps the
universal event proof local to this contract owner. -/
private theorem loadWord_logs_eq {e : Sevm} {s s' : Devm} {k : B256}
    (h : Line.Run e s (loadWord k) s') : s.logs = s'.logs := by
  unfold loadWord at h
  rcases Line.of_run_cons h with ⟨s1, qpush, hrest⟩
  rcases Line.of_run_cons hrest with ⟨s2, qmload, hnil⟩
  cases hnil
  rcases of_run_reg qmload with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, u1⟩, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨u2, h2, run2⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have hb := Devm.burn_of_chargeGas h2
  have hp := Devm.push_of_push run2
  exact (of_run_pushB256 qpush).logs.trans
    (((p1.logs.trans hb.logs).trans rfl).trans hp.logs)

/-- **D1: the exact `PauseTriggered` prefix, for an arbitrary entry.**

The only value premises are the two frame-local memory windows.  The theorem
splits the actual `pauseSuccess` derivation, emits the exact `LOG3`, and returns
the actual remaining walk; it assumes nothing about target code, returndata,
storage, transient storage, or the incoming output. -/
theorem pauseSuccess_pauseTriggered_prefix
    {fs : List Func} {sevm : Sevm} {pre : Devm} {ex : Execution}
    {target duration : B256}
    (htarget : MemWordAt pre (targetWord * 32).toNat target)
    (hduration : MemWordAt pre (durationWord * 32).toNat duration)
    (run : Func.RunCompiledTo fs sevm pre pauseSuccess ex) :
    ∃ eventPost : Devm,
      Line.Run sevm pre pauseSuccessEventLine eventPost ∧
      eventPost.logs = pre.logs ++ [pauseTriggeredLog sevm target duration] ∧
      Func.RunCompiledTo fs sevm eventPost
        (Ninst.caller ::: tagTop countRegion +++ Ninst.sload ::: Ninst.iszero :::
          ((Ninst.pushB256 0 ::: pauseExpiryFinish) <?>
            (checkedHeartbeatExpiry <| pauseExpiryFinish))) ex := by
  have hshape : pauseSuccess =
      pauseSuccessEventLine +++
        (Ninst.caller ::: tagTop countRegion +++ Ninst.sload ::: Ninst.iszero :::
          ((Ninst.pushB256 0 ::: pauseExpiryFinish) <?>
            (checkedHeartbeatExpiry <| pauseExpiryFinish))) := rfl
  rw [hshape] at run
  obtain ⟨eventPost, hevent, htail⟩ := runCompiledTo_prepend_inv run
  unfold pauseSuccessEventLine at hevent
  simp only [List.append_assoc] at hevent
  obtain ⟨s1, hdurationRun, hrest⟩ :=
    of_run_append (loadWord durationWord) hevent
  obtain ⟨s2, hmstore, hrest⟩ := of_run_append (mstoreAt 0) hrest
  obtain ⟨s3, hcallerLine, hrest⟩ := of_run_append [Ninst.caller] hrest
  obtain ⟨s4, htargetRun, hrest⟩ :=
    of_run_append (loadWord targetWord) hrest
  obtain ⟨s5, heventPushLine, hlog⟩ :=
    of_run_append [Ninst.pushB256 pauseTriggeredEvent] hrest
  have pd : duration :: ([] : Stack) <<+ s1.stack :=
    prefix_of_loadWord_window hduration nil_pref hdurationRun
  obtain ⟨_, hmemDuration⟩ := of_run_mstoreAt_val hmstore pd
  have target1 := htarget.acrossLoadWord hdurationRun
  have target2 := target1.acrossMstoreAt (by decide) hmstore
  have target3 := target2.acrossLine (by line_inv) hcallerLine
  have pc : sevm.caller.toB256 :: ([] : Stack) <<+ s3.stack := by
    rcases Line.of_run_cons hcallerLine with ⟨_, qcaller, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_caller qcaller) nil_pref
  have pt : target :: sevm.caller.toB256 :: ([] : Stack) <<+ s4.stack :=
    prefix_of_loadWord_window target3 pc htargetRun
  have pe : pauseTriggeredEvent :: target :: sevm.caller.toB256 ::
      ([] : Stack) <<+ s5.stack := by
    rcases Line.of_run_cons heventPushLine with ⟨_, qpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 qpush) pt
  obtain ⟨img1, image1⟩ :=
    (hduration.acrossLoadWord hdurationRun).memImage
  have duration2 : MemWordAt s2 0 duration :=
    MemWordAt.of_write image1 hmemDuration
  have duration3 := duration2.acrossLine (by line_inv) hcallerLine
  have duration4 := duration3.acrossLoadWord htargetRun
  have duration5 := duration4.acrossLine (by line_inv) heventPushLine
  obtain ⟨_, img5, hreads5, hslice5⟩ := duration5
  have hdata : (s5.memory.read 0 32).1 = duration.toBytes := by
    rw [Mem.Reads.read hreads5 0 32, hslice5]
  obtain ⟨_, hlogs⟩ := of_logWith201_val pe hlog
  have hlogsPrefix : pre.logs = s5.logs :=
    (loadWord_logs_eq hdurationRun).trans
      ((Line.of_inv Devm.logs (by unfold mstoreAt; line_inv) hmstore).trans
        ((Line.of_inv Devm.logs (by line_inv) hcallerLine).trans
          ((loadWord_logs_eq htargetRun).trans
            (Line.of_inv Devm.logs (by line_inv) heventPushLine))))
  refine ⟨eventPost, ?_, ?_, htail⟩
  · exact hevent
  · rw [hlogs, ← hlogsPrefix, hdata]
    rfl

/-- Value-carrying `LOG2` companion for `logWith 1 0 1`. -/
private theorem of_logWith101_val {e : Sevm} {s s' : Devm}
    {ev a : B256} {xs : Stack}
    (hp : ev :: a :: xs <<+ s.stack)
    (h : Line.Run e s (logWith 1 0 1) s') :
    xs <<+ s'.stack ∧
      s'.logs =
        s.logs ++ [⟨e.currentTarget, [ev, a], (s.memory.read 0 32).1⟩] := by
  rcases Line.of_run_cons h with ⟨s1, h32, hrest1⟩
  rcases Line.of_run_cons hrest1 with ⟨s2, h0, hrest2⟩
  rcases Line.of_run_cons hrest2 with ⟨s3, hlog, hnil⟩
  cases hnil
  have hb32 := of_run_pushB256 h32
  have hb0 := of_run_pushB256 h0
  have h32word : (1 * 32 : B256) = 32 := by decide +kernel
  have h0word : (0 * 32 : B256) = 0 := by decide +kernel
  rw [h32word] at hb32
  rw [h0word] at hb0
  have hp1 : (32 : B256) :: ev :: a :: xs <<+ s1.stack := by
    simpa using prefix_of_push hb32 hp
  have hp2 : (0 : B256) :: 32 :: ev :: a :: xs <<+ s2.stack := by
    simpa using prefix_of_push hb0 hp1
  rcases of_run_log_val hlog with ⟨mi, sz, topics, hlen, hpop, hlogs⟩
  have hknown : ([0, 32, ev, a] : List B256) <<+ s2.stack := by
    exact @pref_trans _ [0, 32, ev, a]
      ([0, 32, ev, a] ++ xs) _ ⟨xs, rfl⟩ (by simpa using hp2)
  have heq : ([0, 32, ev, a] : List B256) = mi :: sz :: topics :=
    List.pref_unique (by simp [hlen]) hknown (pref_of_split hpop)
  simp only [List.cons.injEq] at heq
  rcases heq with ⟨rfl, rfl, rfl⟩
  constructor
  · exact of_append_pref hpop (by simpa using hp2)
  · rw [hlogs, ← hb0.logs, ← hb32.logs, ← hb0.memory, ← hb32.memory]
    rfl

/-- Read the successful `SSTORE` semantics at every account, not only at the
current account.  Kept private because the public claim is the contract's
whole `pauseSuccess` walk rather than a new shared opcode API. -/
private theorem sstore_getStor_all
    {sevm : Sevm} {pre post : Devm} {key value : B256}
    {tail : List B256}
    (run : Ninst.Run sevm pre Ninst.sstore post)
    (stack : key :: value :: tail <<+ pre.stack) :
    ∀ owner,
      Devm.getStor post owner =
        if owner = sevm.currentTarget then
          (Devm.getStor pre owner).set key value
        else Devm.getStor pre owner := by
  intro owner
  rcases of_run_reg run with ⟨pc, hr⟩
  simp only [Rinst.run, Rinst.runCore] at hr
  rcases Except.bind_eq_ok hr with ⟨⟨poppedKey, s1⟩, h1, hr1⟩
  rcases Except.bind_eq_ok hr1 with ⟨⟨poppedValue, s2⟩, h2, hr2⟩
  rcases Except.bind_eq_ok hr2 with ⟨_, h3, hr3⟩
  rcases Except.bind_eq_ok hr3 with ⟨⟨s3, gas2⟩, h4, hr4⟩
  rcases Except.bind_eq_ok hr4 with ⟨gas3, h5, hr5⟩
  rcases Except.bind_eq_ok hr5 with ⟨s4, h6, hr6⟩
  rcases Except.bind_eq_ok hr6 with ⟨s5, h7, hr7⟩
  rcases Except.bind_eq_ok hr7 with ⟨_, h8, h9⟩
  have hs1 : pre.stack = poppedKey :: s1.stack :=
    (Devm.pop_of_pop h1).stack
  have hs2 : s1.stack = poppedValue :: s2.stack :=
    (Devm.pop_of_pop h2).stack
  have hkeys : key = poppedKey ∧ value = poppedValue := by
    rw [hs1, hs2] at stack
    rcases stack with ⟨suffix, hstack⟩
    injection hstack with hk hrest
    injection hrest with hv _
    exact ⟨hk.symm, hv.symm⟩
  have e1 : Devm.getStor pre = Devm.getStor s1 := Devm.pop_getStor_eq h1
  have e2 : Devm.getStor s1 = Devm.getStor s2 := Devm.pop_getStor_eq h2
  have e4 : Devm.getStor s2 = Devm.getStor s3 := by
    split at h4 <;> (injection h4 with eq; injection eq with eq _; subst eq)
    · exact addAccessedStorageKey_getStor.symm
    · rfl
  have e6 : Devm.getStor s3 = Devm.getStor s4 := by
    injection h6 with eq
    rw [← eq]
    rfl
  have e7 : Devm.getStor s4 = Devm.getStor s5 :=
    chargeGas_getStor_eq h7
  have E : Devm.getStor pre = Devm.getStor s5 :=
    e1.trans (e2.trans (e4.trans (e6.trans e7)))
  injection h9 with eq
  rw [← eq]
  by_cases howner : owner = sevm.currentTarget
  · subst owner
    rw [if_pos rfl, setStorVal_getStor_self, hkeys.1, hkeys.2,
      ← congrFun E sevm.currentTarget]
  · rw [if_neg howner]
    exact (setStorVal_getStor_ne (fun h => howner h.symm)).trans
      (congrFun E owner).symm

/-- Exact effects of the expiry-write/heartbeat-log line, before the two lock
pushes.  The single `value` binder feeds both the `SSTORE` and the log data. -/
private theorem storeHeartbeatExpiryFromStack_result
    {sevm : Sevm} {pre post : Devm} {value : B256} {tail : List B256}
    (stack : value :: tail <<+ pre.stack)
    (run : Line.Run sevm pre storeHeartbeatExpiryFromStack post) :
    tail <<+ post.stack ∧
    post.logs = pre.logs ++ [heartbeatUpdatedLog sevm value] ∧
    (∀ owner,
      Devm.getStor post owner =
        if owner = sevm.currentTarget then
          (Devm.getStor pre owner).set
            (expirySlot sevm.caller.toB256) value
        else Devm.getStor pre owner) ∧
    post.transientStorage = pre.transientStorage ∧
    post.output = pre.output := by
  unfold storeHeartbeatExpiryFromStack at run
  simp only [List.append_assoc] at run
  obtain ⟨s1, rdup, rest⟩ := of_run_append [Ninst.dup 0] run
  obtain ⟨s2, rmstore, rest⟩ := of_run_append (mstoreAt 0) rest
  obtain ⟨s3, rcallerKey, rest⟩ := of_run_append [Ninst.caller] rest
  obtain ⟨s4, rtag, rest⟩ := of_run_append (tagTop expiryRegion) rest
  obtain ⟨s5, rsstoreLine, rest⟩ := of_run_append [Ninst.sstore] rest
  obtain ⟨s6, reventPrefix, rlog⟩ :=
    of_run_append [Ninst.caller, Ninst.pushB256 heartbeatUpdatedEvent] rest
  rcases Line.of_run_cons rdup with ⟨_, qdup, hnil⟩
  cases hnil
  have p1 : value :: value :: tail <<+ s1.stack := by
    exact prefix_of_dup_val qdup (by show_nth) stack
  obtain ⟨p2, hmemWrite⟩ := of_run_mstoreAt_val rmstore p1
  rcases Line.of_run_cons rcallerKey with ⟨_, qcallerKey, hnil⟩
  cases hnil
  have p3 : sevm.caller.toB256 :: value :: tail <<+ s3.stack :=
    prefix_of_push (of_run_caller qcallerKey) p2
  unfold tagTop at rtag
  rcases Line.of_run_cons rtag with ⟨u, qregion, rtag⟩
  rcases Line.of_run_cons rtag with ⟨_, qor, hnil⟩
  cases hnil
  have pregion : regionWord expiryRegion :: sevm.caller.toB256 ::
      value :: tail <<+ u.stack :=
    prefix_of_push (of_run_pushB256 qregion) p3
  have p4 : expirySlot sevm.caller.toB256 :: value :: tail <<+ s4.stack := by
    change (regionWord expiryRegion ||| sevm.caller.toB256) ::
      value :: tail <<+ s4.stack
    exact prefix_of_or qor pregion
  rcases Line.of_run_cons rsstoreLine with ⟨_, qsstore, hnil⟩
  cases hnil
  have p5 : tail <<+ s5.stack := prefix_of_sstore qsstore p4
  rcases Line.of_run_cons reventPrefix with ⟨u1, qcallerEvent, restEvent⟩
  rcases Line.of_run_cons restEvent with ⟨_, qevent, hnil⟩
  cases hnil
  have p6 : heartbeatUpdatedEvent :: sevm.caller.toB256 :: tail <<+
      s6.stack := prefix_of_push (of_run_pushB256 qevent)
        (prefix_of_push (of_run_caller qcallerEvent) p5)
  obtain ⟨p7, hlog⟩ := of_logWith101_val p6 rlog
  have hvalueBytes : value.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes value
    rw [h] at hlen
    simp at hlen
  have hmem2to6 : s2.memory = s6.memory :=
    (Line.of_inv Devm.memory (by line_inv) rcallerKey).trans
      (((of_run_pushB256 qregion).memory.trans
        (Ninst.Hinv.inv (f := Devm.memory) qor)).trans
        ((Ninst.Hinv.inv (f := Devm.memory) qsstore).trans
          (Line.of_inv Devm.memory (by line_inv) reventPrefix)))
  have hdata : (s6.memory.read 0 32).1 = value.toBytes := by
    rw [← hmem2to6, hmemWrite]
    change ((s1.memory.write 0 value.toBytes).read 0 32).1 = _
    simpa only [B256.length_toBytes] using
      (Mem.read_write_zero s1.memory hvalueBytes)
  have hlogsPrefix : pre.logs = s6.logs :=
    (Line.of_inv Devm.logs (by line_inv) rdup).trans
      ((Line.of_inv Devm.logs (by unfold mstoreAt; line_inv) rmstore).trans
        ((Line.of_inv Devm.logs (by line_inv) rcallerKey).trans
          (((of_run_pushB256 qregion).logs.trans
            (Ninst.Hinv.inv (f := Devm.logs) qor)).trans
            ((Ninst.Hinv.inv (f := Devm.logs) qsstore).trans
              (Line.of_inv Devm.logs (by line_inv) reventPrefix)))))
  have hstorPrefix : Devm.getStor pre = Devm.getStor s4 :=
    (Line.of_inv Devm.getStor (by line_inv) rdup).trans
      ((Line.of_inv Devm.getStor (by unfold mstoreAt; line_inv) rmstore).trans
        ((Line.of_inv Devm.getStor (by line_inv) rcallerKey).trans
          (Line.of_inv Devm.getStor (by line_inv)
            (Line.Run.cons qregion (Line.Run.cons qor Line.Run.nil)))))
  have hstorSuffix : Devm.getStor s5 = Devm.getStor post :=
    (Line.of_inv Devm.getStor (by line_inv) reventPrefix).trans
      (Line.of_inv Devm.getStor (by unfold logWith; line_inv) rlog)
  have htransient : pre.transientStorage = post.transientStorage := by
    calc
      pre.transientStorage = s1.transientStorage :=
        Line.of_inv Devm.transientStorage (by line_inv) rdup
      _ = s2.transientStorage :=
        Line.of_inv Devm.transientStorage
          (by unfold mstoreAt; line_inv) rmstore
      _ = s3.transientStorage :=
        Line.of_inv Devm.transientStorage (by line_inv) rcallerKey
      _ = u.transientStorage :=
        Ninst.Hinv.inv (f := Devm.transientStorage) qregion
      _ = s4.transientStorage :=
        Ninst.Hinv.inv (f := Devm.transientStorage) qor
      _ = s5.transientStorage :=
        Ninst.Hinv.inv (f := Devm.transientStorage) qsstore
      _ = s6.transientStorage :=
        Line.of_inv Devm.transientStorage (by line_inv) reventPrefix
      _ = post.transientStorage :=
        Line.of_inv Devm.transientStorage
          (by unfold logWith; line_inv) rlog
  have houtput : pre.output = post.output := by
    calc
      pre.output = s1.output := Line.of_inv Devm.output (by line_inv) rdup
      _ = s2.output := Line.of_inv Devm.output
        (by unfold mstoreAt; line_inv) rmstore
      _ = s3.output := Line.of_inv Devm.output (by line_inv) rcallerKey
      _ = u.output := Ninst.Hinv.inv (f := Devm.output) qregion
      _ = s4.output := Ninst.Hinv.inv (f := Devm.output) qor
      _ = s5.output := Ninst.Hinv.inv (f := Devm.output) qsstore
      _ = s6.output := Line.of_inv Devm.output (by line_inv) reventPrefix
      _ = post.output := Line.of_inv Devm.output
        (by unfold logWith; line_inv) rlog
  constructor
  · exact p7
  constructor
  · rw [hlog, ← hlogsPrefix, hdata]
    rfl
  constructor
  · intro owner
    rw [← congrFun hstorSuffix owner,
      sstore_getStor_all qsstore p4 owner,
      ← congrFun hstorPrefix owner]
  constructor
  · exact htransient.symm
  · exact houtput.symm

/-- `TSTORE` changes neither accumulated logs nor the active-frame output.
This contract-local projection accompanies `tstore_run_cell`, whose public
frame result intentionally abstracts those two fields. -/
private theorem tstore_logs_output
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre Ninst.tstore post) :
    post.logs = pre.logs ∧ post.output = pre.output := by
  rcases of_run_reg run with ⟨pc, hr⟩
  simp only [Rinst.run, Rinst.runCore] at hr
  rcases Except.bind_eq_ok hr with ⟨⟨key, s1⟩, h1, hr1⟩
  rcases Except.bind_eq_ok hr1 with ⟨⟨value, s2⟩, h2, hr2⟩
  rcases Except.bind_eq_ok hr2 with ⟨charged, h3, hr3⟩
  rcases Except.bind_eq_ok hr3 with ⟨_, h4, h5⟩
  have p1 := Devm.pop_of_pop h1
  have p2 := Devm.pop_of_pop h2
  have burn := Devm.burn_of_chargeGas h3
  injection h5 with eq
  rw [← eq]
  exact ⟨(p1.logs.trans (p2.logs.trans burn.logs)).symm,
    (p1.output.trans (p2.output.trans burn.output)).symm⟩

/-- **D2/D4/D5 at the common finish:** the heartbeat log uses the expiry
write's own binder, the literal lock operands clear exactly one transient
cell, `STOP` preserves the incoming output, and persistent storage changes at
exactly the caller's expiry cell across all accounts. -/
theorem PauseSuccessFinishTrace.result
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {value : B256}
    (trace : PauseSuccessFinishTrace fs sevm pre post value) :
    post.logs = pre.logs ++ [heartbeatUpdatedLog sevm value] ∧
    (∀ owner,
      Devm.getStor post owner =
        if owner = sevm.currentTarget then
          (Devm.getStor pre owner).set
            (expirySlot sevm.caller.toB256) value
        else Devm.getStor pre owner) ∧
    post.getTransVal sevm.currentTarget lockKey = 0 ∧
    (∀ owner key,
      (owner, key) ≠ (sevm.currentTarget, lockKey) →
        post.getTransVal owner key = pre.getTransVal owner key) ∧
    post.output = pre.output := by
  rcases trace with
    ⟨storePost, zeroPost, lockPre, lockPost, tail, hstack, hstore,
      hpushZero, hpushKey, htstore, hstop⟩
  rcases storeHeartbeatExpiryFromStack_result hstack hstore with
    ⟨pstorePost, hlogs, hstor, htransientStore, houtputStore⟩
  have rpushZero := Ninst.Run.of_runCompiled hpushZero
  have rpushKey := Ninst.Run.of_runCompiled hpushKey
  have bpushZero := of_run_pushB256 rpushZero
  have bpushKey := of_run_pushB256 rpushKey
  have pzeroPost : (0 : B256) :: tail <<+ zeroPost.stack :=
    prefix_of_push bpushZero pstorePost
  have plockPre : lockKey :: 0 :: tail <<+ lockPre.stack :=
    prefix_of_push bpushKey pzeroPost
  rcases plockPre with ⟨suffix, hlockStack'⟩
  have hlockStack : lockPre.stack = lockKey :: 0 :: (tail ++ suffix) := by
    unfold Split at hlockStack'
    simpa only [List.cons_append, List.append_assoc] using hlockStack'
  have rtstore := Ninst.Run.of_runCompiled htstore
  rcases tstore_logs_output rtstore with ⟨htstoreLogs, htstoreOutput⟩
  rcases tstore_run_cell rtstore hlockStack with
    ⟨_, hlock, hother, _, hframe, _⟩
  have hstopRun := runCompiledTo_last_inv hstop
  have hpost : post = lockPost := by
    simp [Linst.Run, Linst.run] at hstopRun
    exact hstopRun.symm
  subst post
  have hstorPushZero : Devm.getStor storePost = Devm.getStor zeroPost :=
    Ninst.Hinv.inv (f := Devm.getStor) rpushZero
  have hstorPushKey : Devm.getStor zeroPost = Devm.getStor lockPre :=
    Ninst.Hinv.inv (f := Devm.getStor) rpushKey
  have hstorTstore : Devm.getStor lockPre = Devm.getStor lockPost := by
    funext owner
    unfold Devm.getStor Devm.getAcct
    rw [hframe.state]
  have htransientPrefix : pre.transientStorage = lockPre.transientStorage :=
    htransientStore.symm.trans
      (bpushZero.transientStorage.trans bpushKey.transientStorage)
  constructor
  · rw [htstoreLogs, ← bpushKey.logs, ← bpushZero.logs, hlogs]
  constructor
  · intro owner
    rw [← congrFun hstorTstore owner,
      ← congrFun hstorPushKey owner,
      ← congrFun hstorPushZero owner, hstor owner]
  constructor
  · exact hlock
  constructor
  · intro owner key hne
    rw [hother owner key hne]
    unfold Devm.getTransVal
    rw [← htransientPrefix]
  · exact htstoreOutput.trans
      (bpushKey.output.symm.trans
        (bpushZero.output.symm.trans houtputStore))

/-- Invert the source's common finishing function into its trace-linked line,
two pushes, `TSTORE`, and terminal `STOP`. -/
private theorem pauseExpiryFinish_trace
    {fs : List Func} {sevm : Sevm} {pre : Devm} {ex : Execution}
    {value : B256} {tail : List B256}
    (hvalue : value :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre pauseExpiryFinish ex) :
    ∃ post,
      ex = .ok post ∧ PauseSuccessFinishTrace fs sevm pre post value := by
  have hshape : pauseExpiryFinish =
      storeHeartbeatExpiryFromStack +++
        (Ninst.pushB256 0 ::: Ninst.pushB256 lockKey :::
          Ninst.tstore ::: Func.stop) := rfl
  rw [hshape] at run
  obtain ⟨storePost, hstore, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨zeroPost, hpushZero, run⟩ := runCompiledTo_next_inv run
  obtain ⟨lockPre, hpushKey, run⟩ := runCompiledTo_next_inv run
  obtain ⟨lockPost, htstore, hstop⟩ := runCompiledTo_next_inv run
  have hstopRun := runCompiledTo_last_inv hstop
  have hex : ex = .ok lockPost := by
    simp [Linst.Run, Linst.run] at hstopRun
    exact hstopRun.symm
  have hstop' : Func.RunCompiledTo fs sevm lockPost Func.stop (.ok lockPost) := by
    rw [← hex]
    exact hstop
  exact ⟨lockPost, hex, storePost, zeroPost, lockPre, lockPost, tail,
    hvalue, hstore, hpushZero, hpushKey, htstore, hstop'⟩

/-- The checked-addition line leaves Solidity's overflow flag above the
computed expiry, for the interval read at the line's own entry state. -/
private theorem checkedHeartbeatExpiryTest_result
    {sevm : Sevm} {pre post : Devm} {interval : B256}
    (hinterval : pre.getStorVal sevm.currentTarget heartbeatIntervalSlot =
      interval)
    (run : Line.Run sevm pre checkedHeartbeatExpiryTest post) :
    ((interval + sevm.benvStat.time) <? sevm.benvStat.time) ::
      (interval + sevm.benvStat.time) :: ([] : Stack) <<+ post.stack := by
  unfold checkedHeartbeatExpiryTest at run
  rcases Line.of_run_cons run with ⟨s1, qtime1, run⟩
  rcases Line.of_run_cons run with ⟨s2, qslot, run⟩
  rcases Line.of_run_cons run with ⟨s3, qsload, run⟩
  rcases Line.of_run_cons run with ⟨s4, qadd, run⟩
  rcases Line.of_run_cons run with ⟨s5, qdup, run⟩
  rcases Line.of_run_cons run with ⟨s6, qtime2, run⟩
  rcases Line.of_run_cons run with ⟨s7, qswap, run⟩
  rcases Line.of_run_cons run with ⟨_, qlt, hnil⟩
  cases hnil
  have timestampPush : ∀ {a b : Devm},
      Ninst.Run sevm a Ninst.timestamp b →
        Devm.PushBurn [sevm.benvStat.time] a b := by
    intro a b q
    change Ninst.Run sevm a (.reg .timestamp) b at q
    rcases of_run_reg q with ⟨pc, instructionRun⟩
    simp only [Rinst.run, Rinst.runCore] at instructionRun
    exact Devm.pushBurn_of_pushItem instructionRun
  have p1 : [sevm.benvStat.time] <<+ s1.stack :=
    prefix_of_push (timestampPush qtime1) nil_pref
  have p2 : heartbeatIntervalSlot :: sevm.benvStat.time ::
      ([] : Stack) <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 qslot) p1
  rcases prefix_of_sload qsload p2 with ⟨read, p3, hread⟩
  have hstor2 : Devm.getStor pre = Devm.getStor s2 :=
    (Ninst.Hinv.inv (f := Devm.getStor) qtime1).trans
      (Ninst.Hinv.inv (f := Devm.getStor) qslot)
  have hreadInterval : read = interval := by
    rw [hread, ← hinterval]
    exact congrArg (fun stor => (stor sevm.currentTarget).get
      heartbeatIntervalSlot) hstor2.symm
  rw [hreadInterval] at p3
  have p4 : (interval + sevm.benvStat.time) :: ([] : Stack) <<+ s4.stack :=
    prefix_of_add qadd p3
  have p5 : (interval + sevm.benvStat.time) ::
      (interval + sevm.benvStat.time) :: ([] : Stack) <<+ s5.stack :=
    prefix_of_dup_val qdup (by show_nth) p4
  have p6 : sevm.benvStat.time :: (interval + sevm.benvStat.time) ::
      (interval + sevm.benvStat.time) :: ([] : Stack) <<+ s6.stack :=
    prefix_of_push (timestampPush qtime2) p5
  have hswap : Stack.Swap (0 : Fin 16).val
      [sevm.benvStat.time, interval + sevm.benvStat.time,
        interval + sevm.benvStat.time]
      [interval + sevm.benvStat.time, sevm.benvStat.time,
        interval + sevm.benvStat.time] := by
    apply Stack.swapCore_zero
  have p7 : (interval + sevm.benvStat.time) :: sevm.benvStat.time ::
      (interval + sevm.benvStat.time) :: ([] : Stack) <<+ s7.stack :=
    Stack.prefix_of_swap hswap (of_run_swap qswap) p6
  exact prefix_of_lt qlt p7

/-- Recover the checked-extension specification from the source's own zero
overflow flag. -/
private lemma success_checkedExtension_of_not_lt
    {timestamp interval : B256}
    (noWrap : ¬ (interval + timestamp < timestamp)) :
    CheckedHeartbeatExtension timestamp interval (interval + timestamp) := by
  have hbound : timestamp.toNat + interval.toNat < 2 ^ 256 := by
    by_contra hwrap
    refine noWrap ?_
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_add]
    have hi := B256.toNat_lt interval
    have ht := B256.toNat_lt timestamp
    have hmod : (interval.toNat + timestamp.toNat) ↾ 256 =
        interval.toNat + timestamp.toNat - 2 ^ 256 := by
      unfold Nat.lo
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    omega
  have hnof : B256.Nof interval timestamp := by
    unfold B256.Nof; omega
  refine ⟨hbound, B256.toNat_inj _ _ ?_⟩
  rw [B256.toNat_add_eq_of_nof _ _ hnof,
    B256.toNat_toB256_of_lt hbound]
  omega

/-- A positive source overflow flag contradicts mathematical no-overflow. -/
private lemma success_not_nof_of_lt {timestamp interval : B256}
    (wrap : interval + timestamp < timestamp) :
    ¬ B256.Nof timestamp interval := by
  intro hnof
  have hnof' : B256.Nof interval timestamp := by
    unfold B256.Nof at hnof ⊢; omega
  rw [B256.lt_iff_toNat_lt_toNat,
    B256.toNat_add_eq_of_nof _ _ hnof'] at wrap
  omega

/-- Read the complete source control flow backwards.  The successful side
retains the exact count arm, finishing trace, and value relation; the failure
side retains the actual call into the arithmetic-panic slot. -/
private theorem pauseSuccess_trace_dichotomy
    {fs : List Func} {sevm : Sevm} {pre : Devm} {ex : Execution}
    {target duration count interval : B256}
    (inputs : PauseSuccessInputs sevm pre target duration count interval)
    (run : Func.RunCompiledTo fs sevm pre pauseSuccess ex) :
    (exists post value,
      ex = .ok post ∧
      PauseSuccessCommitTrace fs sevm pre post target duration value ∧
      PauseExpiryValue sevm.benvStat.time interval count value) ∨
    (count ≠ 0 ∧ ¬ B256.Nof sevm.benvStat.time interval ∧
      PauseSuccessPanicTrace fs sevm pre target duration ex) := by
  rcases inputs with ⟨htarget, hduration, hcount, hinterval⟩
  obtain ⟨eventPost, hevent, htriggered, htail⟩ :=
    pauseSuccess_pauseTriggered_prefix htarget hduration run
  have htailShape :
      (Ninst.caller ::: tagTop countRegion +++ Ninst.sload ::: Ninst.iszero :::
        ((Ninst.pushB256 0 ::: pauseExpiryFinish) <?>
          (checkedHeartbeatExpiry <| pauseExpiryFinish))) =
      heartbeatCountTest +++
        ((Ninst.pushB256 0 ::: pauseExpiryFinish) <?>
          (checkedHeartbeatExpiry <| pauseExpiryFinish)) := rfl
  rw [htailShape] at htail
  obtain ⟨countPost, hcountRun, hbranch⟩ :=
    runCompiledTo_prepend_inv htail
  have hstorEvent : Devm.getStor pre = Devm.getStor eventPost :=
    Line.of_inv Devm.getStor pauseSuccessEvent_storInv hevent
  have hcountEvent : eventPost.getStorVal sevm.currentTarget
      (countSlot sevm.caller.toB256) = count := by
    rw [← hcount]
    exact congrArg (fun stor => (stor sevm.currentTarget).get
      (countSlot sevm.caller.toB256)) hstorEvent.symm
  have hstorCount : Devm.getStor pre = Devm.getStor countPost :=
    hstorEvent.trans
      (Line.of_inv Devm.getStor (by unfold heartbeatCountTest tagTop; line_inv)
        hcountRun)
  rcases runCompiledTo_branch_inv hbranch with
    ⟨checkedPre, hcountStack, hcountPop, hcheckedArm⟩ |
      ⟨countWord, zeroPre, hcountWordNonzero, hcountStack, hcountPop,
        hzeroArm⟩
  · have hcountFlag : (0 : B256) = (count =? 0) :=
      pauseCount_word hcountEvent hcountRun 0 checkedPre.stack hcountStack
    have hcountNonzero : count ≠ 0 := by
      intro hzero
      have hbad : (0 : B256) = 1 := by
        rw [hzero, B256.eqCheck, if_pos rfl] at hcountFlag
        exact hcountFlag
      exact absurd hbad (by decide)
    have hstorChecked : Devm.getStor pre = Devm.getStor checkedPre :=
      hstorCount.trans
        (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hcountPop))
    have hintervalChecked : checkedPre.getStorVal sevm.currentTarget
        heartbeatIntervalSlot = interval := by
      rw [← hinterval]
      exact congrArg (fun stor => (stor sevm.currentTarget).get
        heartbeatIntervalSlot) hstorChecked.symm
    have hcheckedShape : checkedHeartbeatExpiry pauseExpiryFinish =
        checkedHeartbeatExpiryTest +++
          Func.branch pauseExpiryFinish (Func.call arithmeticPanicSlot) := rfl
    rw [hcheckedShape] at hcheckedArm
    obtain ⟨checkedPost, hchecked, hcheckedBranch⟩ :=
      runCompiledTo_prepend_inv hcheckedArm
    have hcheckedPrefix :=
      checkedHeartbeatExpiryTest_result hintervalChecked hchecked
    rcases runCompiledTo_branch_inv hcheckedBranch with
      ⟨finishPre, hcheckedStack, hcheckedPop, hfinish⟩ |
        ⟨checkedWord, panicPre, hcheckedWordNonzero, hcheckedStack,
          hcheckedPop, hpanic⟩
    · have hflag :
          ((interval + sevm.benvStat.time) <? sevm.benvStat.time) = 0 :=
        (List.of_cons_pref_of_cons_pref hcheckedPrefix
          (pref_of_split (show [(0 : B256)] <++ checkedPost.stack ++>
            finishPre.stack by
              unfold Split
              simpa using hcheckedStack))).left
      have hnoWrap :
          ¬ (interval + sevm.benvStat.time < sevm.benvStat.time) := by
        intro hlt
        rw [B256.ltCheck, if_pos hlt] at hflag
        exact absurd hflag (by decide)
      have hvalue : [interval + sevm.benvStat.time] <<+ finishPre.stack :=
        prefix_of_pop ⟨_, Devm.PopBurn.of_popBurnBy hcheckedPop⟩
          hcheckedPrefix
      obtain ⟨post, hex, hfinishTrace⟩ :=
        pauseExpiryFinish_trace hvalue hfinish
      refine Or.inl ⟨post, interval + sevm.benvStat.time, hex, ?_, ?_⟩
      · refine ⟨eventPost, countPost, finishPre, hevent, htriggered, hcountRun,
          Or.inl ?_, hfinishTrace⟩
        exact ⟨checkedPre, checkedPost, hcountStack, hcountPop, hchecked,
          hcheckedStack, hcheckedPop⟩
      · exact ⟨fun hzero => absurd hzero hcountNonzero,
          fun _ => success_checkedExtension_of_not_lt hnoWrap⟩
    · have hflag :
          ((interval + sevm.benvStat.time) <? sevm.benvStat.time) =
            checkedWord :=
        (List.of_cons_pref_of_cons_pref hcheckedPrefix
          (pref_of_split (show [checkedWord] <++ checkedPost.stack ++>
            panicPre.stack by
              unfold Split
              simpa using hcheckedStack))).left
      have hwrap : interval + sevm.benvStat.time < sevm.benvStat.time := by
        by_contra hcontra
        rw [B256.ltCheck, if_neg hcontra] at hflag
        exact hcheckedWordNonzero hflag.symm
      have hcheckedWordOne : checkedWord = 1 := by
        rw [B256.ltCheck, if_pos hwrap] at hflag
        exact hflag.symm
      rw [hcheckedWordOne] at hcheckedStack hcheckedPop
      exact Or.inr ⟨hcountNonzero, success_not_nof_of_lt hwrap,
        eventPost, countPost, checkedPre, checkedPost, panicPre,
        hevent, htriggered, hcountRun, hcountStack, hcountPop, hchecked,
        hcheckedStack, hcheckedPop, hpanic⟩
  · have hcountFlag : countWord = (count =? 0) :=
      pauseCount_word hcountEvent hcountRun countWord zeroPre.stack hcountStack
    have hcountZero : count = 0 := by
      by_contra hcontra
      rw [B256.eqCheck, if_neg hcontra] at hcountFlag
      exact hcountWordNonzero hcountFlag
    have hcountWordOne : countWord = 1 := by
      rw [B256.eqCheck, if_pos hcountZero] at hcountFlag
      exact hcountFlag
    rw [hcountWordOne] at hcountStack hcountPop
    obtain ⟨finishPre, hpushZero, hfinish⟩ :=
      runCompiledTo_next_inv hzeroArm
    have hvalue : [(0 : B256)] <<+ finishPre.stack := by
      exact prefix_of_push
        (of_run_pushB256 (Ninst.Run.of_runCompiled hpushZero)) nil_pref
    obtain ⟨post, hex, hfinishTrace⟩ :=
      pauseExpiryFinish_trace hvalue hfinish
    refine Or.inl ⟨post, 0, hex, ?_, ?_⟩
    · refine ⟨eventPost, countPost, finishPre, hevent, htriggered, hcountRun,
        Or.inr ?_, hfinishTrace⟩
      exact ⟨zeroPre, hcountStack, hcountPop, hpushZero⟩
    · exact ⟨fun _ => rfl, fun hcontra => absurd hcountZero hcontra⟩

/-- A successful `pauseSuccess` changes no persistent-storage cell other than
the caller's expiry slot at the CircuitBreaker account.  The theorem is
pointwise over both the account and key so composition proofs can frame the
two protocol cells without reconstructing the success trace. -/
theorem pauseSuccess_ok_getStorVal_eq_of_ne
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {owner : Adr} {key : B256}
    (hpanic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (different : (owner, key) ≠
      (sevm.currentTarget, expirySlot sevm.caller.toB256))
    (run : Func.RunCompiledTo fs sevm pre pauseSuccess (.ok post)) :
    post.getStorVal owner key = pre.getStorVal owner key := by
  have hshape : pauseSuccess =
      pauseSuccessEventLine +++
        (heartbeatCountTest +++
          ((Ninst.pushB256 0 ::: pauseExpiryFinish) <?>
            (checkedHeartbeatExpiry <| pauseExpiryFinish))) := rfl
  rw [hshape] at run
  obtain ⟨eventPost, hevent, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨countPost, hcount, hbranch⟩ :=
    runCompiledTo_prepend_inv run
  have hstorEvent : Devm.getStor pre = Devm.getStor eventPost :=
    Line.of_inv Devm.getStor pauseSuccessEvent_storInv hevent
  have hstorCount : Devm.getStor eventPost = Devm.getStor countPost :=
    Line.of_inv Devm.getStor
      (by unfold heartbeatCountTest tagTop; line_inv) hcount
  have finishCell : ∀ {finishPre : Devm},
      Devm.getStor pre = Devm.getStor finishPre →
      Func.RunCompiledTo fs sevm finishPre pauseExpiryFinish (.ok post) →
      post.getStorVal owner key = pre.getStorVal owner key := by
    intro finishPre hprefix hfinish
    have hdup := hfinish
    rw [show pauseExpiryFinish =
      storeHeartbeatExpiryFromStack +++
        (Ninst.pushB256 0 ::: Ninst.pushB256 lockKey :::
          Ninst.tstore ::: Func.stop) from rfl] at hdup
    obtain ⟨_, hstore, -⟩ := runCompiledTo_prepend_inv hdup
    unfold storeHeartbeatExpiryFromStack at hstore
    simp only [List.append_assoc] at hstore
    obtain ⟨_, hdup, -⟩ := of_run_append [Ninst.dup 0] hstore
    rcases Line.of_run_cons hdup with ⟨_, hdup, hnil⟩
    cases hnil
    obtain ⟨value, hhead, -⟩ := of_run_dup hdup
    cases hstack : finishPre.stack with
    | nil => simp [hstack] at hhead
    | cons head tail =>
      simp [hstack] at hhead
      subst head
      have hvalue : value :: ([] : List B256) <<+ finishPre.stack := by
        exact ⟨tail, by unfold Split; simp [hstack]⟩
      obtain ⟨_, hex, trace⟩ := pauseExpiryFinish_trace hvalue hfinish
      cases Except.ok.inj hex
      have hstor := (PauseSuccessFinishTrace.result trace).2.1 owner
      change (Devm.getStor post owner).get key =
        (Devm.getStor pre owner).get key
      rw [hstor]
      by_cases howner : owner = sevm.currentTarget
      · rw [if_pos howner]
        apply (Stor.get_set_ne _ ?_ _).trans
          (congrArg (fun stor => (stor owner).get key) hprefix).symm
        intro hkey
        apply different
        exact Prod.ext howner hkey.symm
      · rw [if_neg howner]
        exact (congrArg (fun stor => (stor owner).get key) hprefix).symm
  rcases runCompiledTo_branch_inv hbranch with
    ⟨checkedPre, -, hcountPop, hcheckedArm⟩ |
      ⟨_, zeroPre, -, -, hcountPop, hzeroArm⟩
  · have hcheckedShape : checkedHeartbeatExpiry pauseExpiryFinish =
        checkedHeartbeatExpiryTest +++
          Func.branch pauseExpiryFinish
            (Func.call arithmeticPanicSlot) := rfl
    rw [hcheckedShape] at hcheckedArm
    obtain ⟨checkedPost, hchecked, hcheckedBranch⟩ :=
      runCompiledTo_prepend_inv hcheckedArm
    rcases runCompiledTo_branch_inv hcheckedBranch with
      ⟨finishPre, -, hcheckedPop, hfinish⟩ |
        ⟨_, panicPre, -, -, -, hpanicRun⟩
    · apply finishCell
      · exact hstorEvent.trans (hstorCount.trans
          ((PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hcountPop)).trans
            ((Line.of_inv Devm.getStor
              (by unfold checkedHeartbeatExpiryTest; line_inv) hchecked).trans
              (PopBurn.Inv.inv
                (Devm.PopBurn.of_popBurnBy hcheckedPop)))))
      · exact hfinish
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv hpanic hpanicRun
      exact (Func.RunCompiledTo.not_ok_revertData hbody).elim
  · obtain ⟨finishPre, hpush, hfinish⟩ :=
      runCompiledTo_next_inv hzeroArm
    apply finishCell
    · exact hstorEvent.trans (hstorCount.trans
        ((PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hcountPop)).trans
          (Ninst.Hinv.inv (f := Devm.getStor)
            (Ninst.Run.of_runCompiled hpush))))
    · exact hfinish

/-- A successful `pauseSuccess` preserves the complete persistent-storage map
of every account other than the CircuitBreaker itself. -/
theorem pauseSuccess_ok_getStor_eq_of_owner_ne
    {fs : List Func} {sevm : Sevm} {pre post : Devm} {owner : Adr}
    (hpanic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (ownerNe : owner ≠ sevm.currentTarget)
    (run : Func.RunCompiledTo fs sevm pre pauseSuccess (.ok post)) :
    Devm.getStor post owner = Devm.getStor pre owner := by
  have hshape : pauseSuccess =
      pauseSuccessEventLine +++
        (heartbeatCountTest +++
          ((Ninst.pushB256 0 ::: pauseExpiryFinish) <?>
            (checkedHeartbeatExpiry <| pauseExpiryFinish))) := rfl
  rw [hshape] at run
  obtain ⟨eventPost, hevent, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨countPost, hcount, hbranch⟩ :=
    runCompiledTo_prepend_inv run
  have hstorEvent : Devm.getStor pre = Devm.getStor eventPost :=
    Line.of_inv Devm.getStor pauseSuccessEvent_storInv hevent
  have hstorCount : Devm.getStor eventPost = Devm.getStor countPost :=
    Line.of_inv Devm.getStor
      (by unfold heartbeatCountTest tagTop; line_inv) hcount
  have finishStor : ∀ {finishPre : Devm},
      Devm.getStor pre = Devm.getStor finishPre →
      Func.RunCompiledTo fs sevm finishPre pauseExpiryFinish (.ok post) →
      Devm.getStor post owner = Devm.getStor pre owner := by
    intro finishPre hprefix hfinish
    have hdup := hfinish
    rw [show pauseExpiryFinish =
      storeHeartbeatExpiryFromStack +++
        (Ninst.pushB256 0 ::: Ninst.pushB256 lockKey :::
          Ninst.tstore ::: Func.stop) from rfl] at hdup
    obtain ⟨_, hstore, -⟩ := runCompiledTo_prepend_inv hdup
    unfold storeHeartbeatExpiryFromStack at hstore
    simp only [List.append_assoc] at hstore
    obtain ⟨_, hdup, -⟩ := of_run_append [Ninst.dup 0] hstore
    rcases Line.of_run_cons hdup with ⟨_, hdup, hnil⟩
    cases hnil
    obtain ⟨value, hhead, -⟩ := of_run_dup hdup
    cases hstack : finishPre.stack with
    | nil => simp [hstack] at hhead
    | cons head tail =>
      simp [hstack] at hhead
      subst head
      have hvalue : value :: ([] : List B256) <<+ finishPre.stack := by
        exact ⟨tail, by unfold Split; simp [hstack]⟩
      obtain ⟨_, hex, trace⟩ := pauseExpiryFinish_trace hvalue hfinish
      cases Except.ok.inj hex
      have hstor := (PauseSuccessFinishTrace.result trace).2.1 owner
      rw [if_neg ownerNe] at hstor
      exact hstor.trans (congrFun hprefix owner).symm
  rcases runCompiledTo_branch_inv hbranch with
    ⟨checkedPre, -, hcountPop, hcheckedArm⟩ |
      ⟨_, zeroPre, -, -, hcountPop, hzeroArm⟩
  · have hcheckedShape : checkedHeartbeatExpiry pauseExpiryFinish =
        checkedHeartbeatExpiryTest +++
          Func.branch pauseExpiryFinish
            (Func.call arithmeticPanicSlot) := rfl
    rw [hcheckedShape] at hcheckedArm
    obtain ⟨checkedPost, hchecked, hcheckedBranch⟩ :=
      runCompiledTo_prepend_inv hcheckedArm
    rcases runCompiledTo_branch_inv hcheckedBranch with
      ⟨finishPre, -, hcheckedPop, hfinish⟩ |
        ⟨_, panicPre, -, -, -, hpanicRun⟩
    · apply finishStor
      · exact hstorEvent.trans (hstorCount.trans
          ((PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hcountPop)).trans
            ((Line.of_inv Devm.getStor
              (by unfold checkedHeartbeatExpiryTest; line_inv) hchecked).trans
              (PopBurn.Inv.inv
                (Devm.PopBurn.of_popBurnBy hcheckedPop)))))
      · exact hfinish
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv hpanic hpanicRun
      exact (Func.RunCompiledTo.not_ok_revertData hbody).elim
  · obtain ⟨finishPre, hpush, hfinish⟩ :=
      runCompiledTo_next_inv hzeroArm
    apply finishStor
    · exact hstorEvent.trans (hstorCount.trans
        ((PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hcountPop)).trans
          (Ninst.Hinv.inv (f := Devm.getStor)
            (Ninst.Run.of_runCompiled hpush))))
    · exact hfinish

/-- The source branch relation determines its carried value. -/
private theorem PauseExpiryValue.unique
    {timestamp interval count left right : B256}
    (hleft : PauseExpiryValue timestamp interval count left)
    (hright : PauseExpiryValue timestamp interval count right) :
    left = right := by
  by_cases hzero : count = 0
  · rw [hleft.1 hzero, hright.1 hzero]
  · rcases hleft.2 hzero with ⟨-, hleftValue⟩
    rcases hright.2 hzero with ⟨-, hrightValue⟩
    exact hleftValue.trans hrightValue.symm

/-- `loadWord` preserves the active output.  Like its log companion above,
this is kept local because `MLOAD` has no global output-invariance instance. -/
private theorem loadWord_output_eq {e : Sevm} {s s' : Devm} {k : B256}
    (h : Line.Run e s (loadWord k) s') : s.output = s'.output := by
  unfold loadWord at h
  rcases Line.of_run_cons h with ⟨s1, qpush, hrest⟩
  rcases Line.of_run_cons hrest with ⟨s2, qmload, hnil⟩
  cases hnil
  rcases of_run_reg qmload with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, u1⟩, h1, run1⟩
  rcases Except.bind_eq_ok run1 with ⟨u2, h2, run2⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have hb := Devm.burn_of_chargeGas h2
  have hp := Devm.push_of_push run2
  exact (of_run_pushB256 qpush).output.trans
    ((p1.output.trans hb.output).trans hp.output)

/-- The event prefix preserves output even though it writes memory and emits a
log. -/
private theorem pauseSuccessEvent_output_eq
    {sevm : Sevm} {pre post : Devm}
    (run : Line.Run sevm pre pauseSuccessEventLine post) :
    pre.output = post.output := by
  unfold pauseSuccessEventLine at run
  simp only [List.append_assoc] at run
  obtain ⟨s1, hduration, rest⟩ := of_run_append (loadWord durationWord) run
  obtain ⟨s2, hmstore, rest⟩ := of_run_append (mstoreAt 0) rest
  obtain ⟨s3, hcaller, rest⟩ := of_run_append [Ninst.caller] rest
  obtain ⟨s4, htarget, rest⟩ := of_run_append (loadWord targetWord) rest
  obtain ⟨s5, hevent, hlog⟩ :=
    of_run_append [Ninst.pushB256 pauseTriggeredEvent] rest
  exact (loadWord_output_eq hduration).trans
    ((Line.of_inv Devm.output (by unfold mstoreAt; line_inv) hmstore).trans
      ((Line.of_inv Devm.output (by line_inv) hcaller).trans
        ((loadWord_output_eq htarget).trans
          ((Line.of_inv Devm.output (by line_inv) hevent).trans
            (Line.of_inv Devm.output (by unfold logWith; line_inv) hlog)))))

/-- `TIMESTAMP` is a push/burn step and preserves logs and output. -/
private theorem timestamp_logs_output
    {sevm : Sevm} {pre post : Devm}
    (run : Ninst.Run sevm pre Ninst.timestamp post) :
    pre.logs = post.logs ∧ pre.output = post.output := by
  change Ninst.Run sevm pre (.reg .timestamp) post at run
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  have hpush := Devm.pushBurn_of_pushItem instructionRun
  exact ⟨hpush.logs, hpush.output⟩

/-- The checked-addition test itself emits no log and does not alter output. -/
private theorem checkedHeartbeatExpiryTest_logs_output
    {sevm : Sevm} {pre post : Devm}
    (run : Line.Run sevm pre checkedHeartbeatExpiryTest post) :
    pre.logs = post.logs ∧ pre.output = post.output := by
  unfold checkedHeartbeatExpiryTest at run
  rcases Line.of_run_cons run with ⟨s1, qtime1, run⟩
  rcases Line.of_run_cons run with ⟨s2, qslot, run⟩
  rcases Line.of_run_cons run with ⟨s3, qsload, run⟩
  rcases Line.of_run_cons run with ⟨s4, qadd, run⟩
  rcases Line.of_run_cons run with ⟨s5, qdup, run⟩
  rcases Line.of_run_cons run with ⟨s6, qtime2, run⟩
  rcases Line.of_run_cons run with ⟨s7, qswap, run⟩
  rcases Line.of_run_cons run with ⟨_, qlt, hnil⟩
  cases hnil
  rcases timestamp_logs_output qtime1 with ⟨lt1, ot1⟩
  rcases timestamp_logs_output qtime2 with ⟨lt2, ot2⟩
  constructor
  · exact lt1.trans
      ((Ninst.Hinv.inv (f := Devm.logs) qslot).trans
        ((Ninst.Hinv.inv (f := Devm.logs) qsload).trans
          ((Ninst.Hinv.inv (f := Devm.logs) qadd).trans
            ((Ninst.Hinv.inv (f := Devm.logs) qdup).trans
              (lt2.trans
                ((Ninst.Hinv.inv (f := Devm.logs) qswap).trans
                  (Ninst.Hinv.inv (f := Devm.logs) qlt)))))))
  · exact ot1.trans
      ((Ninst.Hinv.inv (f := Devm.output) qslot).trans
        ((Ninst.Hinv.inv (f := Devm.output) qsload).trans
          ((Ninst.Hinv.inv (f := Devm.output) qadd).trans
            ((Ninst.Hinv.inv (f := Devm.output) qdup).trans
              (ot2.trans
                ((Ninst.Hinv.inv (f := Devm.output) qswap).trans
                  (Ninst.Hinv.inv (f := Devm.output) qlt)))))))

/-- Lift the common finish result across either source count arm.  This is the
whole-walk exact log, persistent-storage, transient-storage, and output frame
result; it consumes no premise about callback behaviour. -/
theorem PauseSuccessCommitTrace.result
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {target duration value : B256}
    (trace : PauseSuccessCommitTrace fs sevm pre post
      target duration value) :
    post.logs = pre.logs ++
      [pauseTriggeredLog sevm target duration,
        heartbeatUpdatedLog sevm value] ∧
    (∀ owner,
      Devm.getStor post owner =
        if owner = sevm.currentTarget then
          (Devm.getStor pre owner).set
            (expirySlot sevm.caller.toB256) value
        else Devm.getStor pre owner) ∧
    post.getTransVal sevm.currentTarget lockKey = 0 ∧
    (∀ owner key,
      (owner, key) ≠ (sevm.currentTarget, lockKey) →
        post.getTransVal owner key = pre.getTransVal owner key) ∧
    post.output = pre.output := by
  rcases trace with ⟨eventPost, countPost, finishPre, hevent, htriggered,
    hcount, hroute, hfinish⟩
  have hlogsCount : eventPost.logs = countPost.logs :=
    Line.of_inv Devm.logs (by unfold heartbeatCountTest tagTop; line_inv) hcount
  have hstorCount : Devm.getStor pre = Devm.getStor countPost :=
    (Line.of_inv Devm.getStor pauseSuccessEvent_storInv hevent).trans
      (Line.of_inv Devm.getStor
        (by unfold heartbeatCountTest tagTop; line_inv) hcount)
  have htransientCount : pre.transientStorage = countPost.transientStorage :=
    (Line.of_inv Devm.transientStorage
      (by unfold pauseSuccessEventLine loadWord mstoreAt logWith; line_inv)
      hevent).trans
      (Line.of_inv Devm.transientStorage
        (by unfold heartbeatCountTest tagTop; line_inv) hcount)
  have houtputCount : pre.output = countPost.output :=
    (pauseSuccessEvent_output_eq hevent).trans
      (Line.of_inv Devm.output
        (by unfold heartbeatCountTest tagTop; line_inv) hcount)
  have hprefix :
      eventPost.logs = finishPre.logs ∧
      Devm.getStor pre = Devm.getStor finishPre ∧
      pre.transientStorage = finishPre.transientStorage ∧
      pre.output = finishPre.output := by
    rcases hroute with
      ⟨checkedPre, checkedPost, -, hcountPop, hchecked, -, hcheckedPop⟩ |
        ⟨zeroPre, -, hcountPop, hpushZero⟩
    · have hcountPop' := Devm.PopBurn.of_popBurnBy hcountPop
      have hcheckedPop' := Devm.PopBurn.of_popBurnBy hcheckedPop
      rcases checkedHeartbeatExpiryTest_logs_output hchecked with
        ⟨hcheckedLogs, hcheckedOutput⟩
      refine ⟨hlogsCount.trans
          (hcountPop'.logs.trans
            (hcheckedLogs.trans hcheckedPop'.logs)), ?_, ?_, ?_⟩
      · exact hstorCount.trans
          ((PopBurn.Inv.inv hcountPop').trans
            ((Line.of_inv Devm.getStor
              (by unfold checkedHeartbeatExpiryTest; line_inv) hchecked).trans
              (PopBurn.Inv.inv hcheckedPop')))
      · exact htransientCount.trans
          ((PopBurn.Inv.inv hcountPop').trans
            ((Line.of_inv Devm.transientStorage
              (by unfold checkedHeartbeatExpiryTest; line_inv) hchecked).trans
              (PopBurn.Inv.inv hcheckedPop')))
      · exact houtputCount.trans
          (hcountPop'.output.trans
            (hcheckedOutput.trans hcheckedPop'.output))
    · have hcountPop' := Devm.PopBurn.of_popBurnBy hcountPop
      have hpush := Ninst.Run.of_runCompiled hpushZero
      have hpushEffect := of_run_pushB256 hpush
      refine ⟨hlogsCount.trans
          (hcountPop'.logs.trans hpushEffect.logs), ?_, ?_, ?_⟩
      · exact hstorCount.trans
          ((PopBurn.Inv.inv hcountPop').trans
            (Ninst.Hinv.inv (f := Devm.getStor) hpush))
      · exact htransientCount.trans
          ((PopBurn.Inv.inv hcountPop').trans
            (Ninst.Hinv.inv (f := Devm.transientStorage) hpush))
      · exact houtputCount.trans
          (hcountPop'.output.trans hpushEffect.output)
  rcases PauseSuccessFinishTrace.result hfinish with
    ⟨hlogs, hstor, hlock, hother, houtput⟩
  rcases hprefix with ⟨hlogsPrefix, hstorPrefix, htransientPrefix,
    houtputPrefix⟩
  constructor
  · rw [hlogs, ← hlogsPrefix, htriggered]
    simp only [List.append_assoc, List.singleton_append]
  constructor
  · intro owner
    rw [hstor owner, ← congrFun hstorPrefix owner]
  constructor
  · exact hlock
  constructor
  · intro owner key hne
    rw [hother owner key hne]
    unfold Devm.getTransVal
    rw [← htransientPrefix]
  · exact houtput.trans houtputPrefix.symm

/-- The target staging window survives the first event.  Its offset is far
above the one word that the event re-stages at memory zero. -/
private theorem pauseSuccessEvent_target_survives
    {sevm : Sevm} {pre post : Devm} {target : B256}
    (window : MemWordAt pre (targetWord * 32).toNat target)
    (run : Line.Run sevm pre pauseSuccessEventLine post) :
    MemWordAt post (targetWord * 32).toNat target := by
  unfold pauseSuccessEventLine at run
  simp only [List.append_assoc] at run
  obtain ⟨s1, hduration, rest⟩ := of_run_append (loadWord durationWord) run
  obtain ⟨s2, hmstore, rest⟩ := of_run_append (mstoreAt 0) rest
  obtain ⟨s3, hcaller, rest⟩ := of_run_append [Ninst.caller] rest
  obtain ⟨s4, htarget, rest⟩ := of_run_append (loadWord targetWord) rest
  obtain ⟨s5, hevent, hlog⟩ :=
    of_run_append [Ninst.pushB256 pauseTriggeredEvent] rest
  exact (((((window.acrossLoadWord hduration).acrossMstoreAt (by decide)
    hmstore).acrossLine (by line_inv) hcaller).acrossLoadWord htarget).acrossLine
      (by line_inv) hevent).acrossLogWith hlog

/-- **D1–D6: every reached `pauseSuccess` either commits its exact result or
enters the production arithmetic-panic body.**

The theorem is universal over the function table except for the one lookup
that identifies the panic slot's payload.  Its count and interval are facts
about the actual post-callback entry state. -/
theorem pauseSuccess_outcome
    {fs : List Func} {sevm : Sevm} {pre : Devm} {ex : Execution}
    {target duration count interval : B256}
    (hpanic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (inputs : PauseSuccessInputs sevm pre target duration count interval)
    (run : Func.RunCompiledTo fs sevm pre pauseSuccess ex) :
    PauseSuccessOutcome fs sevm pre target duration count interval ex := by
  have traced := pauseSuccess_trace_dichotomy inputs run
  rcases traced with
    ⟨post, value, hex, htrace, hvalue⟩ |
      ⟨hcountNonzero, hnof, htrace⟩
  · rcases inputs with ⟨htarget, hduration, hcount, hinterval⟩
    rcases PauseSuccessCommitTrace.result htrace with
      ⟨hlogs, hstor, hlock, hother, houtput⟩
    rcases pauseSuccess_expiryWrite_dichotomy rfl hcount hinterval run with
      ⟨written, hwrite, hwrittenValue⟩ |
        ⟨hcountNonzero, hpanicNof, panicPre, hpanicRun⟩
    · have hwritten : written = value :=
        PauseExpiryValue.unique hwrittenValue hvalue
      subst written
      refine Or.inl ⟨post, value, hex, ?_⟩
      exact ⟨⟨htarget, hduration, hcount, hinterval⟩,
        by rw [← hex]; exact run, htrace, hwrite, hvalue,
        hlogs, hstor, hlock, hother, houtput⟩
    · have hnof' : B256.Nof sevm.benvStat.time interval :=
        (hvalue.2 hcountNonzero).1
      exact absurd hnof' hpanicNof
  · rcases inputs with ⟨htarget, hduration, hcount, hinterval⟩
    rcases htrace with
      ⟨eventPost, countPost, checkedPre, checkedPost, panicPre,
        hevent, htriggered, hcountRun, hcountStack, hcountPop, hchecked,
        hcheckedStack, hcheckedPop, hpanicCall⟩
    obtain ⟨bodyPre, hcallBurn, hbody⟩ :=
      runCompiledTo_call_inv hpanic hpanicCall
    have countBurn := Devm.PopBurn.of_popBurnBy hcountPop
    have checkedBurn := Devm.PopBurn.of_popBurnBy hcheckedPop
    have callBurn := Devm.Burn.of_burnBy hcallBurn
    have hstorBody : Devm.getStor pre = Devm.getStor bodyPre :=
      (Line.of_inv Devm.getStor pauseSuccessEvent_storInv hevent).trans
        ((Line.of_inv Devm.getStor
          (by unfold heartbeatCountTest tagTop; line_inv) hcountRun).trans
          ((PopBurn.Inv.inv countBurn).trans
            ((Line.of_inv Devm.getStor
              (by unfold checkedHeartbeatExpiryTest; line_inv) hchecked).trans
              ((PopBurn.Inv.inv checkedBurn).trans
                (Burn.Inv.inv callBurn)))))
    have htransientBody : pre.transientStorage = bodyPre.transientStorage :=
      (Line.of_inv Devm.transientStorage
        (by unfold pauseSuccessEventLine loadWord mstoreAt logWith; line_inv)
        hevent).trans
        ((Line.of_inv Devm.transientStorage
          (by unfold heartbeatCountTest tagTop; line_inv) hcountRun).trans
          (countBurn.transientStorage.trans
            ((Line.of_inv Devm.transientStorage
              (by unfold checkedHeartbeatExpiryTest; line_inv) hchecked).trans
              (checkedBurn.transientStorage.trans
                callBurn.transientStorage))))
    rcases checkedHeartbeatExpiryTest_logs_output hchecked with
      ⟨hcheckedLogs, -⟩
    have heventBodyLogs : eventPost.logs = bodyPre.logs :=
      (Line.of_inv Devm.logs
        (by unfold heartbeatCountTest tagTop; line_inv) hcountRun).trans
        (countBurn.logs.trans
          (hcheckedLogs.trans
            (checkedBurn.logs.trans callBurn.logs)))
    have hbodyLogs :
        bodyPre.logs =
          pre.logs ++ [pauseTriggeredLog sevm target duration] :=
      heventBodyLogs.symm.trans htriggered
    have targetEvent := pauseSuccessEvent_target_survives htarget hevent
    have targetCount := targetEvent.acrossLine
      (by unfold heartbeatCountTest tagTop; line_inv) hcountRun
    have targetChecked := MemWordAt.of_memory_eq countBurn.memory.symm targetCount
    have targetCheckedPost := targetChecked.acrossLine
      (by unfold checkedHeartbeatExpiryTest; line_inv) hchecked
    have targetPanic :=
      MemWordAt.of_memory_eq checkedBurn.memory.symm targetCheckedPost
    have targetBody := MemWordAt.of_memory_eq callBurn.memory.symm targetPanic
    obtain ⟨image, hwf, hreads⟩ := targetBody.memImage
    have hblob : heartbeatArithmeticPanicData.length < 2 ^ 256 := by
      decide +kernel
    have hwords :
        32 * (bytesWords heartbeatArithmeticPanicData).length < 2 ^ 256 := by
      decide +kernel
    rcases runCompiledTo_revertData_frame_inv hwf hreads hblob hwords hbody with
      ⟨d, herror, hstor, htransient, hlogs⟩ |
        ⟨panicPost, herror, hpayload, hstor, htransient, hlogs⟩
    · refine Or.inr ⟨⟨htarget, hduration, hcount, hinterval⟩, run, hpanic,
        ?_, hcountNonzero, hnof, Or.inl ?_⟩
      · exact ⟨eventPost, countPost, checkedPre, checkedPost, panicPre,
          hevent, htriggered, hcountRun, hcountStack, hcountPop,
          hchecked, hcheckedStack, hcheckedPop, hpanicCall⟩
      · exact ⟨d, herror, hstor.trans hstorBody.symm,
          htransient.trans htransientBody.symm,
          hlogs.trans hbodyLogs⟩
    · refine Or.inr ⟨⟨htarget, hduration, hcount, hinterval⟩, run, hpanic,
        ?_, hcountNonzero, hnof, Or.inr ?_⟩
      · exact ⟨eventPost, countPost, checkedPre, checkedPost, panicPre,
          hevent, htriggered, hcountRun, hcountStack, hcountPop,
          hchecked, hcheckedStack, hcheckedPop, hpanicCall⟩
      · exact ⟨panicPost, herror, hpayload,
          hstor.trans hstorBody.symm,
          htransient.trans htransientBody.symm,
          hlogs.trans hbodyLogs⟩

/-! ## Composition through the two calls and decode -/

/-- A staged word at or beyond byte 320 survives the `pauseFor` calldata
staging line. -/
private theorem memWordAt_acrossPauseCallStaging
    {sevm : Sevm} {pre post : Devm} {offset : Nat} {word : B256}
    (hpast : 320 ≤ offset)
    (window : MemWordAt pre offset word)
    (run : Line.Run sevm pre pauseCallStaging post) :
    MemWordAt post offset word := by
  unfold pauseCallStaging at run
  simp only [List.append_assoc] at run
  obtain ⟨s1, hprefix, rest⟩ :=
    of_run_append [Ninst.pop, Ninst.pushB256 pauseForSelector] run
  obtain ⟨s2, hselector, rest⟩ := of_run_append (mstoreAt 8) rest
  obtain ⟨s3, hduration, rest⟩ := of_run_append (loadWord durationWord) rest
  obtain ⟨s4, hdurationStore, rest⟩ := of_run_append (mstoreAt 9) rest
  obtain ⟨s5, hargs, rest⟩ :=
    of_run_append (pushList [0, 0, 36, 0x11c, 0]) rest
  obtain ⟨s6, htarget, hgas⟩ := of_run_append (loadWord targetWord) rest
  exact ((((((window.acrossLine (by line_inv) hprefix).acrossMstoreAt
    (Or.inr (by change 288 ≤ offset; omega)) hselector).acrossLoadWord
      hduration).acrossMstoreAt
      (Or.inr (by change 320 ≤ offset; omega)) hdurationStore).acrossLine
        (by unfold pushList; simp only [List.map]; line_inv) hargs).acrossLoadWord
          htarget).acrossLine (by line_inv) hgas

/-- A staged word at or beyond byte 288 survives the `isPaused()` calldata
staging line. -/
private theorem memWordAt_acrossPauseStatStaging
    {sevm : Sevm} {pre post : Devm} {offset : Nat} {word : B256}
    (hpast : 288 ≤ offset)
    (window : MemWordAt pre offset word)
    (run : Line.Run sevm pre pauseStatStaging post) :
    MemWordAt post offset word := by
  unfold pauseStatStaging at run
  simp only [List.append_assoc] at run
  obtain ⟨s1, hpush, rest⟩ :=
    of_run_append [Ninst.pushB256 isPausedSelector] run
  obtain ⟨s2, hselector, rest⟩ := of_run_append (mstoreAt 8) rest
  obtain ⟨s3, hargs, rest⟩ :=
    of_run_append (pushList [32, 0, 4, 0x11c]) rest
  obtain ⟨s4, htarget, hgas⟩ := of_run_append (loadWord targetWord) rest
  exact ((((window.acrossLine (by line_inv) hpush).acrossMstoreAt
    (Or.inr (by change 288 ≤ offset; omega)) hselector).acrossLine
      (by unfold pushList; simp only [List.map]; line_inv) hargs).acrossLoadWord
        htarget).acrossLine (by line_inv) hgas

/-- Public successor for carrying a high memory word through CALL staging. -/
theorem _root_.Blanc.MemWordAt.acrossPauseCallStagingBoundary
    {sevm : Sevm} {pre post : Devm} {offset : Nat} {word : B256}
    (hpast : 320 ≤ offset)
    (window : MemWordAt pre offset word)
    (run : Line.Run sevm pre pauseCallStaging post) :
    MemWordAt post offset word :=
  memWordAt_acrossPauseCallStaging hpast window run

/-- Public successor for carrying a high memory word through STATICCALL
staging. -/
theorem _root_.Blanc.MemWordAt.acrossPauseStatStagingBoundary
    {sevm : Sevm} {pre post : Devm} {offset : Nat} {word : B256}
    (hpast : 288 ≤ offset)
    (window : MemWordAt pre offset word)
    (run : Line.Run sevm pre pauseStatStaging post) :
    MemWordAt post offset word :=
  memWordAt_acrossPauseStatStaging hpast window run

/-- Contract-local value-carrying `EXTCODESIZE` inversion used by the
strengthened code-guard handoff. -/
private lemma success_of_extcodesize_val
    {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Ninst.Run e s Ninst.extcodesize r) :
    ((s.getCode x.toAdr).size.toB256 :: xs <<+ r.stack) ∧
      s.memory = r.memory := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨adr, d1⟩, hpopAdr, hrun⟩
  rw [Devm.popToAdr_def] at hpopAdr
  dsimp [(· <&> ·), Functor.mapRev, Functor.map, Except.map] at hpopAdr
  rcases hpop : Devm.pop s with _ | ⟨word, d0⟩ <;> simp [hpop] at hpopAdr
  rcases hpopAdr with ⟨rfl, rfl⟩
  have hpop' := Devm.pop_of_pop hpop
  have hx : x = word :=
    (List.of_cons_pref_of_cons_pref hp (pref_of_split hpop'.stack)).left
  subst word
  have htail : xs <<+ d0.stack := of_append_pref hpop'.stack hp
  split at hrun
  · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hstate : s.state = d2.state :=
      hpop'.state.trans (Devm.burn_of_chargeGas hgas).state
    have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
      unfold Devm.getCode Devm.getAcct
      rw [hstate]
    refine ⟨?_, ?_⟩
    · rw [← hcode]
      exact append_pref (Devm.push_of_push hpush).stack
        (by rw [← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
    · exact hpop'.memory.trans
        ((Devm.burn_of_chargeGas hgas).memory.trans
          (Devm.push_of_push hpush).memory)
  · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hstate : s.state = d2.state :=
      hpop'.state.trans
        ((show d0.state = (addAccessedAddress d0 x.toAdr).state from rfl).trans
          (Devm.burn_of_chargeGas hgas).state)
    have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
      unfold Devm.getCode Devm.getAcct
      rw [hstate]
    refine ⟨?_, ?_⟩
    · rw [← hcode]
      exact append_pref (Devm.push_of_push hpush).stack
        (by rw [← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
    · exact hpop'.memory.trans
        ((show d0.memory = (addAccessedAddress d0 x.toAdr).memory from rfl).trans
          ((Devm.burn_of_chargeGas hgas).memory.trans
            (Devm.push_of_push hpush).memory))

/-- The code guard, strengthened only on its live arm with both staged-memory
windows. -/
private theorem pauseAfterSet_codeGuard_arms_words
    {fs : List Func} {sevm : Sevm} {entry : Devm} {target : Adr}
    {duration : B256} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (hTarget : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (hDuration : MemWordAt entry (durationWord * 32).toNat duration)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet ex) :
    ((entry.getCode target).size.toB256 = 0 ∧
        ∃ post, ex = .error (.revert, post) ∧ post.output = []) ∨
    ((entry.getCode target).size.toB256 ≠ 0 ∧
      ∃ guardPost : Devm,
        MemWordAt guardPost (targetWord * 32).toNat target.toB256 ∧
        MemWordAt guardPost (durationWord * 32).toNat duration ∧
        Func.RunCompiledTo fs sevm guardPost
          (pauseCallStaging +++
            (Ninst.call ::: pauseAfterCallBranch)) ex) := by
  rw [pauseAfterSet_eq_afterCall] at run
  obtain ⟨guardTestPost, hguard, hbranch⟩ :=
    runCompiledTo_prepend_inv run
  unfold pauseCodeGuard at hguard
  obtain ⟨s1, hload, hrest⟩ := of_run_append (loadWord targetWord) hguard
  rcases Line.of_run_cons hrest with ⟨s2, hdup, hrest⟩
  rcases Line.of_run_cons hrest with ⟨s3, hcodesize, hrest⟩
  rcases Line.of_run_cons hrest with ⟨_, hiszero, hnil⟩
  cases hnil
  have targetGuard := (((hTarget.acrossLoadWord hload).acrossNinst hdup).acrossNinst
    hcodesize).acrossNinst hiszero
  have durationGuard :=
    (((hDuration.acrossLoadWord hload).acrossNinst hdup).acrossNinst
      hcodesize).acrossNinst hiszero
  have htargetStack : target.toB256 :: ([] : Stack) <<+ s1.stack :=
    prefix_of_loadWord_window hTarget nil_pref hload
  have hdupStack : target.toB256 :: [target.toB256] <<+ s2.stack :=
    prefix_of_dup_val hdup (by show_nth) htargetStack
  obtain ⟨hcodeStack, -⟩ := success_of_extcodesize_val hdupStack hcodesize
  have hcode : s2.getCode = entry.getCode := by
    have hloadCode : Devm.getCode entry = Devm.getCode s1 :=
      Line.of_inv Devm.getCode (by unfold loadWord; line_inv) hload
    have hdupCode : Devm.getCode s1 = Devm.getCode s2 :=
      Ninst.Hinv.inv hdup
    exact (hloadCode.trans hdupCode).symm
  rw [toAdr_toB256 target, hcode] at hcodeStack
  have hflag := prefix_of_iszero hiszero hcodeStack
  rcases runCompiledTo_branch_inv hbranch with
    ⟨guardPost, hzeroStack, hpop, hlive⟩ |
      ⟨word, revertPre, hword, hwordStack, hpop, hrevert⟩
  · have hflagZero : ((entry.getCode target).size.toB256 =? 0) = 0 := by
      obtain ⟨tail, htail⟩ := hflag
      rw [htail] at hzeroStack
      exact (List.cons.inj hzeroStack).1
    have pop := Devm.PopBurn.of_popBurnBy hpop
    have hcodeNonzero : (entry.getCode target).size.toB256 ≠ 0 := by
      intro hzero
      rw [hzero, B256.eqCheck, if_pos rfl] at hflagZero
      exact absurd hflagZero (by decide)
    exact Or.inr ⟨hcodeNonzero, guardPost,
      MemWordAt.of_memory_eq pop.memory.symm targetGuard,
      MemWordAt.of_memory_eq pop.memory.symm durationGuard, hlive⟩
  · have hflagWord : ((entry.getCode target).size.toB256 =? 0) = word := by
      obtain ⟨tail, htail⟩ := hflag
      rw [htail] at hwordStack
      exact (List.cons.inj hwordStack).1
    obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_empty hrevert
    have hcodeZero : (entry.getCode target).size.toB256 = 0 := by
      by_contra hnonzero
      rw [B256.eqCheck, if_neg hnonzero] at hflagWord
      exact hword hflagWord.symm
    exact Or.inl ⟨hcodeZero, runCompiledTo_revert_inv hbody⟩

/-- The post-`CALL` branch, with both staged words carried into whichever arm
the source selects. -/
private theorem pauseAfterCall_arms_words
    {fs : List Func} {sevm : Sevm} {target : Adr} {duration : B256}
    {callPre callPost : Devm} {ex : Execution} {next : Func}
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (targetWindow : MemWordAt callPost
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt callPost
      (durationWord * 32).toNat duration)
    (run : Func.RunCompiledTo fs sevm callPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> next)) ex) :
    ∃ child armPre : Devm,
      callPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      MemWordAt armPre (targetWord * 32).toNat target.toB256 ∧
      MemWordAt armPre (durationWord * 32).toNat duration ∧
      ((child.error.isSome = true ∧
          Func.RunCompiledTo fs sevm armPre
            (Func.call bubbleRevertSlot) ex) ∨
        (child.error.isSome = false ∧
          Func.RunCompiledTo fs sevm armPre next ex)) := by
  obtain ⟨mid, hiszero, hbranch⟩ := runCompiledTo_next_inv run
  obtain ⟨child, rest, hcallStack, hmidStack, hreturn, hmidReturn⟩ :=
    pauseCall_branchWord boundary hiszero
  have targetMid := targetWindow.acrossNinst
    (Ninst.Run.of_runCompiled hiszero)
  have durationMid := durationWindow.acrossNinst
    (Ninst.Run.of_runCompiled hiszero)
  rcases runCompiledTo_branch_inv hbranch with
    ⟨armPre, hzeroStack, hpop, harm⟩ |
      ⟨word, armPre, hwordNonzero, hwordStack, hpop, harm⟩
  · have hflag : (if child.error.isSome then (1 : B256) else 0) = 0 := by
      rw [hmidStack] at hzeroStack
      exact (List.cons.inj hzeroStack).1
    have pop := Devm.PopBurn.of_popBurnBy hpop
    refine ⟨child, armPre, hreturn,
          pop.returnData.symm.trans hmidReturn,
      MemWordAt.of_memory_eq pop.memory.symm targetMid,
      MemWordAt.of_memory_eq pop.memory.symm durationMid, Or.inr ⟨?_, harm⟩⟩
    revert hflag
    cases child.error.isSome
    · intro; rfl
    · intro h
      exact absurd h (by decide)
  · have hflag : (if child.error.isSome then (1 : B256) else 0) = word := by
      rw [hmidStack] at hwordStack
      exact (List.cons.inj hwordStack).1
    have pop := Devm.PopBurn.of_popBurnBy hpop
    refine ⟨child, armPre, hreturn,
          pop.returnData.symm.trans hmidReturn,
      MemWordAt.of_memory_eq pop.memory.symm targetMid,
      MemWordAt.of_memory_eq pop.memory.symm durationMid, Or.inl ⟨?_, harm⟩⟩
    cases hchild : child.error.isSome
    · exfalso
      apply hwordNonzero
      simpa [hchild] using hflag.symm
    · rfl

/-- Public window-carrying code-guard decomposition used by public-entry
composition.  It exposes no new premise and preserves both terminal polarities. -/
theorem pauseAfterSet_codeGuard_arms_windows
    {fs : List Func} {sevm : Sevm} {entry : Devm} {target : Adr}
    {duration : B256} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (hTarget : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (hDuration : MemWordAt entry (durationWord * 32).toNat duration)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet ex) :
    ((entry.getCode target).size.toB256 = 0 ∧
        ∃ post, ex = .error (.revert, post) ∧ post.output = []) ∨
      ((entry.getCode target).size.toB256 ≠ 0 ∧
        ∃ guardPost : Devm,
          MemWordAt guardPost (targetWord * 32).toNat target.toB256 ∧
          MemWordAt guardPost (durationWord * 32).toNat duration ∧
          Func.RunCompiledTo fs sevm guardPost
            (pauseCallStaging +++
              (Ninst.call ::: pauseAfterCallBranch)) ex) :=
  pauseAfterSet_codeGuard_arms_words h_empty hTarget hDuration run

/-- Public window-carrying post-CALL decomposition used to attach the actual
CALL boundary to the settled outcome family. -/
theorem pauseAfterCall_arms_windows
    {fs : List Func} {sevm : Sevm} {target : Adr} {duration : B256}
    {callPre callPost : Devm} {ex : Execution} {next : Func}
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (targetWindow : MemWordAt callPost
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt callPost
      (durationWord * 32).toNat duration)
    (run : Func.RunCompiledTo fs sevm callPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> next)) ex) :
    ∃ child armPre : Devm,
      callPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      MemWordAt armPre (targetWord * 32).toNat target.toB256 ∧
      MemWordAt armPre (durationWord * 32).toNat duration ∧
      ((child.error.isSome = true ∧
          Func.RunCompiledTo fs sevm armPre
            (Func.call bubbleRevertSlot) ex) ∨
        (child.error.isSome = false ∧
          Func.RunCompiledTo fs sevm armPre next ex)) :=
  pauseAfterCall_arms_words boundary targetWindow durationWindow run

/-- The post-observation branch, carrying both staged words into the bubble or
decode arm selected by the child's actual status. -/
private theorem pauseObservation_arms_words
    {fs : List Func} {sevm : Sevm} {target : Adr} {duration : B256}
    {statPre statPost : Devm} {ex : Execution} {next : Func}
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (targetWindow : MemWordAt statPre
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt statPre
      (durationWord * 32).toNat duration)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> next)) ex) :
    ∃ child armPre : Devm, ∃ memory : Mem,
      statPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      armPre.memory = memory.write 0 (child.output.take 32) ∧
      MemWordAt armPre (targetWord * 32).toNat target.toB256 ∧
      MemWordAt armPre (durationWord * 32).toNat duration ∧
      ((child.error.isSome = true ∧
          Func.RunCompiledTo fs sevm armPre
            (Func.call bubbleRevertSlot) ex) ∨
        (child.error.isSome = false ∧
          Func.RunCompiledTo fs sevm armPre next ex)) := by
  obtain ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
    hstackPre, hargs, hparentMemory, hpstate, hpcreated, hptransient, hplogs,
    hpreturnData, hdepth, hdelegation, hmsg, hcurrentTarget, hcodeAddress,
    hcaller, hvalue, hstatic, hdata, hmsgTransient, hfilled, hprocess, hstep,
    hresume, hpostMemory, hpostReturnData, hpostStack⟩ := boundary
  have targetPost := pauseStat_stagedWord_survives
    ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
      hstackPre, hargs, hparentMemory, hpstate, hpcreated, hptransient, hplogs,
      hpreturnData, hdepth, hdelegation, hmsg, hcurrentTarget, hcodeAddress,
      hcaller, hvalue, hstatic, hdata, hmsgTransient, hfilled, hprocess, hstep,
      hresume, hpostMemory, hpostReturnData, hpostStack⟩
    (by decide) targetWindow
  have durationPost := pauseStat_stagedWord_survives
    ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
      hstackPre, hargs, hparentMemory, hpstate, hpcreated, hptransient, hplogs,
      hpreturnData, hdepth, hdelegation, hmsg, hcurrentTarget, hcodeAddress,
      hcaller, hvalue, hstatic, hdata, hmsgTransient, hfilled, hprocess, hstep,
      hresume, hpostMemory, hpostReturnData, hpostStack⟩
    (by decide) durationWindow
  obtain ⟨mid, hiszero, hbranch⟩ := runCompiledTo_next_inv run
  obtain ⟨hmidStack, hmidMemory, hmidReturn⟩ :=
    iszero_stack_inv hiszero hpostStack
  have targetMid := MemWordAt.of_memory_eq hmidMemory targetPost
  have durationMid := MemWordAt.of_memory_eq hmidMemory durationPost
  rcases runCompiledTo_branch_inv hbranch with
    ⟨armPre, hzeroStack, hpop, harm⟩ |
      ⟨word, armPre, hwordNonzero, hwordStack, hpop, harm⟩
  · have hflag :
        ((if child.error.isSome then (0 : B256) else 1) =? 0) = 0 := by
      rw [hmidStack] at hzeroStack
      exact (List.cons.inj hzeroStack).1
    have pop := Devm.PopBurn.of_popBurnBy hpop
    refine ⟨child, armPre, parent.memory, hpostReturnData,
      (pop.returnData.symm.trans hmidReturn).trans hpostReturnData,
      ?_, MemWordAt.of_memory_eq pop.memory.symm targetMid,
      MemWordAt.of_memory_eq pop.memory.symm durationMid, Or.inr ⟨?_, harm⟩⟩
    · exact (pop.memory.symm.trans hmidMemory).trans hpostMemory
    · revert hflag
      cases child.error.isSome
      · intro; rfl
      · intro h
        exact absurd h (by decide)
  · have hflag :
        ((if child.error.isSome then (0 : B256) else 1) =? 0) = word := by
      rw [hmidStack] at hwordStack
      exact (List.cons.inj hwordStack).1
    have pop := Devm.PopBurn.of_popBurnBy hpop
    refine ⟨child, armPre, parent.memory, hpostReturnData,
      (pop.returnData.symm.trans hmidReturn).trans hpostReturnData,
      ?_, MemWordAt.of_memory_eq pop.memory.symm targetMid,
      MemWordAt.of_memory_eq pop.memory.symm durationMid, Or.inl ⟨?_, harm⟩⟩
    · exact (pop.memory.symm.trans hmidMemory).trans hpostMemory
    · cases hchild : child.error.isSome
      · exfalso
        apply hwordNonzero
        rw [hchild, B256.eqCheck, if_neg (by decide)] at hflag
        exact hflag.symm
      · rfl

/-- On the already-classified canonical-long answer, the decode carries both
staged windows to the actual `pauseSuccess` entry it reaches. -/
private theorem pauseDecode_success_words
    {fs : List Func} {sevm : Sevm} {decodePre : Devm}
    {memory : Mem} {out : Bytes} {ex : Execution}
    {target duration : B256}
    (hmemory : decodePre.memory = memory.write 0 (out.take 32))
    (hreturnData : decodePre.returnData = out)
    (hnotShort : ¬ Nat.toB256 out.length < (32 : B256))
    (hone : pausedAnswer out = 1)
    (targetWindow : MemWordAt decodePre
      (targetWord * 32).toNat target)
    (durationWindow : MemWordAt decodePre
      (durationWord * 32).toNat duration)
    (run : Func.RunCompiledTo fs sevm decodePre decodePausedResult ex) :
    ∃ successPre : Devm,
      MemWordAt successPre (targetWord * 32).toNat target ∧
      MemWordAt successPre (durationWord * 32).toNat duration ∧
      Func.RunCompiledTo fs sevm successPre pauseSuccess ex := by
  rw [decodePausedResult] at run
  obtain ⟨shortPost, hshort, hbranch⟩ := runCompiledTo_prepend_inv run
  obtain ⟨hflag, -, -⟩ := of_returnDataShorterThan_val nil_pref hshort
  rw [hreturnData] at hflag
  have targetShort := targetWindow.acrossLine
    (by unfold returnDataShorterThan; line_inv) hshort
  have durationShort := durationWindow.acrossLine
    (by unfold returnDataShorterThan; line_inv) hshort
  rcases runCompiledTo_branch_inv hbranch with
    ⟨loadPre, hzeroStack, hpopShort, hloadArm⟩ |
      ⟨shortWord, shortPre, hshortWord, hshortStack, hpopShort, hshortArm⟩
  · have hflagZero : (Nat.toB256 out.length <? (32 : B256)) = 0 := by
      obtain ⟨tail, htail⟩ := hflag
      rw [htail] at hzeroStack
      exact (List.cons.inj hzeroStack).1
    have popShort := Devm.PopBurn.of_popBurnBy hpopShort
    have targetLoadPre := MemWordAt.of_memory_eq popShort.memory.symm targetShort
    have durationLoadPre :=
      MemWordAt.of_memory_eq popShort.memory.symm durationShort
    have hloadMemory : loadPre.memory = memory.write 0 (out.take 32) :=
      popShort.memory.symm.trans
        ((Line.of_inv Devm.memory
          (by unfold returnDataShorterThan; line_inv) hshort).symm.trans hmemory)
    obtain ⟨loadedPost, hload, hloadArm⟩ :=
      runCompiledTo_prepend_inv hloadArm
    have targetLoaded := targetLoadPre.acrossLoadWord hload
    have durationLoaded := durationLoadPre.acrossLoadWord hload
    obtain ⟨dupPost, hdup, hloadArm⟩ := runCompiledTo_next_inv hloadArm
    have targetDup := targetLoaded.acrossNinst (Ninst.Run.of_runCompiled hdup)
    have durationDup :=
      durationLoaded.acrossNinst (Ninst.Run.of_runCompiled hdup)
    obtain ⟨zeroPost, hiszero, hzeroBranch⟩ :=
      runCompiledTo_next_inv hloadArm
    have targetZero := targetDup.acrossNinst
      (Ninst.Run.of_runCompiled hiszero)
    have durationZero := durationDup.acrossNinst
      (Ninst.Run.of_runCompiled hiszero)
    have hanswerPrefix : pausedAnswer out :: ([] : Stack) <<+
        loadedPost.stack := by
      obtain ⟨hanswer, -⟩ :=
        pauseDecode_loadWord_eq_answer hloadMemory
          (le_length_of_not_toB256_lt_32 hnotShort) nil_pref hload
      exact hanswer
    have hdupPrefix : pausedAnswer out :: [pausedAnswer out] <<+
        dupPost.stack :=
      prefix_of_dup_val (Ninst.Run.of_runCompiled hdup)
        (by show_nth) hanswerPrefix
    have hzeroPrefix :=
      prefix_of_iszero (Ninst.Run.of_runCompiled hiszero) hdupPrefix
    rcases runCompiledTo_branch_inv hzeroBranch with
      ⟨canonicalPre, hzeroStack, hpopZero, hcanonicalArm⟩ |
        ⟨zeroWord, failedPre, hzeroWord, hzeroWordStack, hpopZero, hfailedArm⟩
    · have hanswerFlag : (pausedAnswer out =? 0) = 0 := by
        obtain ⟨tail, htail⟩ := hzeroPrefix
        rw [htail] at hzeroStack
        exact (List.cons.inj hzeroStack).1
      have popZero := Devm.PopBurn.of_popBurnBy hpopZero
      have targetCanonical :=
        MemWordAt.of_memory_eq popZero.memory.symm targetZero
      have durationCanonical :=
        MemWordAt.of_memory_eq popZero.memory.symm durationZero
      obtain ⟨onePost, hpushOne, hcanonicalArm⟩ :=
        runCompiledTo_next_inv hcanonicalArm
      have targetOne := targetCanonical.acrossNinst
        (Ninst.Run.of_runCompiled hpushOne)
      have durationOne := durationCanonical.acrossNinst
        (Ninst.Run.of_runCompiled hpushOne)
      obtain ⟨equalPost, hequal, hequalBranch⟩ :=
        runCompiledTo_next_inv hcanonicalArm
      have targetEqual := targetOne.acrossNinst
        (Ninst.Run.of_runCompiled hequal)
      have durationEqual := durationOne.acrossNinst
        (Ninst.Run.of_runCompiled hequal)
      have hrest : [pausedAnswer out] <<+ canonicalPre.stack := by
        rw [hanswerFlag] at hzeroPrefix
        exact of_append_pref (Devm.PopBurn.of_popBurnBy hpopZero).stack
          hzeroPrefix
      have honePrefix := prefix_of_push
        (of_run_pushB256 (Ninst.Run.of_runCompiled hpushOne)) hrest
      have hequalPrefix := prefix_of_eq
        (Ninst.Run.of_runCompiled hequal) honePrefix
      rcases runCompiledTo_branch_inv hequalBranch with
        ⟨emptyPre, hequalZero, hequalPop, hempty⟩ |
          ⟨equalWord, successPre, hequalWord, hequalStack, hequalPop, hsuccess⟩
      · have hequalFlag : ((1 : B256) =? pausedAnswer out) = 0 := by
          obtain ⟨tail, htail⟩ := hequalPrefix
          rw [htail] at hequalZero
          exact (List.cons.inj hequalZero).1
        rw [hone, B256.eqCheck, if_pos rfl] at hequalFlag
        exact absurd hequalFlag (by decide)
      · have hequalFlag : ((1 : B256) =? pausedAnswer out) = equalWord := by
          obtain ⟨tail, htail⟩ := hequalPrefix
          rw [htail] at hequalStack
          exact (List.cons.inj hequalStack).1
        have hequalOne : equalWord = 1 := by
          rw [hone, B256.eqCheck, if_pos rfl] at hequalFlag
          exact hequalFlag.symm
        have popEqual := Devm.PopBurn.of_popBurnBy hequalPop
        exact ⟨successPre,
          MemWordAt.of_memory_eq popEqual.memory.symm targetEqual,
          MemWordAt.of_memory_eq popEqual.memory.symm durationEqual,
          hsuccess⟩
    · have hanswerFlag : (pausedAnswer out =? 0) = zeroWord := by
        obtain ⟨tail, htail⟩ := hzeroPrefix
        rw [htail] at hzeroWordStack
        exact (List.cons.inj hzeroWordStack).1
      rw [hone, B256.eqCheck, if_neg (by decide)] at hanswerFlag
      exact absurd hanswerFlag.symm hzeroWord
  · have hflagWord :
        (Nat.toB256 out.length <? (32 : B256)) = shortWord := by
      obtain ⟨tail, htail⟩ := hflag
      rw [htail] at hshortStack
      exact (List.cons.inj hshortStack).1
    rw [B256.ltCheck, if_neg hnotShort] at hflagWord
    exact absurd hflagWord.symm hshortWord

/-- The observation's five outcomes with the canonical `1` arm completed.
The final count and interval are the pause-entry values, so the named
noninterference relation is visible in the evidence that justifies them. -/
def PauseObservationCommittedOutcomes
    (fs : List Func) (sevm : Sevm) (entry statPost : Devm)
    (target : Adr) (duration : B256) (ex : Execution) : Prop :=
  ∃ child : Devm,
    statPost.returnData = child.output ∧
    ((child.error.isSome = true ∧
        ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
          (∃ post, ex = .error (.revert, post) ∧
            post.output =
              child.output.take child.output.length.toB256.toNat))) ∨
      (child.error.isSome = false ∧
        Nat.toB256 child.output.length < (32 : B256) ∧
        (∃ post, ex = .error (.revert, post) ∧ post.output = [])) ∨
      (child.error.isSome = false ∧
        ¬ Nat.toB256 child.output.length < (32 : B256) ∧
        32 ≤ child.output.length ∧
        pausedAnswer child.output = 0 ∧
        ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
          (∃ post, ex = .error (.revert, post) ∧
            post.output = customErrorData "PauseFailed"))) ∨
      (child.error.isSome = false ∧
        ¬ Nat.toB256 child.output.length < (32 : B256) ∧
        32 ≤ child.output.length ∧
        pausedAnswer child.output ≠ 0 ∧
        pausedAnswer child.output ≠ 1 ∧
        (∃ post, ex = .error (.revert, post) ∧ post.output = [])) ∨
      (child.error.isSome = false ∧
        ¬ Nat.toB256 child.output.length < (32 : B256) ∧
        32 ≤ child.output.length ∧
        pausedAnswer child.output = 1 ∧
        ∃ successPre : Devm,
          Func.RunCompiledTo fs sevm successPre pauseSuccess ex ∧
          PauseSuccessNoninterference sevm entry successPre ∧
          PauseSuccessOutcome fs sevm successPre target.toB256 duration
            (entry.getStorVal sevm.currentTarget
              (countSlot sevm.caller.toB256))
            (entry.getStorVal sevm.currentTarget heartbeatIntervalSlot) ex))

/-- Complete the observation's accepting arm while leaving its four failure
arms and all their out-of-gas alternatives unchanged. -/
theorem pauseObservation_committed_outcomes
    {fs : List Func} {sevm : Sevm} {entry statPre statPost : Devm}
    {target : Adr} {duration : B256} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (boundary : PauseStatBoundary sevm target statPre statPost)
    (targetWindow : MemWordAt statPre
      (targetWord * 32).toNat target.toB256)
    (durationWindow : MemWordAt statPre
      (durationWord * 32).toNat duration)
    (noninterference : ∀ successPre,
      Func.RunCompiledTo fs sevm successPre pauseSuccess ex →
        PauseSuccessNoninterference sevm entry successPre)
    (run : Func.RunCompiledTo fs sevm statPost
      (Ninst.iszero :::
        ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex) :
    PauseObservationCommittedOutcomes fs sevm entry statPost
      target duration ex := by
  obtain ⟨child, armPre, memory, hreturn, harmReturn, harmMemory,
    targetArm, durationArm, harms⟩ :=
    pauseObservation_arms_words boundary targetWindow durationWindow run
  refine ⟨child, hreturn, ?_⟩
  rcases harms with ⟨herror, hbubble⟩ | ⟨hsuccess, hdecode⟩
  · obtain ⟨bubblePre, hburn, hbody⟩ :=
      runCompiledTo_call_inv h_bubble hbubble
    have hbubbleReturn : bubblePre.returnData = child.output :=
      hburn.returnData.symm.trans harmReturn
    rcases Func.runCompiledTo_revertReturnData_inv hbody with
      hoog | ⟨post, hpost, houtput⟩
    · exact Or.inl ⟨herror, Or.inl hoog⟩
    · exact Or.inl ⟨herror, Or.inr ⟨post, hpost,
        by rw [houtput, hbubbleReturn]⟩⟩
  · obtain ⟨decodeArm, hdecodeArms⟩ :=
      pauseDecode_arms harmMemory harmReturn hdecode
    rcases hdecodeArms with
      ⟨hshort, hempty⟩ |
        ⟨hnotShort, hlong, hzero, hfailed⟩ |
        ⟨hnotShort, hlong, hnonzero, hnonone, hempty⟩ |
        ⟨hnotShort, hlong, hone, hsuccessRun⟩
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_empty hempty
      exact Or.inr (Or.inl ⟨hsuccess, hshort, runCompiledTo_revert_inv hbody⟩)
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_failed hfailed
      rw [show pauseFailedError =
        Func.revertSelector (customErrorData "PauseFailed")
          (by simp [customErrorData, B256.length_toBytes]) from rfl] at hbody
      exact Or.inr (Or.inr (Or.inl
        ⟨hsuccess, hnotShort, hlong, hzero,
          runCompiledTo_revertSelector_inv hbody⟩))
    · obtain ⟨_, -, hbody⟩ := runCompiledTo_call_inv h_empty hempty
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hsuccess, hnotShort, hlong, hnonzero, hnonone,
          runCompiledTo_revert_inv hbody⟩)))
    · obtain ⟨successPre, targetSuccess, durationSuccess, hsuccessWalk⟩ :=
        pauseDecode_success_words harmMemory harmReturn hnotShort hone
          targetArm durationArm hdecode
      have hni := noninterference successPre hsuccessWalk
      have successInputs : PauseSuccessInputs sevm successPre
          target.toB256 duration
          (entry.getStorVal sevm.currentTarget
            (countSlot sevm.caller.toB256))
          (entry.getStorVal sevm.currentTarget heartbeatIntervalSlot) :=
        ⟨targetSuccess, durationSuccess, hni.1, hni.2⟩
      have houtcome :=
        pauseSuccess_outcome h_panic successInputs hsuccessWalk
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hsuccess, hnotShort, hlong, hone, successPre,
          hsuccessWalk, hni, houtcome⟩)))

/-- The full seven-outcome `pauseAfterSet` classification, with outcome 7
ending in the committed `pauseSuccess` result.  As in the predecessor, the two
call-boundary relations remain implications at the exact states reached; the
noninterference premise is consumed only inside the canonical-`1` arm. -/
def PauseAfterSetCommittedOutcomes
    (fs : List Func) (sevm : Sevm) (entry : Devm)
    (target : Adr) (duration : B256) (ex : Execution) : Prop :=
  ((entry.getCode target).size.toB256 = 0 ∧
      ∃ post, ex = .error (.revert, post) ∧ post.output = []) ∨
    ((entry.getCode target).size.toB256 ≠ 0 ∧
      ∃ guardPost callPre callPost : Devm,
        Line.Run sevm guardPost pauseCallStaging callPre ∧
        Ninst.RunCompiled sevm callPre (.exec .call) callPost ∧
        (PauseCallBoundary sevm target duration callPre callPost →
          ((∃ callChild : Devm,
              callChild.error.isSome = true ∧
              callPost.returnData = callChild.output ∧
              ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
                (∃ post, ex = .error (.revert, post) ∧
                  post.output = callChild.output.take
                    callChild.output.length.toB256.toNat))) ∨
            (∃ armPre statPre statPost : Devm,
              Line.Run sevm armPre pauseStatStaging statPre ∧
              Ninst.RunCompiled sevm statPre (.exec .staticcall) statPost ∧
              (PauseStatBoundary sevm target statPre statPost →
                PauseObservationCommittedOutcomes fs sevm entry statPost
                  target duration ex)))))

/-- **D8: `pauseAfterSet`'s seven outcomes with the accepting arm completed.**

The two frame-local words are transported from `entry` through staging, both
arbitrary callees' resumptions, and the decode.  The only facts related back to
entry storage are the two fields of `PauseSuccessNoninterference`. -/
theorem pauseAfterSet_committed_outcomes
    {fs : List Func} {sevm : Sevm} {entry : Devm}
    {target : Adr} {duration : B256} {ex : Execution}
    (h_empty : fs[emptyRevertSlot]? = some Func.revert)
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revertReturnData)
    (h_failed : fs[pauseFailedErrorSlot]? = some pauseFailedError)
    (h_panic : fs[arithmeticPanicSlot]? =
      some (Func.revertData heartbeatArithmeticPanicData))
    (hTarget : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (hDuration : MemWordAt entry (durationWord * 32).toNat duration)
    (noninterference : ∀ successPre,
      Func.RunCompiledTo fs sevm successPre pauseSuccess ex →
        PauseSuccessNoninterference sevm entry successPre)
    (run : Func.RunCompiledTo fs sevm entry pauseAfterSet ex) :
    PauseAfterSetCommittedOutcomes fs sevm entry target duration ex := by
  rcases pauseAfterSet_codeGuard_arms_words h_empty hTarget hDuration run with
    hnocode | ⟨hcode, guardPost, targetGuard, durationGuard, hlive⟩
  · exact Or.inl hnocode
  · obtain ⟨callPre, hcallStaging, hlive⟩ :=
      runCompiledTo_prepend_inv hlive
    obtain ⟨callPost, hcall, hafterCall⟩ := runCompiledTo_next_inv hlive
    have targetCallPre := targetGuard.acrossPauseCallStagingBoundary
      (by decide) hcallStaging
    have durationCallPre := durationGuard.acrossPauseCallStagingBoundary
      (by decide) hcallStaging
    refine Or.inr ⟨hcode, guardPost, callPre, callPost,
      hcallStaging, hcall, fun callBoundary => ?_⟩
    have targetCallPost :=
      pauseCall_targetWord_survives callBoundary targetCallPre
    have durationCallPost :=
      pauseCall_targetWord_survives callBoundary durationCallPre
    rw [pauseAfterCallBranch] at hafterCall
    obtain ⟨callChild, armPre, hcallReturn, harmReturn, targetArm, durationArm,
      hcallArms⟩ := pauseAfterCall_arms_words callBoundary
        targetCallPost durationCallPost hafterCall
    rcases hcallArms with ⟨hcallError, hbubble⟩ | ⟨hcallSuccess, hstat⟩
    · refine Or.inl ⟨callChild, hcallError, hcallReturn, ?_⟩
      obtain ⟨bubblePre, hburn, hbody⟩ :=
        runCompiledTo_call_inv h_bubble hbubble
      have hbubbleReturn : bubblePre.returnData = callChild.output :=
        hburn.returnData.symm.trans harmReturn
      rcases Func.runCompiledTo_revertReturnData_inv hbody with
        hoog | ⟨post, hpost, houtput⟩
      · exact Or.inl hoog
      · exact Or.inr ⟨post, hpost, by rw [houtput, hbubbleReturn]⟩
    · rw [pauseStatArm] at hstat
      obtain ⟨statPre, hstatStaging, hstat⟩ :=
        runCompiledTo_prepend_inv hstat
      obtain ⟨statPost, hstatCall, hobservation⟩ :=
        runCompiledTo_next_inv hstat
      have targetStatPre := targetArm.acrossPauseStatStagingBoundary
        (by decide) hstatStaging
      have durationStatPre := durationArm.acrossPauseStatStagingBoundary
        (by decide) hstatStaging
      exact Or.inr ⟨armPre, statPre, statPost, hstatStaging, hstatCall,
        fun statBoundary =>
          pauseObservation_committed_outcomes h_empty h_bubble h_failed
            h_panic statBoundary targetStatPre durationStatPre
            noninterference hobservation⟩

/-! ## The explicit noninterference bridge -/

/-- Consume both, and only, assumed noninterference equalities to restate the
post-callback inputs in terms of `pauseAfterSet` entry storage.  The transported
memory words pass through untouched. -/
theorem PauseSuccessInputs.of_noninterference
    {sevm : Sevm} {entry postCallback : Devm}
    {target duration postCount postInterval : B256}
    (inputs : PauseSuccessInputs sevm postCallback
      target duration postCount postInterval)
    (assumed : PauseSuccessNoninterference sevm entry postCallback) :
    PauseSuccessInputs sevm postCallback target duration
      (entry.getStorVal sevm.currentTarget
        (countSlot sevm.caller.toB256))
      (entry.getStorVal sevm.currentTarget heartbeatIntervalSlot) := by
  rcases inputs with ⟨htarget, hduration, hcount, hinterval⟩
  rcases assumed with ⟨hcountEq, hintervalEq⟩
  refine ⟨htarget, hduration, ?_, ?_⟩
  · exact hcountEq
  · exact hintervalEq

/-! Compatibility names retained for the established public Lido boundary
theorems after hoisting `MemWordAt`. -/
abbrev MemWordAt.acrossPauseCallStagingBoundary :=
  @Blanc.MemWordAt.acrossPauseCallStagingBoundary
abbrev MemWordAt.acrossPauseStatStagingBoundary :=
  @Blanc.MemWordAt.acrossPauseStatStagingBoundary

end Blanc.LidoCircuitBreaker
