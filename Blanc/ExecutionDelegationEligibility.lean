import Blanc.ExecutionTrace
import Blanc.LadderBase

/-!
# Eligibility at actual sequential delegation occurrences

The local write gate is not fork-gated: the raw Jaune step is callable on its
own. Fork enablement belongs to the actual call wrapper. Occurrences retain
every tuple and its intermediate message/refund, including zero-target clears
and tuples preceding a later VM rollback.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Local gates for a possible code write at `a`, before knowing recovery.
`auth.address` is the delegation target, not the recovered authority. -/
def AuthMayWrite (a : Adr) (auth : Auth) (msg : Msg) : Prop :=
  (auth.chainId = msg.benv.stat.chainId.toB256 ∨ auth.chainId = 0) ∧
  auth.nonce ≠ UInt64.max ∧
  ((msg.benv.state.get a).code.isEmpty = true ∨
    isValidDelegation (msg.benv.state.get a).code) ∧
  (msg.benv.state.get a).nonce = auth.nonce

/-- Exact eligible-query exclusion suffices for the raw step, including code
clearing. Invalid-signature and other error branches follow Jaune's result. -/
theorem setDelegationStep_getCode_of_mayWrite
    {a : Adr} {auth : Auth} {msg msg' : Msg} {rc rc' : B256}
    (exclude : AuthMayWrite a auth msg → recoverAuthority auth ≠ .ok a)
    (run : setDelegationStep auth msg rc = .ok (msg', rc')) :
    msg'.benv.state.getCode a = msg.benv.state.getCode a := by
  unfold setDelegationStep at run
  dsimp only at run
  split at run
  · cases run; rfl
  · rename_i chain
    split at run
    · cases run; rfl
    · rename_i nonce
      split at run
      · cases run; rfl
      · cases run
      · rename_i authority recovered
        split at run
        · cases run; rfl
        · rename_i codeEligible
          split at run
          · cases run; rfl
          · rename_i nonceMatches
            simp only [Except.ok.injEq, Prod.mk.injEq] at run
            rcases run with ⟨rfl, _⟩
            have different : authority ≠ a := by
              intro equal
              subst authority
              apply exclude ?_ recovered
              refine ⟨?_, nonce, not_not.mp codeEligible, ?_⟩
              · simpa only [Bool.and_eq_true, bne_iff_ne, not_and_or, not_not] using chain
              · simpa only [bne_iff_ne, not_not] using nonceMatches
            show ((((msg.benv.state.setCode authority
              (if auth.address = 0 then ByteArray.empty
                else (eoaDelegationMarker ++ auth.address.toBytes).toByteArray)).incrNonce
                authority).get a).code) = (msg.benv.state.get a).code
            rw [State.incrNonce_get_code, State.setCode_get_code_ne different]

/-- Sequential composition of the canonical loop, including failures. -/
theorem setDelegationLoop_append (xs ys : List Auth) (msg : Msg) (rc : B256) :
    setDelegationLoop (xs ++ ys) msg rc = (do
      let pair ← setDelegationLoop xs msg rc
      setDelegationLoop ys pair.1 pair.2) := by
  induction xs generalizing msg rc with
  | nil => rfl
  | cons auth xs ih =>
      cases step : setDelegationStep auth msg rc with
      | error error => simp only [List.cons_append, setDelegationLoop, step, Except.bind_error]
      | ok pair =>
          rcases pair with ⟨middle, refund⟩
          simpa only [List.cons_append, setDelegationLoop, step, Except.bind_ok] using
            ih middle refund

/-- One actual tuple, retaining the entire successful prefix/step/suffix.
Repeated values retain their distinct prefix lengths. -/
structure DelegationOccurrence (auths : List Auth) (start : Msg)
    (startRefund : B256) (finish : Msg) (finishRefund : B256) where
  before : List Auth
  auth : Auth
  after : List Auth
  split : auths = before ++ auth :: after
  middle : Msg
  middleRefund : B256
  next : Msg
  nextRefund : B256
  prefixRun : setDelegationLoop before start startRefund = .ok (middle, middleRefund)
  stepRun : setDelegationStep auth middle middleRefund = .ok (next, nextRefund)
  suffixRun : setDelegationLoop after next nextRefund = .ok (finish, finishRefund)

/-- The actual list index of this occurrence. -/
def DelegationOccurrence.index {auths start rc finish rc'}
    (occ : DelegationOccurrence auths start rc finish rc') : Nat := occ.before.length

/-- A preceding actual step embeds every suffix occurrence without changing
its intermediate message, refund or tuple. -/
def DelegationOccurrence.prepend {auth : Auth} {auths : List Auth}
    {start middle finish : Msg} {rc middleRefund rc' : B256}
    (step : setDelegationStep auth start rc = .ok (middle, middleRefund))
    (occ : DelegationOccurrence auths middle middleRefund finish rc') :
    DelegationOccurrence (auth :: auths) start rc finish rc' where
  before := auth :: occ.before
  auth := occ.auth
  after := occ.after
  split := congrArg (auth :: ·) occ.split
  middle := occ.middle
  middleRefund := occ.middleRefund
  next := occ.next
  nextRefund := occ.nextRefund
  prefixRun := by simpa only [setDelegationLoop, step, Except.bind_ok] using occ.prefixRun
  stepRun := occ.stepRun
  suffixRun := occ.suffixRun

/-- Every occurrence is a decomposition of the same actual successful loop. -/
theorem DelegationOccurrence.result {auths start rc finish rc'}
    (occ : DelegationOccurrence auths start rc finish rc') :
    setDelegationLoop auths start rc = .ok (finish, rc') := by
  rw [occ.split, setDelegationLoop_append, occ.prefixRun]
  simp only [Except.bind_ok, setDelegationLoop, occ.stepRun]
  exact occ.suffixRun

/-- Every actual list index has a witness with the exact indexed tuple and
the real sequential intermediate message/refund. No supplied scope list. -/
theorem exists_delegationOccurrence_at
    {auths : List Auth} {start finish : Msg} {rc rc' : B256}
    (run : setDelegationLoop auths start rc = .ok (finish, rc'))
    (i : Nat) (bound : i < auths.length) :
    ∃ occ : DelegationOccurrence auths start rc finish rc',
      occ.index = i ∧ auths[i]? = some occ.auth := by
  induction auths generalizing start rc i with
  | nil => simp only [List.length_nil] at bound; omega
  | cons auth auths ih =>
      obtain ⟨⟨middle, middleRefund⟩, step, tail⟩ := Except.bind_eq_ok run
      cases i with
      | zero =>
          exact ⟨{
            before := [], auth := auth, after := auths, split := rfl
            middle := start, middleRefund := rc, next := middle, nextRefund := middleRefund
            prefixRun := rfl, stepRun := step, suffixRun := tail }, rfl, rfl⟩
      | succ i =>
          obtain ⟨occ, index, tuple⟩ := ih tail i (by
            simp only [List.length_cons] at bound
            omega)
          refine ⟨occ.prepend step, ?_, ?_⟩
          · simpa only [DelegationOccurrence.index, DelegationOccurrence.prepend,
              List.length_cons] using congrArg Nat.succ index
          · simpa only [DelegationOccurrence.prepend, List.getElem?_cons_succ] using tuple

/-- The successful loop keeps code using exclusion only at its actual
eligible occurrences; no endpoint code premise replaces the fold. -/
theorem setDelegationLoop_getCode_of_occurrences
    {a : Adr} {auths : List Auth} {start finish : Msg} {rc rc' : B256}
    (run : setDelegationLoop auths start rc = .ok (finish, rc'))
    (exclude : ∀ occ : DelegationOccurrence auths start rc finish rc',
      AuthMayWrite a occ.auth occ.middle → recoverAuthority occ.auth ≠ .ok a) :
    finish.benv.state.getCode a = start.benv.state.getCode a := by
  induction auths generalizing start rc with
  | nil => cases run; rfl
  | cons auth auths ih =>
      obtain ⟨⟨middle, middleRefund⟩, step, tail⟩ := Except.bind_eq_ok run
      let head : DelegationOccurrence (auth :: auths) start rc finish rc' := {
        before := [], auth := auth, after := auths, split := rfl
        middle := start, middleRefund := rc, next := middle, nextRefund := middleRefund
        prefixRun := rfl, stepRun := step, suffixRun := tail }
      have first := setDelegationStep_getCode_of_mayWrite (exclude head) step
      exact (ih tail (fun occ => exclude (occ.prepend step))).trans first

/-- Sound compatibility from the older, stronger all-tuples exclusion. -/
theorem DelegationOccurrence.excluded_of_all {a : Adr} {auths start rc finish rc'}
    (occ : DelegationOccurrence auths start rc finish rc')
    (all : ∀ auth ∈ auths, recoverAuthority auth ≠ .ok a) :
    recoverAuthority occ.auth ≠ .ok a := by
  apply all occ.auth
  exact (congrArg (fun xs : List Auth => occ.auth ∈ xs) occ.split).mpr
    (List.mem_append.mpr (.inr (List.mem_cons_self ..)))

/-- Any supplied occurrence has an in-range actual index. -/
theorem DelegationOccurrence.index_lt {auths start rc finish rc'}
    (occ : DelegationOccurrence auths start rc finish rc') :
    occ.index < auths.length := by
  have lengths := congrArg List.length occ.split
  simp only [List.length_append, List.length_cons] at lengths
  unfold index
  omega

/-- The tuple at that index is the occurrence's retained tuple. -/
theorem DelegationOccurrence.auth_at_index {auths start rc finish rc'}
    (occ : DelegationOccurrence auths start rc finish rc') :
    auths[occ.index]? = some occ.auth := by
  have split := congrArg (fun xs : List Auth => xs[occ.before.length]?) occ.split
  exact split.trans (by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl)

/-- The actual call-wrapper prefix. The processed arm retains the real
loop endpoint, target-code refresh and refund-word conversion. -/
inductive MessageCallDelegationTrace (msg : Msg) : Msg → Nat → Type
  | skipped
      (guard : (!msg.benv.stat.rules.delegationEnabled || msg.tenv.stat.auths.isEmpty) = true) :
      MessageCallDelegationTrace msg msg 0
  | processed
      {delegated : Msg} {refund : Nat}
      (enabled : msg.benv.stat.rules.delegationEnabled = true)
      (nonempty : msg.tenv.stat.auths.isEmpty = false)
      (loopMsg : Msg) (loopRefund : B256) (address : Adr)
      (loopRun : setDelegationLoop msg.tenv.stat.auths msg 0 = .ok (loopMsg, loopRefund))
      (codeAddress : loopMsg.codeAddress = some address)
      (refreshed : delegated = {loopMsg with code := loopMsg.benv.state.getCode address})
      (refundEq : refund = loopRefund.toNat) :
      MessageCallDelegationTrace msg delegated refund

/-- The carrier describes the actual canonical wrapper, not a synthetic
authorization list chosen after execution. -/
theorem MessageCallDelegationTrace.result {msg delegated : Msg} {refund : Nat}
    (trace : MessageCallDelegationTrace msg delegated refund) :
    messageCallDelegation msg = .ok (delegated, refund) := by
  cases trace with
  | skipped guard =>
      simp only [messageCallDelegation, processMessageCall.legacyAuthorization, guard, ↓reduceIte]
  | processed enabled nonempty loopMsg loopRefund address loopRun codeAddress refreshed refundEq =>
      rw [refreshed, refundEq]
      simp only [messageCallDelegation, processMessageCall.legacyAuthorization, enabled,
        nonempty, Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
        setDelegation, loopRun, Except.bind_ok, codeAddress]

/-- Every successful wrapper has the corresponding skipped/processed trace.
No tuple is omitted because the later VM body will revert. -/
theorem exists_messageCallDelegationTrace {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok (delegated, refund)) :
    Nonempty (MessageCallDelegationTrace msg delegated refund) := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · rename_i guard
    simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨.skipped guard⟩
  · rename_i active
    have enabled : msg.benv.stat.rules.delegationEnabled = true := by
      cases value : msg.benv.stat.rules.delegationEnabled with
      | false => simp only [value, Bool.not_false, Bool.true_or] at active; exact (active trivial).elim
      | true => rfl
    have nonempty : msg.tenv.stat.auths.isEmpty = false := by
      cases value : msg.tenv.stat.auths.isEmpty with
      | false => rfl
      | true => simp only [value, Bool.or_true] at active; exact (active trivial).elim
    obtain ⟨⟨finished, word⟩, delegation, rest⟩ := Except.bind_eq_ok run
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, rfl⟩
    unfold setDelegation at delegation
    obtain ⟨⟨loopMsg, loopRefund⟩, loopRun, refresh⟩ := Except.bind_eq_ok delegation
    cases codeAddress : loopMsg.codeAddress with
    | none => simp only [codeAddress, Except.bind_error, reduceCtorEq] at refresh
    | some address =>
        simp only [codeAddress, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at refresh
        rcases refresh with ⟨rfl, rfl⟩
        refine ⟨.processed enabled nonempty loopMsg loopRefund address loopRun codeAddress ?_ rfl⟩
        simp only [codeAddress]

/-- Eligible-query exclusion at every actual sequential occurrence. The
wrapper carries fork enablement; skipped/empty wrappers have no occurrences. -/
def MessageCallDelegationTrace.NoEligibleAuthorityAt
    {msg delegated : Msg} {refund : Nat} (a : Adr) :
    MessageCallDelegationTrace msg delegated refund → Prop
  | .skipped _ => True
  | .processed _ _ loopMsg loopRefund _ _ _ _ _ =>
      ∀ occ : DelegationOccurrence msg.tenv.stat.auths msg 0 loopMsg loopRefund,
        AuthMayWrite a occ.auth occ.middle → recoverAuthority occ.auth ≠ .ok a

/-- Actual wrapper producer for eligibility-sensitive code preservation.
The trace's `result` and extraction theorem connect this to the recorded
`messageCallDelegation` equation without strengthening the crypto premise. -/
theorem messageCallDelegation_getCode_of_eligible
    {a : Adr} {msg delegated : Msg} {refund : Nat}
    (trace : MessageCallDelegationTrace msg delegated refund)
    (exclude : trace.NoEligibleAuthorityAt a) :
    delegated.benv.state.getCode a = msg.benv.state.getCode a := by
  cases trace with
  | skipped => rfl
  | processed _ _ _ _ _ loopRun _ refreshed _ =>
      have preserved := setDelegationLoop_getCode_of_occurrences loopRun exclude
      rw [refreshed]
      exact preserved

/-- Existing all-tuples exclusion implies this weaker actual eligibility
condition. No converse or universal cryptographic strengthening is asserted. -/
theorem MessageCallDelegationTrace.excluded_of_all
    {a : Adr} {msg delegated : Msg} {refund : Nat}
    (trace : MessageCallDelegationTrace msg delegated refund)
    (all : ∀ auth ∈ msg.tenv.stat.auths, recoverAuthority auth ≠ .ok a) :
    trace.NoEligibleAuthorityAt a := by
  cases trace with
  | skipped => trivial
  | processed => exact fun occ _ => occ.excluded_of_all all

end Blanc.ExecutionTrace
