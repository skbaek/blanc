import Blanc.LidoCircuitBreakerAccess

/-!
The conditional pause-expiry suffix.

`pause` reaches `pauseSuccess` only through `pauseAfterSet`, which performs the
contract's two external-call sites — a `CALL` to `pauseFor` and a `STATICCALL`
to `isPaused`.  Nothing here constructs either of them.  Every result in this
module takes the *post-callback* suffix walk as a hypothesis, entered at an
arbitrary `Devm`, and reads the exact expiry `SSTORE` back out of it.  That is
the whole boundary: the callback is never built, no terminal success is proved,
and nothing is claimed about the final state or about interference.

What is proved is the value at the one write `pauseSuccess` can perform.  The
source branches on `iszero` of the post-callback count word read at the caller,
so the suffix stores `0` exactly on the zero arm and the checked
`timestamp + heartbeatInterval` — the same `CheckedHeartbeatExtension`
discipline the registration side uses — on the other.  The nonzero arm can also
fail closed: `checkedHeartbeatExpiry` diverts to `arithmeticPanicSlot` when the
sum wraps, and no write happens at all.  `pauseSuccess_expiryWrite_dichotomy`
returns exactly those two possibilities, so the reachedness hypothesis of the
conditional form below is not a guess about the walk but the complement of the
one way it can miss the write.

The count word this reads is the one the `SLOAD` actually sees after the
callback returned.  It is deliberately *not* identified with any stable
last-assignment fact: a hostile target can leave the caller unassigned while an
earlier expiry is still live, and that intermediate state is exactly what this
module declines to erase.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## Inversion for the outcome-generalised walk

`Blanc/Reverts.lean`'s `Func.RunCompiledTo` is the walk an actually reached
suffix hands over: every intermediate step succeeded, and only the terminal
instruction's outcome is free.  The three lemmas below are its `cases`, kept as
lemmas for the reason `Blanc/CommonProofs.lean`'s `of_run_call` gives — a
`cases` on the relation inside a long walk's context generalizes that whole
context against the indices.

Each `.next` is handed on as a source-level `Ninst.Run`, because that is what
the `prefix_of_*` stack kit consumes; the designated write keeps its
`Ninst.RunCompiled` so the reported occurrence is the gas-exact one. -/

private lemma of_runCompiledTo_next {fs : List Func} {sevm : Sevm} {devm : Devm}
    {i : Ninst} {f : Func} {out : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.next i f) out) :
    ∃ devm', Ninst.RunCompiled sevm devm i devm' ∧
      Func.RunCompiledTo fs sevm devm' f out := by
  cases h with
  | next step tail => exact ⟨_, step, tail⟩

private lemma of_runCompiledTo_prepend {fs : List Func} {sevm : Sevm}
    {s : Devm} {out : Execution} :
    ∀ p q, Func.RunCompiledTo fs sevm s (p +++ q) out →
      ∃ s', Line.Run sevm s p s' ∧ Func.RunCompiledTo fs sevm s' q out
  | [], _, h => ⟨s, .nil, h⟩
  | (_ :: p), q, h => by
      rcases of_runCompiledTo_next h with ⟨s0, step, tail⟩
      rcases of_runCompiledTo_prepend p q tail with ⟨s1, hp, hq⟩
      exact ⟨s1, .cons (Ninst.Run.of_runCompiled step) hp, hq⟩

/-- `TIMESTAMP` pushes the block time.  `Blanc/Tactics.lean`'s `line_prefix`
has no case for it, so the two lines the checked addition needs are supplied
here. -/
private lemma prefix_of_timestamp {sevm : Sevm} {pre post : Devm} {xs : Stack}
    (stackPrefix : xs <<+ pre.stack)
    (run : Ninst.Run sevm pre Ninst.timestamp post) :
    sevm.benvStat.time :: xs <<+ post.stack := by
  change Ninst.Run sevm pre (.reg .timestamp) post at run
  rcases of_run_reg run with ⟨pc, instructionRun⟩
  simp only [Rinst.run, Rinst.runCore] at instructionRun
  exact prefix_of_push (Devm.pushBurn_of_pushItem instructionRun) stackPrefix

/-! ## The store both arms fall into -/

/-- The straight-line prefix of `pauseExpiryFinish` that turns the carried
expiry into the `SSTORE` operand pair. -/
private def expiryStoreKeyLine : Line :=
  Ninst.dup 0 :: mstoreAt 0 ++ Ninst.caller :: tagTop expiryRegion

private lemma prefix_of_expiryStoreKeyLine {sevm : Sevm} {s s' : Devm}
    {value : B256} {xs : Stack}
    (hp : value :: xs <<+ s.stack)
    (h : Line.Run sevm s expiryStoreKeyLine s') :
    (regionWord expiryRegion ||| sevm.caller.toB256) :: value :: xs
      <<+ s'.stack := by
  unfold expiryStoreKeyLine mstoreAt tagTop at h
  generalize_line_prefix

/-- `pauseExpiryFinish` writes the word it is entered with to the caller's
expiry slot, and that write is the walk's first `SSTORE`.  Nothing about the
tail — the transient unlock, the log, the terminal `STOP` — is used or
claimed. -/
private lemma pauseExpiryFinish_expiryWrite
    {fs : List Func} {sevm : Sevm} {s : Devm} {out : Execution}
    {ca : Adr} {value : B256} {xs : Stack}
    (howner : sevm.currentTarget = ca)
    (hstack : value :: xs <<+ s.stack)
    (hrun : Func.RunCompiledTo fs sevm s pauseExpiryFinish out) :
    ∃ mid post : Devm,
      Ninst.RunCompiled sevm mid Ninst.sstore post ∧
      expirySlot sevm.caller.toB256 :: value :: xs <<+ mid.stack ∧
      Devm.getStor mid ca = Devm.getStor s ca ∧
      Devm.getStor post ca =
        (Devm.getStor s ca).set (expirySlot sevm.caller.toB256) value := by
  have hshape : pauseExpiryFinish =
      expiryStoreKeyLine +++
        (Ninst.sstore :::
          (Ninst.caller :: Ninst.pushB256 heartbeatUpdatedEvent ::
            logWith 1 0 1) +++
            (Ninst.pushB256 0 ::: Ninst.pushB256 lockKey :::
              Ninst.tstore ::: Func.stop)) := rfl
  rw [hshape] at hrun
  rcases of_runCompiledTo_prepend expiryStoreKeyLine _ hrun with
    ⟨mid, hkeyLine, htail⟩
  rcases of_runCompiledTo_next htail with ⟨post, hstore, _⟩
  have hkey : expirySlot sevm.caller.toB256 :: value :: xs <<+ mid.stack :=
    prefix_of_expiryStoreKeyLine hstack hkeyLine
  have hstor : Devm.getStor s = Devm.getStor mid :=
    Line.of_inv Devm.getStor
      (by unfold expiryStoreKeyLine mstoreAt tagTop; line_inv) hkeyLine
  refine ⟨mid, post, hstore, hkey, ?_, ?_⟩
  · exact (congrFun hstor ca).symm
  · have heffect := sstore_getStor_set (Ninst.Run.of_runCompiled hstore) hkey
    rw [howner] at heffect
    rw [heffect, ← congrFun hstor ca]

/-! ## The count read `pauseSuccess` branches on

`pauseSuccess`'s prefix stages the duration word into memory, emits
`PauseTriggered`, and then loads the caller's count word.  Two `MLOAD`s split
the prefix into three straight-line pieces, because `line_prefix` carries no
value for a memory read — and none is needed: both loaded words are consumed
by the event, and only the `SLOAD` result reaches the branch. -/

private def pausePrefixA : Line := [Ninst.pushB256 (durationWord * 32)]

private def pausePrefixB : Line :=
  mstoreAt 0 ++ [Ninst.caller, Ninst.pushB256 (targetWord * 32)]

private def pausePrefixC : Line :=
  Ninst.pushB256 pauseTriggeredEvent :: logWith 2 0 1 ++
    Ninst.caller :: tagTop countRegion

private lemma prefix_of_pausePrefixA {sevm : Sevm} {s s' : Devm}
    (hp : ([] : Stack) <<+ s.stack)
    (h : Line.Run sevm s pausePrefixA s') :
    [durationWord * 32] <<+ s'.stack := by
  unfold pausePrefixA at h
  generalize_line_prefix

private lemma prefix_of_pausePrefixB {sevm : Sevm} {s s' : Devm} {duration : B256}
    (hp : [duration] <<+ s.stack)
    (h : Line.Run sevm s pausePrefixB s') :
    [targetWord * 32, sevm.caller.toB256] <<+ s'.stack := by
  unfold pausePrefixB mstoreAt at h
  generalize_line_prefix

private lemma prefix_of_pausePrefixC {sevm : Sevm} {s s' : Devm} {target : B256}
    (hp : [target, sevm.caller.toB256] <<+ s.stack)
    (h : Line.Run sevm s pausePrefixC s') :
    [regionWord countRegion ||| sevm.caller.toB256] <<+ s'.stack := by
  unfold pausePrefixC tagTop at h
  generalize_line_prefix

/-! ## The checked addition's own two straight-line pieces -/

private lemma prefix_of_sumDup {sevm : Sevm} {s s' : Devm}
    {interval timestamp : B256} {xs : Stack}
    (hp : interval :: timestamp :: xs <<+ s.stack)
    (h : Line.Run sevm s [Ninst.add, Ninst.dup 0] s') :
    (interval + timestamp) :: (interval + timestamp) :: xs <<+ s'.stack := by
  generalize_line_prefix

private lemma prefix_of_overflowFlag {sevm : Sevm} {s s' : Devm}
    {sum timestamp : B256} {xs : Stack}
    (hp : timestamp :: sum :: sum :: xs <<+ s.stack)
    (h : Line.Run sevm s [Ninst.swap 0, Ninst.lt] s') :
    (sum <? timestamp) :: sum :: xs <<+ s'.stack := by
  generalize_line_prefix

/-! ## What a reached suffix write is, and which word it stores -/

/-- An actually reached `pauseSuccess` expiry `SSTORE`, read back out of the
suffix walk: a gas-exact write step whose entry storage still agrees with the
post-callback state `pre`, whose operand pair is the caller's expiry key and
`value`, and whose effect on the CircuitBreaker's own storage is exactly that
one cell.

This is an occurrence claim about the walk it came from.  It says nothing
about the outcome of the walk, nothing about any later frame, and nothing
about whether the cell still holds `value` at the end of the transaction. -/
def PauseExpiryWrite (sevm : Sevm) (pre : Devm) (ca : Adr) (value : B256) :
    Prop :=
  ∃ mid post : Devm,
    Ninst.RunCompiled sevm mid Ninst.sstore post ∧
    [expirySlot sevm.caller.toB256, value] <<+ mid.stack ∧
    Devm.getStor mid ca = Devm.getStor pre ca ∧
    Devm.getStor post ca =
      (Devm.getStor pre ca).set (expirySlot sevm.caller.toB256) value

/-- The word the suffix stores, as the source's own `iszero` branch fixes it:
zero exactly on the zero post-callback count, and the checked
`timestamp + interval` — same `CheckedHeartbeatExtension` discipline as the
registration and heartbeat sides — otherwise.

`count` is the word the post-callback `SLOAD` actually returned.  It is *not*
a claim that the caller holds no assignment: during a pause the count may read
zero while an earlier expiry is still live, and this predicate deliberately
says nothing about that. -/
def PauseExpiryValue (timestamp interval count value : B256) : Prop :=
  (count = 0 → value = 0) ∧
  (count ≠ 0 → CheckedHeartbeatExtension timestamp interval value)

/-- The stored word is zero exactly on the zero-count arm, except in the one
degenerate world where the block time and the then-current interval are both
zero and the checked sum is therefore zero too. -/
theorem PauseExpiryValue.eq_zero_iff {timestamp interval count value : B256}
    (h : PauseExpiryValue timestamp interval count value) :
    value = 0 ↔ (count = 0 ∨ (timestamp = 0 ∧ interval = 0)) := by
  rcases h with ⟨zeroArm, checkedArm⟩
  constructor
  · intro hzero
    rcases eq_or_ne count 0 with hc | hc
    · exact Or.inl hc
    · refine Or.inr ?_
      rcases checkedArm hc with ⟨bound, hvalue⟩
      rw [hzero] at hvalue
      have hsum : timestamp.toNat + interval.toNat = 0 := by
        by_contra hne
        have : (0 : B256).toNat = timestamp.toNat + interval.toNat := by
          rw [hvalue, B256.toNat_toB256_of_lt bound]
        rw [B256.toNat_zero] at this
        omega
      refine ⟨B256.toNat_inj _ _ ?_, B256.toNat_inj _ _ ?_⟩
      · rw [B256.toNat_zero]; omega
      · rw [B256.toNat_zero]; omega
  · rintro (hc | ⟨rfl, rfl⟩)
    · exact zeroArm hc
    · rcases eq_or_ne count 0 with hc | hc
      · exact zeroArm hc
      · rcases checkedArm hc with ⟨_, hvalue⟩
        rw [hvalue, B256.toNat_zero]
        rfl

/-- The goal's own sentence, once the degenerate world is excluded: the
reached write stores zero if and only if the post-callback count word read is
zero. -/
theorem PauseExpiryValue.eq_zero_iff_count_eq_zero
    {timestamp interval count value : B256}
    (h : PauseExpiryValue timestamp interval count value)
    (nondegenerate : ¬ (timestamp = 0 ∧ interval = 0)) :
    value = 0 ↔ count = 0 := by
  rw [h.eq_zero_iff]
  exact or_iff_left nondegenerate

/-! ## The checked addition, read backwards

`Blanc/LidoCircuitBreakerAccess.lean` states `CheckedHeartbeatExtension`
forwards, for a walk being built.  The suffix walk arrives with the source's
own flag already decided, so the two directions of Solidity's overflow test
are recovered here from that flag alone. -/

private lemma checkedExtension_of_not_lt {timestamp interval : B256}
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
  rw [B256.toNat_add_eq_of_nof _ _ hnof, B256.toNat_toB256_of_lt hbound]
  omega

private lemma not_nof_of_lt {timestamp interval : B256}
    (wrap : interval + timestamp < timestamp) :
    ¬ B256.Nof timestamp interval := by
  intro hnof
  have hnof' : B256.Nof interval timestamp := by
    unfold B256.Nof at hnof ⊢; omega
  rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_add_eq_of_nof _ _ hnof'] at wrap
  omega

/-! ## The two arms

Both arms end in `pauseExpiryFinish`, so both are read out through the same
store lemma; they differ only in the word they carry into it. -/

private lemma pauseSuccess_zeroCountArm
    {fs : List Func} {sevm : Sevm} {pre s : Devm} {out : Execution}
    (hstor : Devm.getStor pre = Devm.getStor s)
    (hrun : Func.RunCompiledTo fs sevm s
      (Ninst.pushB256 0 ::: pauseExpiryFinish) out) :
    PauseExpiryWrite sevm pre sevm.currentTarget 0 := by
  rcases of_runCompiledTo_next hrun with ⟨s', hpush, hfinish⟩
  have hp : [(0 : B256)] <<+ s'.stack := by
    simpa using prefix_of_push
      (of_run_pushB256 (Ninst.Run.of_runCompiled hpush)) nil_pref
  have hstor' : Devm.getStor pre = Devm.getStor s' :=
    hstor.trans (Ninst.Hinv.inv (f := Devm.getStor)
      (Ninst.Run.of_runCompiled hpush))
  rcases pauseExpiryFinish_expiryWrite rfl hp hfinish with
    ⟨mid, post, hstore, hkey, hmid, heffect⟩
  refine ⟨mid, post, hstore, hkey, ?_, ?_⟩
  · rw [hmid, ← congrFun hstor' sevm.currentTarget]
  · rw [heffect, ← congrFun hstor' sevm.currentTarget]

set_option maxRecDepth 4096 in
private lemma pauseSuccess_checkedArm
    {fs : List Func} {sevm : Sevm} {pre s : Devm} {out : Execution}
    {interval : B256}
    (hinterval : Devm.getStorVal pre sevm.currentTarget heartbeatIntervalSlot =
      interval)
    (hstor : Devm.getStor pre = Devm.getStor s)
    (hrun : Func.RunCompiledTo fs sevm s
      (checkedHeartbeatExpiry pauseExpiryFinish) out) :
    (∃ value : B256, PauseExpiryWrite sevm pre sevm.currentTarget value ∧
        CheckedHeartbeatExtension sevm.benvStat.time interval value) ∨
      (¬ B256.Nof sevm.benvStat.time interval ∧
        ∃ panicPre : Devm,
          Func.RunCompiledTo fs sevm panicPre
            (Func.call arithmeticPanicSlot) out) := by
  have hshape : checkedHeartbeatExpiry pauseExpiryFinish =
      Ninst.timestamp ::: Ninst.pushB256 heartbeatIntervalSlot :::
        Ninst.sload ::: ([Ninst.add, Ninst.dup 0] +++
          (Ninst.timestamp ::: ([Ninst.swap 0, Ninst.lt] +++
            Func.branch pauseExpiryFinish
              (Func.call arithmeticPanicSlot)))) := rfl
  rw [hshape] at hrun
  rcases of_runCompiledTo_next hrun with ⟨t1, htime1, hrun1⟩
  rcases of_runCompiledTo_next hrun1 with ⟨t2, hpushSlot, hrun2⟩
  rcases of_runCompiledTo_next hrun2 with ⟨t3, hsload, hrun3⟩
  rcases of_runCompiledTo_prepend [Ninst.add, Ninst.dup 0] _ hrun3 with
    ⟨t4, hsumLine, hrun4⟩
  rcases of_runCompiledTo_next hrun4 with ⟨t5, htime2, hrun5⟩
  rcases of_runCompiledTo_prepend [Ninst.swap 0, Ninst.lt] _ hrun5 with
    ⟨t6, hflagLine, hbranch⟩
  have hp1 : [sevm.benvStat.time] <<+ t1.stack :=
    prefix_of_timestamp nil_pref (Ninst.Run.of_runCompiled htime1)
  have hp2 : [heartbeatIntervalSlot, sevm.benvStat.time] <<+ t2.stack := by
    simpa using prefix_of_push
      (of_run_pushB256 (Ninst.Run.of_runCompiled hpushSlot)) hp1
  rcases prefix_of_sload (Ninst.Run.of_runCompiled hsload) hp2 with
    ⟨read, hp3, hreadVal⟩
  have hstor2 : Devm.getStor pre = Devm.getStor t2 :=
    hstor.trans ((Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled htime1)).trans
      (Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled hpushSlot)))
  have hreadInterval : read = interval := by
    rw [hreadVal, ← hinterval]
    exact congrArg (fun stor => (stor sevm.currentTarget).get
      heartbeatIntervalSlot) hstor2.symm
  rw [hreadInterval] at hp3
  have hp4 : (interval + sevm.benvStat.time) ::
      (interval + sevm.benvStat.time) :: ([] : Stack) <<+ t4.stack :=
    prefix_of_sumDup hp3 hsumLine
  have hp5 : sevm.benvStat.time :: (interval + sevm.benvStat.time) ::
      (interval + sevm.benvStat.time) :: ([] : Stack) <<+ t5.stack :=
    prefix_of_timestamp hp4 (Ninst.Run.of_runCompiled htime2)
  have hp6 : ((interval + sevm.benvStat.time) <? sevm.benvStat.time) ::
      (interval + sevm.benvStat.time) :: ([] : Stack) <<+ t6.stack :=
    prefix_of_overflowFlag hp5 hflagLine
  have hstor6 : Devm.getStor pre = Devm.getStor t6 :=
    hstor2.trans ((Ninst.Hinv.inv (f := Devm.getStor)
        (Ninst.Run.of_runCompiled hsload)).trans
      ((Line.of_inv Devm.getStor (by line_inv) hsumLine).trans
        ((Ninst.Hinv.inv (f := Devm.getStor)
            (Ninst.Run.of_runCompiled htime2)).trans
          (Line.of_inv Devm.getStor (by line_inv) hflagLine))))
  cases hbranch with
  | zero hroom hpop htail =>
      have hflag : ((interval + sevm.benvStat.time) <? sevm.benvStat.time) = 0 :=
        (List.of_cons_pref_of_cons_pref hp6 (pref_of_split hpop.stack)).left
      have hnoWrap : ¬ (interval + sevm.benvStat.time < sevm.benvStat.time) := by
        intro hlt
        rw [B256.ltCheck, if_pos hlt] at hflag
        exact absurd hflag (by decide)
      have hp7 : [interval + sevm.benvStat.time] <<+ _ :=
        prefix_of_pop ⟨_, Devm.PopBurn.of_popBurnBy hpop⟩ hp6
      have hstor7 := hstor6.trans
        (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hpop))
      rcases pauseExpiryFinish_expiryWrite rfl hp7 htail with
        ⟨mid, post, hstore, hkey, hmid, heffect⟩
      refine Or.inl ⟨interval + sevm.benvStat.time, ⟨mid, post, hstore, hkey,
        ?_, ?_⟩, checkedExtension_of_not_lt hnoWrap⟩
      · rw [hmid, ← congrFun hstor7 sevm.currentTarget]
      · rw [heffect, ← congrFun hstor7 sevm.currentTarget]
  | succ hne hroom hpop htail =>
      have hflag : ((interval + sevm.benvStat.time) <? sevm.benvStat.time) = _ :=
        (List.of_cons_pref_of_cons_pref hp6 (pref_of_split hpop.stack)).left
      have hwrap : interval + sevm.benvStat.time < sevm.benvStat.time := by
        by_contra hcontra
        rw [B256.ltCheck, if_neg hcontra] at hflag
        exact hne hflag.symm
      exact Or.inr ⟨not_nof_of_lt hwrap, _, htail⟩

/-! ## The reached suffix write -/


set_option maxRecDepth 4096 in
/-- Everything an actually reached post-callback `pauseSuccess` walk settles
about its expiry `SSTORE`.

The walk is a hypothesis: it is entered at an arbitrary `pre`, which is what
the two external calls of `pauseAfterSet` left behind, and no part of that
callback is constructed here.  Exactly two things can happen.  Either the
expiry write is reached, and then its key, its value and its effect on the
CircuitBreaker's storage are pinned exactly; or the post-callback count was
nonzero, `timestamp + interval` wrapped, and the walk went into the shared
`Panic(0x11)` function instead, performing no expiry write at all.

Nothing here claims the walk succeeds, that `count = 0` means the caller lost
its assignment, or that the written cell survives to the end of the
transaction. -/
theorem pauseSuccess_expiryWrite_dichotomy
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {ca : Adr} {count interval : B256}
    (howner : sevm.currentTarget = ca)
    (hcount : Devm.getStorVal pre ca (countSlot sevm.caller.toB256) = count)
    (hinterval : Devm.getStorVal pre ca heartbeatIntervalSlot = interval)
    (hrun : Func.RunCompiledTo fs sevm pre pauseSuccess out) :
    (∃ value : B256,
        PauseExpiryWrite sevm pre ca value ∧
        PauseExpiryValue sevm.benvStat.time interval count value) ∨
      (count ≠ 0 ∧ ¬ B256.Nof sevm.benvStat.time interval ∧
        ∃ panicPre : Devm,
          Func.RunCompiledTo fs sevm panicPre
            (Func.call arithmeticPanicSlot) out) := by
  subst howner
  have hshape : pauseSuccess =
      pausePrefixA +++ (Ninst.mload ::: (pausePrefixB +++ (Ninst.mload :::
        (pausePrefixC +++ (Ninst.sload ::: Ninst.iszero :::
          Func.branch (checkedHeartbeatExpiry pauseExpiryFinish)
            (Ninst.pushB256 0 ::: pauseExpiryFinish)))))) := rfl
  rw [hshape] at hrun
  rcases of_runCompiledTo_prepend pausePrefixA _ hrun with ⟨s1, hA, hrun1⟩
  rcases of_runCompiledTo_next hrun1 with ⟨s2, hload1, hrun2⟩
  rcases of_runCompiledTo_prepend pausePrefixB _ hrun2 with ⟨s3, hB, hrun3⟩
  rcases of_runCompiledTo_next hrun3 with ⟨s4, hload2, hrun4⟩
  rcases of_runCompiledTo_prepend pausePrefixC _ hrun4 with ⟨s5, hC, hrun5⟩
  rcases of_runCompiledTo_next hrun5 with ⟨s6, hsload, hrun6⟩
  rcases of_runCompiledTo_next hrun6 with ⟨s7, hiszero, hbranch⟩
  -- the stack the count branch sees
  have hp1 : [durationWord * 32] <<+ s1.stack :=
    prefix_of_pausePrefixA nil_pref hA
  rcases prefix_of_mload (Ninst.Run.of_runCompiled hload1) hp1 with
    ⟨duration, hp2⟩
  have hp3 : [targetWord * 32, sevm.caller.toB256] <<+ s3.stack :=
    prefix_of_pausePrefixB hp2 hB
  rcases prefix_of_mload (Ninst.Run.of_runCompiled hload2) hp3 with
    ⟨target, hp4⟩
  have hp5 : [countSlot sevm.caller.toB256] <<+ s5.stack :=
    prefix_of_pausePrefixC hp4 hC
  rcases prefix_of_sload (Ninst.Run.of_runCompiled hsload) hp5 with
    ⟨read, hp6, hreadVal⟩
  have hp7 : [read =? 0] <<+ s7.stack :=
    prefix_of_iszero (Ninst.Run.of_runCompiled hiszero) hp6
  -- storage is untouched from the post-callback state up to the branch
  have hstor5 : Devm.getStor pre = Devm.getStor s5 :=
    (Line.of_inv Devm.getStor (by unfold pausePrefixA; line_inv) hA).trans
      ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled hload1)).trans
        ((Line.of_inv Devm.getStor
            (by unfold pausePrefixB mstoreAt; line_inv) hB).trans
          ((Ninst.Hinv.inv (f := Devm.getStor)
              (Ninst.Run.of_runCompiled hload2)).trans
            (Line.of_inv Devm.getStor
              (by unfold pausePrefixC tagTop; line_inv) hC))))
  have hstor7 : Devm.getStor pre = Devm.getStor s7 :=
    hstor5.trans
      ((Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled hsload)).trans
        (Ninst.Hinv.inv (f := Devm.getStor)
          (Ninst.Run.of_runCompiled hiszero)))
  have hreadCount : read = count := by
    rw [hreadVal, ← hcount]
    exact congrArg (fun stor => (stor sevm.currentTarget).get
      (countSlot sevm.caller.toB256)) hstor5.symm
  rw [hreadCount] at hp7
  cases hbranch with
  | zero hroom hpop htail =>
      -- the branch word is zero, so the post-callback count word was nonzero
      have hflag : (count =? 0) = 0 :=
        (List.of_cons_pref_of_cons_pref hp7 (pref_of_split hpop.stack)).left
      have hnonzero : count ≠ 0 := by
        intro hzero
        rw [hzero, B256.eqCheck, if_pos rfl] at hflag
        exact absurd hflag (by decide)
      rcases pauseSuccess_checkedArm hinterval
          (hstor7.trans (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hpop)))
          htail with ⟨value, hwrite, hextension⟩ | ⟨hnof, hpanic⟩
      · exact Or.inl ⟨value, hwrite,
          fun hzero => absurd hzero hnonzero, fun _ => hextension⟩
      · exact Or.inr ⟨hnonzero, hnof, hpanic⟩
  | succ hne hroom hpop htail =>
      -- the branch word is nonzero, so the post-callback count word was zero
      have hflag : (count =? 0) = _ :=
        (List.of_cons_pref_of_cons_pref hp7 (pref_of_split hpop.stack)).left
      have hzero : count = 0 := by
        by_contra hcontra
        rw [B256.eqCheck, if_neg hcontra] at hflag
        exact hne hflag.symm
      exact Or.inl ⟨0, pauseSuccess_zeroCountArm
        (hstor7.trans (PopBurn.Inv.inv (Devm.PopBurn.of_popBurnBy hpop))) htail,
        fun _ => rfl, fun hcontra => absurd hzero hcontra⟩

/-! ## The conditional suffix result

The dichotomy's second branch is the only way an entered `pauseSuccess` walk
can miss its expiry write, so ruling it out is exactly the statement that the
write is reached.  `hreached` says nothing more than that: on the nonzero-count
arm the checked addition does not wrap.  It is not a success premise — the walk
may still revert later, in a later frame, or be rolled back — and it is not a
construction: no callback, no returndata and no target behaviour is supplied
anywhere. -/

/-- The checked extension of a non-wrapping sum, in the form the reached-write
statements need it. -/
theorem checkedHeartbeatExtension_of_nof {timestamp interval : B256}
    (hnof : B256.Nof timestamp interval) :
    CheckedHeartbeatExtension timestamp interval (timestamp + interval) := by
  refine ⟨hnof, B256.toNat_inj _ _ ?_⟩
  rw [B256.toNat_add_eq_of_nof _ _ hnof, B256.toNat_toB256_of_lt hnof]

private lemma pauseExpiryValue_ite {timestamp interval count : B256}
    (hreached : count ≠ 0 → B256.Nof timestamp interval) :
    PauseExpiryValue timestamp interval count
      (if count = 0 then 0 else timestamp + interval) := by
  refine ⟨fun hzero => by rw [if_pos hzero], fun hnonzero => ?_⟩
  rw [if_neg hnonzero]
  exact checkedHeartbeatExtension_of_nof (hreached hnonzero)

/-- **An actually reached pause-expiry write stores zero on a zero
post-callback count, and the checked `timestamp + interval` otherwise.**

The stored word is pinned as a closed term — no containment, no existential
over "some value".  On the nonzero arm `hreached` is exactly Solidity's checked
addition succeeding, so `sevm.benvStat.time + interval` is the unwrapped sum;
`checkedHeartbeatExtension_of_nof` is the same `CheckedHeartbeatExtension`
discipline the registration and heartbeat sides use.

Four things are deliberately absent.  The zero count is *not* identified with
any stable last-assignment fact — it is the word this `SLOAD` returned after
the callback, and nothing more.  The callback is not constructed.  Terminal
success is neither assumed nor proved.  And no claim is made that the written
cell is undisturbed afterwards. -/
theorem pauseSuccess_expiryWrite_of_reached
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {ca : Adr} {count interval : B256}
    (howner : sevm.currentTarget = ca)
    (hcount : Devm.getStorVal pre ca (countSlot sevm.caller.toB256) = count)
    (hinterval : Devm.getStorVal pre ca heartbeatIntervalSlot = interval)
    (hreached : count ≠ 0 → B256.Nof sevm.benvStat.time interval)
    (hrun : Func.RunCompiledTo fs sevm pre pauseSuccess out) :
    PauseExpiryWrite sevm pre ca
      (if count = 0 then 0 else sevm.benvStat.time + interval) := by
  rcases pauseSuccess_expiryWrite_dichotomy howner hcount hinterval hrun with
    ⟨value, hwrite, hvalue⟩ | ⟨hnonzero, hnof, _⟩
  · rcases eq_or_ne count 0 with hzero | hnonzero
    · rw [if_pos hzero, ← hvalue.1 hzero]
      exact hwrite
    · rw [if_neg hnonzero,
        CheckedHeartbeatExtension.add_eq (hvalue.2 hnonzero)]
      exact hwrite
  · exact absurd (hreached hnonzero) hnof

/-- The same reached write, with the count condition spelled as the
biconditional the source branch actually is: outside the single degenerate
world where the block time and the then-current interval are both zero, the
stored word is zero if and only if the post-callback count word read is
zero. -/
theorem pauseSuccess_expiryWrite_stores_zero_iff
    {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {ca : Adr} {count interval : B256}
    (howner : sevm.currentTarget = ca)
    (hcount : Devm.getStorVal pre ca (countSlot sevm.caller.toB256) = count)
    (hinterval : Devm.getStorVal pre ca heartbeatIntervalSlot = interval)
    (nondegenerate : ¬ (sevm.benvStat.time = 0 ∧ interval = 0))
    (hreached : count ≠ 0 → B256.Nof sevm.benvStat.time interval)
    (hrun : Func.RunCompiledTo fs sevm pre pauseSuccess out) :
    PauseExpiryWrite sevm pre ca
        (if count = 0 then 0 else sevm.benvStat.time + interval) ∧
      ((if count = 0 then (0 : B256) else sevm.benvStat.time + interval) = 0
        ↔ count = 0) :=
  ⟨pauseSuccess_expiryWrite_of_reached howner hcount hinterval hreached hrun,
    (pauseExpiryValue_ite hreached).eq_zero_iff_count_eq_zero nondegenerate⟩

end Blanc.LidoCircuitBreaker