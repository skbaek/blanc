import Blanc.Lift.UniswapV2Pair.PairOuterCalls
import Blanc.Lift.UniswapV2Pair.PairFeeAnswer
import Blanc.Lift.UniswapV2Pair.SourceOccurrence

/-!
# Call-settlement facts of an observed Pair call, and the factory answer

Contract-local Lift facts about one observed call (`SourceCallAt`) of a Pair frame, used by the
child-answer layers (`BalanceAnswers`) and by the token composition:

* `ofCall_settle_committed`: a committed call frame settles to its committed post-machine with the
  message target's touch recorded;
* `sourceCallAt_reply_facts`: the reply is the success flag and output of the processed child;
* `sourceCallAt_entered`: a call to an undelegated non-precompile target enters a code frame;
* `feeAnswer_eq_feeToAnswer`: along a positional consumption of a successful `mint`/`burn`, the
  transcript's third reply is the output of the frame the call's third child call entered.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc

/-- A committed call frame's settlement is its committed post-machine, with the touch of the
message's current target recorded. -/
theorem ofCall_settle_committed {msg : Msg} {raw : Execution}
    (committed : Execution.commits raw = true) :
    (Jaune.Frame.ofCall msg).settle raw = .ok ((Execution.committedPost raw committed).recordTouch
      msg.benv.stat.rules true msg.currentTarget) := by
  cases raw with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    cases errorEq : post.error with
    | none =>
      simp only [Jaune.Frame.settle, Jaune.Frame.settleMsg, Jaune.Frame.ofCall,
        executeCode.handleErrorWith_ok, processMessage.settle, Bind.bind, Except.bind, errorEq,
        Option.isSome_none, Bool.false_eq_true, ite_false, Execution.committedPost]
    | some error =>
      simp only [Execution.commits, errorEq, Option.isNone_some, Bool.false_eq_true] at committed

/-- What the observed reply is, in terms of the processed child. -/
theorem sourceCallAt_reply_facts {root : Exec.Deriv} {frame : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {index : Nat}
    (observed : SourceCallAt root frame request reply index) :
    reply.success = !observed.child.error.isSome ∧ reply.returndata = observed.child.output := by
  cases observed.replyAt with
  | bytes _ success returndata => exact ⟨success, returndata⟩
  | recovery _ success returndata _ => exact ⟨success, returndata⟩

/-- **An observed call to an undelegated non-precompile target enters a code frame**: an empty
child slot means the call ran an enabled precompile at its code address (the `entered` input of
`StepOracle`). -/
theorem sourceCallAt_entered {root : Exec.Deriv} {frame : UniswapV2Pair.Frame}
    {request : Request} {reply : ExternalResult} {index : Nat}
    (observed : SourceCallAt root frame request reply index)
    (undelegated :
      getDelegatedCodeAddress (observed.call.occurrence.node.devm.getCode request.target) = none)
    (notPrecomp : ¬ observed.call.occurrence.node.sevm.benvStat.rules.isPrecomp request.target) :
    observed.call.occurrence.slot.isSome = true := by
  obtain ⟨x, kind, step⟩ := observed.xstep
  have targetEq : observed.message.currentTarget = request.target :=
    Option.some.inj ((Xinst.step_callKind_spawn_target kind step :
      observed.message.target = _).symm.trans observed.target)
  have codeAddress : observed.message.codeAddress = some request.target := by
    have spawned := Xinst.step_callKind_spawn_codeAddress kind step (by
      change getDelegatedCodeAddress
        (observed.call.occurrence.node.devm.getCode observed.message.currentTarget) = none
      rw [targetEq]
      exact undelegated)
    rw [← targetEq]
    exact spawned
  have stat : observed.message.benv.stat = observed.call.occurrence.node.sevm.benvStat :=
    Xinst.step_spawn_benvStat step
  cases slot : observed.call.occurrence.slot with
  | some _ => rfl
  | none =>
    exfalso
    have response := observed.response
    rw [slot] at response
    unfold ProcessMessage RunFrame at response
    cases entered : (Jaune.Frame.ofCall observed.message).enter with
    | run evm =>
      rw [entered] at response
      obtain ⟨_, impossible, _⟩ := response
      cases impossible
    | done result =>
      rw [entered] at response
      obtain ⟨_, resultEq⟩ := response
      unfold Jaune.Frame.enter at entered
      split at entered
      · cases entered
        simp only [Jaune.Frame.settleMsg, Jaune.Frame.ofCall, processMessage.settle, bind,
          Except.bind, Bool.false_eq_true, ite_false, reduceCtorEq] at resultEq
      · rename_i benv transfer
        split at entered
        · cases entered
        · rename_i raw entry
          obtain ⟨adr, routed, -, precomp⟩ := Blanc.executeCode.enter_inr_routing entry
          have benvStat : benv.stat = observed.message.benv.stat := benvAfterTransfer_stat transfer
          simp only [Msg.withBenv, Jaune.Frame.ofCall] at routed precomp
          rw [codeAddress] at routed
          cases routed
          rw [benvStat, stat] at precomp
          exact notPrecomp precomp

/-- **The factory query of a successful `mint`/`burn` entered a committed frame, whose output is
the transcript's third reply**: along an actual positional consumption of a successful
`mint`/`burn` from a checkpoint whose factory is undelegated and not a precompile at the frame's
nodes, the call's third child call entered a committed frame (`childAt f 2`), and the first word of
the transcript's third reply is `feeToAnswer f`. -/
theorem feeAnswer_childAt {f : Exec.Frame} {current : Checkpoint} {ctx : Context}
    {entry : UniswapV2Pair.Entry} {transcript : Transcript} {out : RunResult} {bytes : Bytes}
    (fee : (∃ recipient, entry = .mint recipient) ∨ ∃ recipient, entry = .burn recipient)
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      (startTyped current ctx entry) transcript out)
    (success : out.status = .success bytes)
    (entered : ∀ {node : Exec.Deriv},
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv f) node →
        getDelegatedCodeAddress (node.devm.getCode current.state.factory) = none ∧
          ¬ node.sevm.benvStat.rules.isPrecomp current.state.factory) :
    (childAt f 2).isSome = true ∧
    transcript.ownTail.ownTail.firstWord.toAdr = feeToAnswer f := by
  have lead0 := startTyped_feeLead current ctx (entry := entry) fee
  generalize startTyped current ctx entry = seg0 at lead0 consumed
  rcases seg0 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨F0, req0, c0⟩
  · exact lead0.elim
  · rw [consumed.failed_status] at success
    cases success
  obtain ⟨r0, t0, tail0, obs0, prior0, out0, C0, rfl, -, eq0, below0, static0, rest0, status0⟩ :=
    consumed.suspended_inv
  rw [static0 (by rw [externalStatic, lead0.2.1]; exact Bool.or_true _)] at rest0
  have lead1 := resumeSegment_feeLead_zero lead0 r0
  generalize resumeSegment F0 req0 c0 r0 = seg1 at lead1 rest0
  rcases seg1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨F1, req1, c1⟩
  · exact lead1.elim
  · rw [status0, rest0.failed_status] at success
    cases success
  obtain ⟨r1, t1, tail1, obs1, prior1, out1, C1, rfl, -, eq1, below1, static1, rest1, status1⟩ :=
    rest0.suspended_inv
  rw [static1 (by rw [externalStatic, lead1.2.1]; exact Bool.or_true _)] at rest1
  have lead2 := resumeSegment_feeLead_one lead1 r1
  generalize resumeSegment F1 req1 c1 r1 = seg2 at lead2 rest1
  rcases seg2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨F2, req2, c2⟩
  · exact lead2.elim
  · rw [status0, status1, rest1.failed_status] at success
    cases success
  obtain ⟨r2, t2, tail2, obs2, prior2, out2, -, rfl, gap2, -, -, -, rest2, status2⟩ :=
    rest1.suspended_inv
  have answered : r2.success = true := by
    cases answer : r2.success
    · obtain ⟨_, _, failedEq⟩ := resumeSegment_feeLead_two_failed (fr := prior2) lead2 answer
      rw [failedEq] at rest2
      rw [status0, status1, status2, rest2.failed_status] at success
      cases success
    · rfl
  obtain ⟨targetEq, -, -⟩ := lead2
  obtain ⟨undelegated, notPrecomp⟩ := entered obs2.call.sameFrame
  rw [← targetEq] at undelegated notPrecomp
  have isSome := sourceCallAt_entered obs2 undelegated notPrecomp
  have replyFacts := sourceCallAt_reply_facts obs2
  rcases obs2.queue with ⟨slotNone, -⟩ |
    ⟨childEvm, raw, callee, resume, pc', childRun, next, spawn, enter, resumed, slotSome, nodeExc,
      -⟩
  · rw [slotNone] at isSome
    cases isSome
  have same := spawn.symm.trans obs2.spawned
  simp only [Step.spawn.injEq] at same
  obtain ⟨rfl, -, -⟩ := same
  have response := obs2.response
  rw [slotSome] at response
  obtain ⟨-, settleEq⟩ := RunFrame.some_inv response
  have clean : obs2.child.error.isSome = false := by
    have h := replyFacts.1
    rw [answered] at h
    cases hc : obs2.child.error.isSome
    · rfl
    · rw [hc] at h
      cases h
  have settles := ProcessMessage.settlementCommits_of_some_ok_clean response clean
  have nodeList : Exec.descendantFramePaths [] 2 obs2.call.occurrence.node.exc =
      ⟨[] ++ [2], Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)⟩
        :: (Exec.descendantFramePaths ([] ++ [2]) 0 childRun ++
          Exec.descendantFramePaths [] 3 next) := by
    rw [nodeExc, Exec.descendantFramePaths, dite_eq_left_of_eq_true (eq_true settles),
      List.cons_append]
  have whole : Exec.descendantFramePaths [] 0 f.run = C0 ++ C1 ++
      (⟨[] ++ [2], Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)⟩
        :: (Exec.descendantFramePaths ([] ++ [2]) 0 childRun ++
          Exec.descendantFramePaths [] 3 next)) := by
    change Exec.descendantFramePaths [] 0 (Blanc.Exec.Frame.rootDeriv f).exc = _
    rw [eq0, eq1, gap2.descendantFramePaths_eq, nodeList, List.append_assoc]
  have missing (C : List Exec.LocatedFrame) (i : Nat) (off : i ≠ 2)
      (below : ∀ c ∈ C, [i] <+: c.path) :
      C.find? (fun c => c.path == [2]) = none := by
    rw [List.find?_eq_none]
    intro c member
    obtain ⟨rest, pathEq⟩ := below c member
    rw [← pathEq]
    simp only [List.singleton_append, beq_iff_eq, List.cons.injEq, off, false_and,
      not_false_eq_true]
  have childEq : obs2.child.output =
      (Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)).post.output := by
    have settled := settleEq.trans
      (ofCall_settle_committed (Jaune.Frame.raw_commits_of_settlementCommits settles))
    rw [Except.ok.inj settled, Devm.recordTouch_output]
    rfl
  have found : childAt f 2 = some
      (Exec.Frame.ofRun childRun (Jaune.Frame.raw_commits_of_settlementCommits settles)) := by
    unfold childAt
    rw [whole, List.find?_append, List.find?_append, missing C0 0 (by decide) below0,
      missing C1 1 (by decide) below1]
    simp only [Option.none_or, List.find?_cons, List.nil_append, beq_self_eq_true,
      Option.map_some]
  refine ⟨by rw [found]; rfl, ?_⟩
  unfold feeToAnswer
  rw [found]
  change (Bytes.toB256 (r2.returndata.take 32)).toAdr = _
  rw [replyFacts.2, childEq]

/-- **The transcript's factory answer is the factory frame's output**: along an actual positional
consumption of a successful `mint`/`burn` from a checkpoint whose factory is undelegated and not a
precompile at the frame's nodes, the third reply of the transcript is the output of the frame the
call's third child call entered, so its first word is `feeToAnswer f`. -/
theorem feeAnswer_eq_feeToAnswer {f : Exec.Frame} {current : Checkpoint} {ctx : Context}
    {entry : UniswapV2Pair.Entry} {transcript : Transcript} {out : RunResult} {bytes : Bytes}
    (fee : (∃ recipient, entry = .mint recipient) ∨ ∃ recipient, entry = .burn recipient)
    (consumed : PositionalConsumes (Blanc.Exec.Frame.rootDeriv f) (Blanc.Exec.Frame.rootDeriv f) 0
      (startTyped current ctx entry) transcript out)
    (success : out.status = .success bytes)
    (entered : ∀ {node : Exec.Deriv},
      Exec.Deriv.ParentPrefix (Blanc.Exec.Frame.rootDeriv f) node →
        getDelegatedCodeAddress (node.devm.getCode current.state.factory) = none ∧
          ¬ node.sevm.benvStat.rules.isPrecomp current.state.factory) :
    transcript.ownTail.ownTail.firstWord.toAdr = feeToAnswer f :=
  (feeAnswer_childAt fee consumed success entered).2

end Blanc.Lift.UniswapV2Pair
