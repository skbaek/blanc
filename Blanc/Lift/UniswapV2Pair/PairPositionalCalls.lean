import Blanc.Lift.UniswapV2Pair.PairHistory
import Blanc.Lift.UniswapV2Pair.PairPositionalAdmission
import Blanc.Lift.RetainedTargetCompleteness

namespace Blanc.Lift.UniswapV2Pair

open Jaune Blanc Blanc.ExecutionTrace

/-- Every suspension of a segment is a source request built by `requestFor`. -/
def SegmentResult.Requested (segment : SegmentResult) : Prop :=
  ∀ frame request continuation, segment = .suspended frame request continuation →
    ∃ site target operation, request = requestFor site target operation

theorem startImmediate_requested {current : Checkpoint} {ctx : Context} {entry : Entry}
    {result : SegmentResult} (h : startImmediate current ctx entry = some result) :
    result.Requested := by
  intro frame request continuation hr
  subst hr
  simp only [startImmediate, Frame.fail, Frame.finish, Frame.finishLP] at h
  repeat' split at h
  all_goals cases h

theorem startTyped_requested (current : Checkpoint) (ctx : Context) (entry : Entry) :
    (startTyped current ctx entry).Requested := by
  intro frame request continuation h
  unfold startTyped at h
  split at h
  · rename_i result immediate
    exact startImmediate_requested immediate frame request continuation h
  simp only [Frame.suspend, Frame.fail] at h
  repeat' split at h
  all_goals first
    | (simp only [SegmentResult.suspended.injEq] at h; obtain ⟨-, rfl, -⟩ := h;
        exact ⟨_, _, _, rfl⟩)
    | cases h

theorem resumeSegment_requested (prior : Frame) (request : Request)
    (continuation : Continuation) (reply : ExternalResult) :
    (resumeSegment prior request continuation reply).Requested := by
  intro frame request' continuation' h
  simp only [resumeSegment, Frame.suspend, Frame.fail, Frame.finishUpdated, Frame.finishLocked,
    Frame.finish, Frame.afterSwapTransfer0, Frame.afterSwapTransfer1, Frame.mintAfterFee,
    Frame.burnAfterFee, Frame.finishLP] at h
  repeat' split at h
  all_goals first
    | (simp only [SegmentResult.suspended.injEq] at h; obtain ⟨-, rfl, -⟩ := h;
        exact ⟨_, _, _, rfl⟩)
    | cases h

/-- What one direct child entered at an observed source call carries. -/
def ChildOfRequest (root : Exec.Deriv) (c : Exec.Frame) : Prop :=
  ∃ (frame : Frame) (request : Request),
    (∃ site target operation, request = requestFor site target operation) ∧
    c.sevm.currentTarget = request.target ∧ c.sevm.caller = frame.context.pair ∧
    c.sevm.data = request.calldata ∧ c.sevm.value = request.value ∧
    (getDelegatedCodeAddress (c.pre.getCode c.sevm.currentTarget) = none →
      c.sevm.codeAddress = some request.target) ∧
    c.sevm.isStatic = externalStatic frame request ∧
    frame.context.pair = root.sevm.currentTarget

/-- The observed instruction is the actual `CALL`/`STATICCALL` that spawned the source message. -/
theorem SourceCallAt.xstep {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} (observed : SourceCallAt root frame request reply index) :
    ∃ x : Xinst, (x = .call ∨ x = .staticcall) ∧
      Xinst.step observed.call.occurrence.node.sevm observed.call.occurrence.node.devm x =
        .spawn (Jaune.Frame.ofCall observed.message) observed.resume := by
  obtain ⟨x', decoded, step, -⟩ := Evm.step_spawn_inv observed.spawned
  have actual := observed.call.occurrence.decoded
  rw [observed.call.instruction] at actual
  unfold Xinst.At at decoded
  unfold Ninst.At at actual
  have same := decoded.symm.trans actual
  simp only [Option.some.injEq, Inst.next.injEq, Ninst.exec.injEq] at same
  refine ⟨x', ?_, step⟩
  rw [same]
  split <;> simp only [true_or, or_true]

/-- A child entered at an observed source call is the request's message. -/
theorem SourceCallAt.childOfRequest {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} (observed : SourceCallAt root frame request reply index)
    (shaped : ∃ site target operation, request = requestFor site target operation)
    {c : Exec.Frame} {childEvm : Evm} (enter : (Jaune.Frame.ofCall observed.message).enter = .run childEvm)
    (sevmEq : c.sevm = childEvm.sta) (preEq : c.pre = childEvm.dyna) :
    ChildOfRequest root c := by
  obtain ⟨x, kind, step⟩ := observed.xstep
  have target := Xinst.step_callKind_spawn_target kind step
  have codeAddress := Xinst.step_callKind_spawn_codeAddress kind step
  have code := Xinst.step_spawn_getCode step
  have caller : observed.message.caller =
      observed.call.occurrence.node.sevm.currentTarget := by
    rcases kind with rfl | rfl
    · exact Xinst.step_call_spawn_caller step
    · exact Xinst.step_staticcall_spawn_caller step
  have nodeSevm := Exec.Deriv.ParentPrefix.sevm_eq observed.call.sameFrame
  have targetEq : observed.message.currentTarget = request.target :=
    Option.some.inj ((target : observed.message.target = _).symm.trans observed.target)
  have preCode := Frame.enter_run_getCode enter
  have preTarget := Frame.enter_run_currentTarget enter
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv enter
  refine ⟨frame, request, shaped, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sevmEq]; exact targetEq
  · rw [sevmEq]; exact observed.caller
  · rw [sevmEq]; exact observed.calldata
  · rw [sevmEq]; exact observed.value
  · intro undelegated
    rw [sevmEq]
    rw [sevmEq, preEq, preTarget, preCode] at undelegated
    change observed.message.codeAddress = some request.target
    rw [← targetEq]
    apply codeAddress
    rw [← code]
    exact undelegated
  · rw [sevmEq]; exact observed.static
  · rw [← observed.caller, caller, nodeSevm]

/-- Every direct child of the consumed span is the message of one source request. -/
theorem PositionalConsumes.childOfRequest {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (consumed : PositionalConsumes root start index segment transcript out) :
    segment.Requested → ∀ c ∈ Exec.childFrames start.exc, ChildOfRequest root c := by
  refine PositionalConsumes.rec
    (motive_1 := fun root start _ segment _ _ _ =>
      segment.Requested → ∀ c ∈ Exec.childFrames start.exc, ChildOfRequest root c)
    (motive_2 := fun _ _ _ _ _ _ _ => True) ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed
  · intro root start index frame bytes free _ c member
    rw [Exec.childFrames_eq_nil_of_free start free] at member
    cases member
  · intro root start index frame failure genuine free _ c member
    rw [Exec.childFrames_eq_nil_of_free start free] at member
    cases member
  · intro root start index frame request continuation reply turns tail executed out
      observed gap present noCodeTurns during rest ih requested c member
    rw [gap.childFrames_eq] at member
    rcases Exec.Deriv.ParentStep.childFrames_spawn observed.call.edge observed.spawned c member with
      later | ⟨childEvm, enter, sevmEq, preEq⟩
    · exact ih (resumeSegment_requested _ _ _ _) c later
    · exact observed.childOfRequest (requested frame request continuation rfl) enter sevmEq preEq
  · intro root start index frame request continuation reply turns tail executed out events
      observed gap queue present noCodeTurns during rest _ ih requested c member
    rw [gap.childFrames_eq] at member
    rcases Exec.Deriv.ParentStep.childFrames_spawn observed.call.edge observed.spawned c member with
      later | ⟨childEvm, enter, sevmEq, preEq⟩
    · exact ih (resumeSegment_requested _ _ _ _) c later
    · exact observed.childOfRequest (requested frame request continuation rfl) enter sevmEq preEq
  · intros; trivial
  · intros; trivial
  · intros; trivial

/-- **The verdict lemma (call-shape route), proposed form.**  As the frozen
`PairAdmittedConsumes.child_requests`, except that the code-address conjunct holds only when the
callee holds no EIP-7702 delegation designator (a designator resolves a `CALL`'s code address to
the delegate, so the frozen unconditional conjunct is false for a delegated callback target). -/
theorem PairAdmittedConsumes.child_requests_undelegated {root : Exec.Deriv} {current : Checkpoint}
    {invocation : List Nat} {entry : Entry} {transcript : Transcript} {out : RunResult}
    (admitted : PairAdmittedConsumes root
      (startTyped current (writerContext root.sevm invocation) entry) transcript out) :
    ∀ c ∈ Exec.childFrames root.exc, ∃ (frame : Frame) (request : Request),
      c.sevm.currentTarget = request.target ∧ c.sevm.caller = frame.context.pair ∧
      c.sevm.data = request.calldata ∧ c.sevm.value = request.value ∧
      (getDelegatedCodeAddress (c.pre.getCode c.sevm.currentTarget) = none →
        c.sevm.codeAddress = some request.target) ∧
      c.sevm.isStatic = externalStatic frame request ∧
      frame.context.pair = root.sevm.currentTarget := by
  intro c member
  obtain ⟨frame, request, -, facts⟩ :=
    admitted.positional.childOfRequest (startTyped_requested _ _ _) c member
  exact ⟨frame, request, facts⟩

/-- The Pair context of an observed call is the address the consumed root runs at. -/
theorem SourceCallAt.pair_eq {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} (observed : SourceCallAt root frame request reply index) :
    frame.context.pair = root.sevm.currentTarget := by
  obtain ⟨x, kind, step⟩ := observed.xstep
  have caller : observed.message.caller =
      observed.call.occurrence.node.sevm.currentTarget := by
    rcases kind with rfl | rfl
    · exact Xinst.step_call_spawn_caller step
    · exact Xinst.step_staticcall_spawn_caller step
  rw [← observed.caller, caller, Exec.Deriv.ParentPrefix.sevm_eq observed.call.sameFrame]

/-- A retained frame at the root's address entered at an observed call lies in the continuation
or inside one frame of the call's selected queue. -/
theorem SourceCallAt.descendant_split {root : Exec.Deriv} {frame : Frame} {request : Request}
    {reply : ExternalResult} {index : Nat} (observed : SourceCallAt root frame request reply index)
    {paths : List Exec.LocatedFrame}
    (queue : SourceSlotQueue observed.call frame.context.pair index paths) :
    ∀ D ∈ Exec.descendantFrames observed.call.occurrence.node.exc,
      D.sevm.currentTarget = root.sevm.currentTarget →
      D ∈ Exec.descendantFrames observed.call.returned.exc ∨
        ∃ located ∈ paths, located.frame.sevm.currentTarget = root.sevm.currentTarget ∧
          D ∈ Exec.committedFrames located.frame.run := by
  intro D member atRoot
  rcases queue with ⟨slotNone, -⟩ |
    ⟨childEvm, raw, callee, resume, pc', childRun, next, spawn, enter, resumed, -, nodeExc,
      pathsEq⟩
  · left
    have notRun : ∀ childEvm, (Jaune.Frame.ofCall observed.message).enter ≠ .run childEvm := by
      intro childEvm entered
      have response := observed.response
      rw [slotNone] at response
      unfold ProcessMessage RunFrame at response
      rw [entered] at response
      obtain ⟨_, impossible, _⟩ := response
      cases impossible
    rw [← Exec.Deriv.ParentStep.descendantFrames_spawn_done observed.call.edge observed.spawned
      notRun]
    exact member
  · rcases Exec.Deriv.ParentStep.descendantFrames_runOk observed.call.edge nodeExc D member with
      later | ⟨settles, inChild⟩
    · exact Or.inl later
    · right
      have pair := observed.pair_eq
      rw [pathsEq, ite_eq_left settles, Exec.retainedTargetTurnsAt_filterMap_eq _ _ childRun
        (Jaune.Frame.raw_commits_of_settlementCommits settles)]
      obtain ⟨located, mem, locatedAt, inside⟩ :=
        Exec.retainedTargetFramesFromAt_complete frame.context.pair childRun [index] 0
          (Jaune.Frame.raw_commits_of_settlementCommits settles) D inChild (atRoot.trans pair.symm)
      exact ⟨located, mem, locatedAt.trans pair, inside⟩

/-- A frame with its own positional consumption from a typed entry. -/
def PairLocated (D : Exec.Frame) : Prop :=
  ∃ (current : Checkpoint) (ctx : Context) (entry : Entry) (transcript : Transcript)
    (out : RunResult),
    PositionalConsumes (Blanc.Exec.Frame.rootDeriv D) (Blanc.Exec.Frame.rootDeriv D) 0
      (startTyped current ctx entry) transcript out

/-- **Completeness.**  Every retained non-static frame at the root's address below the consumed
span is itself positionally consumed (a `located` frame of the derivation). -/
theorem PositionalConsumes.complete {root start : Exec.Deriv} {index : Nat}
    {segment : SegmentResult} {transcript : Transcript} {out : RunResult}
    (consumed : PositionalConsumes root start index segment transcript out) :
    ∀ D ∈ Exec.descendantFrames start.exc, D.sevm.currentTarget = root.sevm.currentTarget →
      D.sevm.isStatic = false → PairLocated D := by
  refine PositionalConsumes.rec
    (motive_1 := fun root start _ _ _ _ _ =>
      ∀ D ∈ Exec.descendantFrames start.exc, D.sevm.currentTarget = root.sevm.currentTarget →
        D.sevm.isStatic = false → PairLocated D)
    (motive_2 := fun _ _ _ events _ _ _ =>
      ∀ located, Sum.inr located ∈ events → ∀ D ∈ Exec.committedFrames located.frame.run,
        D.sevm.currentTarget = located.frame.sevm.currentTarget →
        D.sevm.isStatic = false → PairLocated D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ consumed
  · intro root start index frame bytes free D member
    rw [Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt start.exc free] at member
    cases member
  · intro root start index frame failure genuine free D member
    rw [Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt start.exc free] at member
    cases member
  · intro root start index frame request continuation reply turns tail executed out
      observed gap present noCodeTurns during rest ih D member atRoot mutable
    rw [gap.descendantFrames_eq] at member
    rcases observed.descendant_split observed.queue D member atRoot with
      later | ⟨located, mem, -, inside⟩
    · exact ih D later atRoot mutable
    · cases during with
      | staticViews views mapped authentic consumed =>
        rw [← mapped] at mem
        obtain ⟨picked, pickedMem, rfl⟩ := List.mem_map.mp mem
        have static : picked.1.frame.sevm.isStatic = true := (authentic picked pickedMem).2.2.2.1
        rcases Exec.Frame.mem_committedFrames.mp inside with rfl | deeper
        · rw [static] at mutable; cases mutable
        · rw [Exec.descendantFrames_isStatic picked.1.frame.run static D deeper] at mutable
          cases mutable
  · intro root start index frame request continuation reply turns tail executed out events
      observed gap queue present noCodeTurns during rest ihDuring ihRest D member atRoot mutable
    rw [gap.descendantFrames_eq] at member
    rcases observed.descendant_split queue.queue D member atRoot with
      later | ⟨located, mem, locatedAt, inside⟩
    · exact ihRest D later atRoot mutable
    · have event : Sum.inr located ∈ events := by
        obtain ⟨event, eventMem, picked⟩ := List.mem_filterMap.mp mem
        cases event with
        | inl log => cases picked
        | inr located' =>
          cases picked
          exact eventMem
      exact ihDuring located event D inside (atRoot.trans locatedAt.symm) mutable
  · intro frame request turn located member
    cases member
  · intro frame request turn log events tail out mutable rest ih located member
    rcases List.mem_cons.mp member with impossible | later
    · cases impossible
    · exact ih located later
  · intro frame request turn selectedFrame entry events transcript tail child out
      selected output rest ihSelected ihRest located member D inside atLocated mutable
    rcases List.mem_cons.mp member with same | later
    · cases same
      rcases Exec.Frame.mem_committedFrames.mp inside with rfl | deeper
      · exact ⟨_, _, _, _, _, selected⟩
      · exact ihSelected D deeper atLocated mutable
    · exact ihRest located later D inside atLocated mutable

/-- A non-static source request carries the `transfer` or the `uniswapV2Call` selector. -/
theorem requestFor_mutable_selector {frame : Frame} {site : CallSite} {target : Adr}
    {operation : ExternalOperation} (mutable : externalStatic frame (requestFor site target operation) = false)
    {sevm : Sevm} (data : sevm.data = (requestFor site target operation).calldata) :
    Blanc.Sevm.selector sevm = 0xa9059cbb ∨ Blanc.Sevm.selector sevm = 0x10d1e85c := by
  rw [Blanc.Sevm.selector_eq_toB256_takeD_four, data]
  cases operation <;>
    simp only [externalStatic, requestFor, Bool.or_eq_false_iff, beq_self_eq_true,
      Bool.true_eq_false, and_false] at mutable
  · left
    simp only [requestFor, ExternalOperation.encode, List.cons_append, List.takeD, List.headD_cons,
      List.tail_cons]
    rfl
  · right
    simp only [requestFor, ExternalOperation.encode, List.cons_append, List.takeD, List.headD_cons,
      List.tail_cons]
    rfl

/-- A step of an observed replay is consumed from a typed entry. -/
theorem PairObservedReplayWith.consumed_of_mem
    {Consumes : Exec.Deriv → SegmentResult → Transcript → RunResult → Prop}
    {st finish : State} {steps : List PairStep}
    (replay : PairObservedReplayWith Consumes st steps finish) :
    ∀ s ∈ steps, ∃ (current : Checkpoint) (out : RunResult),
      Consumes (Blanc.Exec.Frame.rootDeriv s.frame)
        (startTyped current s.source.context s.source.entry) s.transcript out := by
  induction replay with
  | nil st => intro s member; cases member
  | cons consumed _ _ ih =>
    intro s member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨_, _, consumed⟩
    · exact ih s later

/-- **Call shape from positional consumption, proposed form.**  As the frozen
`pair_history_children_shape`, except that the code-address conjunct holds only when the callee
holds no EIP-7702 delegation designator. -/
theorem pair_history_children_shape_undelegated {pair : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {K₀ : WriterKey → Prop} {st₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pair).toList = pairSem.image)
    (initial : WriterRep K₀ (checkpoint.state.getStor pair) st₀)
    (fresh : WriterFreshKeys K₀ (pairHistoryTouchedKeys pair trace)) :
    ∀ G ∈ trace.settledFrames, G.sevm.currentTarget = pair → G.sevm.isStatic = false →
      ∀ c ∈ Exec.childFrames G.run, c.sevm.isStatic = false →
        c.sevm.caller = pair ∧
          (getDelegatedCodeAddress (c.pre.getCode c.sevm.currentTarget) = none →
            c.sevm.codeAddress = some c.sevm.currentTarget) ∧
          (Blanc.Sevm.selector c.sevm = 0xa9059cbb ∨ Blanc.Sevm.selector c.sevm = 0x10d1e85c) := by
  intro G settled atPair mutableG c child mutable
  obtain ⟨-, steps, observedEq, auth, finish, K', replay, -⟩ :=
    pair_history_committed trace installed initial fresh
  have inPair : G ∈ committedPairFrames pair trace := by
    refine List.mem_flatMap.mpr ⟨G, settled, ?_⟩
    rw [pairFrameObs, ite_eq_left ⟨atPair, mutableG⟩]
    exact List.mem_singleton_self G
  rw [← observedEq] at inPair
  obtain ⟨s, stepMem, inSubtree⟩ := List.mem_flatMap.mp inPair
  obtain ⟨F, frameMem, obs⟩ := List.mem_flatMap.mp inSubtree
  have sameF : G = F := by
    unfold pairFrameObs at obs
    split at obs
    · exact List.mem_singleton.mp obs
    · cases obs
  subst sameF
  obtain ⟨current, out, consumed⟩ := replay.consumed_of_mem s stepMem
  have located : PairLocated G := by
    rcases Exec.Frame.mem_committedFrames.mp frameMem with rfl | deeper
    · exact ⟨_, _, _, _, _, consumed.positional⟩
    · exact consumed.positional.complete G deeper (atPair.trans (auth s stepMem).2.2.1.symm)
        mutableG
  obtain ⟨current', ctx, entry, transcript, out', positional⟩ := located
  obtain ⟨frame, request, ⟨site, target, operation, rfl⟩, targetEq, caller, data, -,
      codeAddress, static, pairEq⟩ :=
    positional.childOfRequest (startTyped_requested _ _ _) c child
  refine ⟨caller.trans (pairEq.trans atPair), fun undelegated => ?_, ?_⟩
  · rw [codeAddress undelegated, targetEq]
  · exact requestFor_mutable_selector (static.symm.trans mutable) data

end Blanc.Lift.UniswapV2Pair
