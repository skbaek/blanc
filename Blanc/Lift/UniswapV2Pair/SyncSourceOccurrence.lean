import Blanc.Lift.UniswapV2Pair.SourceOccurrence
import Blanc.Lift.UniswapV2Pair.SyncOccurrence

/-! The canonical Sync source consumption annotated by its actual calls. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The first source request uses the canonical call, reply and full slot queue. -/
theorem SyncCanonicalResult.firstSourceCall {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : SyncCanonicalResult K current invocation root b post) :
    let ctx := writerContext root.sevm invocation
    ∃ observed : SourceCallAt root (syncSourceLockedFrame current ctx)
        (requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair))
        (syncExternalReply r.out0) 0,
      observed.call = r.firstOccurrenceStep ∧ observed.paths = r.paths0 := by
  let ctx := writerContext root.sevm invocation
  let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
  obtain ⟨parent, child, dp, na, childCode, avail, g, _, process, clean,
    output, _, resumed, _, spawn, branch⟩ := r.firstCall
  let msg := callMsg root.sevm parent (min g.toNat (except64th avail)) 0
    ctx.pair current.state.token0 na true true request.calldata childCode dp
  refine ⟨{
    call := r.firstOccurrenceStep
    message := msg
    resume := Resume.call parent 128 32
    nextPc := r.first.node.pc + 1
    child := child
    outputOffset := 128
    outputSize := 32
    parent := parent
    spawned := spawn
    target := rfl
    caller := rfl
    value := rfl
    calldata := rfl
    static := by simp [msg, callMsg, externalStatic, request, requestFor]
    response := process
    resumeEq := rfl
    resumed := resumed
    replyAt := by
      apply SourceReplyAt.bytes
      · intro digest v rr ss impossible
        cases impossible
      · rw [clean]
        rfl
      · exact output.symm
    guarded := by
      intro _
      exact ⟨fun _ => r.guarded0, fun _ => rfl⟩
    paths := r.paths0
    queue := by
      rcases branch with ⟨none, empty, _⟩ |
        ⟨childEvm, raw, callee, resume, pc', childRun, next, spawn, enter,
          resumed, slot, exactRun, paths⟩
      · exact Or.inl ⟨none, empty⟩
      · exact Or.inr ⟨childEvm, raw, callee, resume, pc', childRun, next,
          spawn, enter, resumed, slot, exactRun, paths⟩
    childFrames := r.childFrames0
    partition := r.rawPartition.2.1
  }, rfl, rfl⟩

/-- The second source request uses the canonical call, reply and full slot queue. -/
theorem SyncCanonicalResult.secondSourceCall {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : SyncCanonicalResult K current invocation root b post) :
    let ctx := writerContext root.sevm invocation
    ∃ observed : SourceCallAt root (syncSourceSecondFrame current ctx)
        (requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair))
        (syncExternalReply r.out1) 1,
      observed.call = r.secondOccurrenceStep ∧ observed.paths = r.paths1 := by
  let ctx := writerContext root.sevm invocation
  let request := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
  obtain ⟨parent, child, dp, na, childCode, avail, g, _, process, clean,
    output, _, resumed, _, spawn, branch⟩ := r.secondCall
  let msg := callMsg root.sevm parent (min g.toNat (except64th avail)) 0
    ctx.pair current.state.token1 na true true request.calldata childCode dp
  refine ⟨{
    call := r.secondOccurrenceStep
    message := msg
    resume := Resume.call parent 128 32
    nextPc := r.second.node.pc + 1
    child := child
    outputOffset := 128
    outputSize := 32
    parent := parent
    spawned := spawn
    target := rfl
    caller := rfl
    value := rfl
    calldata := rfl
    static := by simp [msg, callMsg, externalStatic, request, requestFor]
    response := process
    resumeEq := rfl
    resumed := resumed
    replyAt := by
      apply SourceReplyAt.bytes
      · intro digest v rr ss impossible
        cases impossible
      · rw [clean]
        rfl
      · exact output.symm
    guarded := by
      intro _
      exact ⟨fun _ => r.guarded1, fun _ => rfl⟩
    paths := r.paths1
    queue := by
      rcases branch with ⟨none, empty, _⟩ |
        ⟨childEvm, raw, childRun, next, spawn, enter, resumed, slot, exactRun, paths⟩
      · exact Or.inl ⟨none, empty⟩
      · exact Or.inr ⟨childEvm, raw, Jaune.Frame.ofCall msg, Resume.call parent 128 32,
          r.second.node.pc + 1, childRun, next, spawn, enter, resumed, slot, exactRun, paths⟩
    childFrames := r.childFrames1
    partition := r.rawPartition.2.2.1
  }, rfl, rfl⟩

/-- The exact canonical source run, annotated at both actual calls and the final
call-free parent suffix. Erasure preserves this same transcript and result. -/
theorem SyncCanonicalResult.positionalConsumes {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (r : SyncCanonicalResult K current invocation root b post) :
    let ctx := writerContext root.sevm invocation
    let frame0 := syncSourceLockedFrame current ctx
    let frame1 := syncSourceSecondFrame current ctx
    let request0 := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    let request1 := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
    let sourceFrame := syncSourceUpdatedFrame (frame1.beginResume request1)
      r.sourcePost r.event r.oracle
    PositionalConsumes root root 0 (startTyped current ctx .sync)
      (.next (syncExternalReply r.out0) (staticViewTranscript r.views0 .done)
        (.next (syncExternalReply r.out1) (staticViewTranscript r.views1 .done) .done))
      {status := .success [], frame := sourceFrame, remaining := .done,
        childReturns := staticViewChildReturns frame0 request0 0 r.views0 ++
          staticViewChildReturns frame1 request1 0 r.views1} := by
  dsimp only
  let ctx := writerContext root.sevm invocation
  let frame0 := syncSourceLockedFrame current ctx
  let frame1 := syncSourceSecondFrame current ctx
  let request0 := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
  let request1 := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
  obtain ⟨observed0, call0, paths0⟩ := r.firstSourceCall
  obtain ⟨observed1, call1, paths1⟩ := r.secondSourceCall
  obtain ⟨value, nonstatic, unlocked, _, updated, _, _, authentic0, authentic1,
    turns0, turns1, _⟩ := r.sourceEffects
  have during0 : PositionalTurns frame0 request0 observed0.paths
      (staticViewTranscript r.views0 .done)
      {complete := true, frame := frame0,
        childReturns := staticViewChildReturns frame0 request0 0 r.views0} := by
    rw [paths0]
    exact .staticViews r.views0 r.mapped.1 authentic0 turns0
  have during1 : PositionalTurns frame1 request1 observed1.paths
      (staticViewTranscript r.views1 .done)
      {complete := true, frame := frame1,
        childReturns := staticViewChildReturns frame1 request1 0 r.views1} := by
    rw [paths1]
    exact .staticViews r.views1 r.mapped.2 authentic1 turns1
  have resumed0 :
      resumeSegment frame0 request0 (.syncBalance0 current.state.cachedReserves)
        (syncExternalReply r.out0) =
        .suspended frame1 request1
          (.syncBalance1 current.state.cachedReserves (Bytes.toB256 (r.out0.take 32))) :=
    sync_resumeBalance0 rfl rfl r.widths.1
  have resumed1 :
      resumeSegment frame1 request1
        (.syncBalance1 current.state.cachedReserves (Bytes.toB256 (r.out0.take 32)))
        (syncExternalReply r.out1) =
        .finished (syncSourceUpdatedFrame (frame1.beginResume request1)
          r.sourcePost r.event r.oracle) [] :=
    sync_resumeBalance1 rfl rfl r.widths.2.2.1 updated
  have terminal : PositionalConsumes root r.returned1 2
      (.finished (syncSourceUpdatedFrame (frame1.beginResume request1)
        r.sourcePost r.event r.oracle) []) .done
      {status := .success [],
        frame := syncSourceUpdatedFrame (frame1.beginResume request1)
          r.sourcePost r.event r.oracle,
        remaining := .done, childReturns := []} :=
    .finished _ [] r.finalNoExec
  rw [← resumed1] at terminal
  have second := PositionalConsumes.nextCall (start := r.returned0)
    (continuation := .syncBalance1 current.state.cachedReserves
      (Bytes.toB256 (r.out0.take 32))) observed1
    (by rw [call1]; exact r.occurrenceSteps_ordered.2)
    (by rfl)
    (by intro absent; cases absent)
    during1 (by simpa only [call1, SyncCanonicalResult.secondOccurrenceStep, syncExternalReply, ite_true] using terminal)
  rw [← resumed0] at second
  have first := PositionalConsumes.nextCall (start := root)
    (continuation := .syncBalance0 current.state.cachedReserves) observed0
    (by rw [call0]; exact r.occurrenceSteps_ordered.1)
    (by rfl)
    (by intro absent; cases absent)
    during0 (by simpa only [call0, SyncCanonicalResult.firstOccurrenceStep, syncExternalReply, ite_true] using second)
  rw [sync_startTyped_suspended value nonstatic unlocked]
  simpa only [List.append_nil, syncExternalReply, frame0, frame1, request0, request1, ctx] using first

end Blanc.Lift.UniswapV2Pair
