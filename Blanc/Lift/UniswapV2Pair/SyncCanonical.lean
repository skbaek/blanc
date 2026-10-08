import Blanc.Lift.CursorExact
import Blanc.Lift.UniswapV2Pair.SyncTurns

/-! Canonical same-witness Sync source-frame consumer. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- Decoded finite rows of the actually entered static Pair roots. -/
def syncTraceKeys (root : Exec.Deriv) : List WriterKey :=
  (Exec.rawFrameRoots root.exc).flatMap fun F =>
    if F.sevm.currentTarget = root.sevm.currentTarget ∧ F.sevm.isStatic = true
    then staticViewDecodedKeys F.sevm else []

theorem syncTraceKeys_contains {root : Exec.Deriv} {F : Exec.Deriv}
    (member : F ∈ Exec.rawFrameRoots root.exc)
    (target : F.sevm.currentTarget = root.sevm.currentTarget)
    (static : F.sevm.isStatic = true) :
    ∀ k ∈ staticViewDecodedKeys F.sevm, k ∈ syncTraceKeys root := by
  intro k touched
  apply List.mem_flatMap.mpr
  refine ⟨F, member, ?_⟩
  rw [ite_eq_left ⟨target, static⟩]
  exact touched

theorem syncTraceKeys_fresh {K : WriterKey → Prop} {root : Exec.Deriv}
    (injective : WriterInj (WriterExtend K (syncTraceKeys root)))
    (apart : WriterApart (WriterExtend K (syncTraceKeys root))) :
    ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → F.sevm.isStatic = true →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm) := by
  intro F member target static
  exact Blanc.SlotFootprint.FreshKeys.of_universe injective apart
    (fun _ tracked => Or.inl tracked)
    (fun k touched => Or.inr (syncTraceKeys_contains member target static k touched))

/-- Same-witness successful Sync frame result for the canonical history consumer. -/
structure SyncCanonicalResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  first : Exec.NinstOccurrence root
  returned0 : Exec.Deriv
  second : Exec.NinstOccurrence root
  returned1 : Exec.Deriv
  out0 : Bytes
  out1 : Bytes
  views0 : List StaticViewTurn
  views1 : List StaticViewTurn
  paths0 : List Exec.LocatedFrame
  paths1 : List Exec.LocatedFrame
  childFrames0 : List Exec.LocatedFrame
  childFrames1 : List Exec.LocatedFrame
  sourcePost : State
  event : Event
  oracle : OracleUpdate
  /-- The accepted code guards refer to the actual original target code at each call. -/
  guarded0 : (first.node.devm.getCode current.state.token0).size.toB256 ≠ 0
  guarded1 : (second.node.devm.getCode current.state.token1).size.toB256 ≠ 0
  /-- The actual returned parent has no further external instruction. -/
  finalNoExec : ∀ N, Exec.Deriv.ParentPrefix returned1 N →
    ∀ x, ¬Ninst.At N.sevm.code N.pc (.exec x)
  order :
    Exec.Deriv.ExecFreeUntil root first.node ∧
    first.node.pc = 0x1ee0 ∧ first.node.sevm = root.sevm ∧
    first.instruction = Ninst.staticcall ∧
    Exec.Deriv.ParentStep returned0 first.node ∧
    first.stepResult = .ok returned0.devm ∧
    Exec.Deriv.ExecFreeUntil returned0 second.node ∧
    Exec.Deriv.ParentPrefix root second.node ∧
    second.node.pc = 0x1f7d ∧ second.node.sevm = root.sevm ∧
    second.node.exn = .ok post ∧ second.instruction = Ninst.staticcall ∧
    Exec.Deriv.ParentStep returned1 second.node ∧
    second.stepResult = .ok returned1.devm ∧
    returned1.pc = 0x1f7e ∧ returned1.sevm = root.sevm ∧
    returned1.exn = .ok post
  firstCall :
    let ctx := writerContext root.sevm invocation
    let request := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    ∃ (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256),
      let msg := callMsg root.sevm parent (min g.toNat (except64th avail)) 0
        ctx.pair current.state.token0 na true true request.calldata childCode dp
      Xlot.Filled first.slot ∧
      ProcessMessage msg first.slot (.ok child) ∧
      child.error.isSome = false ∧ child.output = out0 ∧
      returned0.devm.returnData = out0 ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned0.devm ∧
      ((getDelegatedCodeAddress (first.node.devm.getCode current.state.token0) = none ∧
          na = current.state.token0 ∧
          childCode = first.node.devm.getCode current.state.token0 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (first.node.devm.getCode current.state.token0) = some d ∧
          na = d ∧ childCode = first.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨first.node.pc, first.node.sevm, first.node.devm⟩ =
        .spawn (Frame.ofCall msg) (Resume.call parent 128 32) (first.node.pc + 1) ∧
      ((first.slot = .none ∧ paths0 = [] ∧ views0 = []) ∨
        ∃ (childEvm : Evm) (raw : Execution) (callee : Jaune.Frame)
          (resume : Resume) (pc' : Nat)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec pc' first.node.sevm returned0.devm first.node.exn)
          (spawn : Evm.step ⟨first.node.pc, first.node.sevm, first.node.devm⟩ =
            .spawn callee resume pc')
          (enter : callee.enter = .run childEvm)
          (resumed : resume.run (callee.settle raw) = .ok returned0.devm),
          first.slot = .some ⟨childEvm, raw⟩ ∧
          first.node.exc = .runOk spawn enter childRun resumed next ∧
          paths0 = (if Jaune.Frame.settlementCommits callee raw = true then
            (Exec.retainedTargetTurnsAt ctx.pair [0] childRun).filterMap Sum.getRight?
          else []))
  secondCall :
    let ctx := writerContext root.sevm invocation
    let request := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
    ∃ (parent child : Devm) (dp : Bool) (na : Adr)
      (childCode : ByteArray) (avail : Nat) (g : B256),
      let msg := callMsg root.sevm parent (min g.toNat (except64th avail)) 0
        ctx.pair current.state.token1 na true true request.calldata childCode dp
      Xlot.Filled second.slot ∧
      ProcessMessage msg second.slot (.ok child) ∧
      child.error.isSome = false ∧ child.output = out1 ∧
      returned1.devm.returnData = out1 ∧
      (Resume.call parent 128 32).run (.ok child) = .ok returned1.devm ∧
      ((getDelegatedCodeAddress (second.node.devm.getCode current.state.token1) = none ∧
          na = current.state.token1 ∧
          childCode = second.node.devm.getCode current.state.token1 ∧ dp = false) ∨
        (∃ d, getDelegatedCodeAddress (second.node.devm.getCode current.state.token1) = some d ∧
          na = d ∧ childCode = second.node.devm.getCode d ∧ dp = true)) ∧
      Evm.step ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
        .spawn (Frame.ofCall msg) (Resume.call parent 128 32) (second.node.pc + 1) ∧
      ((second.slot = .none ∧ paths1 = [] ∧ views1 = []) ∨
        ∃ (childEvm : Evm) (raw : Execution)
          (childRun : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
          (next : Exec (second.node.pc + 1) second.node.sevm returned1.devm second.node.exn)
          (spawn : Evm.step ⟨second.node.pc, second.node.sevm, second.node.devm⟩ =
            .spawn (Frame.ofCall msg) (Resume.call parent 128 32) (second.node.pc + 1))
          (enter : (Frame.ofCall msg).enter = .run childEvm)
          (resumed : (Resume.call parent 128 32).run ((Frame.ofCall msg).settle raw) =
            .ok returned1.devm),
          second.slot = .some ⟨childEvm, raw⟩ ∧
          second.node.exc = .runOk spawn enter childRun resumed next ∧
          paths1 = (if Jaune.Frame.settlementCommits (Frame.ofCall msg) raw = true then
            (Exec.retainedTargetTurnsAt ctx.pair [1] childRun).filterMap Sum.getRight?
          else []))
  mapped : views0.map Prod.fst = paths0 ∧ views1.map Prod.fst = paths1
  rawPartition :
    Exec.descendantFramePaths [] 0 root.exc = childFrames0 ++ childFrames1 ∧
    Exec.descendantFramePaths [] 0 first.node.exc =
      childFrames0 ++ Exec.descendantFramePaths [] 1 returned0.exc ∧
    Exec.descendantFramePaths [] 1 second.node.exc =
      childFrames1 ++ Exec.descendantFramePaths [] 2 returned1.exc ∧
    Exec.descendantFramePaths [] 2 returned1.exc = []
  widths : 32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
    32 ≤ out1.length ∧ out1.length < 2 ^ 256
  sourceEffects :
    let ctx := writerContext root.sevm invocation
    let balance0 := Bytes.toB256 (out0.take 32)
    let balance1 := Bytes.toB256 (out1.take 32)
    let frame0 := syncSourceLockedFrame current ctx
    let frame1 := syncSourceSecondFrame current ctx
    let request0 := requestFor .syncBalance0 current.state.token0 (.balanceOf ctx.pair)
    let request1 := requestFor .syncBalance1 current.state.token1 (.balanceOf ctx.pair)
    let sourceFrame := syncSourceUpdatedFrame (frame1.beginResume request1)
      sourcePost event oracle
    ctx.value = 0 ∧ ctx.isStatic = false ∧ current.state.unlocked = 1 ∧
    current.state.update ctx balance0 balance1 current.state.reserve0.val
      current.state.reserve1.val = .ok ({sourcePost with unlocked := 1}, event, oracle) ∧
    frame1.current.state.update ctx balance0 balance1 current.state.reserve0.val
      current.state.reserve1.val = .ok (sourcePost, event, oracle) ∧
    WriterRep K (post.getStor ctx.pair) {sourcePost with unlocked := 1} ∧
    event = .sync balance0.toNat balance1.toNat ∧
    (∀ picked ∈ views0, picked.Authentic frame0) ∧
    (∀ picked ∈ views1, picked.Authentic frame1) ∧
    ExactTurns frame0 request0 0 (staticViewTranscript views0 .done)
      {complete := true, frame := frame0,
        childReturns := staticViewChildReturns frame0 request0 0 views0} ∧
    ExactTurns frame1 request1 0 (staticViewTranscript views1 .done)
      {complete := true, frame := frame1,
        childReturns := staticViewChildReturns frame1 request1 0 views1} ∧
    sourceFrame.checkpoint = current ∧ sourceFrame.context = ctx ∧
    sourceFrame.current =
      {state := {sourcePost with unlocked := 1},
        logs := current.logs ++ [.owned ⟨ctx.invocation,2,some .syncBalance1⟩ event],
        updates := current.updates ++ [⟨⟨ctx.invocation,2,some .syncBalance1⟩,oracle⟩]} ∧
    ExactConsumes (startTyped current ctx .sync)
      (.next (syncExternalReply out0) (staticViewTranscript views0 .done)
        (.next (syncExternalReply out1) (staticViewTranscript views1 .done) .done))
      {status := .success [], frame := sourceFrame, remaining := .done,
        childReturns := staticViewChildReturns frame0 request0 0 views0 ++
          staticViewChildReturns frame1 request1 0 views1}
  logs : post.logs = b.logs ++
    [⟨(writerContext root.sevm invocation).pair, [updateSyncTopic],
      encodeWords [Bytes.toB256 (out0.take 32), Bytes.toB256 (out1.take 32)]⟩]
  outputPreserved : post.output = b.output

/-- Canonical Sync consumer under separation of its actual finite trace footprint. -/
theorem sync_canonical_source_frame_result {K : WriterKey → Prop}
    {current : Checkpoint} {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xfff6cae9)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (syncTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (syncTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (SyncCanonicalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  let ctx := writerContext sevm invocation
  have fresh := syncTraceKeys_fresh (root := root) hashTInj hashTApart
  have richResult :=
    sync_root_second_static_parent_exact_consumption (K := K) (current := current)
      (ctx := ctx) (sevm := sevm) (b := b) (post := post) (G := G)
      rfl rep sem image installed rfl codeEq fork selector run rfl rfl fresh
  obtain ⟨occurrence, returned, _, _, parent, child, dp, na, childCode, avail, g, _, out, original,
    afterFirst⟩ := richResult
  obtain ⟨_, _, _, _, _, _, _, _, _, _, long, _, _, _, _, _, _, secondPacket⟩ := afterFirst
  obtain ⟨second, secondReturned, _, g1, _, returnedSecondFree, secondPath, secondPc, secondSevm,
    secondOutcome, secondInstruction, _, _, _, _, _, _, secondFilled, secondEdge,
    secondReturnedPc, secondReturnedSevm, secondReturnedOutcome, secondResult, _, _, _, _, _,
    secondReply⟩ := secondPacket
  obtain ⟨_, _, parent1, child1, dp1, na1, childCode1, avail1, out1, _, _, _, _, _, _, _, _, _,
    outBound1, _, secondReturnedData, childOutput1, clean1, _, _, _, _, _, _, _, authentication1,
    actualProcess1, resumed1, _, _, _, actualSpawn1, _, _, _, _, _, _, finalDecoded⟩ := secondReply
  obtain ⟨_, _, _, _, _, _, _, _, _, _, long1, _, _, _, _, _, _, _, _, _, _, _, _, _, secondGuarded, _, _, _, finished⟩ := finalDecoded
  obtain ⟨_, _, _, sourcePost, event, oracle, childFrames0, childFrames1, actualViews0, actualViews1, _,
    contextValue, contextStatic, unlocked, source, lockedSource, _, finalRep, eventEq, _, _, _,
    allFrames, cut0, cut1, noRemainder, authentic0, authentic1, turns0, turns1, checkpoint,
    context, sourceState, consumed, originalLogs, originalOutput, paths0, paths1, mapped0,
    mapped1, branch0, branch1, finalNoExec⟩ := finished
  have firstCore := original.1
  obtain ⟨⟨firstFree, firstPc, firstSevm, firstInstruction, firstEdge, firstResult,
    firstPrimitive, firstReturnedFree, firstReturnedPc, firstNodePath, firstNodePc,
    firstNodeSevm, firstOutcome, firstTree, firstK, firstOk, firstRep, firstMemory,
    firstStack, firstCalldata, hpost0, outBound0, firstReturnedData, childOutput0, childClean0,
    firstFilled, firstProcess, firstResume, firstAuthentication, firstSpawn⟩,
    firstInstalled, rootPaths, firstFold⟩ := firstCore
  obtain ⟨guardedOccurrence, _, guardedFree, _, _, _, guardedInstruction,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, firstGuarded⟩ :=
    sync_root_first_static_occurrence_request_parent codeEq fork selector run
  have sameFirst : guardedOccurrence.node = occurrence.node :=
    Blanc.Exec.Deriv.ExecFreeUntil.eq_of_execAt guardedFree firstFree
      (guardedInstruction ▸ guardedOccurrence.decoded) (firstInstruction ▸ occurrence.decoded)
  have initialRep : WriterRep K (b.getStor sevm.currentTarget) current.state := rep
  have token0 : (b.getStorVal sevm.currentTarget 6).toAdr = current.state.token0 :=
    initialRep.fixed.2.2.2.1
  have guarded0 : (occurrence.node.devm.getCode current.state.token0).size.toB256 ≠ 0 := by
    rw [← sameFirst, ← token0]
    exact firstGuarded
  exact ⟨{
    first := occurrence
    returned0 := returned
    second := second
    returned1 := secondReturned
    out0 := out
    out1 := out1
    views0 := actualViews0
    views1 := actualViews1
    paths0 := paths0
    paths1 := paths1
    childFrames0 := childFrames0
    childFrames1 := childFrames1
    sourcePost := sourcePost
    event := event
    oracle := oracle
    guarded0 := guarded0
    guarded1 := secondGuarded
    finalNoExec := finalNoExec
    order := ⟨firstFree, firstPc, firstSevm, firstInstruction, firstEdge, firstResult,
      returnedSecondFree, secondPath, secondPc, secondSevm, secondOutcome,
      secondInstruction, secondEdge, secondResult, secondReturnedPc,
      secondReturnedSevm, secondReturnedOutcome⟩
    firstCall := ⟨parent, child, dp, na, childCode, avail, g, firstFilled,
      firstProcess, childClean0, childOutput0, firstReturnedData, firstResume,
      firstAuthentication, firstSpawn, branch0⟩
    secondCall := ⟨parent1, child1, dp1, na1, childCode1, avail1, g1, secondFilled,
      actualProcess1, clean1, childOutput1, secondReturnedData, resumed1,
      authentication1, actualSpawn1, branch1⟩
    mapped := ⟨mapped0, mapped1⟩
    rawPartition := ⟨allFrames, cut0, cut1, noRemainder⟩
    widths := ⟨long, outBound0, long1, outBound1⟩
    sourceEffects := ⟨contextValue, contextStatic, unlocked, source, lockedSource,
      finalRep, eventEq, authentic0, authentic1, turns0, turns1, checkpoint,
      context, sourceState, consumed⟩
    logs := originalLogs
    outputPreserved := originalOutput
  }⟩

end Blanc.Lift.UniswapV2Pair
