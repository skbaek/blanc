import Blanc.Lift.UniswapV2Pair.MintPositionalCalls
import Blanc.Lift.UniswapV2Pair.SourceStaticSlotViews

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Complete actual-slot queues belong to these three particular Mint source requests. -/
structure MintPositionalQueues {root : Exec.Deriv} {b : Devm} (current : Checkpoint)
    (invocation : List Nat) (r : MintRootCallPositions root b) where
  call0 : SourceCallAt root
    (mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
    (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget))
    (feeObservedResult r.out0) 0
  call1 : SourceCallAt root
    ((mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).beginResume
      (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)))
    (requestFor .mintBalance1 current.state.token1 (.balanceOf root.sevm.currentTarget))
    (feeObservedResult r.out1) 1
  callF : SourceCallAt root
    (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr)
    (requestFor .mintFeeTo current.state.factory .feeTo) (feeObservedResult r.fee.out) 2
  same0 : call0.call = r.first.call
  same1 : call1.call = r.second.call
  sameF : callF.call = r.fee.occurrence.call
  views0 : List StaticViewTurn
  views1 : List StaticViewTurn
  viewsF : List StaticViewTurn
  during0 : PositionalTurns (mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr) (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)) call0.paths
    (staticViewTranscript views0 .done)
    {complete := true, frame := (mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr),
      childReturns := staticViewChildReturns (mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr) (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget)) 0 views0}
  during1 : PositionalTurns ((mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).beginResume (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget))) (requestFor .mintBalance1 current.state.token1 (.balanceOf root.sevm.currentTarget)) call1.paths
    (staticViewTranscript views1 .done)
    {complete := true, frame := ((mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).beginResume (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget))),
      childReturns := staticViewChildReturns ((mintSourceLockedFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr).beginResume (requestFor .mintBalance0 current.state.token0 (.balanceOf root.sevm.currentTarget))) (requestFor .mintBalance1 current.state.token1 (.balanceOf root.sevm.currentTarget)) 0 views1}
  duringF : PositionalTurns (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr) (requestFor .mintFeeTo current.state.factory .feeTo) callF.paths
    (staticViewTranscript viewsF .done)
    {complete := true, frame := (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr),
      childReturns := staticViewChildReturns (mintSourceFeeFrame current (writerContext root.sevm invocation) (Sevm.dataWord root.sevm 4).toAdr) (requestFor .mintFeeTo current.state.factory .feeTo) 0 viewsF}

/-- Original Mint calls supply complete source queues, including the .none case.
Root freshness is an internal trace obligation, not a guessed child-queue premise. -/
theorem mint_positional_queues {sevm : Sevm} {b post : Devm} {G : Nat}
    {K : WriterKey → Prop} {current : Checkpoint}
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (r : MintRootCallPositions ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (invocation : List Nat) (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (fresh : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm)) :
    Nonempty (MintPositionalQueues current invocation r) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  let ctx := writerContext sevm invocation
  let recipient := (Sevm.dataWord sevm 4).toAdr
  let frame0 := mintSourceLockedFrame current ctx recipient
  let frame1 := frame0.beginResume (requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair))
  let frameF := mintSourceFeeFrame current ctx recipient
  let request0 := requestFor .mintBalance0 current.state.token0 (.balanceOf ctx.pair)
  let request1 := requestFor .mintBalance1 current.state.token1 (.balanceOf ctx.pair)
  let requestF := requestFor .mintFeeTo current.state.factory .feeTo
  have rootInstalled : some (root.devm.getCode sevm.currentTarget).toList = sem.image := by
    simpa only [root, St, Devm.getCode_setMach] using installed
  have nonempty : (root.devm.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (rootInstalled.symm.trans (congrArg some empty)) rfl
  have installed0 : some (r.first.call.occurrence.node.devm.getCode sevm.currentTarget).toList = sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.first.call.sameFrame).2 sevm.currentTarget nonempty]
    exact rootInstalled
  have installed1 : some (r.second.call.occurrence.node.devm.getCode sevm.currentTarget).toList = sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.second.call.sameFrame).2 sevm.currentTarget nonempty]
    exact rootInstalled
  have installedF : some (r.fee.occurrence.call.occurrence.node.devm.getCode sevm.currentTarget).toList = sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.fee.occurrence.call.sameFrame).2 sevm.currentTarget nonempty]
    exact rootInstalled
  have state0 : r.first.call.occurrence.node.devm.state = (mintRootFirstWorld root b).state := by
    rw [r.first.input]
    exact Devm.setMach_state _ _
  have state1 : r.second.call.occurrence.node.devm.state = (mintRootSecondWorld r.first).state := by
    rw [r.second.input]
    exact Devm.setMach_state _ _
  have stateF : r.fee.occurrence.call.occurrence.node.devm.state =
      (feeFactoryCallWorld r.second.call.returned.sevm r.second.call.returned.devm).state := by
    rw [r.fee.occurrence.input]
    exact Devm.setMach_state _ _
  have rep0 : WriterRep K (r.first.call.occurrence.node.devm.getStor sevm.currentTarget)
      {current.state with unlocked := 0} := by
    rw [getStor_eq_of_state_eq state0, ← r.post0.stor, r.first_storage]
    exact rep.mint_locked_world
  have rep1 : WriterRep K (r.second.call.occurrence.node.devm.getStor sevm.currentTarget)
      {current.state with unlocked := 0} := by
    rw [getStor_eq_of_state_eq state1, ← r.post1.stor, r.second_storage]
    exact rep.mint_locked_world
  have env0 := r.first.returned_sevm
  have env1 := r.second.returned_sevm.trans env0
  have actualReply := r.fee.reply
  simp only [env1] at actualReply
  have feePostRep := (r.fee_entry_rep rep).fee_factory_post actualReply
  rw [feeKLastWorld, afterSload_getStor] at feePostRep
  have repF : WriterRep K (r.fee.occurrence.call.occurrence.node.devm.getStor sevm.currentTarget)
      {current.state with unlocked := 0} := by
    rw [getStor_eq_of_state_eq stateF, ← r.fee.reply.stor]
    exact feePostRep
  obtain ⟨paths0, views0, queue0, mapped0, auth0, turns0⟩ :=
    CallOccurrenceStep.staticSlotViews r.first.call (frame := frame0) (request := request0) 0 sem image installed0 rep0
      (by rw [r.first.sevm_eq]; rfl) (by rw [r.first.sevm_eq]; exact fork) fresh
  obtain ⟨paths1, views1, queue1, mapped1, auth1, turns1⟩ :=
    CallOccurrenceStep.staticSlotViews r.second.call (frame := frame1) (request := request1) 1 sem image installed1 rep1
      (by rw [r.second.sevm_eq, env0]; rfl) (by rw [r.second.sevm_eq, env0]; exact fork) fresh
  obtain ⟨pathsF, viewsF, queueF, mappedF, authF, turnsF⟩ :=
    CallOccurrenceStep.staticSlotViews r.fee.occurrence.call (frame := frameF) (request := requestF) 2 sem image installedF repF
      (by rw [r.fee.occurrence.sevm_eq, env1]; rfl)
      (by rw [r.fee.occurrence.sevm_eq, env1]; exact fork) fresh
  obtain ⟨call0, same0, pathsEq0⟩ := r.firstSourceCall rep invocation fork queue0
  obtain ⟨call1, same1, pathsEq1⟩ := r.secondSourceCall rep invocation fork queue1
  obtain ⟨callF, sameF, pathsEqF⟩ := r.feeSourceCall rep invocation fork queueF
  refine ⟨⟨call0, call1, callF, same0, same1, sameF, views0, views1, viewsF, ?_, ?_, ?_⟩⟩
  · rw [pathsEq0]
    exact .staticViews views0 mapped0 auth0 turns0
  · rw [pathsEq1]
    exact .staticViews views1 mapped1 auth1 turns1
  · rw [pathsEqF]
    exact .staticViews viewsF mappedF authF turnsF

end Blanc.Lift.UniswapV2Pair
