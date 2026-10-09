import Blanc.Lift.UniswapV2Pair.SwapPositionalMutableCallback
import Blanc.Lift.UniswapV2Pair.StaticSourceCall
import Blanc.Lift.UniswapV2Pair.SourceStaticSlotViews
import Blanc.Lift.UniswapV2Pair.SourceSlotQueueEquality

/-! Both balance requests retain their same actual STATICCALL and full static views. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The supplied balance occurrence determines its guarded source request,
full actual bytes and complete original slot queue. -/
theorem SwapBalanceOccurrence.sourceCall {root start : Exec.Deriv} {b : Devm}
    {S : List B256} {M : Mem} {p token : B256} {second : Bool} {K : List SFunc}
    (r : SwapBalanceOccurrence root start b S M p token second K)
    (frame : Frame) (site : CallSite) (index : Nat)
    (pair : frame.context.pair = start.sevm.currentTarget)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ observed : SourceCallAt root frame
        (requestFor site token.toAdr (.balanceOf frame.context.pair)) (feeObservedResult r.out) index,
      observed.call = r.step := by
  let request := requestFor site token.toAdr (.balanceOf frame.context.pair)
  have target : swapTokenWord token = token.toAdr.toB256 := by
    unfold swapTokenWord
    rw [B256.and_comm]
    exact ff20_and_word token
  have operands : (r.gas.toB256 :: token.toAdr.toB256 :: p :: 36 :: p :: 32 :: []) <<+
      r.step.occurrence.node.devm.stack := by
    rw [r.input]
    simp only [St.stack, target]
    exact pref_append _ _
  have data : (r.step.occurrence.node.devm.memory.read p.toNat 36).1 = request.calldata := by
    rw [r.input]
    simp only [St.memory]
    rw [r.calldata, ← pair]
    rfl
  have flag : [1] <<+ r.step.returned.devm.stack := by
    rw [r.reply.stack]; exact pref_append _ _
  have guarded : (r.step.occurrence.node.devm.getCode request.target).size.toB256 ≠ 0 := by
    rw [r.input]
    change ((temporalAccountAccessBase b (swapTokenWord token).toAdr).getCode token.toAdr).size.toB256 ≠ 0
    rw [Blanc.Lift.temporalAccountAccessBase_getCode]
    simpa only [target, toAdr_toB256] using r.codePresent
  obtain ⟨paths, queue⟩ := CallOccurrenceStep.sourceSlotQueue r.step frame.context.pair index
  obtain ⟨observed, same, _⟩ := static_source_call_at (request := request)
    (reply := feeObservedResult r.out) r.step rfl rfl
    (by intro digest v rr ss impossible; cases impossible) rfl
    (by rw [r.sevmEq]; exact pair) operands data flag rfl r.reply.returnData.symm rfl guarded
    (by rw [r.sevmEq]; exact fork) queue
  exact ⟨observed, same⟩

/-- The exact balance queue has the same static getter results and authentic paths. -/
structure SwapBalanceSource {root start : Exec.Deriv} {b : Devm}
    {S : List B256} {M : Mem} {p token : B256} {second : Bool} {K : List SFunc}
    (r : SwapBalanceOccurrence root start b S M p token second K)
    (U : WriterKey → Prop) (ctx : Context) (current : Checkpoint) (base : Devm)
    (frame : Frame) (site : CallSite) (index : Nat) where
  observed : SourceCallAt root frame
    (requestFor site token.toAdr (.balanceOf frame.context.pair)) (feeObservedResult r.out) index
  same : observed.call = r.step
  views : List StaticViewTurn
  mapped : views.map Prod.fst = observed.paths
  authentic : ∀ picked ∈ views, picked.Authentic frame
  during : ExactTurns frame (requestFor site token.toAdr (.balanceOf frame.context.pair)) 0
    (staticViewTranscript views .done)
    {complete := true, frame := frame, childReturns := staticViewChildReturns frame
      (requestFor site token.toAdr (.balanceOf frame.context.pair)) 0 views}
  invariant : SwapFrontState U root.sevm.currentTarget ctx current base frame r.step.returned.devm

/-- Static view supply and final storage are taken from the SAME original balance slot. -/
theorem swap_balance_source {root start : Exec.Deriv} {b : Devm}
    {S : List B256} {M : Mem} {p token : B256} {second : Bool} {K : List SFunc}
    {U : WriterKey → Prop} {ctx : Context} {current : Checkpoint} {base : Devm} {frame : Frame}
    (r : SwapBalanceOccurrence root start b S M p token second K)
    (site : CallSite) (index : Nat) (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (base.getCode root.sevm.currentTarget).toList = sem.image)
    (inv : SwapFrontState U root.sevm.currentTarget ctx current base frame b)
    (pair : ctx.pair = root.sevm.currentTarget) (time : ctx.timestamp = root.sevm.benvStat.time)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    Nonempty (SwapBalanceSource r U ctx current base frame site index) := by
  have env : start.sevm = root.sevm := r.sevmEq.symm.trans
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.step.sameFrame)
  obtain ⟨observed, same⟩ := r.sourceCall frame site index
    (by rw [inv.context, env]; exact pair) (by rw [env]; exact fork)
  have pairEq : frame.context.pair = root.sevm.currentTarget := inv.context ▸ pair
  have preCode : r.step.occurrence.node.devm.getCode root.sevm.currentTarget =
      base.getCode root.sevm.currentTarget := by
    rw [r.input]
    change (temporalAccountAccessBase b (swapTokenWord token).toAdr).getCode _ = _
    rw [Blanc.Lift.temporalAccountAccessBase_getCode]
    exact inv.code
  obtain ⟨keys, sub, rep, locked⟩ := inv.rep
  have preRep : WriterRep keys (r.step.occurrence.node.devm.getStor frame.context.pair)
      frame.current.state := by
    rw [r.input, pairEq]
    change WriterRep keys ((temporalAccountAccessBase b (swapTokenWord token).toAdr).getStor _)
      frame.current.state
    rw [Blanc.Lift.temporalAccountAccessBase_getStor]
    exact rep
  obtain ⟨paths, views, queue, mapped, authentic, during⟩ :=
    CallOccurrenceStep.staticSlotViews r.step (frame := frame)
      (request := requestFor site token.toAdr (.balanceOf frame.context.pair)) index sem image
      (by rw [pairEq, preCode]; exact installed) preRep
      (by rw [r.sevmEq, env, inv.context]; exact time)
      (by rw [r.sevmEq, env]; exact fork)
      (fun F member target => Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub
        (good F member (target.trans pairEq)))
  have observedQueue := observed.queue
  rw [same] at observedQueue
  have pathsEq := queue.paths_unique observedQueue
  have stor (a : Adr) : r.step.returned.devm.getStor a = b.getStor a := by
    rw [r.reply.stor, Blanc.Lift.temporalAccountAccessBase_getStor]
  have logs : r.step.returned.devm.logs = b.logs := by
    rw [r.reply.logs, temporalAccountAccessBase_logs]
  have output : r.step.returned.devm.output = b.output := by
    rw [r.reply.output rfl, temporalAccountAccessBase_output]
  have nonemptyCode : (r.step.occurrence.node.devm.getCode root.sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (by rw [preCode] at empty; rw [← installed, empty]) rfl
  refine ⟨⟨observed, same, views, mapped.trans pathsEq, authentic, during,
    inv.context, ?_, ?_, output.trans inv.output, ?_, inv.checkpoint⟩⟩
  · rw [stor]; exact inv.rep
  · rw [StepIn.codePreserve r.step.toStepIn _ nonemptyCode, preCode]
  · obtain ⟨added, raw, source, rawEq, images⟩ := inv.logs
    exact ⟨added, raw, source, logs.trans rawEq, images⟩

def swapPhysicalBalanceFrame1 {root : Exec.Deriv} {b : Devm}
    (_r : SwapBalances root root.sevm b) (frame : Frame) : Frame :=
  frame.beginResume (requestFor .swapBalance0 (swapInitialToken0 root.sevm b).toAdr
    (.balanceOf frame.context.pair))

/-- Both complete static queues follow the same post-callback frame and physical
returned-node chain; the second source frame resumes the first exact request. -/
structure SwapBalancePairSource {root : Exec.Deriv} {b : Devm}
    (r : SwapBalances root root.sevm b) (U : WriterKey → Prop) (ctx : Context)
    (current : Checkpoint) (base : Devm) (frame : Frame) (index : Nat) where
  first : SwapBalanceSource r.first U ctx current base frame .swapBalance0 index
  second : SwapBalanceSource r.second U ctx current base
    (swapPhysicalBalanceFrame1 r frame) .swapBalance1 (index + 1)

/-- The two source view queues come from these two supplied physical calls,
with freshness derived from the same finite carried representation. -/
theorem swap_balance_pair_source {root : Exec.Deriv} {b : Devm}
    {U : WriterKey → Prop} {ctx : Context} {current : Checkpoint} {frame : Frame}
    (r : SwapBalances root root.sevm b) (index : Nat)
    (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode root.sevm.currentTarget).toList = sem.image)
    (inv : SwapFrontState U root.sevm.currentTarget ctx current b frame r.optional.callback.world)
    (pair : ctx.pair = root.sevm.currentTarget) (time : ctx.timestamp = root.sevm.benvStat.time)
    (fork : CoveredFork root.sevm.benvStat.fork)
    (good : ∀ F ∈ Exec.rawFrameRoots root.exc,
      F.sevm.currentTarget = root.sevm.currentTarget → ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    Nonempty (SwapBalancePairSource r U ctx current b frame index) := by
  obtain ⟨first⟩ := swap_balance_source r.first .swapBalance0 index inj apart sem image
    installed inv pair time fork good
  obtain ⟨second⟩ := swap_balance_source r.second .swapBalance1 (index + 1) inj apart sem image
    installed (first.invariant.beginResume
      (requestFor .swapBalance0 (swapInitialToken0 root.sevm b).toAdr (.balanceOf frame.context.pair)))
    pair time fork good
  exact ⟨⟨first, second⟩⟩

end Blanc.Lift.UniswapV2Pair
