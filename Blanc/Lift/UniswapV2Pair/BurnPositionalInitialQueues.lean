import Blanc.Lift.UniswapV2Pair.BurnPositionalSource
import Blanc.Lift.UniswapV2Pair.BurnEntrySource
import Blanc.Lift.UniswapV2Pair.SourceStaticSlotViews

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The first Burn source request obtains its complete queue and static views
from the retained original occurrence at the exact locked entry frame. -/
theorem BurnInitialPair.firstViews {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {K : WriterKey → Prop} {current : Checkpoint} (r : BurnInitialPair root sevm b)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (invocation : List Nat) (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (root.devm.getCode sevm.currentTarget).toList = sem.image)
    (fork : CoveredFork sevm.benvStat.fork)
    (fresh : ∀ F ∈ Exec.rawFrameRoots root.exc, F.sevm.currentTarget = sevm.currentTarget →
      WriterFreshKeys K (staticViewDecodedKeys F.sevm)) :
    let frame := burnSourceLockedFrame current (writerContext sevm invocation)
      (Sevm.dataWord sevm 4).toAdr
    let request := requestFor .burnInitialBalance0 current.state.token0 (.balanceOf sevm.currentTarget)
    ∃ (observed : SourceCallAt root frame request (feeObservedResult r.out0) 0)
      (views : List StaticViewTurn), observed.call = r.first ∧
      PositionalTurns frame request observed.paths (staticViewTranscript views .done)
        {complete := true, frame := frame,
          childReturns := staticViewChildReturns frame request 0 views} := by
  let frame := burnSourceLockedFrame current (writerContext sevm invocation)
    (Sevm.dataWord sevm 4).toAdr
  let request := requestFor .burnInitialBalance0 current.state.token0 (.balanceOf sevm.currentTarget)
  have env : r.first.occurrence.node.sevm = sevm :=
    (Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.first.sameFrame).trans
      ((Blanc.Exec.Deriv.ParentPrefix.sevm_eq r.second.sameFrame).symm.trans r.second_sevm)
  have nonempty : (root.devm.getCode sevm.currentTarget).toList ≠ [] := by
    intro empty
    exact sem.ne_nil (installed.symm.trans (congrArg some empty)) rfl
  have actualInstalled : some (r.first.occurrence.node.devm.getCode sevm.currentTarget).toList =
      sem.image := by
    rw [(Blanc.Exec.Deriv.ParentPrefix.balSum_le_getCode r.first.sameFrame).2
      sevm.currentTarget nonempty]
    exact installed
  have inputStorage : r.first.occurrence.node.devm.getStor sevm.currentTarget =
      r.first.returned.devm.getStor sevm.currentTarget := by
    rw [r.first_input, r.first_reply.stor]
    simp only [burnFirstCallInput, St_getStor, burnInitialWorld0, burnInitialToken0]
  have actualRep : WriterRep K (r.first.occurrence.node.devm.getStor frame.context.pair)
      frame.current.state := by
    change WriterRep K (r.first.occurrence.node.devm.getStor sevm.currentTarget)
      {current.state with unlocked := 0}
    rw [inputStorage, r.first_storage]
    exact rep.burn_locked_world
  obtain ⟨paths, views, queue, mapped, authentic, turns⟩ :=
    CallOccurrenceStep.staticSlotViews r.first (frame := frame) (request := request) 0 sem image actualInstalled
      actualRep (by rw [env]; rfl) (by rw [env]; exact fork) fresh
  obtain ⟨observed, same, samePaths⟩ := r.firstSourceCall (frame := frame) rep rfl fork queue
  refine ⟨observed, views, same, ?_⟩
  rw [samePaths]
  exact .staticViews views mapped authentic turns

end Blanc.Lift.UniswapV2Pair
