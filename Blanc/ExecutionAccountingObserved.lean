-- ExecutionAccountingObserved.lean : the observed accounting seams and ladder.
--
-- A contract that reads a retained history as an ordered replay often needs
-- more than the existence of the replay: it needs to know which executed frames
-- the replay's steps came from.  A `ReplayObservation` reads a carrier's step
-- lists homomorphically and says what one settled frame contributes; an
-- `AccountingLadder.Observed` adds the root law that a committed root's replay
-- observes exactly that root's committed frames.  The observed seams and rungs
-- then conclude, next to the replay, that the steps observe exactly the
-- settled frames of the retained trace (`ExecutionTraceSettledFrames`).
--
-- The observed statements are the proofs.  `ReplayObservation` and the
-- engines the unobserved seams project from live in
-- `ExecutionAccountingReplay`; `AccountingLadder.Observed`, its rung twins and
-- the two history headlines live in `ExecutionAccountingLadder`, whose
-- unobserved rungs are those twins read through `Observed.trivial`.  This
-- module adds the account-local seam twins and is the one import a consumer of
-- the observed API needs.

import Blanc.ExecutionAccountingLadder
import Blanc.ExecutionTraceSettledFrames

namespace Blanc

open Jaune

namespace ExecutionAccountingReplay

namespace ReplayCarrier

variable {ca : Adr}

/-- `SettlementCarrier.processMessage_of_body_observed` at an account-local
carrier. -/
theorem processMessage_of_body_observed (C : ReplayCarrier ca)
    (V : ReplayObservation C)
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    {settled : List V.O}
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state) ∧
      V.obs steps = settled) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) ∧
      V.obs steps = if Frame.settlementCommits (Frame.ofCall msg) out = true
        then settled else [] :=
  C.toSettlementCarrier.processMessage_of_body_observed V.obs V.obs_nil
    process caller_ne value_zero sum_nof body

/-- `SettlementCarrier.processCreateMessage_of_body_observed` at an
account-local carrier. -/
theorem processCreateMessage_of_body_observed (C : ReplayCarrier ca)
    (V : ReplayObservation C)
    {msg : Msg} {post : Devm}
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (process : ProcessCreateMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, out⟩) (.ok post))
    (caller_ne : msg.shouldTransferValue = true → msg.caller ≠ ca)
    (value_zero : msg.shouldTransferValue = false →
      msg.currentTarget = ca → msg.value = 0)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty)
    (sum_nof : sum msg.benv.state.bal < 2 ^ 256)
    {settled : List V.O}
    (body : ∀ committed : Execution.commits out = true, ∃ steps,
      C.Replay (C.frameEntry sevm pre.state) steps
        (C.ofState (Execution.committedPost out committed).state) ∧
      V.obs steps = settled) :
    ∃ steps,
      C.Replay (C.ofState msg.benv.state) steps (C.ofState post.state) ∧
      V.obs steps = if Frame.settlementCommits (Frame.ofCreate msg) out = true
        then settled else [] :=
  C.toSettlementCarrier.processCreateMessage_of_body_observed V.obs V.obs_nil
    process caller_ne value_zero fresh sum_nof body

/-- Recursive accounting transport for one actual filled executable slot in a
foreign frame, observed.  The `if` is exactly the child segment of
`Exec.descendantFrames` at a `runOk` spawn: a settling child commits, and its
committed frames are its own frame followed by its descendants. -/
theorem xinstForeignSome_observed (C : ReplayCarrier ca)
    (V : ReplayObservation C)
    {sevm : Sevm} {pre post : Devm} {x : Xinst}
    {frame : Frame} {resume : Resume}
    {cevm : Evm} {raw : Execution} {settled : Devm}
    (spawn : Xinst.step sevm pre x = .spawn frame resume)
    (frameRun : RunFrame frame (.some ⟨cevm, raw⟩) (.ok settled))
    (resumeRun : resume.run (.ok settled) = .ok post)
    (target_ne : sevm.currentTarget ≠ ca)
    (hfork : CoveredFork sevm.benvStat.fork)
    (sum_nof : sum pre.state.bal < 2 ^ 256)
    (child : Exec cevm.pc cevm.sta cevm.dyna raw)
    (body : ∀ childCommitted : Execution.commits raw = true, ∃ steps,
      C.Replay (C.frameEntry cevm.sta cevm.dyna.state) steps
        (C.ofState (Execution.committedPost raw childCommitted).state) ∧
      V.obs steps = (Exec.committedFrames child).flatMap V.frameObs) :
    ∃ steps, C.Replay (C.ofState pre.state) steps (C.ofState post.state) ∧
      V.obs steps = (if Frame.settlementCommits frame raw = true
        then (Exec.committedFrames child).flatMap V.frameObs else []) :=
  C.toSettlementCarrier.xinstForeignSome_observed V.obs V.obs_nil spawn
    frameRun resumeRun target_ne hfork sum_nof body

/-- A transition invisible to this account contributes no step, observed as
nothing. -/
theorem silentReplay_observed (C : ReplayCarrier ca) (V : ReplayObservation C)
    {pre post : State}
    (storage_eq : post.getStor ca = pre.getStor ca)
    (balance_eq : (post.bal ca).toNat = (pre.bal ca).toNat) :
    ∃ steps, C.Replay (C.ofState pre) steps (C.ofState post) ∧
      V.obs steps = [] :=
  ⟨[], C.silentReplay storage_eq balance_eq, V.obs_nil⟩

end ReplayCarrier

end ExecutionAccountingReplay

end Blanc
