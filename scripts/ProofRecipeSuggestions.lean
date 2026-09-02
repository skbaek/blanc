import Blanc.ProofRecipeTactic
import Blanc.ForwardCall
import Blanc.RootedExecution
import Blanc.MessageExecution
import Blanc.ExecutionTerminal
import Blanc.ExecutionNoninterference
import Blanc.LinearDispatchCorrectness
import Blanc.ExecutionHistoryStateTrace

namespace Blanc

open Jaune

set_option linter.unusedTactic false

-- EXPECT: runcompiled-construction
example {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func}
    (run : Func.RunCompiled fs sevm pre f post) :
    Func.RunCompiled fs sevm pre f post := by
  blanc_suggest
  exact run

-- EXPECT: runcompiled-construction
example {fs : List Func} {sevm : Sevm} {pre : Devm} {f : Func}
    {out : Execution} (run : Func.RunCompiledTo fs sevm pre f out) :
    Func.RunCompiledTo fs sevm pre f out := by
  blanc_suggest
  exact run

-- EXPECT: linear-dispatch-selection
example {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {fallback : Nat} {entries : List (B256 × Func)} {selector : B256}
    {tail : Stack} {body : Func}
    (unique : selectorUnique entries) (member : (selector, body) ∈ entries)
    (stack : pre.stack = selector :: tail) :
    Func.RunCompiledTo fs sevm pre
      (Blanc.linearDispatchWith fallback entries) out →
      DispatchBodyWitness fs sevm pre entries selector tail body out := by
  blanc_suggest
  intro run
  exact dispatchBodyWitness_of_runCompiledTo unique member stack run

-- EXPECT: linear-dispatch-selection
example {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {fallback : Nat} {entries : List (B256 × Func)} {selector : B256}
    {tail : Stack}
    (nonempty : entries ≠ [])
    (miss : ∀ candidate ∈ entries, candidate.1 ≠ selector)
    (stack : pre.stack = selector :: tail) :
    Func.RunCompiledTo fs sevm pre
      (Blanc.linearDispatchWith fallback entries) out →
      DispatchFallbackWitness fs sevm pre entries selector tail fallback out := by
  blanc_suggest
  intro run
  exact dispatchFallbackWitness_of_runCompiledTo nonempty miss stack run

-- EXPECT: line-run-split
example {sevm : Sevm} {pre post : Devm} {line : Line} :
    Line.Run sevm pre line post → True := by
  blanc_suggest
  intro _
  trivial

-- EXPECT: func-run-prefix-split
example {fs : List Func} {sevm : Sevm} {pre post : Devm} {f : Func} :
    Func.Run fs sevm pre f post → True := by
  blanc_suggest
  intro _
  trivial

-- EXPECT: function-observation-invariance
example {f : Func} (inv : Func.Inv Devm.getBal Devm.getBal f) :
    Func.Inv Devm.getBal Devm.getBal f := by
  blanc_suggest
  exact inv

-- EXPECT: function-observation-invariance
example (inv : Linst.Inv Devm.getCode Devm.getCode Linst.stop) :
    Linst.Inv Devm.getCode Devm.getCode Linst.stop := by
  blanc_suggest
  exact inv

-- EXPECT: successor-projection-normalization
example (devm : Devm) (mach : Mach) (address : Adr) (key : B256) :
    (devm.setMach mach).getStorVal address key = devm.getStorVal address key := by
  blanc_suggest
  rfl

-- EXPECT: devm-projection-bridge
example (devm : Devm) (mach : Mach) :
    (devm.setMach mach).refundCounter = devm.refundCounter := by
  blanc_suggest
  rfl

-- EXPECT: devm-projection-bridge
example (devm : Devm) (mach : Mach) : (devm.setMach mach).mach = mach := by
  blanc_suggest
  rfl

-- EXPECT: devm-projection-bridge
example (devm : Devm) (output : Bytes) :
    (devm.withOutput output).refundCounter = devm.refundCounter := by
  blanc_suggest
  rfl

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize = 1 := by
  blanc_suggest
  decide

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize ≠ 0 := by
  blanc_suggest
  decide

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize ≤ 1 := by
  blanc_suggest
  decide

-- EXPECT: bytesize-composition
example : Func.stop.compileShape.byteSize < 2 := by
  blanc_suggest
  decide

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (f : Func) : f.compileShape.byteSize = f.compileShape.byteSize := by
  blanc_suggest
  rfl

-- EXPECT: shared-subject-kernel-decision
example :
    let subject := ([1, 2, 3] : List Nat)
    (subject.length, subject.reverse.length) = (3, 3) := by
  blanc_suggest
  decide

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (devm : Devm) (output : Bytes) :
    (devm.withOutput output).pop = (devm.withOutput output).pop := by
  blanc_suggest
  rfl

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (proposition : Prop) (proof : proposition) : proposition := by
  blanc_suggest
  exact proof

-- EXPECT: frame-root-carrying-execution
example {P : Exec.Deriv → Prop} {fs : List Func} {sevm : Sevm}
    {pre : Devm} {f : Func} {out : Execution}
    {run : Func.RunCompiledTo fs sevm pre f out}
    (rooted : rootedRunCompiledTo P run) : rootedRunCompiledTo P run := by
  blanc_suggest
  exact rooted

-- EXPECT: retained-write-noninterference
example {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (owner : Adr) (key : B256)
    (notCommitted : Execution.commits out ≠ true) :
    Exec.NoRetainedWriteTo run owner key := by
  blanc_suggest
  exact Exec.noRetainedWriteTo_of_not_commits run notCommitted owner key

-- EXPECT: message-execution-settlement
example (msg : Msg)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true) :
    processMessage msg =
      (Frame.ofCall msg).settle (exec (initEvm msg)) := by
  blanc_suggest
  exact MessageExecution.processMessage_eq_settle_exec msg hentry hdisable

-- EXPECT: devm-common-update-laws
example (devm : Devm) (index : Nat) (value : Bytes) :
    (devm.memWrite index value).memory = devm.memory.write index value := by
  blanc_suggest
  exact Devm.memWrite_memory devm index value

-- EXPECT: compiled-terminal-at-zero
example {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Func.RunCompiledTo fs sevm pre (Func.last .return_) out) :
    Func.RunCompiledTo fs sevm pre (Func.last .return_) out := by
  blanc_suggest
  exact run

-- EXPECT: full-length-slice
example {bytes : Bytes} {size : Nat} (h : bytes.length = size) :
    bytes.sliceD 0 size 0 = bytes := by
  blanc_suggest
  exact Bytes.sliceD_zero_length h

-- EXPECT: retained-wrapper-trace
example {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : Nonempty (ExecutionTrace.MessageCallTrace msg state out)) :
    Nonempty (ExecutionTrace.MessageCallTrace msg state out) := by
  blanc_suggest
  exact trace

-- EXPECT: retained-state-replay
example {Origin : Type} {pre post : State}
    {events : List (StateTransition Origin)}
    (replay : StateReplay pre events post) : StateReplay pre events post := by
  blanc_suggest
  exact replay

-- EXPECT: one-word-source-return
example (word : B256) (devm : Devm) (observed : ReturnsWord word devm) :
    ReturnsWord word devm := by
  blanc_suggest
  exact observed

end Blanc
