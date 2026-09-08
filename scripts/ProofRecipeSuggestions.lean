import Blanc.ProofRecipeTactic
import Blanc.ForwardCall
import Blanc.RootedExecution
import Blanc.MessageExecution
import Blanc.ExecutionTerminal
import Blanc.ExecutionNoninterference
import Blanc.LinearDispatchCorrectness
import Blanc.ExecutionHistoryStateTrace
import Blanc.CompiledShape
import Blanc.CreationArtifact

namespace Blanc

open Jaune

set_option linter.unusedTactic false

elab "expect_recipe_trigger" trigger:str : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  unless ← proofRecipeTriggerMatches target trigger.getString do
    throwError "expected proof-recipe trigger {trigger.getString} to match"

elab "expect_no_recipe_trigger" trigger:str : tactic => do
  let target ← Lean.Elab.Tactic.getMainTarget
  if ← proofRecipeTriggerMatches target trigger.getString then
    throwError "expected proof-recipe trigger {trigger.getString} not to match"

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

-- EXPECT: compiled-shape-byte-navigation
example (locations : List Nat) (n i : Nat) (d : UInt8)
    (leftShape rightShape : Func.CompileShape) (left right : Func) :
    Func.byteAtByShape locations n (.branch leftShape rightShape)
        (.branch left right) i d =
      Func.byteAtByShape locations n (.branch leftShape rightShape)
        (.branch left right) i d := by
  expect_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT: compiled-shape-byte-navigation
example (locations : List Nat) (n i size : Nat) (d : UInt8)
    (restShape : Func.CompileShape) (inst : Ninst) (rest : Func) :
    Func.byteAtByShape locations n (.next size restShape)
        (.next inst rest) i d =
      Func.byteAtByShape locations n (.next size restShape)
        (.next inst rest) i d := by
  expect_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT: compiled-shape-byte-navigation
example (locations : List Nat) (n i : Nat) (d : UInt8)
    (inst0 inst : Ninst) (rest0 rest : Func) :
    Func.byteAtByShape locations n (Func.next inst0 rest0).compileShape
        (.next inst rest) i d =
      Func.byteAtByShape locations n (Func.next inst0 rest0).compileShape
        (.next inst rest) i d := by
  expect_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT: compiled-shape-byte-navigation
example (locations : List Nat) (n i : Nat) (d : UInt8)
    (inst0 inst : Ninst) (p0 p : Func) (hlo : inst0.size ≤ i) :
    Func.byteAtByShape locations n (inst0 ::: p0).compileShape
        (inst ::: p) i d =
      Func.byteAtByShape locations (n + inst0.size) p0.compileShape
        p (i - inst0.size) d := by
  expect_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  exact CompiledShape.byteAt_next_to_tail locations n inst0 inst p0 p i d hlo

-- EXPECT: compiled-shape-byte-navigation
example (locations : List Nat) (n i : Nat) (d : UInt8)
    (left0 right0 left right : Func) :
    Func.byteAtByShape locations n (Func.branch left0 right0).compileShape
        (.branch left right) i d =
      Func.byteAtByShape locations n (Func.branch left0 right0).compileShape
        (.branch left right) i d := by
  expect_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT: compiled-shape-byte-navigation
example (locations : List Nat) (n i : Nat) (d : UInt8) (selector : B256)
    (off0 on0 off on : Func) :
    Func.byteAtByShape locations n
        (CompiledShape.dispatchNode selector off0 on0).compileShape
        (CompiledShape.dispatchNode selector off on) i d =
      Func.byteAtByShape locations n
        (CompiledShape.dispatchNode selector off0 on0).compileShape
        (CompiledShape.dispatchNode selector off on) i d := by
  expect_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (locations : List Nat) (n i : Nat) (d : UInt8)
    (shape : Func.CompileShape) (function : Func) :
    Func.byteAtByShape locations n shape function i d =
      Func.byteAtByShape locations n shape function i d := by
  expect_no_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (locations : List Nat) (n i : Nat) (d : UInt8) (function : Func) :
    Func.byteAtByShape locations n .last function i d =
      Func.byteAtByShape locations n .last function i d := by
  expect_no_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (locations : List Nat) (n i index : Nat) (d : UInt8) :
    Func.byteAtByShape locations n (.call index) (.call index) i d =
      Func.byteAtByShape locations n (.call index) (.call index) i d := by
  expect_no_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

private opaque proofRecipeOpaqueFunction : Func := .last .stop

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (locations : List Nat) (n i : Nat) (d : UInt8) :
    Func.byteAtByShape locations n proofRecipeOpaqueFunction.compileShape
        proofRecipeOpaqueFunction i d =
      Func.byteAtByShape locations n proofRecipeOpaqueFunction.compileShape
        proofRecipeOpaqueFunction i d := by
  expect_no_recipe_trigger "goal-shape:compiled-shape-byte-navigation"
  blanc_suggest
  rfl

-- EXPECT: compile-shape-prepend-congruence
example (l : Line) (p q : Func) (tailShape : p.compileShape = q.compileShape) :
    (l +++ p).compileShape = (l +++ q).compileShape := by
  expect_recipe_trigger "goal-shape:compile-shape-prepend-congruence"
  blanc_suggest
  exact Func.compileShape_prepend_congr l tailShape

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (leftPrefix rightPrefix : Line) (p q : Func)
    (given : (leftPrefix +++ p).compileShape =
      (rightPrefix +++ q).compileShape) :
    (leftPrefix +++ p).compileShape =
      (rightPrefix +++ q).compileShape := by
  expect_no_recipe_trigger "goal-shape:compile-shape-prepend-congruence"
  blanc_suggest
  exact given

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (p q : Func) (given : p.compileShape = q.compileShape) :
    p.compileShape = q.compileShape := by
  expect_no_recipe_trigger "goal-shape:compile-shape-prepend-congruence"
  blanc_suggest
  exact given

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (l : Line) (p : Func) :
    (l +++ p).compileShape = (l +++ p).compileShape := by
  expect_no_recipe_trigger "goal-shape:compile-shape-prepend-congruence"
  blanc_suggest
  rfl

-- EXPECT: bounded-creation-word-encoder
example {sevm : Sevm} {devm : Devm} {G : Nat}
    (gas : devm.gasLeft = G + gVerylow)
    (room : devm.stack.length < 1024) :
    Ninst.RunCompiled sevm devm
      (CreationArtifact.pushB256AsPush2OrPush32 (Nat.toB256 (2 ^ 16)))
      (devm.setMach
        ⟨Nat.toB256 (2 ^ 16) :: devm.stack, devm.memory, G⟩) := by
  expect_recipe_trigger "goal-shape:bounded-creation-word-encoder"
  blanc_suggest
  exact Ninst.runCompiled_pushB256AsPush2OrPush32 gas room

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example {sevm : Sevm} {devm post : Devm}
    (run : Ninst.RunCompiled sevm devm Ninst.sload post) :
    Ninst.RunCompiled sevm devm Ninst.sload post := by
  expect_no_recipe_trigger "goal-shape:bounded-creation-word-encoder"
  blanc_suggest
  exact run

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example {sevm : Sevm} {devm post : Devm} {word : B256}
    (run : Ninst.RunCompiled sevm
      (devm.setMach
        ⟨devm.stack, devm.memory,
          (CreationArtifact.pushB256AsPush2OrPush32 word).size⟩)
      Ninst.sload post) :
    Ninst.RunCompiled sevm
      (devm.setMach
        ⟨devm.stack, devm.memory,
          (CreationArtifact.pushB256AsPush2OrPush32 word).size⟩)
      Ninst.sload post := by
  expect_no_recipe_trigger "goal-shape:bounded-creation-word-encoder"
  blanc_suggest
  exact run

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (word : B256) :
    CreationArtifact.pushB256AsPush2OrPush32 word =
      CreationArtifact.pushB256AsPush2OrPush32 word := by
  expect_no_recipe_trigger "goal-shape:bounded-creation-word-encoder"
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
