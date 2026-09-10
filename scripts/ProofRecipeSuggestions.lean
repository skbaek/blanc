import Blanc.ProofRecipeTactic
import Blanc.RootedExecution
import Blanc.MessageExecution
import Blanc.ExecutionNoninterference
import Blanc.LinearDispatchCorrectness
import Blanc.SymbolicProgram
import Blanc.ExecutionStateTrace
import Blanc.ExecutionTrace
import Blanc.CompiledShape
import Blanc.CreationArtifact
import Blanc.TaggedStorage
import Blanc.AddressSlot
import Blanc.MemoryLayout
import Blanc.CommonProofs
import Blanc.ForwardStorageEffects
import Blanc.CompiledStackSafety

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

-- EXPECT: tagged-storage-region-separation
example {leftRegion rightRegion : Nat} {left right : B256}
    (hlr : leftRegion < 16) (hrr : rightRegion < 16)
    (hleft : left.toNat < 2 ^ 252)
    (hright : right.toNat < 2 ^ 252)
    (hne : leftRegion ≠ rightRegion) :
    TaggedStorage.encode leftRegion left ≠
      TaggedStorage.encode rightRegion right := by
  expect_recipe_trigger "goal-shape:tagged-storage-region-separation"
  blanc_suggest
  exact TaggedStorage.encode_ne_of_region_ne hlr hrr hleft hright hne

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (raw value : B256) :
    addressSlotWriteWord raw value = addressSlotWriteWord raw value := by
  expect_no_recipe_trigger "goal-shape:tagged-storage-region-separation"
  blanc_suggest
  rfl

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

-- EXPECT: symbolic-label-linking
example {Label : Type} [DecidableEq Label] (p : SymbolicProg Label) (map : Label → Nat)
    (hdefs : p.validateDefinitions = .ok ()) (hcalls : p.callsOk map = true) :
    resolve p = .ok (p.erase map) := by
  expect_recipe_trigger "goal-shape:symbolic-label-linking"
  blanc_suggest
  exact resolve_eq_erase_of_callsOk p map hdefs hcalls

-- EXPECT: symbolic-label-linking
example {Label : Type} [DecidableEq Label] (p : SymbolicProg Label) :
    p.findLabel? p.root = some 0 := by
  expect_recipe_trigger "goal-shape:symbolic-label-linking"
  blanc_suggest
  exact findLabel?_root p

-- EXPECT: symbolic-label-linking
example {Label : Type} [DecidableEq Label] (sp : SymbolicProg Label)
    (cert : LinkCertificate sp) : LinkCertificate sp := by
  expect_recipe_trigger "goal-head:LinkCertificate"
  blanc_suggest
  exact cert

-- EXPECT-NO-MATCH: the nearby positional-dispatch relation. `blanc_suggest`
-- must offer `linear-dispatch-selection` here and must NOT offer
-- `symbolic-label-linking`: naming a call target and selecting a dispatch
-- route by selector are different problems, and a symbolic-linking recipe
-- surfacing at a compiled-dispatch goal would be a misdirection.
example {fs : List Func} {sevm : Sevm} {pre : Devm} {out : Execution}
    {fallback : Nat} {entries : List (B256 × Func)} {selector : B256}
    {tail : Stack} {body : Func}
    (unique : selectorUnique entries) (member : (selector, body) ∈ entries)
    (stack : pre.stack = selector :: tail) :
    Func.RunCompiledTo fs sevm pre
      (Blanc.linearDispatchWith fallback entries) out →
      DispatchBodyWitness fs sevm pre entries selector tail body out := by
  expect_no_recipe_trigger "goal-shape:symbolic-label-linking"
  expect_no_recipe_trigger "goal-head:LinkCertificate"
  expect_recipe_trigger "goal-shape:linear-dispatch-selection"
  blanc_suggest
  intro run
  exact dispatchBodyWitness_of_runCompiledTo unique member stack run

-- EXPECT: stack-prefix-transport
example {sevm : Sevm} {pre post : Devm} {line : Line} {p : Stack} :
    Line.Run sevm pre line post → Pref p post.stack → True := by
  expect_recipe_trigger "goal-shape:stack-prefix-line-run"
  blanc_suggest
  intro _ _
  trivial

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example {sevm : Sevm} {pre post : Devm} {line : Line} :
    Line.Run sevm pre line post → True := by
  expect_no_recipe_trigger "goal-shape:stack-prefix-line-run"
  blanc_suggest
  intro _
  trivial

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

-- EXPECT: selector-separation
example (other : B256) (h : selector "name" [] ≠ other) :
    selector "name" [] ≠ other := by
  expect_recipe_trigger "goal-shape:selector-separation"
  blanc_suggest
  exact h

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (a b : B256) (h : a ≠ b) : a ≠ b := by
  expect_no_recipe_trigger "goal-shape:selector-separation"
  blanc_suggest
  exact h

-- EXPECT: fixed-byte-offsets
example (m : Mem) (h : Mem.Wf m) : Mem.Wf m := by
  expect_recipe_trigger "goal-shape:fixed-byte-offset"
  blanc_suggest
  exact h

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (bs : Bytes) : bs = bs := by
  expect_no_recipe_trigger "goal-shape:fixed-byte-offset"
  blanc_suggest
  rfl

-- EXPECT: exact-retained-storage-effects
example {fs : List Func} {sevm : Sevm} {pre : Devm} {body : Func}
    {out : Execution} {effects : List (Adr × B256 × B256)}
    (run : Func.StorageEffectRun fs sevm pre body out effects) :
    Func.StorageEffectRun fs sevm pre body out effects := by
  expect_recipe_trigger "goal-shape:exact-retained-storage-effects"
  blanc_suggest
  exact run

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example {fs : List Func} {sevm : Sevm} {pre : Devm} {f : Func} {post : Devm}
    (run : Func.RunCompiled fs sevm pre f post) :
    Func.RunCompiled fs sevm pre f post := by
  expect_no_recipe_trigger "goal-shape:exact-retained-storage-effects"
  blanc_suggest
  exact run

-- EXPECT: memory-window-transport
example (devm : Devm) (offset : Nat) (w : B256) (h : MemWordAt devm offset w) :
    MemWordAt devm offset w := by
  expect_recipe_trigger "goal-head:MemWordAt"
  blanc_suggest
  exact h

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (w : B256) : w = w := by
  expect_no_recipe_trigger "goal-head:MemWordAt"
  expect_no_recipe_trigger "goal-head:MemImage"
  expect_no_recipe_trigger "implication-premise:MemWordAt"
  blanc_suggest
  rfl

-- EXPECT: operand-stack-certificate
example {sevm : Sevm} {inv : Nat → Devm → Prop} {maximum : Nat}
    (cert : CompiledStackSafety.Certificate sevm inv maximum) :
    CompiledStackSafety.Certificate sevm inv maximum := by
  expect_recipe_trigger "goal-head:CompiledStackSafety.Certificate"
  blanc_suggest
  exact cert

-- EXPECT-NO-MATCH: docs/COMMON_API.md
example (maximum : Nat) : maximum = maximum := by
  expect_no_recipe_trigger "goal-head:CompiledStackSafety.Certificate"
  blanc_suggest
  rfl

/-! ### Checked MemoryStage authoring examples (blanc-memory-example-delivery-v1)

These examples promote the eight validated declarations from the need-first
discovery (Plans `reports/blanc-memory-need-discovery-v1.md` and
`evidence/blanc-memory-need-discovery-v1/validated-snippets.lean`) into the
normal checked authoring path.
-/

/- Three ordered byte writes over an arbitrary existing image. The two guard
premises are intended to be discharged by `decide +kernel` for a concrete
layout, or from the contract's explicit length arithmetic for variable
payloads. -/
theorem intended_staged_windows
    {pre post : Devm} {image first second third : Bytes}
    {trailingWord : B256}
    (source : MemImage pre image)
    (trailing : MemWordAt pre 256 trailingWord)
    (memory : post.memory = MemoryStage.applyMemory
      [(0, first), (64, second), (160, third)] pre.memory)
    (interiorMiss : MemoryStage.avoids
      [(0, first), (64, second), (160, third)] 32 16 = true)
    (trailingMiss : MemoryStage.avoids
      [(0, first), (64, second), (160, third)] 256 32 = true) :
    (MemoryStage.applyImage [(0, first), (64, second), (160, third)]
        image).sliceD 32 16 0 = image.sliceD 32 16 0 ∧
      MemWordAt post 256 trailingWord := by
  constructor
  · exact MemoryStage.applyImage_sliceD_of_avoids
      [(0, first), (64, second), (160, third)] image 32 16 interiorMiss
  · exact MemWordAt.applyStage
      [(0, first), (64, second), (160, third)] source memory trailingMiss
        trailing

/- Exact rounded allocation is available when the initial allocation is word
aligned. -/
theorem intended_staged_allocation
    (stage : MemoryStage) (memory : Mem)
    (aligned : memory.size % 32 = 0) :
    (stage.applyMemory memory).size =
      memExtsSize memory.size stage.footprint := by
  exact MemoryStage.applyMemory_size stage memory aligned

/- A final whole-word write reads back independently of all earlier writes.
The general API permits a later suffix too, provided that suffix avoids this
32-byte window. -/
theorem intended_final_word_image_readback
    (initial : MemoryStage) (image : Bytes) (offset : Nat) (word : B256) :
    ((initial ++ [(offset, word.toBytes)]).applyImage image).sliceD
        offset 32 0 = word.toBytes := by
  simpa only [B256.length_toBytes] using
    (MemoryStage.read_written initial [] image word.toBytes offset (by rfl))

/- Bridge the final symbolic readback to an exact machine word. -/
theorem intended_final_word_machine_readback
    {pre post : Devm} {image : Bytes}
    (initial : MemoryStage) (offset : Nat) (word : B256)
    (source : MemImage pre image)
    (memory : post.memory =
      (initial ++ [(offset, word.toBytes)]).applyMemory pre.memory) :
    MemWordAt post offset word := by
  have target : MemImage post
      ((initial ++ [(offset, word.toBytes)]).applyImage image) :=
    MemImage.applyStage (initial ++ [(offset, word.toBytes)]) source memory
  apply MemWordAt.of_memImage target
  exact intended_final_word_image_readback initial image offset word

theorem intended_overlap_guard_rejected :
    MemoryStage.avoids ([(0, [1]), (1, [2])] : MemoryStage) 0 2 = false := by
  decide +kernel

theorem intended_empty_write_inside_observation :
    MemoryStage.avoids ([(5, [])] : MemoryStage) 0 10 = true := by
  decide +kernel

theorem intended_empty_observation_inside_write :
    MemoryStage.avoids ([(0, [1, 2])] : MemoryStage) 1 0 = true := by
  decide +kernel

theorem intended_relation_with_memory_shape
    {e : Sevm} {pre post : Devm} {line : Line}
    {image : Bytes} {offset : Nat} {word : B256}
    (stage : MemoryStage)
    (_run : Line.Run e pre line post)
    (source : MemImage pre image)
    (shape : post.memory = stage.applyMemory pre.memory)
    (miss : stage.avoids offset 32 = true)
    (window : MemWordAt pre offset word) :
    MemWordAt post offset word := by
  exact MemWordAt.applyStage stage source shape miss window

end Blanc
