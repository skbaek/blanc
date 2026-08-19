import Blanc.LidoCircuitBreakerPauseJoin
import Blanc.TransientSettlement

/-!
# What the CircuitBreaker sends: the pause's two outgoing messages

The pre-control module proved what is already settled at the instant the paused
target receives control.  It deliberately said nothing about **what the target
receives**.  This module says that, for an arbitrary target carrying arbitrary
bytecode.

`pauseAfterSet` makes exactly two outgoing messages, and both are fully
determined by the CircuitBreaker:

* a **CALL** to the paused target, value `0`, arguments the 36 bytes at
  `[0x11c, 0x140)` — `pauseFor(uint256)`'s selector followed by the configured
  duration — with an **empty** return window; and
* on that call's success arm only, a **STATICCALL** to the same target,
  arguments the 4 bytes at `[0x11c, 0x120)` — the `isPaused()` selector — with
  a 32-byte return window at memory `0`.

## How these statements stay true of a hostile callee

`PauseStatBoundary` sits **downstream of arbitrary callee execution**: every
step between the two edges is the target's own run.  A relation that quietly
assumed the callee left something alone would look right and be worthless.
Three deliberate choices keep that from happening.

1. **These are statements about the messages the CircuitBreaker builds, not
   about their effects.**  Neither relation says anything about storage, code,
   balances or logs after the child returns.  The two conjuncts that a
   cooperative callee would supply — storage preservation and code
   preservation, which `responder_call_effects` proves of the witness world's
   responder — are **absent on purpose**.  They are false of a hostile target,
   and dropping them is correct rather than a weakening.

2. **The precompile case is absorbed, not excluded.**  `ProcessMessage` is
   `RunFrame (Frame.ofCall ·)`, which matches on `Frame.enter`; a precompile
   target takes that match's `.done` branch with an empty slot, and
   `Xlot.Filled .none` is `True`.  So `Xlot.Filled xl ∧ ProcessMessage msg xl
   (.ok child)` holds in the precompile case and the ordinary-code case alike,
   and neither relation carries an `isPrecomp` premise.  There is no case split
   to expose here because the frame layer already abstracts over both entries.
   (`responder_call_effects` needs `h_nonprecompile` only because it draws an
   effects conclusion; these relations do not.)

3. **The EIP-7702 delegation case is carried as a disjunct**, never excluded by
   a premise.  Arbitrary bytecode includes a delegation designator.

The bridge between the two edges is `pauseCall_targetWord_survives`, and it is
where the universality bar is actually met.  The staged target word survives
the CALL because the CALL requests a **zero-byte** return window, so its resume
writes `child.output.take 0 = []` — a window survives *whatever the child did*,
by the shape of the resume rather than by the child's good behaviour.  Nothing
of the form "suppose memory is unchanged after the callback" appears anywhere
below.

## What this module does NOT say

* Nothing about what the target does with either message, what it returns, or
  whether it honours the duration.
* No claim that the pause completes, succeeds, or reaches its expiry write.
  The published callback-visible liveness counterexample stands unchanged.
* **No claim that the observation cannot write.**  `msg.isStatic = true` is a
  fact about the message the CircuitBreaker builds.  Deriving "therefore the
  child changed no state" would need a static-context no-write theorem over
  arbitrary code, which exists nowhere in Jaune or Blanc and is not built here.
* Nothing about the *decoding* of the target's answer — short return, words
  other than `0`/`1`, `false`, reverting, or a valid first word with trailing
  bytes.  Every one of those cases is stated against the STATICCALL this module
  pins, and they are the next cut.
* No claim that either edge is reached in any particular run.  Gas sufficiency
  and frame depth appear as explicit conjuncts read off an actual derivation,
  never assumed away silently.
-/

namespace Blanc.LidoCircuitBreaker

open Jaune

/-! ## The calldata encoders

Both relations pin their calldata to an **independently defined encoder**, not
to the bytes the instruction happened to read out of memory.  `callSpawnMsg`
builds its calldata as `p.memory.data.sliceD ii is 0`, so a relation whose
calldata clause said only "the window's content" would be trivially true and
would prove nothing.  The content of these two definitions is what makes the
argument-window conjuncts falsifiable. -/

/-- `pauseFor(uint256)`'s canonical calldata: the four selector bytes followed
by the duration word, 36 bytes in all. -/
def pauseForCalldata (duration : B256) : Bytes :=
  abiSelectorBytes pauseForSelector ++ B256.toBytes duration

/-- `isPaused()`'s canonical calldata: the four selector bytes, and nothing
else. -/
def isPausedCalldata : Bytes := abiSelectorBytes isPausedSelector

/-! ## The two boundary relations -/

/-- **The CALL edge.**  At `callPre` the CircuitBreaker is one instruction away
from handing `target` control, and this relation records everything the
CircuitBreaker determines about that message.

Read the conjuncts in order: the seven operands in the machine's pop order; the
argument window's bytes against `pauseForCalldata`; the suspended parent frame;
the delegation disjunct; the spawned message with its callee, caller, value,
static flag and **transient storage** — the last of which is what turns the
pre-control cut's reentrancy argument into a real one, since the callee is
handed the transient storage that holds the lock; and the resume, whose return
window is empty.

`child.error.isSome` is left free: both arms are in scope, and the flag pushed
back onto the stack is stated as a function of it. -/
def PauseCallBoundary (sevm : Sevm) (target : Adr) (duration : B256)
    (callPre callPost : Devm) : Prop :=
  ∃ (parent child : Devm) (msg : Msg) (xl : Xlot) (delegated : Bool)
      (code : ByteArray) (gasWord : B256) (childGas : Nat),
    -- the seven operands, in the machine's pop order
    callPre.stack =
      gasWord :: target.toB256 :: (0 : B256) :: (0x11c : B256) ::
        (36 : B256) :: (0 : B256) :: (0 : B256) :: parent.stack ∧
    -- the argument window reads the encoder's bytes, not "whatever was there"
    (callPre.memory.read 0x11c 36).1 = pauseForCalldata duration ∧
    -- the frame the CALL suspends on: the two windows are charged for and the
    -- return data cleared, and nothing else about the CircuitBreaker moves
    parent.memory = callPre.memory.extends [(0x11c, 36), (0, 0)] ∧
    parent.state = callPre.state ∧
    parent.createdAccounts = callPre.createdAccounts ∧
    parent.transientStorage = callPre.transientStorage ∧
    parent.logs = callPre.logs ∧
    parent.returnData = [] ∧
    -- depth is honest, not assumed away
    sevm.depth ≠ 0 ∧
    -- EIP-7702: the designator case is carried, never excluded
    ((getDelegatedCodeAddress (callPre.getCode target) = none ∧
        code = callPre.getCode target ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (callPre.getCode target) =
          some delegatedTarget ∧
        code = callPre.getCode delegatedTarget ∧ delegated = true)) ∧
    -- the message the CircuitBreaker builds
    msg = callMsg sevm parent childGas 0 sevm.currentTarget target target
      true false (pauseForCalldata duration) code delegated ∧
    -- ... stated again as claims, because `callMsg`'s twelve positional
    -- arguments do not read as one
    msg.currentTarget = target ∧
    msg.codeAddress = some target ∧
    msg.caller = sevm.currentTarget ∧
    msg.value = 0 ∧
    msg.isStatic = false ∧
    msg.data = pauseForCalldata duration ∧
    msg.tenv.transientStorage = callPre.transientStorage ∧
    -- the child runs; the precompile entry is inside `ProcessMessage`
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    -- the enclosing derivation, at the compiled altitude, on this same slot
    (∀ pc, Ninst.StepRun pc sevm callPre (.exec .call) xl (.ok callPost)) ∧
    -- the empty return window: the resume writes `child.output.take 0 = []`
    (Resume.call parent 0 0).run (.ok child) = .ok callPost ∧
    callPost.memory = parent.memory.write 0 (child.output.take 0) ∧
    callPost.returnData = child.output ∧
    callPost.stack =
      (if child.error.isSome then 0 else 1) :: parent.stack

/-- **The STATICCALL edge.**  Same shape as `PauseCallBoundary`, with six
operands, the bare `isPaused()` selector as calldata, a 32-byte return window
at memory `0`, and `msg.isStatic = true`.

That last conjunct is a property of the **message the CircuitBreaker builds**.
It is not, and must not be read as, a theorem that the child changed no state:
see this module's header. -/
def PauseStatBoundary (sevm : Sevm) (target : Adr)
    (statPre statPost : Devm) : Prop :=
  ∃ (parent child : Devm) (msg : Msg) (xl : Xlot) (delegated : Bool)
      (code : ByteArray) (gasWord : B256) (childGas : Nat),
    statPre.stack =
      gasWord :: target.toB256 :: (0x11c : B256) :: (4 : B256) ::
        (0 : B256) :: (32 : B256) :: parent.stack ∧
    (statPre.memory.read 0x11c 4).1 = isPausedCalldata ∧
    parent.memory = statPre.memory.extends [(0x11c, 4), (0, 32)] ∧
    parent.state = statPre.state ∧
    parent.createdAccounts = statPre.createdAccounts ∧
    parent.transientStorage = statPre.transientStorage ∧
    parent.logs = statPre.logs ∧
    parent.returnData = [] ∧
    sevm.depth ≠ 0 ∧
    ((getDelegatedCodeAddress (statPre.getCode target) = none ∧
        code = statPre.getCode target ∧ delegated = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (statPre.getCode target) =
          some delegatedTarget ∧
        code = statPre.getCode delegatedTarget ∧ delegated = true)) ∧
    msg = callMsg sevm parent childGas 0 sevm.currentTarget target target
      true true isPausedCalldata code delegated ∧
    msg.currentTarget = target ∧
    msg.codeAddress = some target ∧
    msg.caller = sevm.currentTarget ∧
    msg.value = 0 ∧
    msg.isStatic = true ∧
    msg.data = isPausedCalldata ∧
    msg.tenv.transientStorage = statPre.transientStorage ∧
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    (∀ pc, Ninst.StepRun pc sevm statPre (.exec .statcall) xl (.ok statPost)) ∧
    (Resume.call parent 0 32).run (.ok child) = .ok statPost ∧
    statPost.memory = parent.memory.write 0 (child.output.take 32) ∧
    statPost.returnData = child.output ∧
    statPost.stack =
      (if child.error.isSome then 0 else 1) :: parent.stack

/-! ## The universality hinge

`PauseStatBoundary` is stated at a state that sits **downstream of arbitrary
callee execution**.  Everything between the two edges is the target's own run,
so the question that decides whether the second relation is worth anything is:
what does the CircuitBreaker still know about its own memory once the callee
hands control back?

The answer is not "assume the callee behaved".  The CALL's return window is
**zero bytes wide**, so its resume writes `child.output.take 0 = []`, and a
zero-length write misses every offset.  The staged target word therefore
survives by the shape of the resume, for arbitrary child output. -/

/-- Any memory word staged before the pause's CALL survives it, **whatever the
callee returned**.

No premise here is one that only a cooperative target could satisfy, and the
proof never mentions the callee: the two steps are that `Mem.extends` only
grows memory and that the resume's write is empty.  This is what lets
`PauseStatBoundary` be stated after arbitrary callee execution without a
cooperative-callee premise. -/
theorem pauseCall_targetWord_survives {sevm : Sevm} {target : Adr}
    {duration : B256} {callPre callPost : Devm} {offset : Nat} {w : B256}
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (window : MemWordAt callPre offset w) :
    MemWordAt callPost offset w := by
  obtain ⟨parent, child, msg, xl, delegated, code, gasWord, childGas,
    -, -, hpmem, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcmem, -, -⟩ := boundary
  have hmem : callPost.memory =
      (callPre.memory.extends [(284, 36), (0, 0)]).write 0
        (child.output.take 0) := by rw [hcmem, hpmem]
  exact MemWordAt.acrossExtendsWrite hmem (Or.inr (by simp)) window

end Blanc.LidoCircuitBreaker
