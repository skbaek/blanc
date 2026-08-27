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
* No claim that either edge is reached in any particular run.  Gas sufficiency,
  frame depth and the enclosing frame's dynamic context are the three honest
  premises: they appear as explicit conjuncts or explicit hypotheses read off
  an actual derivation, never assumed away silently.

  The third of them is `pauseCall_boundary`'s
  `h_dynamic : sevm.isStatic = false`, and it is a fact about the **enclosing
  frame**, not about the callee.  `callMsg` sets
  `isStatic := isStaticcall || sevm.isStatic`, and a `CALL` passes
  `isStaticcall = false`, so a `CALL`'s `msg.isStatic = false` *is* that flag.
  It is true of every real pause: `pause` writes the reentrancy lock with
  `TSTORE`, which carries Jaune's `assertDynamic` guard
  (`Jaune/Machine.lean:2573`, used at `:2853`), so a pause entered in a static
  context halts with `writeInStaticContext` long before this edge.  Deriving it
  here rather than carrying it would mean composing the whole `pause`-to-`CALL`
  prefix, which this cut excludes.
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

/-- The actual spawned CALL occurrence retained by the boundary constructor.
This is the execution-shaped sibling of `PauseCallBoundary`: it exposes the
same message, slot and settled child already present in that proof together
with the exact parent spawn. -/
def PauseCallExecutionWitness (sevm : Sevm) (target : Adr)
    (duration : B256) (callPre callPost : Devm) : Prop :=
  ∃ (msg : Msg) (xl : Xlot) (child : Devm)
      (pc nextPc : Nat) (resume : Resume),
    msg.currentTarget = target ∧
    msg.target = some target ∧
    msg.codeAddress = some target ∧
    msg.caller = sevm.currentTarget ∧
    msg.value = 0 ∧
    msg.shouldTransferValue = true ∧
    msg.isStatic = false ∧
    msg.data = pauseForCalldata duration ∧
    msg.benv.stat.time = sevm.benvStat.time ∧
    msg.benv.stat.rules = sevm.benvStat.rules ∧
    Ninst.step ⟨pc, sevm, callPre⟩ Ninst.call =
      .spawn (Jaune.Frame.ofCall msg) resume nextPc ∧
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    Ninst.StepRun pc sevm callPre Ninst.call xl (.ok callPost) ∧
    callPost.state = child.state ∧
    callPost.returnData = child.output

/-- The actual spawned STATICCALL occurrence retained by the boundary
constructor. -/
def PauseStatExecutionWitness (sevm : Sevm) (target : Adr)
    (statPre statPost : Devm) : Prop :=
  ∃ (msg : Msg) (xl : Xlot) (child : Devm)
      (pc nextPc : Nat) (resume : Resume),
    msg.currentTarget = target ∧
    msg.target = some target ∧
    msg.codeAddress = some target ∧
    msg.caller = sevm.currentTarget ∧
    msg.value = 0 ∧
    msg.shouldTransferValue = true ∧
    msg.isStatic = true ∧
    msg.data = isPausedCalldata ∧
    msg.benv.stat.time = sevm.benvStat.time ∧
    msg.benv.stat.rules = sevm.benvStat.rules ∧
    Ninst.step ⟨pc, sevm, statPre⟩ Ninst.statcall =
      .spawn (Jaune.Frame.ofCall msg) resume nextPc ∧
    Xlot.Filled xl ∧
    ProcessMessage msg xl (.ok child) ∧
    Ninst.StepRun pc sevm statPre Ninst.statcall xl (.ok statPost) ∧
    statPost.state = child.state ∧
    statPost.returnData = child.output

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

/-! ## The CALL edge, inverted

The forward library evaluates the `.call` arm only on the branch that can pay
its own charge, so the failing branch is named here: an arbitrary derivation
carries no gas premise, and the insufficient branch has to be *refuted* rather
than assumed away.  Both helpers below are private, and both are copies of
`Blanc/LidoCircuitBreakerPauseJoin.lean`'s equally private siblings — that
module's versions are not exported. -/

/-- `chargeGas`, evaluated forward on its failing arm. -/
private lemma callEdge_chargeGas_eq_error {cost : Nat} {devm : Devm}
    (h : devm.gasLeft < cost) :
    chargeGas cost devm = .error ⟨.halt (.outOfGas .none), devm⟩ := by
  rw [chargeGas_def]
  have hs : safeSub devm.gasLeft cost = none := by
    unfold safeSub
    rw [if_neg (by omega)]
  rw [hs]

/-- The `.call` arm at `value = 0` on a frame that cannot pay the call's own
charge: `chargeGas` fails and the step is an out-of-gas halt.  The failing
sibling of `Xinst.step_call_zero_value`. -/
private lemma callEdge_step_call_zero_value_outOfGas {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: 0 :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        cw.toAdr) cw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost cw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : d1.gasLeft < mcc + ext) :
    Xinst.step sevm devm .call =
      .done (.error ⟨.halt (.outOfGas .none), d1⟩) := by
  subst h_ext; subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨callee, d⟩ ← d.popToAdr
    let ⟨value, d⟩ ← d.pop
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost callee d.accessedAddresses
    let d := addAccessedAddress d callee
    let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d callee
    let accessCost := preAccessCost + delegatedAccessGasCost
    let createCost :=
      if (¬ (d.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost := if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas value.toNat gas.toNat d.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let d ← chargeGas (msgCallCost + extendCost) d
    Except.assert (!sevm.isStatic ∨ value = 0)
      ⟨.halt (.writeInStaticContext .none), d⟩
    let d := d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal := (d.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let d ← d.push 0
      return .done
        (.ok ((d.withReturnData []).withGasLeft (d.gasLeft + msgCallStipend)))
    else
      return genericCall.step
        sevm d msgCallStipend value sevm.currentTarget callee callee
        true false inputIndex inputSize outputIndex outputSize
        code disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨cw :: 0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.pop_eq_ok
    (devm := devm.setMach ⟨0 :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  simp only [if_pos (Or.inr trivial), if_pos trivial, Nat.add_zero,
    show ((0 : B256).toNat) = 0 from rfl]
  simp only [h_del, h_split]
  rw [callEdge_chargeGas_eq_error (devm := d1) h_gas]
  rfl

/-- The EIP-7702 disjunct, read off a delegation resolution rather than
excluded by a premise: either the account carries no designator and the code
run is its own, or it carries one and the code run is the designated
account's. -/
private lemma accessDelegation_delegationCases {devm : Devm} {a dadr : Adr}
    {dp : Bool} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    (h : accessDelegation devm a = ⟨dp, dadr, code, dgc, d1⟩) :
    (getDelegatedCodeAddress (devm.getCode a) = none ∧
        code = devm.getCode a ∧ dp = false) ∨
      (∃ delegatedTarget,
        getDelegatedCodeAddress (devm.getCode a) = some delegatedTarget ∧
        code = devm.getCode delegatedTarget ∧ dp = true) := by
  unfold accessDelegation at h
  rcases hgd : getDelegatedCodeAddress (devm.state.getCode a) with _ | dt
  · simp only [hgd] at h
    exact Or.inl ⟨hgd, (congrArg (fun x => x.2.2.1) h).symm,
      (congrArg (fun x => x.1) h).symm⟩
  · simp only [hgd] at h
    exact Or.inr ⟨dt, hgd, (congrArg (fun x => x.2.2.1) h).symm,
      (congrArg (fun x => x.1) h).symm⟩

/-- **The CALL edge, inverted.**  Any derivation that crosses the pause's
`.call` instruction satisfies `PauseCallBoundary`: the seven operands, the
argument window's bytes, the suspended parent frame, the spawned message and
the empty-window resume are all read off that derivation.

**No premise here constrains the callee.**  There is no code pin — the
EIP-7702 cases come out of the delegation resolution as the relation's own
disjunct — and no `isPrecomp` premise, because `ProcessMessage` is
`RunFrame (Frame.ofCall ·)`, a precompile target takes `Frame.enter`'s `.done`
branch with an empty slot, and `Xlot.Filled .none` is `True`.  Gas sufficiency
is not assumed either: on the insufficient branch the step is an out-of-gas
halt, which the derivation's `.ok callPost` refutes.

The operand is `target.toB256` rather than an arbitrary word because
`PauseCallBoundary` pins the canonical encoding of its `Adr` argument;
`B256.toAdr` truncates, so at a stack word with high bits set the relation is
false rather than merely unproved.

`h_dynamic` is an honest premise, in the same family as `h_depth` and for the
same reason: it is a fact about the **enclosing frame**, not about the callee,
and nothing at this edge decides it.  `callMsg` sets `isStatic` to
`isStaticcall || sevm.isStatic`, and a `CALL` passes `isStaticcall = false`, so
the relation's `msg.isStatic = false` is exactly `sevm.isStatic = false`.  A
zero-value `CALL` is itself legal inside a static context — `Xinst.step`'s
`.call` arm discharges its static assertion on `value = 0`, not on
`¬ sevm.isStatic` — so the premise cannot be read off this instruction.

It is nevertheless **true wherever this theorem is instantiated by a real
pause**, and derivably so: `pause` writes the reentrancy lock with `TSTORE`
before it ever reaches `pauseAfterSet`, and `tstore` carries Jaune's
`assertDynamic` guard, so a `pause` entered in a static context halts with
`writeInStaticContext` long before this edge.  `sevm` is frame-static, so that
upstream fact is the same `sevm.isStatic` this premise names.  Discharging it
here rather than carrying it would mean composing the whole `pause`-to-CALL
prefix into this statement, which this cut deliberately does not do. -/
theorem pauseCall_boundary_with_execution
    {sevm : Sevm} {callPre callPost : Devm}
    {gasWord duration : B256} {target : Adr} {rest : List B256}
    (h_stk : callPre.stack =
      gasWord :: target.toB256 :: 0 :: 0x11c :: 36 :: 0 :: 0 :: rest)
    (h_window : (callPre.memory.read 0x11c 36).1 = pauseForCalldata duration)
    (h_depth : sevm.depth ≠ 0)
    (h_dynamic : sevm.isStatic = false)
    (run : Ninst.RunCompiled sevm callPre (.exec .call) callPost) :
    PauseCallBoundary sevm target duration callPre callPost ∧
      PauseCallExecutionWitness sevm target duration callPre callPost := by
  obtain ⟨xl, hfill, hrun⟩ := run
  have hx := hrun 0
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at hx
  have hta : (target.toB256).toAdr = target := toAdr_toB256 target
  rcases hdel : accessDelegation
      (addAccessedAddress
        (callPre.setMach ⟨rest, callPre.memory, callPre.gasLeft⟩) target)
      target with ⟨dp, dadr, code, dgc, d1⟩
  have h_del : accessDelegation
      (addAccessedAddress
        (callPre.setMach ⟨rest, callPre.memory, callPre.gasLeft⟩)
        (target.toB256).toAdr) (target.toB256).toAdr =
      ⟨dp, dadr, code, dgc, d1⟩ := by rw [hta]; exact hdel
  obtain ⟨ext, hext⟩ :
      ∃ n : Nat,
        (callPre.setMach ⟨rest, callPre.memory, callPre.gasLeft⟩).extCost
          [⟨(0x11c : B256).toNat, (36 : B256).toNat⟩,
            ⟨(0 : B256).toNat, (0 : B256).toNat⟩] = n := ⟨_, rfl⟩
  obtain ⟨acc, hacc⟩ :
      ∃ n : Nat,
        accessCost (target.toB256).toAdr
          (callPre.setMach
            ⟨rest, callPre.memory, callPre.gasLeft⟩).accessedAddresses
            + dgc = n := ⟨_, rfl⟩
  rcases hsplit : calculateMsgCallGas 0 gasWord.toNat d1.gasLeft ext acc
    with ⟨mcc, mcs⟩
  by_cases hga : mcc + ext ≤ d1.gasLeft
  case neg =>
    rw [callEdge_step_call_zero_value_outOfGas h_stk hext h_del hacc hsplit
      (by omega)] at hx
    obtain ⟨-, hcontra⟩ := hx
    cases hcontra
  case pos =>
    obtain ⟨hstep, -, -, -, -, -, -, htra⟩ :=
      directCall_zero_spawn h_stk hext h_del hacc hsplit hga h_depth
    rw [hta] at hstep htra
    obtain ⟨hd1stk, hd1mem, -, -⟩ := accessDelegation_inv hdel
    obtain ⟨hd1state, hd1logs, -, -, -⟩ := accessDelegation_frame hdel
    have hifr := accessDelegation_instructionFrame
      (addAccessedAddress
        (callPre.setMach ⟨rest, callPre.memory, callPre.gasLeft⟩) target) target
    rw [hdel] at hifr
    have hstk1 : d1.stack = rest := hd1stk
    have hmem1 : d1.memory = callPre.memory := hd1mem
    have hstate1 : d1.state = callPre.state := hd1state
    have hlogs1 : d1.logs = callPre.logs := hd1logs
    have hca1 : d1.createdAccounts = callPre.createdAccounts :=
      hifr.createdAccounts.symm
    set parent : Devm :=
      callSpawnParent d1 (mcc + ext) ((284 : B256).toNat) ((36 : B256).toNat)
        ((0 : B256).toNat) ((0 : B256).toNat) with hparent
    have hpstk : parent.stack = rest := by rw [hparent]; exact hstk1
    have hpmem : parent.memory =
        callPre.memory.extends [(0x11c, 36), (0, 0)] := by
      rw [hparent]
      show d1.memory.extends _ = _
      rw [hmem1]
      rfl
    have hpstate : parent.state = callPre.state := by
      rw [hparent]; exact hstate1
    have hplogs : parent.logs = callPre.logs := by rw [hparent]; exact hlogs1
    have hpca : parent.createdAccounts = callPre.createdAccounts := by
      rw [hparent]; exact hca1
    have hprd : parent.returnData = [] := by rw [hparent]; rfl
    have hptra : parent.transientStorage = callPre.transientStorage := htra
    -- the argument window carries the encoder's bytes, not "whatever was there"
    have hdata : parent.memory.data.sliceD ((284 : B256).toNat)
        ((36 : B256).toNat) 0 = pauseForCalldata duration := by
      rw [hpmem]; exact h_window
    have hmsgeq : callSpawnMsg sevm parent mcs target ((284 : B256).toNat)
        ((36 : B256).toNat) code dp =
        callMsg sevm parent mcs 0 sevm.currentTarget target target true false
          (pauseForCalldata duration) code dp := by
      show callMsg sevm parent mcs 0 sevm.currentTarget target target true false
        (parent.memory.data.sliceD ((284 : B256).toNat) ((36 : B256).toNat) 0)
        code dp = _
      rw [hdata]
    -- the EIP-7702 disjunct, never a premise
    have hdisj0 := accessDelegation_delegationCases hdel
    have hdisj : (getDelegatedCodeAddress (callPre.getCode target) = none ∧
          code = callPre.getCode target ∧ dp = false) ∨
        (∃ delegatedTarget,
          getDelegatedCodeAddress (callPre.getCode target) =
            some delegatedTarget ∧
          code = callPre.getCode delegatedTarget ∧ dp = true) := hdisj0
    rw [hstep] at hx
    obtain ⟨r, hframe, hres⟩ := hx
    rcases r with ⟨e, st, ca, tra⟩ | child
    · rw [Resume.run_call_fatal] at hres
      cases hres
    rw [hmsgeq] at hframe
    have hres' : (Resume.call parent 0 0).run (.ok child) = .ok callPost :=
      hres.symm
    let msg := callMsg sevm parent mcs 0 sevm.currentTarget target target
      true false (pauseForCalldata duration) code dp
    have hspawn : Ninst.step ⟨0, sevm, callPre⟩ Ninst.call =
        .spawn (Jaune.Frame.ofCall msg) (.call parent 0 0) 1 := by
      simp only [Ninst.call, Ninst.step_exec]
      change XStep.toStep 1 (Xinst.step sevm callPre .call) = _
      rw [hstep, hmsgeq]
      rfl
    have boundary : PauseCallBoundary sevm target duration callPre callPost := by
      refine ⟨parent, child, msg, xl, dp, code, gasWord, mcs,
        by rw [hpstk]; exact h_stk, h_window, hpmem, hpstate, hpca, hptra,
        hplogs, hprd, h_depth, hdisj, rfl, rfl, rfl, rfl, rfl, ?_, rfl,
        hptra, hfill, hframe, hrun, hres', Resume.call_memory hres',
        Resume.call_returnData hres', Resume.call_stack_flag hres'⟩
      -- `callMsg` leaves the caller's frame-static bit in the CALL message.
      show sevm.isStatic = false
      exact h_dynamic
    refine ⟨boundary, msg, xl, child, 0, 1, .call parent 0 0,
      rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, hspawn, hfill, hframe,
      hrun 0, Resume.call_state hres', Resume.call_returnData hres'⟩
    show sevm.isStatic = false
    exact h_dynamic

/-- The established CALL boundary, retained as the compatibility projection
of the execution-shaped constructor. -/
theorem pauseCall_boundary {sevm : Sevm} {callPre callPost : Devm}
    {gasWord duration : B256} {target : Adr} {rest : List B256}
    (h_stk : callPre.stack =
      gasWord :: target.toB256 :: 0 :: 0x11c :: 36 :: 0 :: 0 :: rest)
    (h_window : (callPre.memory.read 0x11c 36).1 = pauseForCalldata duration)
    (h_depth : sevm.depth ≠ 0)
    (h_dynamic : sevm.isStatic = false)
    (run : Ninst.RunCompiled sevm callPre (.exec .call) callPost) :
    PauseCallBoundary sevm target duration callPre callPost :=
  (pauseCall_boundary_with_execution h_stk h_window h_depth h_dynamic run).1

/-! ## The STATICCALL edge, inverted

The observation's edge is inverted the same way, and for the same reason: an
arbitrary derivation carries no gas premise, so the branch that cannot pay the
call's own charge is refuted rather than assumed away.  The helper below is a
private copy of `Blanc/LidoCircuitBreakerPauseJoin.lean`'s equally private
`.statcall` sibling, which that module does not export. -/

/-- The `.statcall` arm on a frame that cannot pay the call's own charge:
`chargeGas` fails and the step is an out-of-gas halt.  The failing sibling of
`Xinst.step_statcall_spawn`. -/
private lemma statEdge_step_statcall_outOfGas {sevm : Sevm} {devm : Devm}
    {gw tw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: tw :: iiw :: isw :: oiw :: osw :: s)
    (h_ext : (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).extCost
      [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩] = ext)
    (h_del : accessDelegation
      (addAccessedAddress (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩)
        tw.toAdr) tw.toAdr = ⟨dp, dadr, code, dgc, d1⟩)
    (h_acc : accessCost tw.toAdr
      (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩).accessedAddresses
        + dgc = acc)
    (h_split : calculateMsgCallGas 0 gw.toNat d1.gasLeft ext acc = ⟨mcc, mcs⟩)
    (h_gas : d1.gasLeft < mcc + ext) :
    Xinst.step sevm devm .statcall =
      .done (.error ⟨.halt (.outOfGas .none), d1⟩) := by
  subst h_ext; subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨target, d⟩ ← d.popToAdr
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost target d.accessedAddresses
    let d := addAccessedAddress d target
    let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d target
    let accessCost := preAccessCost + delegatedAccessGasCost
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas 0 gas.toNat d.gasLeft extendCost accessCost
    let d ← chargeGas (msgCallCost + extendCost) d
    let d :=
      d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    return genericCall.step
      sevm d msgCallStipend 0 sevm.currentTarget target target true true
      inputIndex inputSize outputIndex outputSize code
      disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨tw :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach,
    Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨oiw :: osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  rw [Devm.popToNat_eq_ok
    (devm := devm.setMach ⟨osw :: s, devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
  simp only [h_del, h_split]
  rw [callEdge_chargeGas_eq_error (devm := d1) h_gas]
  rfl


/-- **The STATICCALL edge, inverted.**  Any derivation that crosses the pause's
`.statcall` instruction satisfies `PauseStatBoundary`: the six operands, the
argument window's bytes, the suspended parent frame, the spawned message and
the 32-byte-window resume are all read off that derivation.

**No premise here constrains the callee**, and none constrains what the callee
did before this edge either.  This instruction sits downstream of arbitrary
callee execution — every step between it and the pause's CALL is the target's
own run — so a premise of the form "suppose memory is unchanged after the
callback" would empty the statement.  There is none: the argument window is
supplied by `pauseCall_targetWord_survives`, which survives arbitrary child
output by the shape of the CALL's empty resume.  There is likewise no code pin
— the EIP-7702 cases come out of the delegation resolution as the relation's
own disjunct — and no `isPrecomp` premise, because `ProcessMessage` is
`RunFrame (Frame.ofCall ·)`, a precompile target takes `Frame.enter`'s `.done`
branch with an empty slot, and `Xlot.Filled .none` is `True`.  Gas sufficiency
is not assumed either: on the insufficient branch the step is an out-of-gas
halt, which the derivation's `.ok statPost` refutes.

Unlike `pauseCall_boundary` this theorem carries **no `sevm.isStatic`
premise**, and the difference is not an oversight in either direction.
`callMsg` sets `isStatic := isStaticcall || sevm.isStatic`; a `CALL` passes
`isStaticcall = false`, leaving `msg.isStatic = false` equivalent to a fact
about the enclosing frame, while a `STATICCALL` passes `isStaticcall = true`,
so `msg.isStatic = true` holds outright whatever the enclosing frame's static
flag is.  The conjunct closes by `rfl`.

As on the CALL edge, the operand is `target.toB256` rather than an arbitrary
word because `PauseStatBoundary` pins the canonical encoding of its `Adr`
argument; `B256.toAdr` truncates, so at a stack word with high bits set the
relation is false rather than merely unproved. -/
theorem pauseStat_boundary_with_execution
    {sevm : Sevm} {statPre statPost : Devm}
    {gasWord : B256} {target : Adr} {rest : List B256}
    (h_stk : statPre.stack =
      gasWord :: target.toB256 :: 0x11c :: 4 :: 0 :: 32 :: rest)
    (h_window : (statPre.memory.read 0x11c 4).1 = isPausedCalldata)
    (h_depth : sevm.depth ≠ 0)
    (run : Ninst.RunCompiled sevm statPre (.exec .statcall) statPost) :
    PauseStatBoundary sevm target statPre statPost ∧
      PauseStatExecutionWitness sevm target statPre statPost := by
  obtain ⟨xl, hfill, hrun⟩ := run
  have hx := hrun 0
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at hx
  have hta : (target.toB256).toAdr = target := toAdr_toB256 target
  rcases hdel : accessDelegation
      (addAccessedAddress
        (statPre.setMach ⟨rest, statPre.memory, statPre.gasLeft⟩) target)
      target with ⟨dp, dadr, code, dgc, d1⟩
  have h_del : accessDelegation
      (addAccessedAddress
        (statPre.setMach ⟨rest, statPre.memory, statPre.gasLeft⟩)
        (target.toB256).toAdr) (target.toB256).toAdr =
      ⟨dp, dadr, code, dgc, d1⟩ := by rw [hta]; exact hdel
  obtain ⟨ext, hext⟩ :
      ∃ n : Nat,
        (statPre.setMach ⟨rest, statPre.memory, statPre.gasLeft⟩).extCost
          [⟨(0x11c : B256).toNat, (4 : B256).toNat⟩,
            ⟨(0 : B256).toNat, (32 : B256).toNat⟩] = n := ⟨_, rfl⟩
  obtain ⟨acc, hacc⟩ :
      ∃ n : Nat,
        accessCost (target.toB256).toAdr
          (statPre.setMach
            ⟨rest, statPre.memory, statPre.gasLeft⟩).accessedAddresses
            + dgc = n := ⟨_, rfl⟩
  rcases hsplit : calculateMsgCallGas 0 gasWord.toNat d1.gasLeft ext acc
    with ⟨mcc, mcs⟩
  by_cases hga : mcc + ext ≤ d1.gasLeft
  case neg =>
    rw [statEdge_step_statcall_outOfGas h_stk hext h_del hacc hsplit
      (by omega)] at hx
    obtain ⟨-, hcontra⟩ := hx
    cases hcontra
  case pos =>
    obtain ⟨hstep, -, -, -, -, -, -, htra⟩ :=
      directStatcall_spawn h_stk hext h_del hacc hsplit hga h_depth
    rw [hta] at hstep htra
    obtain ⟨hd1stk, hd1mem, -, -⟩ := accessDelegation_inv hdel
    obtain ⟨hd1state, hd1logs, -, -, -⟩ := accessDelegation_frame hdel
    have hifr := accessDelegation_instructionFrame
      (addAccessedAddress
        (statPre.setMach ⟨rest, statPre.memory, statPre.gasLeft⟩) target)
      target
    rw [hdel] at hifr
    have hstk1 : d1.stack = rest := hd1stk
    have hmem1 : d1.memory = statPre.memory := hd1mem
    have hstate1 : d1.state = statPre.state := hd1state
    have hlogs1 : d1.logs = statPre.logs := hd1logs
    have hca1 : d1.createdAccounts = statPre.createdAccounts :=
      hifr.createdAccounts.symm
    set parent : Devm :=
      callSpawnParent d1 (mcc + ext) ((284 : B256).toNat) ((4 : B256).toNat)
        ((0 : B256).toNat) ((32 : B256).toNat) with hparent
    have hpstk : parent.stack = rest := by rw [hparent]; exact hstk1
    have hpmem : parent.memory =
        statPre.memory.extends [(0x11c, 4), (0, 32)] := by
      rw [hparent]
      show d1.memory.extends _ = _
      rw [hmem1]
      rfl
    have hpstate : parent.state = statPre.state := by
      rw [hparent]; exact hstate1
    have hplogs : parent.logs = statPre.logs := by rw [hparent]; exact hlogs1
    have hpca : parent.createdAccounts = statPre.createdAccounts := by
      rw [hparent]; exact hca1
    have hprd : parent.returnData = [] := by rw [hparent]; rfl
    have hptra : parent.transientStorage = statPre.transientStorage := htra
    -- the argument window carries the encoder's bytes, not "whatever was there"
    have hdata : parent.memory.data.sliceD ((284 : B256).toNat)
        ((4 : B256).toNat) 0 = isPausedCalldata := by
      rw [hpmem]; exact h_window
    have hmsgeq : statcallSpawnMsg sevm parent mcs target ((284 : B256).toNat)
        ((4 : B256).toNat) code dp =
        callMsg sevm parent mcs 0 sevm.currentTarget target target true true
          isPausedCalldata code dp := by
      show callMsg sevm parent mcs 0 sevm.currentTarget target target true true
        (parent.memory.data.sliceD ((284 : B256).toNat) ((4 : B256).toNat) 0)
        code dp = _
      rw [hdata]
    -- the EIP-7702 disjunct, never a premise
    have hdisj0 := accessDelegation_delegationCases hdel
    have hdisj : (getDelegatedCodeAddress (statPre.getCode target) = none ∧
          code = statPre.getCode target ∧ dp = false) ∨
        (∃ delegatedTarget,
          getDelegatedCodeAddress (statPre.getCode target) =
            some delegatedTarget ∧
          code = statPre.getCode delegatedTarget ∧ dp = true) := hdisj0
    rw [hstep] at hx
    obtain ⟨r, hframe, hres⟩ := hx
    rcases r with ⟨e, st, ca, tra⟩ | child
    · rw [Resume.run_call_fatal] at hres
      cases hres
    rw [hmsgeq] at hframe
    have hres' : (Resume.call parent 0 32).run (.ok child) = .ok statPost :=
      hres.symm
    let msg := callMsg sevm parent mcs 0 sevm.currentTarget target target
      true true isPausedCalldata code dp
    have hspawn : Ninst.step ⟨0, sevm, statPre⟩ Ninst.statcall =
        .spawn (Jaune.Frame.ofCall msg) (.call parent 0 32) 1 := by
      simp only [Ninst.statcall, Ninst.step_exec]
      change XStep.toStep 1 (Xinst.step sevm statPre .statcall) = _
      rw [hstep, hmsgeq]
      rfl
    have boundary : PauseStatBoundary sevm target statPre statPost := by
      exact ⟨parent, child, msg, xl, dp, code, gasWord, mcs,
        by rw [hpstk]; exact h_stk, h_window, hpmem, hpstate, hpca, hptra,
        hplogs, hprd, h_depth, hdisj, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        hptra, hfill, hframe, hrun, hres', Resume.call_memory hres',
        Resume.call_returnData hres', Resume.call_stack_flag hres'⟩
    exact ⟨boundary, msg, xl, child, 0, 1, .call parent 0 32,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hspawn, hfill, hframe,
      hrun 0, Resume.call_state hres', Resume.call_returnData hres'⟩

/-- The established STATICCALL boundary, retained as the compatibility
projection of the execution-shaped constructor. -/
theorem pauseStat_boundary {sevm : Sevm} {statPre statPost : Devm}
    {gasWord : B256} {target : Adr} {rest : List B256}
    (h_stk : statPre.stack =
      gasWord :: target.toB256 :: 0x11c :: 4 :: 0 :: 32 :: rest)
    (h_window : (statPre.memory.read 0x11c 4).1 = isPausedCalldata)
    (h_depth : sevm.depth ≠ 0)
    (run : Ninst.RunCompiled sevm statPre (.exec .statcall) statPost) :
    PauseStatBoundary sevm target statPre statPost :=
  (pauseStat_boundary_with_execution h_stk h_window h_depth run).1

/-! ## The pause's post-CALL branch

Everything above is about the two messages.  What follows is about the
**order** in which the CircuitBreaker sends them: the second message exists
only on the first one's success arm, and the first one's failure arm goes to
the bubble instead.  The two names below cut `pauseAfterSet` at its `CALL` so
that the ordering can be stated against the program rather than against a
paraphrase of it. -/

/-- The pause's observation arm: the `isPaused()` staging line, the
`STATICCALL` itself, and the flag test that follows it. -/
def pauseStatArm : Func :=
  pauseStatStaging +++
    (Ninst.statcall ::: Ninst.iszero :::
      ((Func.call bubbleRevertSlot) <?> decodePausedResult))

/-- Everything `pauseAfterSet` does after its `CALL`: the `ISZERO` that inverts
the call's flag word, and the branch that reads the inverted word.  The bubble
is the branch's **nonzero** arm and the observation its **zero** arm, which is
what `pauseAfterCall_arms` below turns into a statement about the callee's
success. -/
def pauseAfterCallBranch : Func :=
  Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> pauseStatArm)

/-- The two names above are `pauseAfterSet` itself, cut at the code guard and
at the `CALL`.  Nothing downstream is a claim about a paraphrase. -/
theorem pauseAfterSet_eq_afterCall :
    pauseAfterSet =
      pauseCodeGuard +++
        ((Func.call emptyRevertSlot) <?>
          (pauseCallStaging +++ (Ninst.call ::: pauseAfterCallBranch))) := rfl

/-! ## The branch flag, inverted

The CALL pushes `1` on success and `0` on failure, and `pauseAfterSet` runs
that word through `ISZERO` before the branch reads it.  So the branch's zero
arm — the arm `Func.branch` takes when the popped word is `0` — is the arm the
**successful** call reaches, and the nonzero arm is the failing call's.  The
inversion is one instruction wide and is stated first, so that the two arm
theorems below can be read without re-deriving it. -/

/-- `ISZERO` at a known stack top: the word it pushes, the tail it leaves, and
the return data it does not touch. -/
private lemma iszero_inv {sevm : Sevm} {pre post : Devm} {w : B256}
    {rest : List B256}
    (run : Ninst.RunCompiled sevm pre Ninst.iszero post)
    (h_stk : pre.stack = w :: rest) :
    post.stack = (w =? 0) :: rest ∧ post.returnData = pre.returnData := by
  rcases of_run_reg (Ninst.Run.of_runCompiled run) with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  obtain ⟨x, hdiff⟩ := Devm.diffBurn_of_applyUnary hrun
  obtain ⟨mid, hpop, hpush⟩ := hdiff.stack
  have hpop' : w :: rest = x :: mid := by rw [← h_stk]; exact hpop
  injection hpop' with hw hrest
  subst hw
  subst hrest
  exact ⟨hpush, hdiff.returnData.symm⟩

/-- **The word `pauseAfterSet`'s branch reads.**  The CALL's flag is `0`
exactly when the child errored, and the `ISZERO` between the CALL and the
branch inverts it, so the branch pops `1` exactly when the child errored.

This is a statement about the CircuitBreaker's own stack and the `Devm` the
frame layer handed back; **it constrains the callee in no way**.  Which of the
two values the flag actually takes is the callee's business, and both are
carried: the `if` is on `child.error.isSome`, which is left free here exactly
as `PauseCallBoundary` leaves it free.  Nothing here says the child's error is
its own fault, that the returndata means anything, or that either arm is
reached in any particular run. -/
theorem pauseCall_branchWord {sevm : Sevm} {target : Adr} {duration : B256}
    {callPre callPost mid : Devm}
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (run : Ninst.RunCompiled sevm callPost Ninst.iszero mid) :
    ∃ (child : Devm) (rest : List B256),
      callPost.stack = (if child.error.isSome then 0 else 1) :: rest ∧
      mid.stack = (if child.error.isSome then 1 else 0) :: rest ∧
      callPost.returnData = child.output ∧
      mid.returnData = child.output := by
  obtain ⟨parent, child, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hrd, hstk⟩ := boundary
  obtain ⟨hmidstk, hmidrd⟩ := iszero_inv run hstk
  refine ⟨child, parent.stack, hstk, ?_, hrd, hmidrd.trans hrd⟩
  rw [hmidstk]
  cases child.error.isSome <;>
    simp only [Bool.false_eq_true, if_false] <;> rfl

/-- **Both flag values occur in the relation, and only these two.**  A
`PauseCallBoundary` never leaves the branch a third possibility, and it never
decides which of the two it gets. -/
theorem pauseCall_flag_dichotomy {sevm : Sevm} {target : Adr} {duration : B256}
    {callPre callPost : Devm}
    (boundary : PauseCallBoundary sevm target duration callPre callPost) :
    callPost.stack.head? = some 0 ∨ callPost.stack.head? = some 1 := by
  obtain ⟨parent, child, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstk⟩ := boundary
  rw [hstk]
  cases child.error.isSome
  · exact Or.inr (by simp only [Bool.false_eq_true, if_false]; rfl)
  · exact Or.inl rfl

/-! ## Both arms

The ordering claim itself.  `Func.RunCompiledTo` rather than
`Func.RunCompiled` is the vehicle, because the bubble arm settles at a
**revert**: an `.ok`-only relation cannot state what the failing arm does, only
that it does not happen.  Both outcomes are in scope here, and which one occurs
is read off the derivation rather than assumed. -/

/-- `Func.RunCompiledTo` at a `.next` node, as an existential. -/
private lemma runCompiledTo_next_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {i : Ninst} {f : Func} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.next i f) ex) :
    ∃ mid, Ninst.RunCompiled sevm devm i mid ∧
      Func.RunCompiledTo fs sevm mid f ex := by
  cases h with | next hn hrest => exact ⟨_, hn, hrest⟩

/-- `Func.RunCompiledTo` at a `.branch` node: the word the branch pops decides
the arm, and the two arms are named by the word rather than by fiat. -/
private lemma runCompiledTo_branch_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {f g : Func} {ex : Execution}
    (h : Func.RunCompiledTo fs sevm devm (Func.branch f g) ex) :
    (∃ armPre, devm.stack = 0 :: armPre.stack ∧
        Devm.PopBurnBy [0] (gVerylow + gHigh) devm armPre ∧
        Func.RunCompiledTo fs sevm armPre f ex) ∨
      (∃ (w : B256) (armPre : Devm), w ≠ 0 ∧
        devm.stack = w :: armPre.stack ∧
        Devm.PopBurnBy [w] (gVerylow + gHigh + gJumpdest) devm armPre ∧
        Func.RunCompiledTo fs sevm armPre g ex) := by
  cases h with
  | zero hroom hpop harm => exact Or.inl ⟨_, hpop.stack, hpop, harm⟩
  | succ hne hroom hpop harm =>
    exact Or.inr ⟨_, _, hne, hpop.stack, hpop, harm⟩

/-- **The pause's post-CALL branch, inverted: both arms.**  A walk of the
`ISZERO` and the branch that follows the pause's `CALL` takes the bubble arm
exactly when the child errored, and the observation arm exactly when it did
not.  In both cases the state entering the arm still carries the child's
returndata.

The continuation `g` is arbitrary: this theorem is about the branch, not about
what the success arm goes on to do, and `pauseCall_successArm_reachesStatcall`
below instantiates it at the program's own observation arm.

**No premise constrains the callee.**  `child.error.isSome` is not assumed on
either side; it is produced, together with the arm the derivation actually
took.  Nothing here says the child's error is the child's fault, that a
successful child honoured the duration, or that the pause completes.  In
particular the success arm's conclusion is that the walk *continues*, not that
it succeeds. -/
theorem pauseAfterCall_arms {fs : List Func} {sevm : Sevm} {target : Adr}
    {duration : B256} {callPre callPost : Devm} {ex : Execution} {g : Func}
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (run : Func.RunCompiledTo fs sevm callPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) ex) :
    ∃ (child armPre : Devm) (rest : List B256),
      callPost.stack = (if child.error.isSome then 0 else 1) :: rest ∧
      callPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      ((child.error.isSome = true ∧
          Func.RunCompiledTo fs sevm armPre (Func.call bubbleRevertSlot) ex) ∨
        (child.error.isSome = false ∧
          Func.RunCompiledTo fs sevm armPre g ex)) := by
  obtain ⟨parent, child, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hrd, hstk⟩ := boundary
  obtain ⟨mid, hn, hrest⟩ := runCompiledTo_next_inv run
  obtain ⟨hmidstk, hmidrd⟩ := iszero_inv hn hstk
  rcases runCompiledTo_branch_inv hrest with
    ⟨armPre, hmid0, hpop, harm⟩ | ⟨w, armPre, hne, hmidw, hpop, harm⟩
  · -- the branch popped `0`: the `ISZERO` inverted a `1`, so the CALL succeeded
    have hw : ((if child.error.isSome then (0 : B256) else 1) =? 0) = 0 := by
      rw [hmidstk] at hmid0
      exact (List.cons.inj hmid0).1
    refine ⟨child, armPre, parent.stack, hstk, hrd,
      (hpop.returnData.symm.trans hmidrd).trans hrd,
      Or.inr ⟨?_, harm⟩⟩
    revert hw
    cases hc : child.error.isSome
    · intro; rfl
    · intro h; exact absurd h (by decide)
  · -- the branch popped a nonzero word: the `ISZERO` inverted a `0`
    have hw : ((if child.error.isSome then (0 : B256) else 1) =? 0) = w := by
      rw [hmidstk] at hmidw
      exact (List.cons.inj hmidw).1
    refine ⟨child, armPre, parent.stack, hstk, hrd,
      (hpop.returnData.symm.trans hmidrd).trans hrd,
      Or.inl ⟨?_, harm⟩⟩
    revert hw hne
    cases hc : child.error.isSome
    · intro hne hw; exact absurd (hw.symm.trans (by decide)) hne
    · intro _ _; rfl

/-! ## The failure arm: the bubble

`bubbleRevertSlot` is `13`, and `aux`'s thirteenth entry — `aux[12]`, since the
table is `main :: aux` — is `Func.revReturnData`, which copies the preceding
call's complete returndata to memory `0` and reverts with it.  The lookup is a
premise here rather than a computation, so that the statement is about
*whatever* the table binds at that slot and a witness discharges it against the
program it is actually running.

The arm is selected by the flag word on the CircuitBreaker's own stack, which
is what `pauseCall_flag_dichotomy` shows takes exactly the two values and
`pauseCall_branchWord` shows equals `child.error.isSome`.  That is the case
split C6 asks for, not a premise about the callee: the sibling theorem below
states the other case, and neither is assumed away. -/

/-- `Func.RunCompiledTo` at a `.call` node, against a known table entry. -/
private lemma runCompiledTo_call_inv {fs : List Func} {sevm : Sevm}
    {devm : Devm} {k : Nat} {f : Func} {ex : Execution}
    (h_get : fs[k]? = some f)
    (h : Func.RunCompiledTo fs sevm devm (Func.call k) ex) :
    ∃ mid, Devm.BurnBy (gVerylow + gMid + gJumpdest) devm mid ∧
      Func.RunCompiledTo fs sevm mid f ex := by
  cases h with
  | call hget hroom hburn hrest =>
    cases Option.some.inj (hget.symm.trans h_get)
    exact ⟨_, hburn, hrest⟩

/-- The CircuitBreaker's own table binds `bubbleRevertSlot` to
`Func.revReturnData`, so the lookup premise the bubble theorems carry is
discharged by the program itself rather than left to a consumer. -/
theorem runtime_bubbleRevertSlot (dp : DeployParams) :
    ((runtime dp).main :: (runtime dp).aux)[bubbleRevertSlot]? =
      some Func.revReturnData := rfl

/-- **The CALL's failure arm reaches the bubble, holding the callee's
returndata.**  When the flag the CALL pushed is `0` the branch's nonzero arm is
taken, that arm is the internal `.call` to `bubbleRevertSlot`, and the state
that enters the slot's body still carries `child.output` as its return data —
the `ISZERO`, the branch's own pop and the `.call`'s burn touch the stack and
the gas and nothing else.

What this does **not** claim.  It does not say the bubbled bytes mean anything:
`child.output` is whatever the hostile target chose to return, including
nothing at all, and `Func.revReturnData`'s own docstring records that a
zero-length child revert is an ordinary empty revert.  It does not say the
revert payload is byte-identical to `child.output` — that is the separate
`Func.revReturnData` walk, and constructing it (`callbackBubble_runCompiledTo`
is WETH10's instance) needs memory well-formedness, alignment and exact-gas
premises this cut does not carry; see this section's closing note.  And it does
not say this arm is reached: `h_fail` is the case hypothesis, discharged by a
caller that has a flag, never by an assumption about how the callee
behaves. -/
theorem pauseCall_failureArm_bubbles {fs : List Func} {sevm : Sevm}
    {target : Adr} {duration : B256} {callPre callPost : Devm}
    {ex : Execution} {g : Func}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (h_fail : callPost.stack.head? = some 0)
    (run : Func.RunCompiledTo fs sevm callPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) ex) :
    ∃ child bubblePre : Devm,
      child.error.isSome = true ∧
      callPost.returnData = child.output ∧
      bubblePre.returnData = child.output ∧
      Func.RunCompiledTo fs sevm bubblePre Func.revReturnData ex := by
  obtain ⟨child, armPre, rest, hstk, hrd, hard, harm⟩ :=
    pauseAfterCall_arms boundary run
  rcases harm with ⟨herr, hcall⟩ | ⟨herr, -⟩
  · obtain ⟨bubblePre, hburn, hbody⟩ := runCompiledTo_call_inv h_bubble hcall
    exact ⟨child, bubblePre, herr, hrd,
      (hburn.returnData.symm.trans hard), hbody⟩
  · exfalso
    rw [hstk, herr] at h_fail
    exact absurd (Option.some.inj h_fail) (by decide)

/-! ## The success arm: the observation

Only here does the pause reach its second message.  The staging line and the
`STATICCALL` are inside the branch's zero arm, so a derivation that gets to the
`.statcall` instruction has already produced the CALL's success flag. -/

/-- A walk of a `Line`-prefixed body splits at the line's end. -/
private lemma runCompiledTo_prepend_inv {fs : List Func} {sevm : Sevm}
    {l : Line} {f : Func} {ex : Execution} :
    ∀ {devm : Devm}, Func.RunCompiledTo fs sevm devm (l +++ f) ex →
      ∃ mid, Line.Run sevm devm l mid ∧
        Func.RunCompiledTo fs sevm mid f ex := by
  induction l with
  | nil => exact fun h => ⟨_, Line.Run.nil, h⟩
  | cons i l ih =>
    intro devm h
    obtain ⟨mid, hn, hrest⟩ := runCompiledTo_next_inv h
    obtain ⟨fin, hline, hf⟩ := ih hrest
    exact ⟨fin, Line.Run.cons (Ninst.Run.of_runCompiled hn) hline, hf⟩

/-- **The CALL's success arm is the only route to the STATICCALL.**  When the
flag the CALL pushed is `1` the branch's zero arm is taken, the walk runs
`pauseStatStaging` — the `isPaused()` selector restage and the six operands —
and then crosses the `.statcall` instruction itself, handing back exactly the
`Ninst.RunCompiled` premise `pauseStat_boundary` consumes.

What this does **not** claim.  It says nothing about the six operands' values:
that the staged target word is still the CircuitBreaker's is
`pauseCall_targetWord_survives`'s business, and it is proved there without a
cooperative-callee premise rather than assumed here.  It does not say the
observation succeeds, that the target answers, or that what comes back decodes
— the continuation is handed on as a walk, not as a result.  And it does not
say this arm is reached: `h_ok` is the case hypothesis, the sibling of
`pauseCall_failureArm_bubbles`'s `h_fail`, and `pauseCall_flag_dichotomy` shows
the two exhaust the possibilities. -/
theorem pauseCall_successArm_reachesStatcall {fs : List Func} {sevm : Sevm}
    {target : Adr} {duration : B256} {callPre callPost : Devm}
    {ex : Execution}
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (h_ok : callPost.stack.head? = some 1)
    (run : Func.RunCompiledTo fs sevm callPost pauseAfterCallBranch ex) :
    ∃ child armPre statPre statPost : Devm,
      child.error.isSome = false ∧
      callPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      Line.Run sevm armPre pauseStatStaging statPre ∧
      Ninst.RunCompiled sevm statPre (.exec .statcall) statPost ∧
      Func.RunCompiledTo fs sevm statPost
        (Ninst.iszero :::
          ((Func.call bubbleRevertSlot) <?> decodePausedResult)) ex := by
  rw [pauseAfterCallBranch] at run
  obtain ⟨child, armPre, rest, hstk, hrd, hard, harm⟩ :=
    pauseAfterCall_arms boundary run
  rcases harm with ⟨herr, -⟩ | ⟨herr, hstat⟩
  · exfalso
    rw [hstk, herr] at h_ok
    exact absurd (Option.some.inj h_ok) (by decide)
  · rw [pauseStatArm] at hstat
    obtain ⟨statPre, hline, hrest⟩ := runCompiledTo_prepend_inv hstat
    obtain ⟨statPost, hcross, htail⟩ := runCompiledTo_next_inv hrest
    exact ⟨child, armPre, statPre, statPost, herr, hrd, hard, hline, hcross,
      htail⟩

/-! ## What the failure arm settles at

`Func.revReturnData` ends in `REVERT`, and `Blanc/SourceAttainment.lean`'s
finite certificate already knows what that means for a whole body.  Two
consequences are worth naming separately, because together they are the honest
statement of "the pause bubbles": the arm the failing call takes cannot commit,
and — contrapositively — a post-CALL walk that *does* commit was on the
success arm all along.

The byte-level payload is settled below by `pauseCall_failureArm_payload`,
against `Func.runCompiledTo_revReturnData_inv`.  Of the three obstacles this
note used to list, two are gone: the read-after-write lemma exists, and the
`REVERT`'s memory expansion needed no gas premise at all, because every earlier
step of `Func.RunCompiledTo` witnesses that its own instruction succeeded.

What remains is **not** removable and is stated as a disjunct rather than
assumed away: without `memory.size % 32 = 0` the `REVERT`'s own expansion charge
is not provably zero — memory size `33` with a `33`-byte payload expands to
`ceil32 33 = 64` — so no honest inequality in `gasLeft` alone refutes it.

The `B256` round-trip is also unresolved, and deliberately so.  Collapsing
`take (n.toB256).toNat` to the whole list needs `n < 2 ^ 256` for the child's
output length, which is not a fact about this edge but the invariant that every
`Devm` reachable under `Exec` has bounded output — an induction over `Exec` and
every precompile, belonging upstream rather than in a contract module.  The raw
form is carried instead. -/

/-- `Func.revReturnData` is certified-reverting against any table: it contains
no `.call`, so the certificate does not consult one. -/
private lemma revReturnData_alwaysReverts (fs : List Func) :
    Func.alwaysRevertsWithin 7 fs Func.revReturnData = true := rfl

/-- The bubble slot is certified-reverting once the table is known to bind it
to `Func.revReturnData`. -/
private lemma bubbleCall_alwaysReverts {fs : List Func}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData) :
    Func.alwaysRevertsWithin 8 fs (Func.call bubbleRevertSlot) = true := by
  show (match fs[bubbleRevertSlot]? with
    | none => false
    | some body => Func.alwaysRevertsWithin 7 fs body) = true
  rw [h_bubble]
  exact revReturnData_alwaysReverts fs

/-- **The failure arm cannot commit.**  When the flag the CALL pushed is `0`,
the walk of the pause's post-CALL fragment settles at an outcome that does not
commit — the bubble's `REVERT` is the only terminal it can reach.

This says nothing about the payload, and nothing about the callee beyond the
flag it caused: a target that reverts and a target that returns failure some
other way are treated alike, because `PauseCallBoundary` distinguishes them
not at all. -/
theorem pauseCall_failureArm_neverCommits {fs : List Func} {sevm : Sevm}
    {target : Adr} {duration : B256} {callPre callPost : Devm}
    {ex : Execution} {g : Func}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (h_fail : callPost.stack.head? = some 0)
    (run : Func.RunCompiledTo fs sevm callPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) ex) :
    Execution.commits ex = false := by
  obtain ⟨child, bubblePre, -, -, -, hbody⟩ :=
    pauseCall_failureArm_bubbles h_bubble boundary h_fail run
  exact Func.RunCompiledTo.not_commits_of_alwaysRevertsWithin 7 hbody
    (revReturnData_alwaysReverts fs)

/-- **The observation is reachable only after a successful CALL.**  The
ordering claim with no case hypothesis at all: any *successful* walk of the
pause's post-CALL fragment took the branch's zero arm, and that arm exists only
because the child did not error.  The failure arm is excluded by its own
terminal, not by a premise.

This is the `.ok` shadow of `pauseAfterCall_arms`, and it is the form a caller
that already holds a `Func.RunCompiled` derivation wants: it converts "the
frame got past the branch" into "the `pauseFor(uint256)` call succeeded",
without ever asking what the target did to succeed.  It still claims nothing
about the observation that follows — only that the walk continues into it. -/
theorem pauseAfterCall_ok_forces_callSuccess {fs : List Func} {sevm : Sevm}
    {target : Adr} {duration : B256} {callPre callPost post : Devm} {g : Func}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (run : Func.RunCompiled fs sevm callPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) post) :
    ∃ child armPre : Devm,
      child.error.isSome = false ∧
      callPost.returnData = child.output ∧
      armPre.returnData = child.output ∧
      Func.RunCompiled fs sevm armPre g post := by
  obtain ⟨child, armPre, rest, -, hrd, hard, harm⟩ :=
    pauseAfterCall_arms boundary (Func.RunCompiledTo.of_runCompiled run)
  rcases harm with ⟨-, hcall⟩ | ⟨herr, hstat⟩
  · exact (Func.RunCompiledTo.not_ok_of_alwaysRevertsWithin 8 hcall
      (bubbleCall_alwaysReverts h_bubble)).elim
  · exact ⟨child, armPre, herr, hrd, hard,
      Func.RunCompiled.of_runCompiledTo_ok hstat⟩

/-! ## What the failure arm outputs

The note above listed three things standing between this boundary and the
byte-level payload, and recorded that turning `Func.runCompiledTo_revReturnData`
into an inversion was separate work.  That work now exists upstream as
`Func.runCompiledTo_revReturnData_inv`, which reads the settled outcome off an
arbitrary derivation of the walk and carries no premise at all — not about gas,
not about the frame's memory, not about the callee.  Applying it to the bubble
that `pauseCall_failureArm_bubbles` already hands over is all that remains.

One of the three obstructions survives the inversion, and it is stated rather
than assumed away.  `Func.revReturnData` ends in a `REVERT` over the window it
has just filled, and that `REVERT` pays its own memory-expansion charge; the
walk says nothing about the gas left when the charge falls due, so the pause
frame may settle at an out-of-gas exceptional halt instead.  No bound on
`gasLeft` alone refutes that leg either: the expansion is free only at an
aligned memory size, and at an unaligned one it is genuinely nonzero — size
`33` with a 33-byte payload expands to `ceil32 33 = 64` — while this cut
carries no alignment fact about the CircuitBreaker's memory.  So the conclusion
below is a **two-leg disjunction**, and its left leg is real. -/

/-- **What the failure arm outputs: out of gas, or the callee's bytes.**  When
the flag the CALL pushed is `0`, the pause frame settles in exactly one of two
ways — it ran out of gas at the bubble's own `REVERT`, or it reverted carrying
the callee's returndata as its payload.

Read the disjunction as written; this is **not** an unconditional payload
claim.  The left leg is the bubble's `REVERT` refusing its own
memory-expansion charge, and it is frame-local: the CircuitBreaker's gas, not
the callee's and not the caller's.  It is not removable at this cut, for the
reason the section note above records.

The payload is stated as `List.take` at the `B256` round trip of the child
output's length, because that is what the machine copies: `RETURNDATACOPY`
moves `size` bytes where `size` is the word `RETURNDATASIZE` pushed.  It is the
*whole* of `child.output` at every length a real execution can produce, since
`List.take n xs = xs` as soon as `xs.length ≤ n`, and `(Nat.toB256 n).toNat = n`
for `n < 2 ^ 256`.  Collapsing it to `child.output` in the statement would take
`child.output.length < 2 ^ 256` as a hypothesis — a premise about what the
callee returned, and this module admits none.  The bound is true of every
reachable execution, but deriving it is an invariant over `Exec` and the
precompiles, not a consequence of this boundary.

What this does **not** claim.  It does not say the bubbled bytes mean anything:
`child.output` is whatever the hostile target chose to return, empty included,
and `Func.revReturnData`'s own docstring records that a zero-length child
revert is an ordinary empty revert.  And it does not say this arm is reached —
`h_fail` is the case hypothesis, the sibling of
`pauseCall_successArm_reachesStatcall`'s `h_ok`, and
`pauseCall_flag_dichotomy` shows the two exhaust the possibilities. -/
theorem pauseCall_failureArm_payload {fs : List Func} {sevm : Sevm}
    {target : Adr} {duration : B256} {callPre callPost : Devm}
    {ex : Execution} {g : Func}
    (h_bubble : fs[bubbleRevertSlot]? = some Func.revReturnData)
    (boundary : PauseCallBoundary sevm target duration callPre callPost)
    (h_fail : callPost.stack.head? = some 0)
    (run : Func.RunCompiledTo fs sevm callPost
      (Ninst.iszero ::: ((Func.call bubbleRevertSlot) <?> g)) ex) :
    ∃ child : Devm,
      child.error.isSome = true ∧
      callPost.returnData = child.output ∧
      ((∃ d, ex = .error (.halt (.outOfGas .none), d)) ∨
        (∃ post, ex = .error (.revert, post) ∧
          post.output =
            child.output.take child.output.length.toB256.toNat)) := by
  obtain ⟨child, bubblePre, herr, hrd, hard, hbody⟩ :=
    pauseCall_failureArm_bubbles h_bubble boundary h_fail run
  refine ⟨child, herr, hrd, ?_⟩
  rcases Func.runCompiledTo_revReturnData_inv hbody with
    h_oog | ⟨post, hpost, hout⟩
  · exact Or.inl h_oog
  · exact Or.inr ⟨post, hpost, by rw [hout, hard]⟩

/-! ## The staged calldata

`pauseCall_boundary`'s `h_window` premise asks for the 36 bytes at `0x11c`.
This section discharges it from the staged duration word alone, so that the
duration's provenance closes inside the staging line rather than being threaded
through the pause route.

The arithmetic is entirely about the CircuitBreaker's own memory: `mstoreAt 8`
writes `[256, 288)`, `mstoreAt 9` writes `[288, 320)`, a selector sits
right-aligned in its word so its four bytes are `[284, 288)`, and
`0x11c = 284`.  The CALL's window `[284, 320)` is therefore the selector's four
bytes followed by the whole duration word, which is `pauseForCalldata`. -/

private lemma sliceD_split {ξ : Type} (xs : List ξ) (d : ξ) :
    ∀ (a m b : Nat),
      xs.sliceD m (a + b) d = xs.sliceD m a d ++ xs.sliceD (m + a) b d := by
  intro a
  induction a with
  | zero => intro m b; simp [List.sliceD, List.takeD]
  | succ a ih =>
    intro m b
    rw [show a + 1 + b = (a + b) + 1 from by omega, List.sliceD_succ,
      ih (m + 1) b, List.sliceD_succ xs m a d,
      show m + (a + 1) = m + 1 + a from by omega]
    rfl

private lemma drop_of_length_append {ξ : Type} (A B : List ξ) (n : Nat)
    (h : A.length = n) : (A ++ B).drop n = B := by
  subst h; exact List.drop_left

/-- The 36 bytes the CALL's window reads out of an image carrying a selector
word at `256` and a value word at `288`: the selector's low four bytes followed
by the whole value word.  Pure `Bytes` arithmetic — no `Devm` and no run. -/
private lemma sliceD_stagedCalldata (img : Bytes) (sel dur : B256) :
    (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
        288 (B256.toBytes dur)).sliceD 284 36 0 =
      abiSelectorBytes sel ++ B256.toBytes dur := by
  have hsel : (B256.toBytes sel).length = 32 := B256.length_toBytes sel
  have hdur : (B256.toBytes dur).length = 32 := B256.length_toBytes dur
  have hhigh :
      (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
        288 (B256.toBytes dur)).sliceD 288 32 0 = B256.toBytes dur := by
    have h := Bytes.sliceD_writeAt
      (Bytes.writeAt img 256 (B256.toBytes sel)) (B256.toBytes dur) 288
    rwa [hdur] at h
  have hlow0 :
      (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
        288 (B256.toBytes dur)).sliceD 284 4 0 =
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0 :=
    Bytes.sliceD_writeAt_before _ _ 284 4 288 (by omega)
  have hword :
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 32 0 =
        B256.toBytes sel := by
    have h := Bytes.sliceD_writeAt img (B256.toBytes sel) 256
    rwa [hsel] at h
  have hinner := sliceD_split
    (Bytes.writeAt img 256 (B256.toBytes sel)) (0 : UInt8) 28 256 4
  simp only [show (28 : Nat) + 4 = 32 from rfl,
    show (256 : Nat) + 28 = 284 from rfl] at hinner
  have hA : ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0).length
      = 28 := List.takeD_length _ _ _
  have hlow :
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0 =
        abiSelectorBytes sel := by
    have hd : abiSelectorBytes sel =
        ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0 ++
            (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0).drop
          28 := by
      rw [← hinner, hword]
      rfl
    rw [hd, drop_of_length_append _ _ 28 hA]
  have houter := sliceD_split
    (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes sel))
      288 (B256.toBytes dur)) (0 : UInt8) 4 284 32
  simp only [show (4 : Nat) + 32 = 36 from rfl,
    show (284 : Nat) + 4 = 288 from rfl] at houter
  rw [houter, hlow0, hlow, hhigh]

/-- **The staging line builds `pauseFor(uint256)`'s calldata.**  From nothing
but the staged duration word, the CALL's argument window at `0x11c` reads back
as the canonical encoder's 36 bytes.

This is a statement about the CircuitBreaker's own memory across its own
straight-line code.  There is no callee in it: `pauseCallStaging` runs strictly
*before* the `CALL`, so no premise here could constrain a target even in
principle, and none is present — the only hypothesis is that memory reads
`duration` at the duration word, which is where `pause` put it. -/
theorem pauseCallStaging_calldata {sevm : Sevm} {entry callPre : Devm}
    {duration : B256}
    (hword : MemWordAt entry (durationWord * 32).toNat duration)
    (hstaging : Line.Run sevm entry pauseCallStaging callPre) :
    (callPre.memory.read 0x11c 36).1 = pauseForCalldata duration := by
  obtain ⟨hwf0, img, hreads0, hslice0⟩ := hword
  have hdw : ((durationWord : B256) * 32).toNat = 736 := by decide
  have hsel8 : ((8 : B256) * 32).toNat = 256 := by decide
  have hsel9 : ((9 : B256) * 32).toNat = 288 := by decide
  have hlensel : (B256.toBytes pauseForSelector).length = 32 :=
    B256.length_toBytes pauseForSelector
  unfold pauseCallStaging at hstaging
  simp only [List.append_assoc] at hstaging
  -- `POP` and the selector push: memory untouched, selector on top
  obtain ⟨s1, h1, hstaging⟩ := of_run_append _ hstaging
  have hm1 : entry.memory = s1.memory :=
    Line.of_inv Devm.memory (by line_inv) h1
  have hp1 : pauseForSelector :: [] <<+ s1.stack := by
    rcases Line.of_run_cons h1 with ⟨u1, -, h1'⟩
    rcases Line.of_run_cons h1' with ⟨u2, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) nil_pref
  have hwf1 : Mem.Wf s1.memory := by rw [← hm1]; exact hwf0
  have hr1 : Mem.Reads s1.memory img := by rw [← hm1]; exact hreads0
  -- `mstoreAt 8`: the selector word lands at 256
  obtain ⟨s2, h2, hstaging⟩ := of_run_append _ hstaging
  obtain ⟨-, hm2⟩ := of_run_mstoreAt_val h2 hp1
  rw [hsel8] at hm2
  have hwf2 : Mem.Wf s2.memory := by rw [hm2]; exact hwf1.write _ _
  have hr2 : Mem.Reads s2.memory
      (Bytes.writeAt img 256 (B256.toBytes pauseForSelector)) := by
    rw [hm2]; exact Mem.Reads.write hwf1 hr1 _ _
  -- `loadWord durationWord`: the staged word comes back, untouched by the
  -- selector write, which lands 448 bytes below it
  obtain ⟨s3, h3, hstaging⟩ := of_run_append _ hstaging
  have hslice1 :
      (Bytes.writeAt img 256 (B256.toBytes pauseForSelector)).sliceD 736 32 0 =
        B256.toBytes duration := by
    rw [Bytes.sliceD_writeAt_after img (B256.toBytes pauseForSelector)
      736 32 256 (by rw [hlensel]; omega)]
    rw [← hdw]; exact hslice0
  have hp3 : duration :: [] <<+ s3.stack ∧ Mem.Wf s3.memory ∧
      Mem.Reads s3.memory
        (Bytes.writeAt img 256 (B256.toBytes pauseForSelector)) := by
    rcases Line.of_run_cons h3 with ⟨v1, hoff, h3'⟩
    rcases Line.of_run_cons h3' with ⟨v2, hml, hnil⟩
    cases hnil
    have hpb := of_run_pushB256 hoff
    obtain ⟨hstk, hmem, -⟩ :=
      prefix_of_mload_val hml (prefix_of_push hpb nil_pref)
        (by rw [← hpb.memory]; exact hr2)
    rw [hdw, hslice1, B256.toB256_toBytes] at hstk
    refine ⟨hstk, ?_, ?_⟩
    · rw [hmem, ← hpb.memory]; exact hwf2.extend _ _
    · rw [hmem, ← hpb.memory]; exact hr2.extend _ _
  obtain ⟨hp3stk, hwf3, hr3⟩ := hp3
  -- `mstoreAt 9`: the duration word lands at 288, directly above the selector
  obtain ⟨s4, h4, hstaging⟩ := of_run_append _ hstaging
  obtain ⟨-, hm4⟩ := of_run_mstoreAt_val h4 hp3stk
  rw [hsel9] at hm4
  have hr4 : Mem.Reads s4.memory
      (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes pauseForSelector))
        288 (B256.toBytes duration)) := by
    rw [hm4]; exact Mem.Reads.write hwf3 hr3 _ _
  have hwf4 : Mem.Wf s4.memory := by rw [hm4]; exact hwf3.write _ _
  -- the five constant pushes, the target load and `GAS` only extend memory
  obtain ⟨s5, h5, hstaging⟩ := of_run_append _ hstaging
  have hm5 : s4.memory = s5.memory := by
    refine Line.of_inv Devm.memory ?_ h5
    unfold pushList
    simp only [List.map]
    line_inv
  obtain ⟨s6, h6, h7⟩ := of_run_append _ hstaging
  obtain ⟨i6, hm6⟩ := of_run_loadWord_mem h6
  have hm7 : s6.memory = callPre.memory :=
    Line.of_inv Devm.memory (by line_inv) h7
  have hrFinal : Mem.Reads callPre.memory
      (Bytes.writeAt (Bytes.writeAt img 256 (B256.toBytes pauseForSelector))
        288 (B256.toBytes duration)) := by
    rw [← hm7, hm6, ← hm5]
    exact hr4.extend _ _
  rw [Mem.Reads.read hrFinal 0x11c 36]
  exact sliceD_stagedCalldata img pauseForSelector duration

/-! ## The joined boundary

The pieces above each cover one edge, one survival fact or one arm.  What none
of them says alone is the sentence the cut is for: *at a pause's external
boundary these are the CircuitBreaker's two outgoing messages, both to that
target, in that order.*

Joining them is not a conjunction.  Both boundary relations are stated at an
operand stack, and a joined statement that took those stack shapes as premises
would be worthless — the shapes are exactly what a consumer cannot check.  So
they are **derived**: `pauseCallStaging` and `pauseStatStaging` are walked
forward from the staged target word, and the seven and six operands come out of
the staging lines rather than out of a hypothesis.  The second walk starts from
the word `pauseCall_targetWord_survives` carried across the CALL, so nothing in
it assumes the callee left memory alone. -/

/-- The four selector bytes an `mstoreAt 8` leaves in the CALL's window: a
selector sits right-aligned in its word, so `[284, 288)` is its low four
bytes.  Pure `Bytes` arithmetic — the selector-only half of what
`sliceD_stagedCalldata` proves for the 36-byte encoding. -/
private lemma sliceD_stagedSelector (img : Bytes) (sel : B256) :
    (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0 =
      abiSelectorBytes sel := by
  have hsel : (B256.toBytes sel).length = 32 := B256.length_toBytes sel
  have hword :
      (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 32 0 =
        B256.toBytes sel := by
    have h := Bytes.sliceD_writeAt img (B256.toBytes sel) 256
    rwa [hsel] at h
  have hinner := sliceD_split
    (Bytes.writeAt img 256 (B256.toBytes sel)) (0 : UInt8) 28 256 4
  simp only [show (28 : Nat) + 4 = 32 from rfl,
    show (256 : Nat) + 28 = 284 from rfl] at hinner
  have hA : ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0).length
      = 28 := List.takeD_length _ _ _
  have hd : abiSelectorBytes sel =
      ((Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 256 28 0 ++
          (Bytes.writeAt img 256 (B256.toBytes sel)).sliceD 284 4 0).drop
        28 := by
    rw [← hinner, hword]
    rfl
  rw [hd, drop_of_length_append _ _ 28 hA]

/-- **The observation's staging line builds `isPaused()`'s calldata.**  The
selector is pushed and stored inside the line itself, so the only thing needed
from before it is that memory has *some* image — no premise about what the
callee left there. -/
private lemma pauseStatStaging_calldata {sevm : Sevm} {armPre statPre : Devm}
    (himage : ∃ img : Bytes, MemImage armPre img)
    (hstaging : Line.Run sevm armPre pauseStatStaging statPre) :
    (statPre.memory.read 0x11c 4).1 = isPausedCalldata := by
  obtain ⟨img, hwf0, hreads0⟩ := himage
  have hsel8 : ((8 : B256) * 32).toNat = 256 := by decide
  unfold pauseStatStaging at hstaging
  simp only [List.append_assoc] at hstaging
  -- the selector push: memory untouched, selector on top
  obtain ⟨s1, h1, hstaging⟩ :=
    of_run_append [Ninst.pushB256 isPausedSelector] hstaging
  have hm1 : armPre.memory = s1.memory :=
    Line.of_inv Devm.memory (by line_inv) h1
  have hp1 : isPausedSelector :: [] <<+ s1.stack := by
    rcases Line.of_run_cons h1 with ⟨u1, hpush, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 hpush) nil_pref
  have hwf1 : Mem.Wf s1.memory := by rw [← hm1]; exact hwf0
  have hr1 : Mem.Reads s1.memory img := by rw [← hm1]; exact hreads0
  -- `mstoreAt 8`: the selector word lands at 256
  obtain ⟨s2, h2, hstaging⟩ := of_run_append (mstoreAt 8) hstaging
  obtain ⟨-, hm2⟩ := of_run_mstoreAt_val h2 hp1
  rw [hsel8] at hm2
  have hr2 : Mem.Reads s2.memory
      (Bytes.writeAt img 256 (B256.toBytes isPausedSelector)) := by
    rw [hm2]; exact Mem.Reads.write hwf1 hr1 _ _
  -- the four constant pushes, the target load and `GAS` only extend memory
  obtain ⟨s3, h3, hstaging⟩ := of_run_append (pushList [32, 0, 4, 0x11c]) hstaging
  have hm3 : s2.memory = s3.memory := by
    refine Line.of_inv Devm.memory ?_ h3
    unfold pushList
    simp only [List.map]
    line_inv
  obtain ⟨s4, h4, h5⟩ := of_run_append (loadWord targetWord) hstaging
  obtain ⟨i4, hm4⟩ := of_run_loadWord_mem h4
  have hm5 : s4.memory = statPre.memory :=
    Line.of_inv Devm.memory (by line_inv) h5
  have hrFinal : Mem.Reads statPre.memory
      (Bytes.writeAt img 256 (B256.toBytes isPausedSelector)) := by
    rw [← hm5, hm4, ← hm3]
    exact hr2.extend _ _
  rw [Mem.Reads.read hrFinal 0x11c 4]
  exact sliceD_stagedSelector img isPausedSelector

/-- **The CALL's seven operands, derived.**  `pauseCallStaging`'s tail is
`pushList [0, 0, 36, 0x11c, 0] ++ loadWord targetWord ++ [GAS]`, so the operand
stack at the `CALL` is forced by the line and the staged target word: nothing
about it is assumed.  The window is handed on as well, for the crossing. -/
private lemma pauseCallStaging_operands {sevm : Sevm} {entry callPre : Devm}
    {target : B256}
    (hword : MemWordAt entry (targetWord * 32).toNat target)
    (hstaging : Line.Run sevm entry pauseCallStaging callPre) :
    ∃ (gasWord : B256) (rest : List B256),
      callPre.stack =
        gasWord :: target :: 0 :: 0x11c :: 36 :: 0 :: 0 :: rest ∧
      MemWordAt callPre (targetWord * 32).toNat target := by
  unfold pauseCallStaging at hstaging
  simp only [List.append_assoc] at hstaging
  obtain ⟨t1, u1, hstaging⟩ :=
    of_run_append [Ninst.pop, Ninst.pushB256 pauseForSelector] hstaging
  obtain ⟨t2, u2, hstaging⟩ := of_run_append (mstoreAt 8) hstaging
  obtain ⟨t3, u3, hstaging⟩ := of_run_append (loadWord durationWord) hstaging
  obtain ⟨t4, u4, hstaging⟩ := of_run_append (mstoreAt 9) hstaging
  obtain ⟨t5, u5, hstaging⟩ :=
    of_run_append (pushList [0, 0, 36, 0x11c, 0]) hstaging
  obtain ⟨t6, u6, hstaging⟩ := of_run_append (loadWord targetWord) hstaging
  have wt5 : MemWordAt t5 (targetWord * 32).toNat target :=
    ((((hword.acrossLine (by line_inv) u1).acrossMstoreAt (by decide)
      u2).acrossLoadWord u3).acrossMstoreAt (by decide) u4).acrossLine
      (by line_inv) u5
  have p5 : (0 : B256) :: 0x11c :: 36 :: 0 :: 0 :: [] <<+ t5.stack := by
    simp only [pushList, List.map] at u5
    rcases Line.of_run_cons u5 with ⟨_v1, x1, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v2, x2, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v3, x3, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v4, x4, u5⟩
    rcases Line.of_run_cons u5 with ⟨_v5, x5, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 x5)
      (prefix_of_push (of_run_pushB256 x4)
        (prefix_of_push (of_run_pushB256 x3)
          (prefix_of_push (of_run_pushB256 x2)
            (prefix_of_push (of_run_pushB256 x1) nil_pref))))
  have p6 : target :: 0 :: 0x11c :: 36 :: 0 :: 0 :: [] <<+ t6.stack :=
    prefix_of_loadWord_window wt5 p5 u6
  have wt6 := wt5.acrossLoadWord u6
  rcases Line.of_run_cons hstaging with ⟨_t7, qg, hnil⟩
  cases hnil
  obtain ⟨gw, pbg⟩ := of_run_gas qg
  obtain ⟨rest, hrest⟩ := prefix_of_push pbg p6
  exact ⟨gw, rest, hrest, wt6.acrossNinst qg⟩

/-- **The STATICCALL's six operands, derived.**  Same shape as its CALL
sibling: `pauseStatStaging`'s tail is `pushList [32, 0, 4, 0x11c] ++
loadWord targetWord ++ [GAS]`, so the operand stack at the `STATICCALL` follows
from the line and the staged target word.  The word this consumes is the one
`pauseCall_targetWord_survives` carries across the CALL, never an assumption
that the callee left memory alone. -/
private lemma pauseStatStaging_operands {sevm : Sevm} {armPre statPre : Devm}
    {target : B256}
    (hword : MemWordAt armPre (targetWord * 32).toNat target)
    (hstaging : Line.Run sevm armPre pauseStatStaging statPre) :
    ∃ (gasWord : B256) (rest : List B256),
      statPre.stack = gasWord :: target :: 0x11c :: 4 :: 0 :: 32 :: rest ∧
      MemWordAt statPre (targetWord * 32).toNat target := by
  unfold pauseStatStaging at hstaging
  simp only [List.append_assoc] at hstaging
  obtain ⟨y1, v1, hstaging⟩ :=
    of_run_append [Ninst.pushB256 isPausedSelector] hstaging
  obtain ⟨y2, v2, hstaging⟩ := of_run_append (mstoreAt 8) hstaging
  obtain ⟨y3, v3, hstaging⟩ :=
    of_run_append (pushList [32, 0, 4, 0x11c]) hstaging
  obtain ⟨y4, v4, hstaging⟩ := of_run_append (loadWord targetWord) hstaging
  have wy3 : MemWordAt y3 (targetWord * 32).toNat target :=
    ((hword.acrossLine (by line_inv) v1).acrossMstoreAt (by decide)
      v2).acrossLine (by line_inv) v3
  have q3 : (0x11c : B256) :: 4 :: 0 :: 32 :: [] <<+ y3.stack := by
    simp only [pushList, List.map] at v3
    rcases Line.of_run_cons v3 with ⟨_z1, c1, v3⟩
    rcases Line.of_run_cons v3 with ⟨_z2, c2, v3⟩
    rcases Line.of_run_cons v3 with ⟨_z3, c3, v3⟩
    rcases Line.of_run_cons v3 with ⟨_z4, c4, hnil⟩
    cases hnil
    exact prefix_of_push (of_run_pushB256 c4)
      (prefix_of_push (of_run_pushB256 c3)
        (prefix_of_push (of_run_pushB256 c2)
          (prefix_of_push (of_run_pushB256 c1) nil_pref)))
  have q4 : target :: 0x11c :: 4 :: 0 :: 32 :: [] <<+ y4.stack :=
    prefix_of_loadWord_window wy3 q3 v4
  have wy4 := wy3.acrossLoadWord v4
  rcases Line.of_run_cons hstaging with ⟨_y5, qg, hnil⟩
  cases hnil
  obtain ⟨gw, pbg⟩ := of_run_gas qg
  obtain ⟨rest, hrest⟩ := prefix_of_push pbg q4
  exact ⟨gw, rest, hrest, wy4.acrossNinst qg⟩

/-- Public successor for the CALL staging operand extractor.  This is the
exact premise `pauseCall_boundary` consumes. -/
theorem pauseCallStaging_boundary_operands
    {sevm : Sevm} {entry callPre : Devm} {target : B256}
    (hword : MemWordAt entry (targetWord * 32).toNat target)
    (hstaging : Line.Run sevm entry pauseCallStaging callPre) :
    ∃ (gasWord : B256) (rest : List B256),
      callPre.stack =
        gasWord :: target :: 0 :: 0x11c :: 36 :: 0 :: 0 :: rest ∧
      MemWordAt callPre (targetWord * 32).toNat target :=
  pauseCallStaging_operands hword hstaging

/-- Public successor for the STATICCALL staging operand extractor. -/
theorem pauseStatStaging_boundary_operands
    {sevm : Sevm} {armPre statPre : Devm} {target : B256}
    (hword : MemWordAt armPre (targetWord * 32).toNat target)
    (hstaging : Line.Run sevm armPre pauseStatStaging statPre) :
    ∃ (gasWord : B256) (rest : List B256),
      statPre.stack = gasWord :: target :: 0x11c :: 4 :: 0 :: 32 :: rest ∧
      MemWordAt statPre (targetWord * 32).toNat target :=
  pauseStatStaging_operands hword hstaging

/-- Public successor for the STATICCALL staging calldata extractor. -/
theorem pauseStatStaging_boundary_calldata
    {sevm : Sevm} {armPre statPre : Devm}
    (himage : ∃ img : Bytes, MemImage armPre img)
    (hstaging : Line.Run sevm armPre pauseStatStaging statPre) :
    (statPre.memory.read 0x11c 4).1 = isPausedCalldata :=
  pauseStatStaging_calldata himage hstaging

/-- **The pause's external boundary, joined.**  From the two staged words and
the two crossings: the CALL is `PauseCallBoundary`'s message to `target`, the
staged target word is still the CircuitBreaker's when the observation is
staged, and the STATICCALL is `PauseStatBoundary`'s message to the **same**
target.  The order is in the statement's own shape — `callPost` is where
`pauseStatStaging` starts — and `pauseCall_successArm_reachesStatcall` is what
supplies that walk from the program.

Neither operand stack is a premise.  Both are derived by forward evaluation of
the staging lines, and the second is derived from the target word that
`pauseCall_targetWord_survives` carries across the CALL, so no hypothesis here
says the callee left memory, storage or anything else alone.

What this does **not** claim about a hostile target.  It says nothing about
what the target does with either message, what it returns, whether it honours
the duration, or whether the pause completes; the published callback-visible
liveness counterexample stands unchanged.  It does not say the two crossings
are reached in any particular run — `hCall` and `hStat` are derivations handed
in, and `hDepth`/`hDynamic` are the enclosing frame's honest premises.  And, as
in `PauseStatBoundary` itself, `msg.isStatic = true` on the observation is a
property of the **message the CircuitBreaker builds**, not a theorem that the
child changed no state: deriving that would need a static-context no-write
result over arbitrary code, which exists nowhere in Jaune or Blanc and is not
built here. -/
theorem pause_externalBoundary {sevm : Sevm} {target : Adr} {duration : B256}
    {entry callPre callPost statPre statPost : Devm}
    (hTarget : MemWordAt entry (targetWord * 32).toNat target.toB256)
    (hDuration : MemWordAt entry (durationWord * 32).toNat duration)
    (hCallStaging : Line.Run sevm entry pauseCallStaging callPre)
    (hDepth : sevm.depth ≠ 0)
    (hDynamic : sevm.isStatic = false)
    (hCall : Ninst.RunCompiled sevm callPre (.exec .call) callPost)
    (hStatStaging : Line.Run sevm callPost pauseStatStaging statPre)
    (hStat : Ninst.RunCompiled sevm statPre (.exec .statcall) statPost) :
    PauseCallBoundary sevm target duration callPre callPost ∧
      MemWordAt statPre (targetWord * 32).toNat target.toB256 ∧
      PauseStatBoundary sevm target statPre statPost := by
  obtain ⟨gasWord, rest, hstk, wCall⟩ :=
    pauseCallStaging_operands hTarget hCallStaging
  have hcall : PauseCallBoundary sevm target duration callPre callPost :=
    pauseCall_boundary hstk
      (pauseCallStaging_calldata hDuration hCallStaging) hDepth hDynamic hCall
  have wPost : MemWordAt callPost (targetWord * 32).toNat target.toB256 :=
    pauseCall_targetWord_survives hcall wCall
  obtain ⟨gasWord', rest', hstk', wStat⟩ :=
    pauseStatStaging_operands wPost hStatStaging
  exact ⟨hcall, wStat,
    pauseStat_boundary hstk'
      (pauseStatStaging_calldata wPost.memImage hStatStaging) hDepth hStat⟩

end Blanc.LidoCircuitBreaker
