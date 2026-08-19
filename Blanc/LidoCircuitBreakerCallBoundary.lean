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
theorem pauseCall_boundary {sevm : Sevm} {callPre callPost : Devm}
    {gasWord duration : B256} {target : Adr} {rest : List B256}
    (h_stk : callPre.stack =
      gasWord :: target.toB256 :: 0 :: 0x11c :: 36 :: 0 :: 0 :: rest)
    (h_window : (callPre.memory.read 0x11c 36).1 = pauseForCalldata duration)
    (h_depth : sevm.depth ≠ 0)
    (h_dynamic : sevm.isStatic = false)
    (run : Ninst.RunCompiled sevm callPre (.exec .call) callPost) :
    PauseCallBoundary sevm target duration callPre callPost := by
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
    refine ⟨parent, child,
      callMsg sevm parent mcs 0 sevm.currentTarget target target true false
        (pauseForCalldata duration) code dp,
      xl, dp, code, gasWord, mcs,
      by rw [hpstk]; exact h_stk, h_window, hpmem, hpstate, hpca, hptra, hplogs,
      hprd, h_depth, hdisj, rfl, rfl, rfl, rfl, rfl, ?_, rfl, hptra, hfill,
      hframe, hrun, hres', Resume.call_memory hres',
      Resume.call_returnData hres', Resume.call_stack_flag hres'⟩
    -- The one open conjunct.  `callMsg` sets `isStatic := isStaticcall ||
    -- sevm.isStatic` and a `CALL` passes `isStaticcall = false`, so this goal
    -- is definitionally `sevm.isStatic = false`: a property of the *caller's*
    -- frame, not of the message the CircuitBreaker builds and not of the
    -- callee.  A zero-value `CALL` is legal inside a static context — the
    -- static-context assertion in `Xinst.step`'s `.call` arm is discharged by
    -- `value = 0` — so nothing at this edge decides it.  It is the honest
    -- enclosing-frame premise `h_dynamic`; see the theorem's docstring for why
    -- a real pause always satisfies it.
    show sevm.isStatic = false
    exact h_dynamic

end Blanc.LidoCircuitBreaker
