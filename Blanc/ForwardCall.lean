-- ForwardCall.lean : crossing a `CALL`, forward.
--
-- `Blanc/Forward.lean` builds `Ninst.RunCompiled` derivations for every
-- instruction whose step is childless.  A `CALL` is not one of those: its step
-- outcome is a `.spawn`, its premise is genuinely existential in the child slot
-- (`Ninst.RunCompiled`'s `∃ xl, xl.Filled`), and the successor state is what
-- `Resume.run` makes of whatever the child settled at.  That is the one thing
-- the forward layer could not do, and this module is it.
--
-- Three things carry the weight, and each is small on its own.
--
-- * **The child comes from totality, never from a premise.**  Jaune's `exec` is
--   total and fuel-free (`Jaune/Sufficiency.lean`), `Blanc/Semantics.lean`'s
--   `exec_iff_exec_eq` is bidirectional for a general `Execution`, and
--   `Xlot.filled_exec` fills the slot for *any* machine.  So the slot obligation
--   an external call carries -- the one a proof about arbitrary callee bytecode
--   would normally have to assume away -- is discharged here by a theorem, at
--   `exec cevm`, with no premise about the callee at all.  Nothing below says
--   the child succeeds, terminates quickly, or behaves; it says only that its
--   derivation exists, which is what the caller then case-splits on.
-- * **The resume is characterised, not unfolded at the call site.**
--   `Resume.run (.call parent oi os)` has exactly three outcomes, and each is
--   one lemma: the settle propagated an error, the child settled with an error
--   set, the child settled clean.  The middle one is where the parent *keeps its
--   own warm sets* -- `incorporateChildOnError` copies state, transient storage,
--   created accounts, return data and gas and nothing else -- which is what
--   makes a post-`CALL` worst case deterministic rather than callee-controlled.
-- * **`value = 0` collapses the `.call` arm.**  Blanc's callbacks forward no
--   value, and at `value = 0` the new-account charge, the transfer charge and
--   the stipend are all zero, the static-context assertion passes on its right
--   disjunct, and the balance short-circuit `senderBal < 0` is unreachable.
--   What is left is one `min` and one `except64th`, which is the whole EIP-150
--   content at this altitude.  The nonzero-value case is not stated: no Blanc
--   contract needs it, and an unused generalisation of a lemma this shape is a
--   maintenance surface, not a capability.
--
-- Nothing here is contract-specific and nothing here mentions a `Func`: this is
-- the `Ninst`/`Xinst` altitude, and the walk that consumes it lives in a
-- contract-owned module.
--
-- The import is `Blanc/Reverts.lean` rather than `Blanc/Forward.lean` so that a
-- caller building a `Func.RunCompiledTo` walk has both layers from one import;
-- `Reverts.lean` imports `Forward.lean`, so nothing is duplicated.

import Blanc.Reverts

namespace Blanc

open Jaune

/-! ## The spawn premise, discharged by totality

`Ninst.RunCompiled sevm devm (.exec x) devm'` unfolds to
`∃ xl, xl.Filled ∧ ∀ pc, Ninst.StepRun pc sevm devm (.exec x) xl (.ok devm')`.
For a childless instruction the slot is `.none` and `Filled` is `True`; for a
spawning one it is a real obligation, and these three lemmas are the three ways
to meet it. -/

/-- A spawning instruction whose frame **enters**: the slot is filled at
`exec cevm` by `Xlot.filled_exec`, and the successor is whatever `Resume.run`
makes of the settle.

This is the arc's crossing lemma.  Read the premises: `h_step` is about the
parent's own state, `h_enter` is about the message the parent built, and
`h_res` is about the resume.  **There is no premise about the child.**  Its
derivation is `exec cevm`, an opaque term the caller case-splits on. -/
lemma Ninst.runCompiled_exec_run {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {cevm : Evm} {devm' : Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .run cevm)
    (h_res : rsm.run (f.settle (exec cevm)) = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.some ⟨cevm, exec cevm⟩, Xlot.filled_exec cevm, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨_, RunFrame.of_run h_enter, h_res.symm⟩

/-- A spawning instruction whose frame **does not enter** — the value transfer
failed, or the callee is a precompile.  No child machine exists, the slot is
`.none`, and `Filled` is `True`. -/
lemma Ninst.runCompiled_exec_doneFrame {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume} {devm' : Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_step : Xinst.step sevm devm x = .spawn f rsm)
    (h_enter : f.enter = .done r) (h_res : rsm.run r = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨r, RunFrame.of_done h_enter, h_res.symm⟩

/-- A call-type instruction that never spawns at all: `Xinst.step` itself
returned `.done`.  The depth-1024 arm below is the case this exists for. -/
lemma Ninst.runCompiled_exec_done {sevm : Sevm} {devm : Devm} {x : Xinst}
    {devm' : Devm} (h_step : Xinst.step sevm devm x = .done (.ok devm')) :
    Ninst.RunCompiled sevm devm (.exec x) devm' := by
  refine ⟨.none, trivial, fun pc => ?_⟩
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep]
  show XStep.Run (Xinst.step sevm devm x) _ _
  rw [h_step]
  exact ⟨rfl, rfl⟩

/-- `Devm.popToAdr`, evaluated forward — the mirror of `Blanc/Forward.lean`'s
`Devm.popToNat_eq_ok`, needed because a `CALL`'s second operand is an address.
It lives here rather than there for **A4**'s reason: `Blanc/Forward.lean`'s
elaboration row is the one this arc may not raise. -/
lemma Devm.popToAdr_eq_ok {x : B256} {s : List B256} {devm : Devm}
    (h : devm.stack = x :: s) :
    devm.popToAdr =
      .ok ⟨x.toAdr, devm.setMach ⟨s, devm.memory, devm.gasLeft⟩⟩ := by
  rw [Devm.popToAdr_def, Devm.pop_eq_ok h]
  rfl

/-! ## EIP-150, at `value = 0`

`calculateMsgCallGas` is where the 63/64 rule lives, and P4 of
`~/plans/adversarial-progress.md` settles that it is *frame-local*: the cap is
computed inside `Xinst.step`, and no transaction layer is touched.  At
`value = 0` the stipend vanishes and the pair collapses to one `min`. -/

/-- `calculateMsgCallGas` at `value = 0`, in the branch where the frame can
afford its own overhead.  The forwarded amount is `min` of what the operand
asked for and the 63/64 cap; the stipend is zero. -/
lemma calculateMsgCallGas_zero {gas gl ext acc : Nat} (h : acc + ext ≤ gl) :
    calculateMsgCallGas 0 gas gl ext acc =
      ⟨min gas (except64th (gl - ext - acc)) + acc,
        min gas (except64th (gl - ext - acc))⟩ := by
  rw [calculateMsgCallGas, if_pos (rfl : (0 : Nat) = 0), if_neg (by omega)]
  show (min gas (except64th (gl - ext - acc)) + acc,
    min gas (except64th (gl - ext - acc)) + 0) = _
  rw [Nat.add_zero]

/-- **The retained gas, bounded below.**  Whatever the operand asked for, the
frame keeps at least a sixty-fourth of what it had after its own overhead:
`except64th n = n - n / 64` leaves `n / 64` behind, and `min` can only leave
more.

This is what makes a post-`CALL` continuation provable against a *closed* bound
without any premise about the callee — the callee cannot take the last
sixty-fourth however it behaves. -/
lemma le_retained_of_calculateMsgCallGas_zero {gas gl ext acc mcc mcs : Nat}
    (h : acc + ext ≤ gl)
    (h_split : calculateMsgCallGas 0 gas gl ext acc = ⟨mcc, mcs⟩) :
    (gl - ext - acc) / 64 ≤ gl - (mcc + ext) := by
  rw [calculateMsgCallGas_zero h] at h_split
  injection h_split with h_cost _
  subst h_cost
  rw [show except64th (gl - ext - acc)
    = (gl - ext - acc) - (gl - ext - acc) / 64 from rfl]
  have h_div : (gl - ext - acc) / 64 ≤ gl - ext - acc := Nat.div_le_self _ _
  omega

/-- The `min` collapses when the operand asked for at least the cap — which is
what a frame that pushed its own `GAS` and forwarded it does, since the cap is
strictly below the account the push read. -/
lemma calculateMsgCallGas_zero_of_cap_le {gas gl ext acc : Nat}
    (h : acc + ext ≤ gl) (h_cap : except64th (gl - ext - acc) ≤ gas) :
    calculateMsgCallGas 0 gas gl ext acc =
      ⟨except64th (gl - ext - acc) + acc, except64th (gl - ext - acc)⟩ := by
  rw [calculateMsgCallGas_zero h, Nat.min_eq_right h_cap]

/-! ## `genericCall.step`

Two arms, and the depth test is the whole difference.  At `sevm.depth = 0` no
child is spawned at all: the frame pushes `0`, gets the forwarded gas back and
carries on — a *revert-path* case for a contract that checks the return value,
never a premise. -/

/-- The spawning arm: at nonzero depth, the message is built and the frame
suspends.  Nothing is evaluated here that the caller cannot read off the
conclusion. -/
lemma genericCall.step_spawn {sevm : Sevm} {devm : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_depth : sevm.depth ≠ 0) :
    genericCall.step sevm devm gas value caller target codeAddress stv isStatic
        ii is oi os code dp =
      .spawn
        (Frame.ofCall
          (callMsg sevm (devm.withReturnData []) gas value caller target
            codeAddress stv isStatic
            ((devm.withReturnData []).memory.data.sliceD ii is 0) code dp))
        (.call (devm.withReturnData []) oi os) := by
  rw [genericCall.step, if_neg h_depth]

/-- The depth-limit arm: `sevm.depth = 0` is Jaune's encoding of "no room for a
child", and the instruction answers `0` on the stack with the requested gas
handed straight back.

A contract that branches on the returned flag reverts here, which is why P2's
trichotomy needs this arm and not a premise excluding it. -/
lemma genericCall.step_zero_depth {sevm : Sevm} {devm : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {stv isStatic : Bool} {ii is oi os : Nat} {code : ByteArray} {dp : Bool}
    (h_depth : sevm.depth = 0)
    (h_room : devm.stack.length < 1024) :
    genericCall.step sevm devm gas value caller target codeAddress stv isStatic
        ii is oi os code dp =
      .done (.ok ((devm.withReturnData []).setMach
        ⟨0 :: devm.stack, devm.memory, devm.gasLeft + gas⟩)) := by
  rw [genericCall.step, if_pos h_depth]
  show XStep.ofExcept
    (Devm.push 0
      (((devm.withReturnData []).withGasLeft
        ((devm.withReturnData []).gasLeft + gas))) >>= fun d =>
          Except.ok (XStep.done (.ok d))) = _
  rw [Devm.push_eq_ok
    (devm := (devm.withReturnData []).withGasLeft
      ((devm.withReturnData []).gasLeft + gas))
    (by show devm.stack.length < 1024; exact h_room)]
  rfl

/-! ## `Xinst.step`'s `.call` arm, at `value = 0`

Seven pops, one memory-expansion charge, one delegation resolution, the EIP-150
split, and then `genericCall.step`.  Every step of that is either arithmetic the
caller supplies as an equation or a projection of the popped state.

The two branches a nonzero value would open are *closed* here rather than
assumed away: the static-context assertion succeeds on `value = 0`, and the
balance short-circuit tests `senderBal < 0`, which no `B256` satisfies. -/

/-- The `.call` arm reduced to a `genericCall.step`, at `value = 0`.

The premises name what the arm computes and this layer does not: the
memory-expansion charge (`h_ext`), the delegation resolution (`h_del` — EIP-7702
can add a second cold-account charge, and `dgc` is it), the collected access
cost (`h_acc`), and the EIP-150 split (`h_split`).  `h_afford` is the branch
condition of `calculateMsgCallGas`, and `h_gas` is the frame's own ability to
pay. -/
lemma Xinst.step_call_zero_value {sevm : Sevm} {devm : Devm}
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
    (h_gas : mcc + ext ≤ d1.gasLeft) :
    Xinst.step sevm devm .call =
      genericCall.step sevm
        ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
        mcs 0 sevm.currentTarget cw.toAdr cw.toAdr true false
        iiw.toNat isw.toNat oiw.toNat osw.toNat code dp := by
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
  -- `value = 0` closes the new-account and transfer charges, and the
  -- static-context assertion, on their right disjuncts.  `simp only` rather
  -- than `rw` for `h_del`: the new-account `if` carries a `Decidable` instance
  -- that depends on the term being rewritten.
  simp only [if_pos (Or.inr trivial), if_pos trivial, Nat.add_zero,
    show ((0 : B256).toNat) = 0 from rfl]
  simp only [h_del, h_split]
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  simp only [Except.assert, if_pos (Or.inr trivial)]
  -- The balance short-circuit tests `senderBal < 0`, which no `B256` satisfies:
  -- at `value = 0` the branch is unreachable rather than excluded by a premise.
  rw [if_neg (by
    rw [B256.lt_iff_toNat_lt_toNat]
    exact Nat.not_lt.mpr (Nat.zero_le _))]
  rfl

/-! ### The spawned frame, named

Step 2 of the arc has to state what the child starts from, and Step 4's success
form has to *quantify over it by name* rather than existentially (**A5**: an
∃-form boundary premise cannot compose forward, which the `fmint-restoration`
R4 finding established).  These two definitions are where that name comes from:
they are the spawn's two components, written as functions of the parent's own
state, so a statement about the callee is a statement about a term the caller
can build. -/

/-- The parent state a `value = 0` `CALL` suspends on: charged, window-extended
and with its return data cleared. -/
def callSpawnParent (d1 : Devm) (charge ii is oi os : Nat) : Devm :=
  ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - charge⟩).memExtends
    [⟨ii, is⟩, ⟨oi, os⟩]).withReturnData []

/-- The message a `value = 0` `CALL` builds: the callee is both target and
code address, the value is zero, and the calldata is the input window read out
of the parent's own memory. -/
def callSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (callee : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs 0 sevm.currentTarget callee callee true false
    (p.memory.data.sliceD ii is 0) code dp

/-- The `.call` arm all the way to its `.spawn`, at `value = 0` and nonzero
depth. -/
lemma Xinst.step_call_zero_value_spawn {sevm : Sevm} {devm : Devm}
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
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0) :
    Xinst.step sevm devm .call =
      .spawn
        (Frame.ofCall (callSpawnMsg sevm
          (callSpawnParent d1 (mcc + ext)
            iiw.toNat isw.toNat oiw.toNat osw.toNat)
          mcs cw.toAdr iiw.toNat isw.toNat code dp))
        (.call (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat) := by
  rw [Xinst.step_call_zero_value h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_spawn h_depth]
  rfl

/-- **The crossing, assembled.**

A `value = 0` `CALL` whose frame enters, as one `Ninst.RunCompiled` premise: the
parent's arithmetic on the left, `Resume.run` on the right, and in between the
child's derivation supplied by `Xlot.filled_exec` at `exec cevm`.

Count the premises about the callee: there are none.  `h_enter` is about the
message the *parent* built and `h_res` is about the resume — and the term
`exec cevm` that stands where a behavioural assumption would go is exactly what
a caller case-splits on to get a trichotomy rather than a hypothesis. -/
lemma Ninst.runCompiled_call_zero_value {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {cevm : Evm} {devm' : Devm}
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
    (h_gas : mcc + ext ≤ d1.gasLeft) (h_depth : sevm.depth ≠ 0)
    (h_enter : (Frame.ofCall (callSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs cw.toAdr iiw.toNat isw.toNat code dp)).enter = .run cevm)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      ((Frame.ofCall (callSpawnMsg sevm
        (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat)
        mcs cw.toAdr iiw.toNat isw.toNat code dp)).settle (exec cevm))
        = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .call) devm' :=
  Ninst.runCompiled_exec_run
    (Xinst.step_call_zero_value_spawn h_stk h_ext h_del h_acc h_split h_gas
      h_depth) h_enter h_res

/-! ## The resume, characterised

`Resume.run (.call parent oi os) r` is where the parent comes back.  Three
lemmas, one per outcome, and between them they are the whole post-`CALL` state.

What each says about the parent is the part worth reading twice.

* On a **fatal settle** (`.crypto`/`.internal`, the channel
  `executeCode.handleError` propagates rather than settles) the resume does not
  run at all: the error travels straight out, carrying the child's state.
* On a **settled child with an error** the parent keeps its **own** accessed
  addresses and storage keys, its own logs, its own refund counter and its own
  accounts-to-delete.  `incorporateChildOnError` copies gas, created accounts,
  return data, state and transient storage — and nothing else.  So a post-`CALL`
  worst case is fixed by the frame's own trunk, not by the callee.
* On a **clean child** the sets union, so warm stays warm.

None of the three is conditional on the callee doing anything. -/

/-- The fatal arm: the settle propagated a non-consensus error, so
`liftToExecution` re-raises it against the parent's world. -/
lemma Resume.run_call_fatal {parent : Devm} {oi os : Nat}
    {e : EvmError} {st : State} {ca : AdrSet} {tra : Tra} :
    Resume.run (.call parent oi os) (.error ⟨e, st, ca, tra⟩) =
      .error ⟨e, (parent.withCreatedAccounts ca).setWorld
        {parent.world with state := st, transientStorage := tra}⟩ := rfl

/-- The settled-with-error arm.  `h_err` is read off the child; `h_room` is the
parent's own headroom, which its trunk established. -/
lemma Resume.run_call_err {parent child : Devm} {oi os : Nat}
    (h_err : child.error.isSome = true)
    (h_room : parent.stack.length < 1024) :
    Resume.run (.call parent oi os) (.ok child) =
      .ok (((incorporateChildOnError parent child child.output).setMach
        ⟨0 :: parent.stack, parent.memory,
          parent.gasLeft + child.gasLeft⟩).memWrite oi
            (child.output.take os)) := by
  show (do
    let c ← liftToExecution parent (.ok child)
    let actualOutput := c.output.take os
    if c.error.isSome then
      let evm2 ← (incorporateChildOnError parent c c.output).push 0
      Except.ok (evm2.memWrite oi actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent c c.output).push 1
      Except.ok (evm2.memWrite oi actualOutput)) = _
  show (if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))
    else
      (incorporateChildOnSuccess parent child child.output).push 1 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))) = _
  rw [if_pos h_err, Devm.push_eq_ok
    (devm := incorporateChildOnError parent child child.output)
    (by show parent.stack.length < 1024; exact h_room)]
  rfl

/-- The clean arm.  The pushed flag is `1`, and
`incorporateChildOnSuccess` unions the warm sets, the logs, the refund counter
and the accounts to delete. -/
lemma Resume.run_call_ok {parent child : Devm} {oi os : Nat}
    (h_ok : child.error.isSome = false)
    (h_room : parent.stack.length < 1024) :
    Resume.run (.call parent oi os) (.ok child) =
      .ok (((incorporateChildOnSuccess parent child child.output).setMach
        ⟨1 :: parent.stack, parent.memory,
          parent.gasLeft + child.gasLeft⟩).memWrite oi
            (child.output.take os)) := by
  show (do
    let c ← liftToExecution parent (.ok child)
    let actualOutput := c.output.take os
    if c.error.isSome then
      let evm2 ← (incorporateChildOnError parent c c.output).push 0
      Except.ok (evm2.memWrite oi actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent c c.output).push 1
      Except.ok (evm2.memWrite oi actualOutput)) = _
  show (if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))
    else
      (incorporateChildOnSuccess parent child child.output).push 1 >>= fun e2 =>
        Except.ok (e2.memWrite oi (child.output.take os))) = _
  rw [if_neg (by rw [h_ok]; exact Bool.false_ne_true), Devm.push_eq_ok
    (devm := incorporateChildOnSuccess parent child child.output)
    (by show parent.stack.length < 1024; exact h_room)]
  rfl

/-! ### Reading the resume state

The projections a continuation walk needs, so that it never has to unfold
`incorporateChild*` again. -/

/-- An empty return window writes nothing: `Mem.write` at an empty payload is
the identity, which is why fmint's `(0,0)` window costs the resume nothing. -/
lemma Devm.memWrite_nil {devm : Devm} {i : Nat} : devm.memWrite i [] = devm := rfl

/-- On the error path the parent's accessed storage keys are its own. -/
lemma incorporateChildOnError_accessedStorageKeys {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnError parent child rd).accessedStorageKeys
      = parent.accessedStorageKeys := rfl

/-- And its accessed addresses. -/
lemma incorporateChildOnError_accessedAddresses {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnError parent child rd).accessedAddresses
      = parent.accessedAddresses := rfl

/-- And its logs: a reverted child emits none the parent keeps. -/
lemma incorporateChildOnError_logs {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnError parent child rd).logs = parent.logs := rfl

/-- The return data is the child's output on either path, which is what
`RETURNDATASIZE` then reads. -/
lemma incorporateChildOnError_returnData {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnError parent child rd).returnData = rd := rfl

lemma incorporateChildOnSuccess_returnData {parent child : Devm} {rd : Bytes} :
    (incorporateChildOnSuccess parent child rd).returnData = rd := rfl

/-- On the success path the accessed sets union, so a key the parent warmed
stays warm across the call. -/
lemma incorporateChildOnSuccess_accessedStorageKeys {parent child : Devm}
    {rd : Bytes} :
    (incorporateChildOnSuccess parent child rd).accessedStorageKeys
      = parent.accessedStorageKeys.union child.accessedStorageKeys := rfl

end Blanc
