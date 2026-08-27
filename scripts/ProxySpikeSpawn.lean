import Blanc.TransientSettlement

/-!
# Spike evidence: the `DELEGATECALL` spawn edge

Branch-local evidence for goal `proxy-delegatecall-spike-v1`, rows **P2** and
**P3**. Not a contract, not a port, not production machinery: this file exists
to find out what a `DELEGATECALL` edge costs Blanc, and it is deliberately kept
outside `Blanc/` so that it binds no gate and states no baseline.

`Blanc/ForwardCall.lean` carries a three-member family of spawn-edge lemmas —
zero-value `CALL`, nonzero-value `CALL`, `STATICCALL` — built on one generic
`genericCall.step_spawn` whose `caller`, `target` and `codeAddress` are already
three distinct variables. Nothing in `Blanc/` crosses a `DELEGATECALL`. This
file adds the fourth member and measures what that cost.

The ownership vocabulary is the product. Every statement below names the three
roles separately:

* **storage owner** — `Msg.currentTarget`, the account whose `SSTORE`/`SLOAD`
  and `TSTORE`/`TLOAD` are hit;
* **code address** — `Msg.codeAddress`, the account whose code runs;
* **caller** — `Msg.caller`, what `CALLER` observes inside the child.

Under `CALL` and `STATICCALL` the first two coincide, and `Blanc`'s three
existing spawn-message constructors record that by writing one variable twice
(`callSpawnMsg`: "the callee is both target and code address"). Under
`DELEGATECALL` they must not, and `delcallSpawnMsg` below is exactly that
constructor with the roles kept apart.
-/

namespace Blanc.ProxySpike

open Jaune

/-! ## The spawned message, with the roles kept apart -/

/-- The message a `DELEGATECALL` builds.

Read against `Blanc.callSpawnMsg`, which is `callMsg sevm p mcs 0
sevm.currentTarget callee callee true false …`: there, one `callee` fills both
the `target` and the `codeAddress` slot. Here the two slots take *different*
arguments — `sevm.currentTarget` stays the storage owner and `codeAdr` is the
account whose code runs — and `caller`/`value` are inherited from the parent
frame rather than being set to the parent's own address and zero. -/
def delcallSpawnMsg (sevm : Sevm) (p : Devm) (mcs : Nat) (codeAdr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) : Msg :=
  callMsg sevm p mcs sevm.value sevm.caller sevm.currentTarget codeAdr
    false false (p.memory.data.sliceD ii is 0) code dp

/-! ## The arm

An exact mirror of `Blanc.Xinst.step_statcall`. `DELEGATECALL` and `STATICCALL`
pop the same six words and charge the same way; they differ only in the four
arguments `genericCall.step` is finally handed. -/

lemma Xinst.step_delcall {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
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
    Jaune.Xinst.step sevm devm .delcall =
      genericCall.step sevm
        ((d1.setMach ⟨d1.stack, d1.memory, d1.gasLeft - (mcc + ext)⟩).memExtends
          [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩])
        mcs sevm.value sevm.caller sevm.currentTarget dadr false false
        iiw.toNat isw.toNat oiw.toNat osw.toNat code dp := by
  subst h_ext
  subst h_acc
  show XStep.ofExcept (do
    let ⟨gas, d⟩ ← devm.pop
    let ⟨codeAddress, d⟩ ← d.popToAdr
    let ⟨inputIndex, d⟩ ← d.popToNat
    let ⟨inputSize, d⟩ ← d.popToNat
    let ⟨outputIndex, d⟩ ← d.popToNat
    let ⟨outputSize, d⟩ ← d.popToNat
    let extendCost :=
      d.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := accessCost codeAddress d.accessedAddresses
    let d := addAccessedAddress d codeAddress
    let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, d⟩ :=
      accessDelegation d codeAddress
    let accessCost := preAccessCost + delegatedAccessGasCost
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas 0 gas.toNat d.gasLeft extendCost accessCost
    let d ← chargeGas (msgCallCost + extendCost) d
    let d :=
      d.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    return genericCall.step
      sevm d msgCallStipend sevm.value sevm.caller sevm.currentTarget
      newCodeAddress false false
      inputIndex inputSize outputIndex outputSize code disablePrecompiles) = _
  rw [Devm.pop_eq_ok h_stk]
  simp only [bind, Except.bind]
  rw [Devm.popToAdr_eq_ok
    (devm := devm.setMach ⟨cw :: iiw :: isw :: oiw :: osw :: s,
      devm.memory, devm.gasLeft⟩) rfl]
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach]
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
  rw [chargeGas_eq_ok (devm := d1) h_gas]
  rfl

/-! ## The spawn -/

lemma Xinst.step_delcall_spawn {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
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
    Jaune.Xinst.step sevm devm .delcall =
      .spawn
        (Frame.ofCall (delcallSpawnMsg sevm
          (callSpawnParent d1 (mcc + ext)
            iiw.toNat isw.toNat oiw.toNat osw.toNat)
          mcs dadr iiw.toNat isw.toNat code dp))
        (.call (callSpawnParent d1 (mcc + ext)
          iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat) := by
  rw [Xinst.step_delcall h_stk h_ext h_del h_acc h_split h_gas,
    genericCall.step_spawn h_depth]
  rfl

/-! ## The ownership conclusions

The mirror of `Blanc.directStatcall_spawn`. This is the statement the spike
exists to obtain: on an actual `DELEGATECALL` edge, the child's storage owner
is the **parent's** account while its code address is a **different** one, and
`caller`/`value` are the parent frame's own, not the parent's address and zero.

Compare `Blanc.directStatcall_spawn`, whose conclusion is
`child.currentTarget = tw.toAdr ∧ child.codeAddress = some tw.toAdr` — one
address in both roles. -/

theorem directDelcall_spawn {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
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
    let parent := callSpawnParent d1 (mcc + ext)
      iiw.toNat isw.toNat oiw.toNat osw.toNat
    let child := delcallSpawnMsg sevm parent mcs dadr
      iiw.toNat isw.toNat code dp
    Jaune.Xinst.step sevm devm .delcall =
        .spawn (Frame.ofCall child) (.call parent oiw.toNat osw.toNat) ∧
      child.currentTarget = sevm.currentTarget ∧
      child.codeAddress = some dadr ∧
      child.caller = sevm.caller ∧
      child.value = sevm.value ∧ child.shouldTransferValue = false ∧
      child.isStatic = sevm.isStatic ∧
      child.tenv.transientStorage = devm.transientStorage := by
  dsimp only
  refine ⟨Xinst.step_delcall_spawn h_stk h_ext h_del h_acc h_split h_gas
    h_depth, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact Bool.false_or _
  · have hf := accessDelegation_instructionFrame
      (addAccessedAddress
        (devm.setMach ⟨s, devm.memory, devm.gasLeft⟩) cw.toAdr) cw.toAdr
    rw [h_del] at hf
    exact hf.transientStorage.symm

/-! ## The walk crossing

The mirror of `Blanc.Ninst.runCompiled_statcall_doneFrame`. Note what is *not*
here: no premise about the callee. The child's derivation is supplied by
`Xlot.filled_exec` at `exec cevm`, exactly as for `CALL`. -/

lemma Ninst.runCompiled_delcall_doneFrame {sevm : Sevm} {devm : Devm}
    {gw cw iiw isw oiw osw : B256} {s : List B256}
    {dp : Bool} {dadr : Adr} {code : ByteArray} {dgc : Nat} {d1 : Devm}
    {ext acc mcc mcs : Nat} {devm' : Devm}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (h_stk : devm.stack = gw :: cw :: iiw :: isw :: oiw :: osw :: s)
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
    (h_enter : (Frame.ofCall (delcallSpawnMsg sevm
      (callSpawnParent d1 (mcc + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat)
      mcs dadr iiw.toNat isw.toNat code dp)).enter = .done r)
    (h_res : Resume.run
      (.call (callSpawnParent d1 (mcc + ext)
        iiw.toNat isw.toNat oiw.toNat osw.toNat) oiw.toNat osw.toNat)
      r = .ok devm') :
    Ninst.RunCompiled sevm devm (.exec .delcall) devm' :=
  Ninst.runCompiled_exec_doneFrame
    (Xinst.step_delcall_spawn h_stk h_ext h_del h_acc h_split h_gas h_depth)
    h_enter h_res

/-! ## Anti-vacuity control

A statement about `DELEGATECALL` ownership is worthless unless the same shape
under `CALL` comes out *differently*. At this altitude the control is the pair
of spawn-message constructors: given a code account distinct from the running
frame's own account, `delcallSpawnMsg` separates the two roles and
`callSpawnMsg` fuses them.

The `hne` hypothesis is what makes the control bite: with `sevm.currentTarget =
codeAdr` both constructors would agree, and the separation below would be
vacuously about one address. -/

theorem control_delcall_separates_call_fuses
    (sevm : Sevm) (p : Devm) (mcs : Nat) (codeAdr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool)
    (hne : sevm.currentTarget ≠ codeAdr) :
    -- DELEGATECALL: the storage owner is the *running* account, and the code
    -- account is a different one
    (delcallSpawnMsg sevm p mcs codeAdr ii is code dp).currentTarget =
        sevm.currentTarget ∧
      (delcallSpawnMsg sevm p mcs codeAdr ii is code dp).codeAddress =
        some codeAdr ∧
      (delcallSpawnMsg sevm p mcs codeAdr ii is code dp).currentTarget ≠
        codeAdr ∧
    -- CALL: the callee is both, exactly as `callSpawnMsg`'s doc comment says
      (callSpawnMsg sevm p mcs codeAdr ii is code dp).currentTarget = codeAdr ∧
      (callSpawnMsg sevm p mcs codeAdr ii is code dp).codeAddress =
        some codeAdr ∧
    -- and the two constructors disagree on the storage owner, which is the
    -- whole point
      (delcallSpawnMsg sevm p mcs codeAdr ii is code dp).currentTarget ≠
        (callSpawnMsg sevm p mcs codeAdr ii is code dp).currentTarget :=
  ⟨rfl, rfl, hne, rfl, rfl, hne⟩

/-- The caller and value clauses of the same control. Under `CALL` the child's
`CALLER` is the parent's own account and its `CALLVALUE` is the literal `0`
supplied by the opcode; under `DELEGATECALL` both are inherited from the parent
frame, so a proxy is transparent to `msg.sender` and `msg.value`. -/
theorem control_delcall_inherits_caller_and_value
    (sevm : Sevm) (p : Devm) (mcs : Nat) (codeAdr : Adr)
    (ii is : Nat) (code : ByteArray) (dp : Bool) :
    (delcallSpawnMsg sevm p mcs codeAdr ii is code dp).caller = sevm.caller ∧
      (delcallSpawnMsg sevm p mcs codeAdr ii is code dp).value = sevm.value ∧
      (delcallSpawnMsg sevm p mcs codeAdr ii is code dp).shouldTransferValue
        = false ∧
      (callSpawnMsg sevm p mcs codeAdr ii is code dp).caller
        = sevm.currentTarget ∧
      (callSpawnMsg sevm p mcs codeAdr ii is code dp).value = 0 ∧
      (callSpawnMsg sevm p mcs codeAdr ii is code dp).shouldTransferValue
        = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The child *observes* the outer frame's caller and value

The `directDelcall_spawn` clauses above are about `Msg` fields. This one is
about what the child's own code actually sees: `initSevm` carries those fields
into the child `Sevm`, and the `CALLER` and `CALLVALUE` opcodes read them
(`Jaune/Machine.lean:2802-2803`). So a contract running behind a proxy observes
the proxy's caller and the proxy's value, not the proxy's address and zero —
which is the property that makes a forwarding proxy transparent to
`msg.sender` and `msg.value`.

The `CALL` control is stated in the same theorem so the two cannot drift. -/

theorem delcall_child_observes_outer_caller_and_value
    (sevm : Sevm) (p : Devm) (mcs : Nat) (codeAdr : Adr) (ii is : Nat)
    (code : ByteArray) (dp : Bool) (d : Devm) (pc : Nat)
    (h_room : d.stack.length < 1024) (h_gas : gBase ≤ d.gasLeft) :
    ∃ dc dv cc cv,
      -- under DELEGATECALL the child sees the *outer* frame's caller and value
      Rinst.run ⟨pc, initSevm (delcallSpawnMsg sevm p mcs codeAdr ii is code dp),
        d⟩ .caller = .ok dc ∧ dc.stack = sevm.caller.toB256 :: d.stack ∧
      Rinst.run ⟨pc, initSevm (delcallSpawnMsg sevm p mcs codeAdr ii is code dp),
        d⟩ .callvalue = .ok dv ∧ dv.stack = sevm.value :: d.stack ∧
      -- under CALL it sees the caller's own address and the opcode's zero
      Rinst.run ⟨pc, initSevm (callSpawnMsg sevm p mcs codeAdr ii is code dp),
        d⟩ .caller = .ok cc ∧ cc.stack = sevm.currentTarget.toB256 :: d.stack ∧
      Rinst.run ⟨pc, initSevm (callSpawnMsg sevm p mcs codeAdr ii is code dp),
        d⟩ .callvalue = .ok cv ∧ cv.stack = (0 : B256) :: d.stack := by
  have step : ∀ (w : B256),
      ∃ d', pushItem w gBase d = .ok d' ∧ d'.stack = w :: d.stack := by
    intro w
    rw [pushItem_def, chargeGas_eq_ok h_gas]
    simp only [bind, Except.bind]
    rw [Devm.push_eq_ok
      (devm := d.setMach ⟨d.stack, d.memory, d.gasLeft - gBase⟩)
      (by show d.stack.length < 1024; exact h_room)]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨dc, hdc, hdcs⟩ := step sevm.caller.toB256
  obtain ⟨dv, hdv, hdvs⟩ := step sevm.value
  obtain ⟨cc, hcc, hccs⟩ := step sevm.currentTarget.toB256
  obtain ⟨cv, hcv, hcvs⟩ := step (0 : B256)
  exact ⟨dc, dv, cc, cv, hdc, hdcs, hdv, hdvs, hcc, hccs, hcv, hcvs⟩

/-! ## Axiom audit -/

#print axioms Xinst.step_delcall
#print axioms Xinst.step_delcall_spawn
#print axioms directDelcall_spawn
#print axioms Ninst.runCompiled_delcall_doneFrame
#print axioms control_delcall_separates_call_fuses
#print axioms control_delcall_inherits_caller_and_value
#print axioms delcall_child_observes_outer_caller_and_value

end Blanc.ProxySpike
