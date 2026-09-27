import Blanc.LockExclusion
import Blanc.Lift.Jumpdest

/-!
# Storage-owner discipline from world premises

Which code can run in a frame whose storage owner (`sevm.currentTarget`) is a
fixed account `P`?  This module answers that for every raw frame root of an
execution of any outcome, from premises about the world at the root:

* `P` holds either a code `C` or a straight-line EIP-1167 forwarder `K` whose
  only `DELEGATECALL` addresses an implementation `I` holding `C`
  (`ForwarderShape K I`, decided for concrete bytes);
* `C` is non-empty and is not an EIP-7702 delegation designator;
* no frame running `C` executes `DELEGATECALL` or `CALLCODE`
  (`NoDelegateFrom`, a per-code hypothesis over the same-frame nodes of frames
  running `C`, discharged elsewhere from a certificate).

`Exec.ownerCode_of_world` concludes that every owner-`P` frame root runs `C` or
`K`; `Exec.ownerDiscipline_of_world` restates that as the G3b hypothesis
`LockSpec.OwnerDiscipline` of `Blanc/LockExclusion.lean` once `K` has no
`SSTORE`.  Owner-`P` frames arise only from a message to `P` (code at `P`), a
`DELEGATECALL`/`CALLCODE` from an owner-`P` frame (excluded for `C`; the
forwarder's lands on `I`), or a `CALL`/`STATICCALL` back into `P` (code at `P`).
`CREATE`/`CREATE2` cannot target `P` because `P` has code, and the code at `P`
and `I` is preserved at every reached node (`Exec.effect` with
`Devm.CodePreserve`, which covers `SELFDESTRUCT`).
-/

namespace Blanc

open Jaune
open Blanc.LockExclusion

/-! ## The EIP-1167 forwarder template -/

/-- Byte `i` (0-based, big-endian) of the 20-byte address `I`. -/
def adrByte (I : Adr) (i : Nat) : UInt8 := (I.toB256.toBytes).getD (12 + i) 0

/-- The 45-byte EIP-1167 minimal-proxy runtime delegating to `I`:
`363d3d373d3d3d363d73 ‖ I ‖ 5af43d82803e903d91602b57fd5bf3`. -/
def forwarderCode (I : Adr) : ByteArray := ⟨#[
  0x36, 0x3d, 0x3d, 0x37, 0x3d, 0x3d, 0x3d, 0x36, 0x3d, 0x73,
  adrByte I 0, adrByte I 1, adrByte I 2, adrByte I 3, adrByte I 4,
  adrByte I 5, adrByte I 6, adrByte I 7, adrByte I 8, adrByte I 9,
  adrByte I 10, adrByte I 11, adrByte I 12, adrByte I 13, adrByte I 14,
  adrByte I 15, adrByte I 16, adrByte I 17, adrByte I 18, adrByte I 19,
  0x5a, 0xf4, 0x3d, 0x82, 0x80, 0x3e, 0x90, 0x3d, 0x91, 0x60, 0x2b, 0x57,
  0xfd, 0x5b, 0xf3]⟩

/-- A decoded instruction that is a register instruction other than `SSTORE`. -/
def Inst.plainReg : Option Inst → Bool
  | some (.next (.reg .sstore)) => false
  | some (.next (.reg _)) => true
  | _ => false

/-- The address a 20-byte `PUSH` pushes, if the instruction is one. -/
def Inst.push20Target : Option Inst → Option Adr
  | some (.next (.push xs _)) => if xs.length = 20 then some xs.toB256.toAdr else none
  | _ => none

/-- A decoded `GAS`. -/
def Inst.isGas : Option Inst → Bool
  | some (.next (.reg .gas)) => true
  | _ => false

/-- A decoded `DELEGATECALL`. -/
def Inst.isDelegatecall : Option Inst → Bool
  | some (.next (.exec .delegatecall)) => true
  | _ => false

/-- A decoded instruction that neither enters a frame nor writes storage. -/
def Inst.tailOk : Option Inst → Bool
  | some (.next (.exec _)) => false
  | some (.next (.reg .sstore)) => false
  | _ => true

/-- The shape of the 45-byte forwarder that the owner argument uses: nine
plain register instructions, a `PUSH20 I`, `GAS`, `DELEGATECALL` at 31, then a
tail that enters no frame and writes no storage, whose only jump destinations
lie in the tail.  Decidable; `decide` discharges it for concrete bytes. -/
def ForwarderShape (K : ByteArray) (I : Adr) : Prop :=
  K.size = 45 ∧
  (∀ pc, pc < 9 → Inst.plainReg (K.getInst pc) = true) ∧
  Inst.push20Target (K.getInst 9) = some I ∧
  Inst.isGas (K.getInst 30) = true ∧
  Inst.isDelegatecall (K.getInst 31) = true ∧
  (∀ i, i < 13 → Inst.tailOk (K.getInst (32 + i)) = true) ∧
  (∀ k, k < 45 → jumpable K k = true → 32 ≤ k)

instance (K : ByteArray) (I : Adr) : Decidable (ForwarderShape K I) := by
  unfold ForwarderShape; infer_instance

/-! ## Decoding facts extracted from the shape -/

private theorem Inst.plainReg_spec {o : Option Inst} (h : Inst.plainReg o = true) :
    ∃ r, o = some (.next (.reg r)) ∧ r ≠ .sstore := by
  rcases o with _ | ((_ | _) | (r | _ | _ | _ | _ | _) | _) <;>
    simp only [Inst.plainReg, reduceCtorEq] at h
  · exact ⟨r, rfl, by rintro rfl; simp at h⟩

private theorem Inst.push20Target_spec {o : Option Inst} {I : Adr}
    (h : Inst.push20Target o = some I) :
    ∃ xs le, o = some (.next (.push xs le)) ∧ xs.length = 20 ∧
      xs.toB256.toAdr = I := by
  rcases o with _ | ((_ | _) | (_ | _ | ⟨xs, le⟩ | _ | _ | _) | _) <;>
    simp only [Inst.push20Target, reduceCtorEq] at h
  split at h
  · rename_i hlen
    exact ⟨xs, le, rfl, hlen, Option.some.inj h⟩
  · cases h

private theorem Inst.isGas_spec {o : Option Inst} (h : Inst.isGas o = true) :
    o = some (.next (.reg .gas)) := by
  rcases o with _ | ((_ | _) | (r | _ | _ | _ | _ | _) | _) <;>
    simp only [Inst.isGas, reduceCtorEq] at h
  cases r <;> first | rfl | cases h

private theorem Inst.isDelegatecall_spec {o : Option Inst}
    (h : Inst.isDelegatecall o = true) :
    o = some (.next (.exec .delegatecall)) := by
  rcases o with _ | ((_ | _) | (_ | x | _ | _ | _ | _) | _) <;>
    simp only [Inst.isDelegatecall, reduceCtorEq] at h
  cases x <;> first | rfl | cases h

private theorem Inst.tailOk_spec {o : Option Inst} (h : Inst.tailOk o = true) :
    (∀ x, o ≠ some (.next (.exec x))) ∧ o ≠ some (.next (.reg .sstore)) := by
  refine ⟨fun x hx => ?_, fun hx => ?_⟩ <;> subst hx <;> simp [Inst.tailOk] at h

/-- The forwarder's reachable pcs and its stack at the `DELEGATECALL`: the
prefix `0..9`, `GAS` at 30 with `I` on top, `DELEGATECALL` at 31 with `I`
second, or the tail from 32. -/
def ForwarderReach (I : Adr) (pc : Nat) (stack : List B256) : Prop :=
  pc ≤ 9 ∨
  (pc = 30 ∧ ∃ w s, stack = w :: s ∧ w.toAdr = I) ∨
  (pc = 31 ∧ ∃ g w s, stack = g :: w :: s ∧ w.toAdr = I) ∨
  32 ≤ pc

private theorem jumpable_lt_size {cd : ByteArray} {k : Nat}
    (h : jumpable cd k = true) : k < cd.size := by
  unfold jumpable at h
  split at h
  · assumption
  · cases h

/-- A successful jump instruction either falls through or lands on a
jumpable destination. -/
theorem Jinst.runCore_ok_pc {pc pc' : Nat} {d d' : Devm} {s : Sevm} {j : Jinst}
    (h : Jinst.runCore pc d s j = .ok ⟨pc', d'⟩) :
    pc' = pc + 1 ∨ jumpable s.code pc' = true := by
  cases j <;> simp only [Jinst.runCore, bind, Except.bind, Except.assert] at h <;>
    (repeat' split at h) <;> simp_all

private theorem ForwarderShape.getInst_stop {K : ByteArray} {I : Adr}
    (hK : ForwarderShape K I) {pc : Nat} (hpc : 45 ≤ pc) :
    K.getInst pc = some (.last .stop) := by
  have hout : ¬ pc < K.size := by rw [hK.1]; omega
  unfold ByteArray.getInst
  simp only [hout, ↓reduceDIte]

private theorem Evm.step_ne_cont_of_last {pc pc' : Nat} {sevm : Sevm} {d d' : Devm}
    {l : Linst} (hat : sevm.code.getInst pc = some (.last l)) :
    Evm.step ⟨pc, sevm, d⟩ ≠ .cont pc' d' := by
  rw [Evm.step_last hat]; exact fun h => nomatch h

private theorem Evm.step_ne_spawn_of_last {pc pc' : Nat} {sevm : Sevm} {d : Devm}
    {f : Frame} {rsm : Resume} {l : Linst} (hat : sevm.code.getInst pc = some (.last l)) :
    Evm.step ⟨pc, sevm, d⟩ ≠ .spawn f rsm pc' := by
  rw [Evm.step_last hat]; exact fun h => nomatch h

/-- One continuing step of a forwarder frame keeps it on its reachable pcs. -/
theorem ForwarderShape.reach_cont {K : ByteArray} {I : Adr} (hK : ForwarderShape K I)
    {pc pc' : Nat} {sevm : Sevm} {d d' : Devm} (hcode : sevm.code = K)
    (hreach : ForwarderReach I pc d.stack)
    (hstep : Evm.step ⟨pc, sevm, d⟩ = .cont pc' d') :
    ForwarderReach I pc' d'.stack := by
  obtain ⟨hsize, hhead, hpush, hgas, hdc, -, hjump⟩ := id hK
  rcases hreach with hle | ⟨rfl, w, st, hs, hw⟩ | ⟨rfl, -⟩ | hge
  · rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · obtain ⟨r, hr, -⟩ := Inst.plainReg_spec (hhead pc hlt)
      have hat : Ninst.At sevm.code pc (.reg r) := by rw [hcode]; exact hr
      rw [Evm.step_next hat] at hstep
      have hpc := Ninst.step_cont_pc hstep
      left
      simp only [Ninst.size] at hpc
      omega
    · obtain ⟨xs, le, hx, hlen, hw⟩ := Inst.push20Target_spec hpush
      have hat : Ninst.At sevm.code 9 (.push xs le) := by rw [hcode]; exact hx
      rw [Evm.step_next hat] at hstep
      obtain ⟨hpc, hrun⟩ := Step.ofExecution_cont hstep
      have hpb := (Devm.pushBurn_of_run hrun).stack
      simp only [Stack.Push, Split, List.singleton_append] at hpb
      right; left
      refine ⟨by simp only [Ninst.size, hlen] at hpc; omega, _, _, hpb, hw⟩
  · have hat : Ninst.At sevm.code 30 Ninst.gas := by
      rw [hcode]; exact Inst.isGas_spec hgas
    have hs' := hstep
    rw [Evm.step_next hat] at hs'
    have hpc := Ninst.step_cont_pc hs'
    have hrun : Ninst.Run sevm d Ninst.gas d' := by
      refine ⟨.none, trivial, 30, ?_⟩
      simp only [Ninst.StepRun, hs', Step.Run]
      exact ⟨trivial, trivial⟩
    obtain ⟨x, hpb⟩ := of_run_gas hrun
    have hst := hpb.stack
    simp only [Stack.Push, Split, List.singleton_append] at hst
    right; right; left
    refine ⟨by simp only [Ninst.size] at hpc; omega, x, w, st, by rw [hst, hs], hw⟩
  · have hat : Ninst.At sevm.code 31 (.exec .delegatecall) := by
      rw [hcode]; exact Inst.isDelegatecall_spec hdc
    rw [Evm.step_next hat] at hstep
    have hpc := Ninst.step_cont_pc hstep
    right; right; right
    simp only [Ninst.size] at hpc
    omega
  · right; right; right
    by_cases hbig : 45 ≤ pc
    · exact absurd hstep (Evm.step_ne_cont_of_last
        (by rw [hcode]; exact ForwarderShape.getInst_stop hK hbig))
    rcases hgi : sevm.code.getInst pc with _ | i
    · rw [Evm.step_invOp hgi] at hstep; exact nomatch hstep
    cases i with
    | last l => rw [Evm.step_last hgi] at hstep; exact nomatch hstep
    | next n =>
      rw [Evm.step_next hgi] at hstep
      have := Ninst.step_cont_pc hstep
      simp only at this
      omega
    | jump j =>
      rw [Evm.step_jump hgi] at hstep
      rcases Jinst.runCore_ok_pc (Step.ofJump_cont hstep) with h | h
      · simp only at h; omega
      · rw [hcode] at h
        exact hjump pc' (hsize ▸ jumpable_lt_size h) h

/-! ## Where a spawned child's code comes from -/

/-- A `DELEGATECALL` whose second operand addresses an undelegated account
enters that account's own code. -/
theorem Xinst.step_delegatecall_spawn_code {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {g w : B256} {s : List B256}
    (spawn : Xinst.step sevm devm .delegatecall = .spawn f rsm)
    (hstack : devm.stack = g :: w :: s)
    (notDelegation : ¬ isValidDelegation (devm.getCode w.toAdr)) :
    f.inner.code = devm.getCode w.toAdr := by
  have h1 := Devm.pop_eq_ok hstack
  have hs1 : (devm.setMach ⟨w :: s, devm.memory, devm.gasLeft,
      devm.stateGas⟩).stack = w :: s := rfl
  generalize devm.setMach ⟨w :: s, devm.memory, devm.gasLeft, devm.stateGas⟩ = d1
    at h1 hs1
  rcases h2 : d1.popToAdr with err | ⟨cadr, d2⟩
  · rw [Devm.popToAdr_def, Devm.pop_eq_ok hs1] at h2; cases h2
  have hcadr : cadr = w.toAdr := by
    rw [Devm.popToAdr_def, Devm.pop_eq_ok hs1] at h2
    cases h2; rfl
  subst hcadr
  rcases h3 : d2.popToNat with err | ⟨ii, d3⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Xinst.step, hsg, h1, h2, h3, XStep.ofExcept] at spawn
  rcases h4 : d3.popToNat with err | ⟨isz, d4⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Xinst.step, hsg, h1, h2, h3, h4, XStep.ofExcept] at spawn
  rcases h5 : d4.popToNat with err | ⟨oi, d5⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Xinst.step, hsg, h1, h2, h3, h4, h5, XStep.ofExcept] at spawn
  rcases h6 : d5.popToNat with err | ⟨osz, d6⟩
  · cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, XStep.ofExcept] at spawn
  have hcode : (addAccessedAddress d6 w.toAdr).getCode w.toAdr =
      devm.getCode w.toAdr := by
    rw [addAccessedAddress_getCode, Devm.popToNat_getCode h6,
      Devm.popToNat_getCode h5, Devm.popToNat_getCode h4,
      Devm.popToNat_getCode h3, Devm.popToAdr_getCode h2, Devm.pop_getCode h1]
  have hnd : ¬ isValidDelegation ((addAccessedAddress d6 w.toAdr).getCode w.toAdr) := by
    rw [hcode]; exact notDelegation
  simp only [Xinst.step, h1, h2, h3, h4, h5, h6, Bind.bind, Except.bind,
    Except.assert] at spawn
  repeat' split at spawn
  all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
  all_goals first
    | cases spawn
    | have hf := genericCall.step_spawn_frame spawn
      rw [hf.2.2, congrArg (fun t => t.2.2.1)
        (GasSchedule.accessDelegation_of_not_delegation
          (gas := sevm.benvStat.rules.gas) hnd), hcode]
    | have hf := genericCallAmsterdam.step_spawn_frame spawn
      rw [hf.2.2, amsterdamCallCode_of_not_delegation hnd, hcode]

/-- Shared tail of the direct-call arms: once the operands are popped, an
undelegated callee's own code is what the child enters. -/
private theorem directCall_tail_code {sevm : Sevm} {devm d : Devm} {f : Frame}
    {callee : Adr}
    (hcode : (addAccessedAddress d callee).getCode callee = devm.getCode callee)
    (hnd : ¬ isValidDelegation (devm.getCode callee))
    (htarget : f.inner.currentTarget = callee)
    (hcases : f.inner.code = (sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d callee) callee).2.2.1 ∨
      f.inner.code = (completeDelegationAccess
        (Devm.balReadAccount sevm.benvStat.rules
          (sevm.benvStat.rules.gas.delegationCost (addAccessedAddress d callee) callee).2.1
          (Devm.balReadAccount sevm.benvStat.rules callee (addAccessedAddress d callee)))
        (sevm.benvStat.rules.gas.delegationCost (addAccessedAddress d callee) callee).1
        (sevm.benvStat.rules.gas.delegationCost (addAccessedAddress d callee) callee).2.1).1) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rw [htarget]
  rw [← hcode] at hnd
  rcases hcases with h | h
  · rw [h, congrArg (fun t => t.2.2.1)
      (GasSchedule.accessDelegation_of_not_delegation
        (gas := sevm.benvStat.rules.gas) hnd), hcode]
  · rw [h, amsterdamCallCode_of_not_delegation hnd, hcode]

/-- `CALL` and `STATICCALL` enter the callee's own code when the callee carries
no EIP-7702 designator, including a call back into the current account. -/
theorem Xinst.step_directCall_spawn_code {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (direct : x = .call ∨ x = .staticcall)
    (spawn : Xinst.step sevm devm x = .spawn f rsm)
    (notDelegation : ¬ isValidDelegation (devm.getCode f.inner.currentTarget)) :
    f.inner.code = devm.getCode f.inner.currentTarget := by
  rcases h1 : devm.pop with err | ⟨gas, d1⟩
  · rcases direct with rfl | rfl <;> cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Xinst.step, hsg, h1, XStep.ofExcept] at spawn
  rcases h2 : d1.popToAdr with err | ⟨callee, d2⟩
  · rcases direct with rfl | rfl <;> cases hsg : sevm.benvStat.rules.stateGas <;>
      simp [Xinst.step, hsg, h1, h2, XStep.ofExcept] at spawn
  rcases direct with rfl | rfl
  · rcases h3 : d2.pop with err | ⟨value, d3⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, XStep.ofExcept] at spawn
    rcases h4 : d3.popToNat with err | ⟨ii, d4⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, h4, XStep.ofExcept] at spawn
    rcases h5 : d4.popToNat with err | ⟨isz, d5⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, h4, h5, XStep.ofExcept] at spawn
    rcases h6 : d5.popToNat with err | ⟨oi, d6⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, XStep.ofExcept] at spawn
    rcases h7 : d6.popToNat with err | ⟨osz, d7⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, h7, XStep.ofExcept] at spawn
    have hcode : (addAccessedAddress d7 callee).getCode callee = devm.getCode callee := by
      rw [addAccessedAddress_getCode, Devm.popToNat_getCode h7, Devm.popToNat_getCode h6,
        Devm.popToNat_getCode h5, Devm.popToNat_getCode h4, Devm.pop_getCode h3,
        Devm.popToAdr_getCode h2, Devm.pop_getCode h1]
    simp only [Xinst.step, h1, h2, h3, h4, h5, h6, h7, Bind.bind, Except.bind,
      Except.assert, Pure.pure, Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
    all_goals first
      | cases spawn
      | have hf := genericCall.step_spawn_frame spawn
        exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
          (Or.inl hf.2.2)
      | have hf := genericCallAmsterdam.step_spawn_frame spawn
        exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
          (Or.inr hf.2.2)
  · rcases h3 : d2.popToNat with err | ⟨ii, d3⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, XStep.ofExcept] at spawn
    rcases h4 : d3.popToNat with err | ⟨isz, d4⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, h4, XStep.ofExcept] at spawn
    rcases h5 : d4.popToNat with err | ⟨oi, d5⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, h4, h5, XStep.ofExcept] at spawn
    rcases h6 : d5.popToNat with err | ⟨osz, d6⟩
    · cases hsg : sevm.benvStat.rules.stateGas <;>
        simp [Xinst.step, hsg, h1, h2, h3, h4, h5, h6, XStep.ofExcept] at spawn
    have hcode : (addAccessedAddress d6 callee).getCode callee = devm.getCode callee := by
      rw [addAccessedAddress_getCode, Devm.popToNat_getCode h6, Devm.popToNat_getCode h5,
        Devm.popToNat_getCode h4, Devm.popToNat_getCode h3,
        Devm.popToAdr_getCode h2, Devm.pop_getCode h1]
    simp only [Xinst.step, h1, h2, h3, h4, h5, h6, Bind.bind, Except.bind,
      Except.assert, Pure.pure, Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
    all_goals first
      | cases spawn
      | have hf := genericCall.step_spawn_frame spawn
        exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
          (Or.inl hf.2.2)
      | have hf := genericCallAmsterdam.step_spawn_frame spawn
        exact directCall_tail_code hcode (by rw [← hf.2.1]; exact notDelegation) hf.2.1
          (Or.inr hf.2.2)

/-- `CREATE` and `CREATE2` only enter an account that had no code. -/
theorem Xinst.step_create_spawn_fresh {sevm : Sevm} {devm : Devm} {x : Xinst}
    {f : Frame} {rsm : Resume}
    (creating : x = .create ∨ x = .create2)
    (spawn : Xinst.step sevm devm x = .spawn f rsm) :
    devm.getCode f.inner.currentTarget = .empty := by
  have hsrc := (Xinst.step_spawn_getCode spawn f.inner.currentTarget).symm
  rw [hsrc]
  rcases creating with rfl | rfl <;>
  · simp only [Xinst.step, Bind.bind, Except.bind, Except.assert, Pure.pure,
      Except.pure] at spawn
    repeat' split at spawn
    all_goals simp only [XStep.ofExcept, reduceCtorEq] at spawn
    all_goals first
      | cases spawn
      | have hfresh := genericCreate.step_spawn_frame spawn
        rw [hfresh.1, hfresh.2.1]; exact hfresh.2.2
      | have hfresh := genericCreateAmsterdam.step_spawn_frame spawn
        rw [hfresh.1, hfresh.2.1]; exact hfresh.2.2

/-- The only frame a forwarder frame enters is its `DELEGATECALL` at 31, which
runs the code at `I` and resumes at 32. -/
theorem ForwarderShape.reach_spawn {K : ByteArray} {I : Adr} (hK : ForwarderShape K I)
    {pc pc' : Nat} {sevm : Sevm} {d : Devm} {f : Frame} {rsm : Resume}
    (hcode : sevm.code = K) (hreach : ForwarderReach I pc d.stack)
    (hstep : Evm.step ⟨pc, sevm, d⟩ = .spawn f rsm pc')
    (hnd : ¬ isValidDelegation (d.getCode I)) :
    pc' = 32 ∧ f.inner.code = d.getCode I := by
  obtain ⟨x, hat, hx, hpc'⟩ := Evm.step_spawn_inv hstep
  have hat' : K.getInst pc = some (.next (.exec x)) := by rw [← hcode]; exact hat
  obtain ⟨-, hhead, hpush, hgas, hdc, htail, -⟩ := id hK
  rcases hreach with hle | ⟨rfl, -⟩ | ⟨rfl, g, w, st, hs, hw⟩ | hge
  · rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · obtain ⟨r, hr, -⟩ := Inst.plainReg_spec (hhead pc hlt)
      rw [hr] at hat'; cases hat'
    · obtain ⟨xs, le, hxs, -⟩ := Inst.push20Target_spec hpush
      rw [hxs] at hat'; cases hat'
  · rw [Inst.isGas_spec hgas] at hat'; cases hat'
  · rw [Inst.isDelegatecall_spec hdc] at hat'
    cases hat'
    subst hw
    exact ⟨hpc', Xinst.step_delegatecall_spawn_code hx hs hnd⟩
  · by_cases hbig : 45 ≤ pc
    · rw [ForwarderShape.getInst_stop hK hbig] at hat'; cases hat'
    · have hok := htail (pc - 32) (by omega)
      rw [show 32 + (pc - 32) = pc by omega] at hok
      exact absurd hat' ((Inst.tailOk_spec hok).1 x)

/-! ## The owner-discipline induction -/

/-- The per-code hypothesis on `C` (discharged elsewhere, e.g. by the lift
cursor's `CursorOK.exec_call_or_staticcall`): no same-frame node of a frame of
`run` running `C` decodes `DELEGATECALL` or `CALLCODE`. -/
def Exec.NoDelegateFrom {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (C : ByteArray) : Prop :=
  ∀ F ∈ Exec.rawFrameRoots run, F.sevm.code = C →
    ∀ n, Exec.Deriv.ParentPrefix F n →
      ¬ Xinst.At C n.pc .delegatecall ∧ ¬ Xinst.At C n.pc .callcode

/-- The node-local invariant: `P` holds `K` or `C`, `I` holds `C`, and an
owner-`P` frame runs `C`, or runs `K` on the forwarder's reachable pcs. -/
def OwnerLoc (K C : ByteArray) (P I : Adr) (pc : Nat) (sevm : Sevm) (d : Devm) :
    Prop :=
  (d.getCode P = K ∨ d.getCode P = C) ∧ d.getCode I = C ∧
    (sevm.currentTarget = P →
      sevm.code = C ∨ (sevm.code = K ∧ ForwarderReach I pc d.stack))

private theorem toList_ne_nil_of_size_pos {c : ByteArray} (h : 0 < c.size) :
    c.toList ≠ [] := by
  intro hnil
  have := ByteArray.size_eq_length_toList c
  rw [hnil, List.length_nil] at this
  omega

private theorem ne_empty_of_size_pos {c : ByteArray} (h : 0 < c.size) :
    c ≠ .empty := by
  rintro rfl; exact absurd h (by decide)

private theorem not_delegation_of_size {c : ByteArray} (h : c.size ≠ 23) :
    ¬ isValidDelegation c := fun hd => h hd.1

section Induction

variable {K C : ByteArray} {P I : Adr}

/-- One same-frame edge preserves the invariant. -/
private theorem OwnerLoc.next (hK : ForwarderShape K I) (hC : 0 < C.size)
    (hCdel : ¬ isValidDelegation C)
    {node next : Exec.Deriv} (edge : Exec.Deriv.ParentStep next node)
    (loc : OwnerLoc K C P I node.pc node.sevm node.devm) :
    OwnerLoc K C P I next.pc next.sevm next.devm := by
  have hKsize : 0 < K.size := by rw [hK.1]; decide
  have keep := Blanc.Exec.Deriv.ParentStep.codePreserve edge
  obtain ⟨hP, hI, howner⟩ := loc
  have hPne : (node.devm.getCode P).toList ≠ [] := by
    rcases hP with h | h <;> rw [h]
    · exact toList_ne_nil_of_size_pos hKsize
    · exact toList_ne_nil_of_size_pos hC
  have hIne : (node.devm.getCode I).toList ≠ [] := by
    rw [hI]; exact toList_ne_nil_of_size_pos hC
  refine ⟨by rw [keep P hPne]; exact hP, by rw [keep I hIne]; exact hI, ?_⟩
  rw [Blanc.Exec.Deriv.ParentStep.sevm_eq edge]
  intro htgt
  rcases howner htgt with hcode | ⟨hcode, hreach⟩
  · exact Or.inl hcode
  refine Or.inr ⟨hcode, ?_⟩
  have hnd : ¬ isValidDelegation (node.devm.getCode I) := by rw [hI]; exact hCdel
  cases edge with
  | cont hstep _ => exact hK.reach_cont hcode hreach hstep
  | doneOk hstep _ _ _ =>
      exact Or.inr (Or.inr (Or.inr (le_of_eq (hK.reach_spawn hcode hreach hstep hnd).1.symm)))
  | runOk hstep _ _ _ _ =>
      exact Or.inr (Or.inr (Or.inr (le_of_eq (hK.reach_spawn hcode hreach hstep hnd).1.symm)))

/-- An entered child frame satisfies the invariant at its root. -/
private theorem OwnerLoc.child (hK : ForwarderShape K I) (hC : 0 < C.size)
    (hCdel : ¬ isValidDelegation C)
    {pc pc' : Nat} {sevm : Sevm} {d : Devm} {f : Frame} {rsm : Resume} {cevm : Evm}
    (hs : Evm.step ⟨pc, sevm, d⟩ = .spawn f rsm pc') (he : f.enter = .run cevm)
    (loc : OwnerLoc K C P I pc sevm d)
    (free : sevm.code = C →
      ¬ Xinst.At C pc .delegatecall ∧ ¬ Xinst.At C pc .callcode) :
    OwnerLoc K C P I cevm.pc cevm.sta cevm.dyna := by
  have hKsize : 0 < K.size := by rw [hK.1]; decide
  have hKdel : ¬ isValidDelegation K := not_delegation_of_size (by rw [hK.1]; decide)
  obtain ⟨hpc0, hgc, hsrc⟩ := Evm.step_spawn_child hs he
  obtain ⟨hP, hI, howner⟩ := loc
  refine ⟨by rw [hgc]; exact hP, by rw [hgc]; exact hI, fun htgt => ?_⟩
  have reach0 : ForwarderReach I cevm.pc cevm.dyna.stack := Or.inl (by omega)
  have hPne : d.getCode P ≠ .empty := by
    rcases hP with h | h <;> rw [h]
    · exact ne_empty_of_size_pos hKsize
    · exact ne_empty_of_size_pos hC
  have hPnd : ¬ isValidDelegation (d.getCode P) := by
    rcases hP with h | h <;> rw [h]
    · exact hKdel
    · exact hCdel
  -- The child's code is `P`'s own code, or `C`.
  suffices hcode : cevm.sta.code = d.getCode P ∨ cevm.sta.code = C by
    rcases hcode with h | h
    · rcases hP with hk | hc
      · exact Or.inr ⟨h.trans hk, reach0⟩
      · exact Or.inl (h.trans hc)
    · exact Or.inl h
  by_cases hparent : sevm.currentTarget = P
  · obtain ⟨x, hat, hx, -⟩ := Evm.step_spawn_inv hs
    rw [Frame.enter_run_code he]
    rw [Frame.enter_run_currentTarget he] at htgt
    rcases howner hparent with hcode | ⟨hcode, hreach⟩
    · rw [hcode] at hat
      obtain ⟨nodc, nocc⟩ := free hcode
      cases x with
      | create =>
          exact absurd (htgt ▸ Xinst.step_create_spawn_fresh (Or.inl rfl) hx) hPne
      | create2 =>
          exact absurd (htgt ▸ Xinst.step_create_spawn_fresh (Or.inr rfl) hx) hPne
      | call =>
          exact Or.inl (htgt ▸ Xinst.step_directCall_spawn_code (Or.inl rfl) hx
            (htgt ▸ hPnd))
      | staticcall =>
          exact Or.inl (htgt ▸ Xinst.step_directCall_spawn_code (Or.inr rfl) hx
            (htgt ▸ hPnd))
      | delegatecall => exact absurd hat nodc
      | callcode => exact absurd hat nocc
    · have hnd : ¬ isValidDelegation (d.getCode I) := by rw [hI]; exact hCdel
      exact Or.inr ((hK.reach_spawn hcode hreach hs hnd).2.trans hI)
  · left
    have := hsrc (by rw [htgt]; exact hparent) (by rw [htgt]; exact hPne)
      (by rw [htgt]; exact hPnd)
    rw [this, htgt]

/-- Every entered descendant frame root satisfies the invariant. -/
private theorem Exec.ownerLoc_descendants (hK : ForwarderShape K I) (hC : 0 < C.size)
    (hCdel : ¬ isValidDelegation C) :
    ∀ {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
      (run : Exec pc sevm pre out),
      OwnerLoc K C P I pc sevm pre →
      (∀ n ∈ Exec.rawNodes run, n.sevm.code = C →
        ¬ Xinst.At C n.pc .delegatecall ∧ ¬ Xinst.At C n.pc .callcode) →
      ∀ G ∈ Exec.rawFrameDescendants run, OwnerLoc K C P I G.pc G.sevm G.devm := by
  intro pc sevm pre out run
  induction run with
  | halt _ => intro _ _ G hG; simp [Exec.rawFrameDescendants] at hG
  | doneErr _ _ _ => intro _ _ G hG; simp [Exec.rawFrameDescendants] at hG
  | cont hstep next ih =>
      intro loc free G hG
      simp only [Exec.rawFrameDescendants] at hG
      refine ih (OwnerLoc.next hK hC hCdel (.cont hstep next) loc)
        (fun n hn => free n ?_) G hG
      simp [Exec.rawNodes, hn]
  | doneOk hstep henter hresume next ih =>
      intro loc free G hG
      simp only [Exec.rawFrameDescendants] at hG
      refine ih (OwnerLoc.next hK hC hCdel (.doneOk hstep henter hresume next) loc)
        (fun n hn => free n ?_) G hG
      simp [Exec.rawNodes, hn]
  | runErr hstep henter child hresume ih =>
      intro loc free G hG
      have cloc := OwnerLoc.child hK hC hCdel hstep henter loc
        (free _ (Exec.mem_rawNodes_self _))
      simp only [Exec.rawFrameDescendants, List.mem_cons] at hG
      rcases hG with rfl | hG
      · exact cloc
      · exact ih cloc (fun n hn => free n (by simp [Exec.rawNodes, hn])) G hG
  | runOk hstep henter child hresume next childIh nextIh =>
      intro loc free G hG
      have cloc := OwnerLoc.child hK hC hCdel hstep henter loc
        (free _ (Exec.mem_rawNodes_self _))
      simp only [Exec.rawFrameDescendants, List.mem_cons, List.mem_append] at hG
      rcases hG with rfl | hG | hG
      · exact cloc
      · exact childIh cloc (fun n hn => free n (by simp [Exec.rawNodes, hn])) G hG
      · exact nextIh (OwnerLoc.next hK hC hCdel
          (.runOk hstep henter child hresume next) loc)
          (fun n hn => free n (by simp [Exec.rawNodes, hn])) G hG

end Induction

/-- **Owner code from world premises.**  In any execution (of any outcome)
starting where `P` holds the forwarder `K` or `C` and `I` holds `C`, every
frame root owning `P`'s storage runs `C` or `K`, provided the root frame does
and no frame running `C` executes `DELEGATECALL` or `CALLCODE`. -/
theorem Exec.ownerCode_of_world {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) {P I : Adr} {K C : ByteArray}
    (hK : ForwarderShape K I) (hC : 0 < C.size) (hCdel : ¬ isValidDelegation C)
    (hP : pre.getCode P = K ∨ pre.getCode P = C) (hI : pre.getCode I = C)
    (hroot : sevm.currentTarget = P → sevm.code = K ∨ sevm.code = C)
    (hfree : Exec.NoDelegateFrom run C) :
    ∀ G ∈ Exec.rawFrameRoots run,
      G.sevm.currentTarget = P → G.sevm.code = C ∨ G.sevm.code = K := by
  have rootLoc : OwnerLoc K C P I 0 sevm pre :=
    ⟨hP, hI, fun h => (hroot h).elim (fun hk => Or.inr ⟨hk, Or.inl (by omega)⟩) Or.inl⟩
  have nodeFree : ∀ n ∈ Exec.rawNodes run, n.sevm.code = C →
      ¬ Xinst.At C n.pc .delegatecall ∧ ¬ Xinst.At C n.pc .callcode := by
    intro n hn hcode
    obtain ⟨F, hF, hFn⟩ := (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run n).mp hn
    exact hfree F hF (by rw [← Blanc.Exec.Deriv.ParentPrefix.sevm_eq hFn]; exact hcode) n hFn
  intro G hG htgt
  have loc : OwnerLoc K C P I G.pc G.sevm G.devm := by
    simp only [Exec.rawFrameRoots, List.mem_cons] at hG
    rcases hG with rfl | hG
    · exact rootLoc
    · exact Exec.ownerLoc_descendants hK hC hCdel run rootLoc nodeFree G hG
  rcases loc.2.2 htgt with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- **G3b** (`LockSpec.OwnerDiscipline`) from world premises: with `C = L.code`
and a forwarder without `SSTORE`, every frame owning `P`'s storage runs `L.code`
or a code with no `SSTORE`. -/
theorem Exec.ownerDiscipline_of_world {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec 0 sevm pre out) (L : LockSpec) {P I : Adr} {K : ByteArray}
    (hK : ForwarderShape K I) (hKstore : NoSstore K)
    (hC : 0 < L.code.size) (hCdel : ¬ isValidDelegation L.code)
    (hP : pre.getCode P = K ∨ pre.getCode P = L.code) (hI : pre.getCode I = L.code)
    (hroot : sevm.currentTarget = P → sevm.code = K ∨ sevm.code = L.code)
    (hfree : Exec.NoDelegateFrom run L.code) :
    L.OwnerDiscipline P run := by
  intro G hG htgt
  rcases Exec.ownerCode_of_world run hK hC hCdel hP hI hroot hfree G hG htgt with h | h
  · exact Or.inl h
  · exact Or.inr (h ▸ hKstore)

/-! ## Concrete forwarders -/

/-- A decoded instruction other than `SSTORE`. -/
def Inst.notSstore : Option Inst → Bool
  | some (.next (.reg .sstore)) => false
  | _ => true

/-- `NoSstore` from a finite scan of the code's pcs. -/
theorem noSstore_of_scan {K : ByteArray}
    (scan : ∀ pc, pc < K.size → Inst.notSstore (K.getInst pc) = true) :
    NoSstore K := by
  intro pc hat
  by_cases hpc : pc < K.size
  · have := scan pc hpc
    unfold Ninst.At at hat
    rw [hat] at this
    simp [Inst.notSstore] at this
  · unfold Ninst.At ByteArray.getInst at hat
    simp only [hpc, ↓reduceDIte] at hat
    cases hat

/-- The corrected Curve plain-pool implementation (factory `plain_implementations(2,5)`). -/
def curvePlainImpl847e : Adr := 0x847ee1227a9900b73aeeb3a47fac92c52fd54ed9

/-- The implementation behind the recorded 0x6326 pool forwarders. -/
def curvePlainImpl6326 : Adr := 0x6326debbaa15bcfe603d831e7d75f4fc10d9b43e

theorem forwarderShape_847e :
    ForwarderShape (forwarderCode curvePlainImpl847e) curvePlainImpl847e := by
  decide +kernel

theorem noSstore_forwarder_847e : NoSstore (forwarderCode curvePlainImpl847e) :=
  noSstore_of_scan (by decide +kernel)

theorem forwarderShape_6326 :
    ForwarderShape (forwarderCode curvePlainImpl6326) curvePlainImpl6326 := by
  decide +kernel

theorem noSstore_forwarder_6326 : NoSstore (forwarderCode curvePlainImpl6326) :=
  noSstore_of_scan (by decide +kernel)

end Blanc
