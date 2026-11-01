-- CommonProofs/Hinv.lean : the `Rinst.Hinv` instance family and the scoped `LogOutputHinv` instances.

import Blanc.CommonProofs.Walk

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

class Rinst.Hinv {ξ : Type} (f : Devm → ξ) (o : Rinst) where (inv : Rinst.Inv f o)

instance {ξ : Type} (f : Devm → ξ) (o : Rinst) [Rinst.Hinv f o] :
    Ninst.Hinv f (Ninst.reg o) := ⟨by
  intros e s s' h
  rcases h with ⟨xl, h_filled, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact Rinst.Hinv.inv run.2.symm
⟩

instance {o : Rinst} : Rinst.Hinv Devm.getBal o := ⟨Rinst.preserves_bal⟩

instance : Rinst.Hinv Devm.state Rinst.callvalue :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

instance : Rinst.Hinv Devm.state Rinst.iszero :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

instance : Rinst.Hinv Devm.state Rinst.mstore :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

instance : Rinst.Hinv Devm.state Rinst.mload :=
  ⟨Rinst.preserves_state (by intro h; cases h) (by intro h; cases h)⟩

/-- The whole persistent world state is preserved by every register
instruction except the two store forms; these are the cases the compiled
walks in this repository actually step through. -/
syntax "show_hinv_state" : tactic
macro_rules
  | `(tactic| show_hinv_state) =>
    `(tactic| exact ⟨Rinst.preserves_state (by intro h; cases h)
        (by intro h; cases h)⟩)

instance : Rinst.Hinv Devm.state Rinst.calldatasize := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.calldataload := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.calldatacopy := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.codesize := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.codecopy := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.lt := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.gt := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.add := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.mul := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.sub := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.and := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.or := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.not := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.eq := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.shl := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.shr := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.div := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.mod := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.exp := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.slt := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.sgt := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.timestamp := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.caller := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.gas := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.sload := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.pop := by show_hinv_state

/-- An observation preserved as a whole family is preserved at each index.  A
walk that only tracks one account's balance states its invariant as the
projection `fun d => d.getBal a`, so the family instances above are exposed at
that shape rather than restated per contract. -/
instance {a : Adr} {o : Rinst} : Rinst.Hinv (fun d => Devm.getBal d a) o :=
  ⟨by intro pc sevm pre post hrun; exact congrFun (Rinst.preserves_bal hrun) a⟩

instance {a : Adr} {i : Ninst} [Ninst.Hinv Devm.getBal i] :
    Ninst.Hinv (fun d => Devm.getBal d a) i :=
  ⟨by intros e s s' h; exact congrFun (Ninst.Hinv.inv h) a⟩

instance {o : Rinst} : Rinst.Hinv Devm.getCode o := ⟨by
  intro pc sevm pre post run
  funext a
  exact (Rinst.preserves_getCode run a).symm⟩

syntax "show_hinv_stor" : tactic
macro_rules
  | `(tactic| show_hinv_stor) =>
    `(tactic| exact ⟨Rinst.preserves_stor (by intro; contradiction)⟩)


instance : Rinst.Hinv Devm.getStor Rinst.add := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mul := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sub := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.div := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sdiv := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.smod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.addmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mulmod := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.exp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.signextend := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.lt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.slt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sgt := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.eq := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.iszero := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.and := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.or := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.xor := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.not := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.byte := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shr := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.shl := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sar := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.clz := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.keccak256 := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.address := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.balance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.origin := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.caller := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.callvalue := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldataload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.calldatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.codecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gasprice := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodesize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodecopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.returndatasize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.returndatacopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.extcodehash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blockhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.coinbase := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.timestamp := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.number := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.prevrandao := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gaslimit := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.chainid := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.selfbalance := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.basefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobhash := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.blobbasefee := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pop := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mstore8 := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.sload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tload := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.tstore := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.mcopy := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.pc := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.msize := by show_hinv_stor
instance : Rinst.Hinv Devm.getStor Rinst.gas := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.dup n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.swap n) := by show_hinv_stor
instance {n} : Rinst.Hinv Devm.getStor (Rinst.log n) := by show_hinv_stor

/-! ### `Ninst.Hinv` instances for the push and stack-scratch instructions

The `Rinst.Hinv` layer above covers every register instruction; these cover
the `Ninst` constructors that are not `reg` (`push`, `pushB256`, `dup`) plus
the `Devm.state` observable, which has no blanket `Rinst` instance because
`sstore` moves it.  They live here, with the rest of the `Hinv` API and the
`Ninst.run_push_eq` equation written for them, rather than in a contract's
own file: `line_inv` needs them wherever a dispatcher's scratch lines are
reasoned about, which is now `Ladder.lean`. -/

instance {x} : Ninst.Hinv Devm.getBal (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  rcases hc : chargeGas (if (x.toBytes.sig) = [] then gBase else gVerylow) s with _ | s_gas
  · rw [hc] at run; dsimp only [Except.bind_error] at run; contradiction
  · rw [hc] at run; dsimp only [Except.bind_ok] at run
    rcases hp : Devm.push x.toBytes.sig.toB256 s_gas with _ | s''
    · rw [hp] at run; contradiction
    · rw [hp] at run
      injection run with h_eq; subst h_eq
      apply funext; intro a
      exact (chargeGas_getBal_eq hc a).symm.trans (Devm.push_getBal_eq hp a).symm
⟩

instance {x} : Ninst.Hinv Devm.getStor (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  rcases hc : chargeGas (if (x.toBytes.sig) = [] then gBase else gVerylow) s with _ | s_gas
  · rw [hc] at run; dsimp only [Except.bind_error] at run; contradiction
  · rw [hc] at run; dsimp only [Except.bind_ok] at run
    rcases hp : Devm.push x.toBytes.sig.toB256 s_gas with _ | s''
    · rw [hp] at run; contradiction
    · rw [hp] at run
      injection run with h_eq; subst h_eq
      exact (chargeGas_getStor_eq hc).trans (Devm.push_getStor_eq hp)
⟩

instance {x} : Ninst.Hinv Devm.getCode (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  rcases hc : chargeGas (if (x.toBytes.sig) = [] then gBase else gVerylow) s with _ | s_gas
  · rw [hc] at run; dsimp only [Except.bind_error] at run; contradiction
  · rw [hc] at run; dsimp only [Except.bind_ok] at run
    rcases hp : Devm.push x.toBytes.sig.toB256 s_gas with _ | s''
    · rw [hp] at run; contradiction
    · rw [hp] at run
      injection run with h_eq; subst h_eq
      apply funext; intro a
      exact (chargeGas_getCode_eq hc a).symm.trans (Devm.push_getCode_eq hp a).symm
⟩

instance {x} : Ninst.Hinv Devm.state (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  rcases h_pb with ⟨_, _, _, _, _, _, _, _, _, _, _, h_state, _⟩
  exact h_state
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getBal (Ninst.push xs p) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  funext a; simp only [Devm.getBal, Devm.getAcct]; rw [h_pb.state]
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getStor (Ninst.push xs p) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  funext a; simp only [Devm.getStor, Devm.getAcct]; rw [h_pb.state]
⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.getCode (Ninst.push xs p) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  funext a; simp only [Devm.getCode, Devm.getAcct]; rw [h_pb.state]
⟩

instance : Ninst.Hinv Devm.state (Ninst.reg Rinst.eq) := ⟨by
  intros e s s' h
  obtain ⟨pc, run⟩ := of_run_reg h
  dsimp only [ExceptT.stM_eq, Rinst.run, Rinst.runCore] at run
  rw [applyBinary_def] at run
  rcases hp1 : Devm.pop s with _ | val1
  · rw [hp1] at run; dsimp only [bind, Except.bind, Except.bind_error] at run; contradiction
  · rw [hp1] at run; dsimp only [bind, Except.bind, Except.bind_ok] at run
    rcases val1 with ⟨x1, s1⟩
    rcases hp2 : Devm.pop s1 with _ | val2
    · rw [hp2] at run; dsimp only at run; contradiction
    · rw [hp2] at run; dsimp only at run
      rcases val2 with ⟨x2, s2⟩
      rcases hpush : pushItem _ gVerylow s2 with _ | s''
      · rw [hpush] at run; contradiction
      · rw [hpush] at run
        injection run with h_eq; subst h_eq
        have h_pop1 := Devm.pop_of_pop hp1
        have h_pop2 := Devm.pop_of_pop hp2
        have h_push := Devm.pushBurn_of_pushItem hpush
        rcases h_pop1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩
        rcases h_pop2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs2, _⟩
        rcases h_push with ⟨_, _, _, _, _, _, _, _, _, _, _, hs3, _⟩
        exact hs1.trans (hs2.trans hs3)
⟩

instance {n} : Ninst.Hinv Devm.state (Ninst.dup n) := ⟨by
  intros e s s' h
  obtain ⟨pc, run⟩ := of_run_reg h
  dsimp only [ExceptT.stM_eq, Rinst.run, Rinst.runCore, Fin.getElem?_fin] at run
  rcases hc : chargeGas gVerylow s with _ | s_gas
  · rw [hc] at run; dsimp only [Except.bind_error] at run; contradiction
  · rw [hc] at run; dsimp only [Except.bind_ok] at run
    split at run
    · contradiction
    · rename_i rh word
      have h_run_eq : (chargeGas gVerylow s >>= fun d => d.push rh) = .ok s' := by
        dsimp only [bind, Except.bind]; rw [hc]; exact run
      have h_pb := Devm.pushBurn_of_run h_run_eq
      rcases h_pb with ⟨_, _, _, _, _, _, _, _, _, _, _, h_state, _⟩
      exact h_state
⟩

instance {n} : Ninst.Hinv Devm.state (Ninst.swap n) := ⟨by
  intro e s s' h
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    subst eq
    exact hb.state⟩

instance : Ninst.Hinv Devm.state (Ninst.reg Rinst.gt) := ⟨by
  intros e s s' h
  obtain ⟨pc, run⟩ := of_run_reg h
  dsimp only [ExceptT.stM_eq, Rinst.run, Rinst.runCore] at run
  rw [applyBinary_def] at run
  rcases hp1 : Devm.pop s with _ | val1
  · rw [hp1] at run; dsimp only [bind, Except.bind, Except.bind_error] at run; contradiction
  · rw [hp1] at run; dsimp only [bind, Except.bind, Except.bind_ok] at run
    rcases val1 with ⟨x1, s1⟩
    rcases hp2 : Devm.pop s1 with _ | val2
    · rw [hp2] at run; dsimp only at run; contradiction
    · rw [hp2] at run; dsimp only at run
      rcases val2 with ⟨x2, s2⟩
      rcases hpush : pushItem _ gVerylow s2 with _ | s''
      · rw [hpush] at run; contradiction
      · rw [hpush] at run
        injection run with h_eq; subst h_eq
        have h_pop1 := Devm.pop_of_pop hp1
        have h_pop2 := Devm.pop_of_pop hp2
        have h_push := Devm.pushBurn_of_pushItem hpush
        rcases h_pop1 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs1, _⟩
        rcases h_pop2 with ⟨_, _, _, _, _, _, _, _, _, _, _, hs2, _⟩
        rcases h_push with ⟨_, _, _, _, _, _, _, _, _, _, _, hs3, _⟩
        exact hs1.trans (hs2.trans hs3)
⟩

/-! ### What each instruction does to memory

`Devm.memory` is preserved outright by every instruction except the three that
touch it, so the `line_inv` machinery carries a memory image across whole
`Line`s once these `Hinv` instances exist.  The three exceptions get
value-carrying inversions of their own, further down beside the `Mem` write
algebra.

The block sits *here*, beside the `Devm.state` / `Devm.getStor` / `Devm.getCode`
instances rather than with the `Mem` material, because instance resolution is
position-sensitive within a module and dispatch reachability — immediately below
— needs a memory image carried across the dispatcher's scratch instructions. -/

syntax "show_hinv_mem_binary" : tactic
macro_rules
  | `(tactic| show_hinv_mem_binary) =>
    `(tactic|
        refine ⟨?_⟩ <;>
        intro pc sevm pre post run <;>
        simp only [Rinst.run, Rinst.runCore] at run <;>
        (first | exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.memory | (split at run <;> first | exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.memory | cases run)))

syntax "show_hinv_mem_unary" : tactic
macro_rules
  | `(tactic| show_hinv_mem_unary) =>
    `(tactic|
        refine ⟨?_⟩ <;>
        intro pc sevm pre post run <;>
        simp only [Rinst.run, Rinst.runCore] at run <;>
        exact (Devm.diffBurn_of_applyUnary run).choose_spec.memory)

syntax "show_hinv_mem_push" : tactic
macro_rules
  | `(tactic| show_hinv_mem_push) =>
    `(tactic|
        refine ⟨?_⟩ <;>
        intro pc sevm pre post run <;>
        simp only [Rinst.run, Rinst.runCore] at run <;>
        exact (Devm.pushBurn_of_pushItem run).memory)

instance : Rinst.Hinv Devm.memory Rinst.add := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.sub := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.lt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.gt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.eq := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.and := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.or := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.xor := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.shl := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.shr := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.mul := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.div := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.mod := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.sdiv := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.smod := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.slt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.sgt := by show_hinv_mem_binary
instance : Rinst.Hinv Devm.memory Rinst.not := by show_hinv_mem_unary
instance : Rinst.Hinv Devm.memory Rinst.iszero := by show_hinv_mem_unary
instance : Rinst.Hinv Devm.memory Rinst.address := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.caller := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.callvalue := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.returndatasize := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.calldatasize := by show_hinv_mem_push
instance : Rinst.Hinv Devm.memory Rinst.selfbalance := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  split at run
  ·
    rcases Except.bind_eq_ok run with ⟨d1, hgas, hpush⟩
    have hbr : d1.memory =
        (Devm.balReadAccount sevm.benvStat.rules sevm.currentTarget d1).memory := rfl
    exact ((Devm.burn_of_chargeGas hgas).memory.trans hbr).trans
      (Devm.push_of_push hpush).memory
  · cases run
⟩

instance : Rinst.Hinv Devm.memory Rinst.pop := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨x, s₂⟩ <;> simp only [hp, reduceCtorEq, Except.ok.injEq] at h1
  subst h1
  exact (Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp)
    (Devm.burn_of_chargeGas h2)).memory⟩

instance : Rinst.Hinv Devm.memory Rinst.gas := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact (Devm.pushBurn_of_burn_of_push (Devm.burn_of_chargeGas h1)
    (Devm.push_of_push h2)).memory⟩

instance {n} : Rinst.Hinv Devm.memory (Rinst.dup n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · exact (Devm.pushBurn_of_burn_of_push hb (Devm.push_of_push h2)).memory⟩

instance {n} : Rinst.Hinv Devm.memory (Rinst.swap n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    rw [hb.memory, ← eq]
    rfl⟩

instance : Rinst.Hinv Devm.memory Rinst.calldataload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  exact ((Devm.pop_of_pop h1).memory.trans
    (Devm.burn_of_chargeGas h2).memory).trans (Devm.push_of_push run₂).memory⟩

/-- `SLOAD` reads storage and touches nothing else.  Not covered by the routine
macros above because the cold/warm split makes it two shapes rather than one. -/
instance : Rinst.Hinv Devm.memory Rinst.sload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  refine (Devm.pop_of_pop h1).memory.trans ?_
  suffices H : ∀ (d : Devm) (c : Nat), s₁.memory = d.memory →
      (chargeGas c d >>= fun next => Devm.push
        (Devm.getStorVal (Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget key next) sevm.currentTarget key)
        (Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget key next))
        = .ok post → s₁.memory = post.memory by
    cases haccess : sevm.benvStat.rules.access with
    | eip2929 =>
      simp only [haccess] at run₁
      split at run₁
      · exact H s₁ gasWarmAccess rfl run₁
      · exact H (addAccessedStorageKey s₁ sevm.currentTarget key) gasColdSload rfl run₁
    | flat gas =>
      simp only [haccess] at run₁
      exact H s₁ gas.sload rfl run₁
  intro d c hm run'
  rcases Except.bind_eq_ok run' with ⟨s₂, h2, run₂⟩
  exact (hm.trans (Devm.burn_of_chargeGas h2).memory).trans (Devm.push_of_push run₂).memory⟩

/-- `SSTORE` writes storage and touches nothing else.  The longest of these
proofs only because the instruction has the most intermediate states: the
access-list split, the refund counter, the gas charge and the dynamic assert
each produce one, and every one of them leaves `Devm.memory` alone. -/
instance : Rinst.Hinv Devm.memory Rinst.sstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Legacy gas lane: the regime-selected eight-bind walk.
    simp only [hsg] at run
    split at run
    all_goals
      rcases Except.bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
      rcases Except.bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
      rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
      rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
      rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
      rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
      rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
      rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
      have m3 : s₂.memory = s₃.memory := by
        injection h4 with eq
        repeat' split at eq
        all_goals injection eq with eq _; subst eq; rfl
      have m4 : s₃.memory = s₄.memory := by
        injection h6 with eq; rw [← eq]; rfl
      have eq := Except.ok.inj h9
      rw [← eq]
      show pre.memory = s₅.memory
      exact ((((Devm.pop_of_pop h1).memory.trans (Devm.pop_of_pop h2).memory).trans m3).trans
        m4).trans (Devm.burn_of_chargeGas h7).memory
  · -- Amsterdam: static check first, state-gas second dimension.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, h0, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨x, s₁⟩, h1, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨⟨y, s₂⟩, h2, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, h3, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨s₃, hchg, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨s₄, hstg, h9⟩
    have hstg_mem : s₃.memory = s₄.memory :=
      (Devm.chargeStateGas_memory hstg).symm
    have hmid : s₂.memory = s₄.memory := by
      have e1 := (Devm.burn_of_chargeGas hchg).memory
      have e2 := hstg_mem
      rw [← e2, ← e1]
      simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund,
        Devm.withRefundCounter, Devm.balReadStorage, Devm.setMach_memory]
      try split <;> (try split) <;> rfl
    have eq := Except.ok.inj h9
    rw [← eq]
    show pre.memory = s₄.memory
    exact (Devm.pop_of_pop h1).memory.trans
      ((Devm.pop_of_pop h2).memory.trans hmid)⟩

/-! The two `Ninst` constructors that are not `reg`, so that `line_inv` carries
a memory image across a whole `Line` rather than stopping at the first `PUSH`.
Their `Devm.getBal` / `Devm.getStor` / `Devm.getCode` / `Devm.state` siblings
are above, beside the rest of the `Ninst.Hinv` API. -/

instance {x} : Ninst.Hinv Devm.memory (Ninst.pushB256 x) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).memory⟩

instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.memory (Ninst.push xs p) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).memory⟩

/-! ### What the permit approval tail does to logs and output

Ordinary scratch instructions preserve both fields.  `LOG` is intentionally
absent from the log instances: its exact append effect is exposed by
`of_run_log_val` / `of_logWith201_val` below.  These instances are the minimal
projection seam needed to carry that value-carrying observation across the
surrounding copy/hash/store instructions.  They live in an opt-in scope so
unrelated `line_inv` searches do not pay for these additional candidates. -/

namespace LogOutputHinv

syntax "show_hinv_logs_binary" : tactic
macro_rules
  | `(tactic| show_hinv_logs_binary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      (first | exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs | (split at run <;> first | exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.logs | cases run)))

syntax "show_hinv_output_binary" : tactic
macro_rules
  | `(tactic| show_hinv_output_binary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      (first | exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output | (split at run <;> first | exact (Devm.diffBurn_of_applyBinary run).choose_spec.choose_spec.output | cases run)))

syntax "show_hinv_logs_unary" : tactic
macro_rules
  | `(tactic| show_hinv_logs_unary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      exact (Devm.diffBurn_of_applyUnary run).choose_spec.logs)

syntax "show_hinv_output_unary" : tactic
macro_rules
  | `(tactic| show_hinv_output_unary) =>
    `(tactic|
      refine ⟨?_⟩ <;>
      intro pc sevm pre post run <;>
      simp only [Rinst.run, Rinst.runCore] at run <;>
      exact (Devm.diffBurn_of_applyUnary run).choose_spec.output)

scoped instance : Rinst.Hinv Devm.logs Rinst.and := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.add := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.or := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.eq := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.gt := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.lt := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.shl := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.shr := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.mul := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.div := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.sub := by show_hinv_logs_binary
scoped instance : Rinst.Hinv Devm.logs Rinst.iszero := by show_hinv_logs_unary
scoped instance : Rinst.Hinv Devm.logs Rinst.not := by show_hinv_logs_unary

scoped instance : Rinst.Hinv Devm.output Rinst.and := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.add := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.or := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.eq := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.gt := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.lt := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.shl := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.shr := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.mul := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.div := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.sub := by show_hinv_output_binary
scoped instance : Rinst.Hinv Devm.output Rinst.iszero := by show_hinv_output_unary
scoped instance : Rinst.Hinv Devm.output Rinst.not := by show_hinv_output_unary

scoped instance {x} : Ninst.Hinv Devm.logs (Ninst.pushB256 x) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).logs⟩

scoped instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.logs (Ninst.push xs p) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).logs⟩

scoped instance {n} : Ninst.Hinv Devm.logs (Ninst.dup n) := ⟨by
  intro e s s' h
  rcases of_run_dup h with ⟨x, hx, hpb⟩
  exact hpb.logs⟩

scoped instance {n} : Ninst.Hinv Devm.output (Ninst.dup n) := ⟨by
  intro e s s' h
  rcases of_run_dup h with ⟨x, hx, hpb⟩
  exact hpb.output⟩

scoped instance {x} : Ninst.Hinv Devm.output (Ninst.pushB256 x) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).output⟩

scoped instance {xs} {p : xs.length ≤ 32} : Ninst.Hinv Devm.output (Ninst.push xs p) :=
  ⟨fun h => (Devm.pushBurn_of_run (Ninst.run_push_eq h)).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.address := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.address := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.caller := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.caller := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.callvalue := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.callvalue := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.calldatasize := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.calldatasize := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.timestamp := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.timestamp := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.pop := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨x, s₂⟩ <;> simp only [hp, reduceCtorEq, Except.ok.injEq] at h1
  subst h1
  exact (Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp)
    (Devm.burn_of_chargeGas h2)).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.pop := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨x, s₂⟩ <;> simp only [hp, reduceCtorEq, Except.ok.injEq] at h1
  subst h1
  exact (Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp)
    (Devm.burn_of_chargeGas h2)).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.gas := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact (Devm.burn_of_chargeGas h1).logs.trans
    (Devm.push_of_push h2).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.gas := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact (Devm.burn_of_chargeGas h1).output.trans
    (Devm.push_of_push h2).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.sload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hp := Devm.pop_of_pop h1
  cases haccess : sevm.benvStat.rules.access with
  | eip2929 =>
    simp only [haccess] at run₁
    split at run₁
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      exact hp.logs.trans
        ((Devm.burn_of_chargeGas h2).logs.trans (Devm.balReadStorage_logs.symm.trans (Devm.push_of_push h3).logs))
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      have ha : s₁.logs =
          (addAccessedStorageKey s₁ sevm.currentTarget key).logs := rfl
      exact hp.logs.trans (ha.trans
        ((Devm.burn_of_chargeGas h2).logs.trans (Devm.balReadStorage_logs.symm.trans (Devm.push_of_push h3).logs)))
  | flat gas =>
    simp only [haccess] at run₁
    rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hp.logs.trans
      ((Devm.burn_of_chargeGas h2).logs.trans (Devm.balReadStorage_logs.symm.trans (Devm.push_of_push h3).logs))
⟩

scoped instance : Rinst.Hinv Devm.output Rinst.sload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hp := Devm.pop_of_pop h1
  cases haccess : sevm.benvStat.rules.access with
  | eip2929 =>
    simp only [haccess] at run₁
    split at run₁
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      exact hp.output.trans
        ((Devm.burn_of_chargeGas h2).output.trans (Devm.balReadStorage_output.symm.trans (Devm.push_of_push h3).output))
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      have ha : s₁.output =
          (addAccessedStorageKey s₁ sevm.currentTarget key).output := rfl
      exact hp.output.trans (ha.trans
        ((Devm.burn_of_chargeGas h2).output.trans (Devm.balReadStorage_output.symm.trans (Devm.push_of_push h3).output)))
  | flat gas =>
    simp only [haccess] at run₁
    rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hp.output.trans
      ((Devm.burn_of_chargeGas h2).output.trans (Devm.balReadStorage_output.symm.trans (Devm.push_of_push h3).output))
⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.extcodesize := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨adr, s₁⟩, h1, run₁⟩
  rw [Devm.popToAdr_def] at h1
  dsimp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨word, d0⟩ <;>
    simp only [hp, reduceCtorEq, Except.ok.injEq] at h1
  rcases h1 with ⟨rfl, rfl⟩
  have hpop := Devm.pop_of_pop hp
  cases haccess : sevm.benvStat.rules.access with
  | eip2929 =>
    simp only [haccess] at run₁
    split at run₁
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      exact hpop.logs.trans
        ((Devm.burn_of_chargeGas h2).logs.trans ((Devm.balReadAccount_logs _ _ _).symm.trans (Devm.push_of_push h3).logs))
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      have ha : d0.logs = (addAccessedAddress d0 word.toAdr).logs := rfl
      exact hpop.logs.trans (ha.trans
        ((Devm.burn_of_chargeGas h2).logs.trans ((Devm.balReadAccount_logs _ _ _).symm.trans (Devm.push_of_push h3).logs)))
  | flat gas =>
    simp only [haccess] at run₁
    rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hpop.logs.trans
      ((Devm.burn_of_chargeGas h2).logs.trans ((Devm.balReadAccount_logs _ _ _).symm.trans (Devm.push_of_push h3).logs))
⟩

scoped instance : Rinst.Hinv Devm.output Rinst.extcodesize := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨adr, s₁⟩, h1, run₁⟩
  rw [Devm.popToAdr_def] at h1
  dsimp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop pre with _ | ⟨word, d0⟩ <;>
    simp only [hp, reduceCtorEq, Except.ok.injEq] at h1
  rcases h1 with ⟨rfl, rfl⟩
  have hpop := Devm.pop_of_pop hp
  cases haccess : sevm.benvStat.rules.access with
  | eip2929 =>
    simp only [haccess] at run₁
    split at run₁
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      exact hpop.output.trans
        ((Devm.burn_of_chargeGas h2).output.trans (Devm.balReadAccount_output.symm.trans (Devm.push_of_push h3).output))
    · rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
      have ha : d0.output = (addAccessedAddress d0 word.toAdr).output := rfl
      exact hpop.output.trans (ha.trans
        ((Devm.burn_of_chargeGas h2).output.trans (Devm.balReadAccount_output.symm.trans (Devm.push_of_push h3).output)))
  | flat gas =>
    simp only [haccess] at run₁
    rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, h3⟩
    exact hpop.output.trans
      ((Devm.burn_of_chargeGas h2).output.trans (Devm.balReadAccount_output.symm.trans (Devm.push_of_push h3).output))
⟩


scoped instance {n} : Rinst.Hinv Devm.logs (Rinst.swap n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    rw [hb.logs, ← eq]
    rfl⟩

scoped instance {n} : Rinst.Hinv Devm.output (Rinst.swap n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    rw [hb.output, ← eq]
    rfl⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.calldataload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  exact ((Devm.pop_of_pop h1).logs.trans
    (Devm.burn_of_chargeGas h2).logs).trans (Devm.push_of_push run₂).logs⟩

scoped instance : Rinst.Hinv Devm.output Rinst.calldataload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  exact ((Devm.pop_of_pop h1).output.trans
    (Devm.burn_of_chargeGas h2).output).trans (Devm.push_of_push run₂).output⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.calldatacopy := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.logs
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.logs
  have hp3 := (Devm.pop_of_popToNat h3).choose_spec.logs
  have hb := (Devm.burn_of_chargeGas h4).logs
  injection h5 with eq
  rw [← eq]
  exact ((hp1.trans hp2).trans hp3).trans hb⟩

scoped instance : Rinst.Hinv Devm.output Rinst.calldatacopy := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.output
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.output
  have hp3 := (Devm.pop_of_popToNat h3).choose_spec.output
  have hb := (Devm.burn_of_chargeGas h4).output
  injection h5 with eq
  rw [← eq]
  exact ((hp1.trans hp2).trans hp3).trans hb⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.keccak256 := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.logs
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.logs
  have hb := (Devm.burn_of_chargeGas h3).logs
  have hpush := (Devm.push_of_push run₃).logs
  exact ((hp1.trans hp2).trans hb).trans hpush⟩

scoped instance : Rinst.Hinv Devm.output Rinst.keccak256 := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.output
  have hp2 := (Devm.pop_of_popToNat h2).choose_spec.output
  have hb := (Devm.burn_of_chargeGas h3).output
  have hpush := (Devm.push_of_push run₃).output
  exact ((hp1.trans hp2).trans hb).trans hpush⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.mstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨value, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, h4⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.logs
  have hp2 := (Devm.pop_of_pop h2).logs
  have hb := (Devm.burn_of_chargeGas h3).logs
  injection h4 with eq
  rw [← eq]
  exact (hp1.trans hp2).trans hb⟩

scoped instance : Rinst.Hinv Devm.output Rinst.mstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨value, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, h4⟩
  have hp1 := (Devm.pop_of_popToNat h1).choose_spec.output
  have hp2 := (Devm.pop_of_pop h2).output
  have hb := (Devm.burn_of_chargeGas h3).output
  injection h4 with eq
  rw [← eq]
  exact (hp1.trans hp2).trans hb⟩

scoped instance : Rinst.Hinv Devm.logs Rinst.sstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Legacy gas lane: the regime-selected eight-bind walk.
    simp only [hsg] at run
    split at run
    all_goals
      rcases Except.bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
      rcases Except.bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
      rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
      rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
      rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
      rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
      rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
      rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
      have l3 : s₂.logs = s₃.logs := by
        injection h4 with eq
        repeat' split at eq
        all_goals injection eq with eq _; subst eq; exact Devm.balReadStorage_logs.symm
      have l4 : s₃.logs = s₄.logs := by
        injection h6 with eq
        rw [← eq]
        rfl
      have eq := Except.ok.inj h9
      rw [← eq]
      exact (((((Devm.pop_of_pop h1).logs.trans (Devm.pop_of_pop h2).logs).trans
        l3).trans l4).trans (Devm.burn_of_chargeGas h7).logs).trans (Devm.balReadAccount_logs _ _ _).symm
  · -- Amsterdam: static check first, state-gas second dimension.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, h0, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨x, s₁⟩, h1, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨⟨y, s₂⟩, h2, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, h3, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨s₃, hchg, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨s₄, hstg, h9⟩
    have hstg_br : s₃.logs = s₄.logs :=
      (Devm.chargeStateGas_logs hstg).symm
    have hmid : s₂.logs = s₄.logs := by
      have e1 := (Devm.burn_of_chargeGas hchg).logs
      have e2 := hstg_br
      rw [← e2, ← e1]
      simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund,
        Devm.withRefundCounter, Devm.balReadStorage, Devm.setMach_logs]
      try split <;> (try split) <;> rfl
    have eq := Except.ok.inj h9
    rw [← eq]
    exact ((Devm.pop_of_pop h1).logs.trans
      ((Devm.pop_of_pop h2).logs.trans hmid)).trans
      ((Devm.balReadAccount_logs _ _ _).symm)⟩

scoped instance : Rinst.Hinv Devm.output Rinst.sstore := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : sevm.benvStat.rules.stateGas
  · -- Legacy gas lane: the regime-selected eight-bind walk.
    simp only [hsg] at run
    split at run
    all_goals
      rcases Except.bind_eq_ok run with ⟨⟨x, s₁⟩, h1, run₁⟩
      rcases Except.bind_eq_ok run₁ with ⟨⟨y, s₂⟩, h2, run₂⟩
      rcases Except.bind_eq_ok run₂ with ⟨_, h3, run₃⟩
      rcases Except.bind_eq_ok run₃ with ⟨⟨s₃, g₂⟩, h4, run₄⟩
      rcases Except.bind_eq_ok run₄ with ⟨g₃, h5, run₅⟩
      rcases Except.bind_eq_ok run₅ with ⟨s₄, h6, run₆⟩
      rcases Except.bind_eq_ok run₆ with ⟨s₅, h7, run₇⟩
      rcases Except.bind_eq_ok run₇ with ⟨_, h8, h9⟩
      have o3 : s₂.output = s₃.output := by
        injection h4 with eq
        repeat' split at eq
        all_goals injection eq with eq _; subst eq; exact Devm.balReadStorage_output.symm
      have o4 : s₃.output = s₄.output := by
        injection h6 with eq
        rw [← eq]
        rfl
      have eq := Except.ok.inj h9
      rw [← eq]
      exact (((((Devm.pop_of_pop h1).output.trans (Devm.pop_of_pop h2).output).trans
        o3).trans o4).trans (Devm.burn_of_chargeGas h7).output).trans (Devm.balReadAccount_output).symm
  · -- Amsterdam: static check first, state-gas second dimension.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, h0, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨x, s₁⟩, h1, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨⟨y, s₂⟩, h2, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, h3, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨s₃, hchg, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨s₄, hstg, h9⟩
    have hstg_br : s₃.output = s₄.output :=
      (Devm.chargeStateGas_output hstg).symm
    have hmid : s₂.output = s₄.output := by
      have e1 := (Devm.burn_of_chargeGas hchg).output
      have e2 := hstg_br
      rw [← e2, ← e1]
      simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund,
        Devm.withRefundCounter, Devm.balReadStorage, Devm.setMach_output]
      try split <;> (try split) <;> rfl
    have eq := Except.ok.inj h9
    rw [← eq]
    exact ((Devm.pop_of_pop h1).output.trans
      ((Devm.pop_of_pop h2).output.trans hmid)).trans
      (Devm.balReadAccount_output.symm)⟩

scoped instance {n} : Rinst.Hinv Devm.output (Rinst.log n) := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨_, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨_, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨_, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases hmem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [hmem] at run₅
  injection run₅ with eq
  have hm : s₄.output = s₅.output := by
    simp only [Devm.memRead] at hmem
    rcases hread : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [hread] at hmem
    injection hmem with _ hdevm
    rw [← hdevm]
    rfl
  rw [← eq]
  exact ((((p1.output.trans p2.output).trans p3.output).trans hb.output).trans hm)⟩

scoped instance : Linst.Hinv Devm.logs Devm.logs Linst.stop := by
  constructor
  intro e s r h
  injection h with h_eq
  subst h_eq
  rfl

/-- `RETURN` changes output but leaves the accumulated event log untouched. -/
scoped instance returnLogs : Linst.Hinv Devm.logs Devm.logs Linst.return_ := by
  constructor
  intro e s r h
  simp only [Linst.Run, Linst.run] at h
  rcases Except.bind_eq_ok h with ⟨⟨index, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨size, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  rcases Devm.pop_of_popToNat h1 with ⟨_, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨_, p2⟩
  have hb := Devm.burn_of_chargeGas h3
  rcases hmem : Devm.memRead s₃ index size with ⟨output, s₄⟩
  rw [hmem] at run₃
  injection run₃ with eq
  have hm : s₃.logs = s₄.logs := by
    simp only [Devm.memRead] at hmem
    rcases hread : s₃.memory.read index size with ⟨val, mem⟩
    rw [hread] at hmem
    injection hmem with _ hdevm
    rw [← hdevm]
    rfl
  rw [← eq]
  exact (((p1.logs.trans p2.logs).trans hb.logs).trans hm)

scoped instance : Linst.Hinv Devm.output Devm.output Linst.stop := by
  constructor
  intro e s r h
  injection h with h_eq
  subst h_eq
  rfl

end LogOutputHinv


/-! ### Dispatch reachability

The converse direction of `dispatchWith_inv`.  That lemma transfers a property
through the dispatcher precisely by never knowing which leaf ran; the theorems
here say which leaf runs, and sortedness — consumed for the first time in the
repository — is what supplies the selector→leaf link `dispatchWith_inv`'s
freely-quantified comparisons are deliberately blind to.

**Everything is hypothesis-position.**  A dispatcher run already in hand is
factored through the selector's entry; nothing here asserts that any run
exists, and no consumer may read `reach_of_dispatchWith` as "the selector is
present, therefore its function will be called" — that is a liveness claim and
is not available in this semantics.

The proofs reason from the abstract `sorted` hypothesis and never force a
signature word, so a concrete contract's `String.keccak` selectors stay
unevaluated; at instantiation, sortedness is supplied by the contract's
`decide +kernel` fact (`wethFuncs_sorted`, `fmintFuncs_sorted`). -/

/-! ## Nonpayable entry seam

`nonpayable` lives in `Blanc/CommonCore.lean` and is applied per endpoint by
more than one contract, so the lemmas that peel a successful run through it
live here rather than in any contract's module. -/

/-- A successful run through the nonpayable wrapper factors through the
endpoint body at a world-state- and memory-equivalent machine state, and only
with zero callvalue. The memory equation lets functional observations cross
the wrapper without assuming a pristine scratch area. -/
theorem run_body_of_run_nonpayable_frame
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      s.memory = mid.memory ∧ Func.Run fs sevm mid body r := by
  unfold nonpayable at run
  refine run_prepend_elim _ [callvalue, iszero] ?_ run
  intro s1 hline hbranch
  rcases Line.of_run_cons hline with ⟨s0, hcv, hline'⟩
  rcases Line.of_run_cons hline' with ⟨s1', hiz, hnil⟩
  cases hnil
  have hpv : [sevm.value] <<+ s0.stack :=
    prefix_of_push (of_run_callvalue hcv) nil_pref
  have hpflag : [sevm.value =? 0] <<+ s1.stack :=
    prefix_of_iszero hiz hpv
  rcases of_run_branch hbranch with
    ⟨s2, hpop, hrev⟩ | ⟨w, s2, s3, hnz, hpop, hburn, hbody⟩
  · exact absurd hrev not_run_revert
  · have hpop' := hpop.stack
    simp only [Stack.Pop, Split, List.nil_append, List.cons_append] at hpop'
    rw [hpop'] at hpflag
    have hw : (sevm.value =? 0) = w :=
      pref_head_unique hpflag (pref_append [w] s2.stack)
    have hflag : (sevm.value =? 0) ≠ 0 := by
      rw [hw]
      exact hnz
    have hv : sevm.value = 0 := by
      by_cases hv : sevm.value = 0
      · exact hv
      · simp only [B256.eqCheck, hv, ↓reduceIte, ne_eq, not_true_eq_false] at hflag
    refine ⟨s3, hv, ?_, ?_, hbody⟩
    · exact (Line.of_inv Devm.state (by line_inv) hline).trans
        (hpop.state.trans hburn.state)
    · exact (Line.of_inv Devm.memory (by line_inv) hline).trans
        (hpop.memory.trans hburn.memory)

/-- Compatibility projection of `run_body_of_run_nonpayable_frame` retaining
the original state-level API used by backing proofs. -/
theorem run_body_of_run_nonpayable
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    ∃ mid, sevm.value = 0 ∧ s.state = mid.state ∧
      Func.Run fs sevm mid body r := by
  rcases run_body_of_run_nonpayable_frame run with
    ⟨mid, hv, hstate, _, hbody⟩
  exact ⟨mid, hv, hstate, hbody⟩

/-- A successful run through the shared nonpayable wrapper can only take the
endpoint arm, so the frame value is zero. -/
theorem value_eq_zero_of_run_nonpayable
    {fs : List Func} {sevm : Sevm} {s r : Devm} {body : Func}
    (run : Func.Run fs sevm s (nonpayable body) r) :
    sevm.value = 0 :=
  (run_body_of_run_nonpayable run).choose_spec.1

/-- Identify a popped word from a stack-prefix fact: popping from a stack whose
top is known pops exactly that word, and the prefix below it survives. -/
lemma popBurn_pref {w v : B256} {vs : Stack} {s s' : Devm}
    (h : Devm.PopBurn [w] s s') (h_pfx : v :: vs <<+ s.stack) :
    w = v ∧ (vs <<+ s'.stack) := by
  have h_stk := h.stack
  simp only [Stack.Pop, Split, List.cons_append, List.nil_append] at h_stk
  rcases h_pfx with ⟨t, h_t⟩
  rw [h_stk] at h_t
  simp only [Split, List.cons_append] at h_t
  injection h_t with h_head h_tail
  exact ⟨h_head, ⟨t, h_tail⟩⟩

end Blanc
