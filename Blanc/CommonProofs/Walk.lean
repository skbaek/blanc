-- CommonProofs/Walk.lean : stack-prefix walk lemmas and value-carrying instruction companions.

import Blanc.CommonProofs.Frames
import Blanc.CommonProofs.MemImage

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

syntax "show_prefix_zero" : tactic
macro_rules
  | `(tactic| show_prefix_zero) =>
    `(tactic| intros h0 h1; apply append_pref h0.stack h1)

syntax "show_prefix_one" : tactic
macro_rules
  | `(tactic| show_prefix_one) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases List.of_cons_pref_of_cons_pref h1 (pref_of_split h2) with ⟨hx, h⟩;
              cases hx; clear h; apply append_pref h3 (of_append_pref h2 h1) )

syntax "show_prefix_two" : tactic
macro_rules
  | `(tactic| show_prefix_two) =>
    `(tactic| intros h0 h1; rcases h0 with ⟨x', y', h0⟩;
              rcases h0.stack with ⟨stk, h2, h3⟩; clear h0;
              rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩;
              cases hx; cases hy; clear h; apply append_pref h3 (of_append_pref h2 h1) )


infix:70 " <? "  => B256.ltCheck
infix:70 " >? "  => B256.gtCheck
infix:70 " ±<? " => B256.sltCheck
infix:70 " ±>? " => B256.sgtCheck
infix:70 " =? "  => B256.eqCheck

lemma Bytes.sig_zero_cons (xs) : Bytes.sig (0 :: xs) = Bytes.sig xs := rfl
lemma Bytes.sig_nonzero_cons (x xs) (h : x ≠ 0) : Bytes.sig (x :: xs) = x :: xs := by
  simp only [Jaune.Bytes.sig]; rw [List.dropWhile_cons_of_neg]; simp only [h, decide_false,
    Bool.false_eq_true, not_false_eq_true]

lemma Bytes.toB256_sig (bs : Bytes) : Bytes.toB256 (Bytes.sig bs) = bs.toB256 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases h : b = 0
    · cases h; rw [sig_zero_cons, ih, Bytes.toB256_zero_cons]
    · rw [sig_nonzero_cons b bs h]

def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop :=
  ∃ s' : Stack, Stack.Pop xs s s' ∧ Stack.Push zs s' s''

def Stack.SwapCore (x y : B256) : Nat → Stack → Stack → Prop
  | 0, y' :: xs, x' :: xs' => x = x' ∧ y = y' ∧ xs = xs'
  | n + 1, z :: xs, z' :: xs' => z = z' ∧ SwapCore x y n xs xs'
  | _, _, _ => False

def Stack.Swap (n : Nat) : Stack → Stack → Prop
  | x :: xs, y :: xs' => SwapCore x y n xs xs'
  | _, _ => False

def Devm.Push (xs : List B256) : Devm → Devm → Prop :=
  Devm.Rel {Devm.Rels.eq with stack := Stack.Push xs}

def Devm.DiffBurn (xs ys : List B256) : Devm → Devm → Prop :=
  Devm.Rel {Devm.Rels.eq with stack := Stack.Diff xs ys, gasLeft := (· ≥ ·)}

lemma Devm.push_of_push {x : B256} {s s' : Devm} (h : Devm.push x s = .ok s') :
    Devm.Push [x] s s' := by
  rw [Devm.push_def] at h
  simp only [Except.assert, bind, Except.bind] at h
  split at h
  · cases h
  · injection h with eq; subst eq
    constructor <;>
      simp only [Stack.Push, Split, Devm.setMach, cons_append, nil_append, Devm.Rels.eq]
    all_goals rfl

lemma Devm.pushBurn_of_burn_of_push {xs : List B256} {s s' s'' : Devm}
    (burn : Devm.Burn s s') (push : Devm.Push xs s' s'') :
    Devm.PushBurn xs s s'' := by
  constructor
  · exact burn.stack ▸ push.stack
  · exact Eq.trans burn.memory push.memory
  · rw [← push.gasLeft]; exact burn.gasLeft
  · exact Eq.trans burn.logs push.logs
  · exact Eq.trans burn.refundCounter push.refundCounter
  · exact Eq.trans burn.output push.output
  · exact Eq.trans burn.accountsToDelete push.accountsToDelete
  · exact Eq.trans burn.returnData push.returnData
  · exact Eq.trans burn.error push.error
  · exact Eq.trans burn.accessedAddresses push.accessedAddresses
  · exact Eq.trans burn.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans burn.state push.state
  · exact Eq.trans burn.createdAccounts push.createdAccounts
  · exact Eq.trans burn.transientStorage push.transientStorage
  · exact Eq.trans burn.stateGas push.stateGas
  · exact Eq.trans burn.accountReads push.accountReads
  · exact Eq.trans burn.storageReads push.storageReads
  · exact Eq.trans burn.storageWrites push.storageWrites
  · exact Eq.trans burn.touchedAccounts push.touchedAccounts

lemma Devm.diffBurn_of_pop_of_pushBurn {xs ys : List B256} {s s' s'' : Devm}
    (pop : Devm.Pop xs s s') (push : Devm.PushBurn ys s' s'') :
    Devm.DiffBurn xs ys s s'' := by
  constructor
  · exact ⟨s'.stack, pop.stack, push.stack⟩
  · exact Eq.trans pop.memory push.memory
  · rw [pop.gasLeft]; exact push.gasLeft
  · exact Eq.trans pop.logs push.logs
  · exact Eq.trans pop.refundCounter push.refundCounter
  · exact Eq.trans pop.output push.output
  · exact Eq.trans pop.accountsToDelete push.accountsToDelete
  · exact Eq.trans pop.returnData push.returnData
  · exact Eq.trans pop.error push.error
  · exact Eq.trans pop.accessedAddresses push.accessedAddresses
  · exact Eq.trans pop.accessedStorageKeys push.accessedStorageKeys
  · exact Eq.trans pop.state push.state
  · exact Eq.trans pop.createdAccounts push.createdAccounts
  · exact Eq.trans pop.transientStorage push.transientStorage
  · exact Eq.trans pop.stateGas push.stateGas
  · exact Eq.trans pop.accountReads push.accountReads
  · exact Eq.trans pop.storageReads push.storageReads
  · exact Eq.trans pop.storageWrites push.storageWrites
  · exact Eq.trans pop.touchedAccounts push.touchedAccounts

lemma Devm.pushBurn_of_pushItem {v : B256} {cost : Nat} {s s' : Devm}
    (h : pushItem v cost s = .ok s') : Devm.PushBurn [v] s s' := by
  rw [pushItem_def] at h; exact Devm.pushBurn_of_run h

lemma Devm.diffBurn_of_applyUnary {f : B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyUnary f cost s = .ok s') :
    ∃ x, Devm.DiffBurn [x] [f x] s s' := by
  rw [applyUnary_def] at h
  rcases Except.bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h2⟩
  simp only at h2
  rw [pushItem_def] at h2
  refine ⟨x, Devm.diffBurn_of_pop_of_pushBurn (Devm.pop_of_pop h1) (Devm.pushBurn_of_run h2)⟩

lemma Devm.diffBurn_of_applyBinary {f : B256 → B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyBinary f cost s = .ok s') :
    ∃ x y, Devm.DiffBurn [x, y] [f x y] s s' := by
  rw [applyBinary_def] at h
  rcases Except.bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h'⟩
  rcases Except.bind_eq_ok h' with ⟨⟨y, s₂⟩, h2, h3⟩
  simp only at h3
  rw [pushItem_def] at h3
  refine ⟨x, y, Devm.diffBurn_of_pop_of_pushBurn
    (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2))
    (Devm.pushBurn_of_run h3)⟩

lemma Devm.pop_of_popToNat {k : Nat} {devm devm' : Devm}
    (h : Devm.popToNat devm = .ok ⟨k, devm'⟩) :
    ∃ x, Devm.Pop [x] devm devm' := by
  rw [Devm.popToNat_def] at h
  dsimp only [Functor.mapRev, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩ <;> simp only [hp, reduceCtorEq, Except.ok.injEq] at h
  rcases h with ⟨_, rfl⟩
  exact ⟨x, Devm.pop_of_pop hp⟩

/-- `popToNat` pops a word and reports *that word's* `toNat`.

A third instance of the same projection `of_run_calldataload_val` restores:
`Devm.pop_of_popToNat` above proves `∃ x, Devm.Pop [x] devm devm'` and drops the
only interesting fact, namely that the `Nat` handed to the rest of the
instruction is `x.toNat`. Every memory-address and size operand in the machine
arrives through this function, so the value-carrying form is a prerequisite for
saying anything about *where* an instruction wrote or *how much*. -/
lemma Devm.pop_of_popToNat_val {k : Nat} {devm devm' : Devm}
    (h : Devm.popToNat devm = .ok ⟨k, devm'⟩) :
    ∃ x, Devm.Pop [x] devm devm' ∧ k = x.toNat := by
  rw [Devm.popToNat_def] at h
  dsimp only [Functor.mapRev, Functor.map, Except.map] at h
  rcases hp : devm.pop with _ | ⟨x, devm1⟩ <;> simp only [hp, reduceCtorEq, Except.ok.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  exact ⟨x, Devm.pop_of_pop hp, rfl⟩

lemma of_run_reg {e : Sevm} {s s' : Devm} {r : Rinst}
    (h : Ninst.Run e s (Ninst.reg r) s') :
    ∃ pc, Rinst.run ⟨pc, e, s⟩ r = .ok s' := by
  rcases h with ⟨xl, _, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_reg, Step.run_ofExecution] at run
  exact ⟨pc, run.2.symm⟩

/-- The atomic static fact: `SSTORE` clears `assertDynamic` before it commits,
so a successful storage write witnesses a dynamic context. -/
theorem of_run_sstore_not_static {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s sstore s') : e.isStatic = false := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : e.benvStat.rules.stateGas
  · -- Legacy gas lane: assertDynamic at the end of either regime walk.
    simp only [hsg] at run
    split at run
    all_goals
      rcases Except.bind_eq_ok run with ⟨⟨_, _⟩, _, run₁⟩
      rcases Except.bind_eq_ok run₁ with ⟨⟨_, _⟩, _, run₂⟩
      rcases Except.bind_eq_ok run₂ with ⟨_, _, run₃⟩
      rcases Except.bind_eq_ok run₃ with ⟨⟨_, _⟩, _, run₄⟩
      rcases Except.bind_eq_ok run₄ with ⟨_, _, run₅⟩
      rcases Except.bind_eq_ok run₅ with ⟨_, _, run₆⟩
      rcases Except.bind_eq_ok run₆ with ⟨_, _, run₇⟩
      rcases Except.bind_eq_ok run₇ with ⟨_, hassert, _⟩
      unfold assertDynamic Except.assert at hassert
      split at hassert
      · rename_i hdynamic
        simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using hdynamic
      · exact absurd hassert (by simp only [reduceCtorEq, not_false_eq_true])
  · -- Amsterdam: assertDynamic first.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, hassert, _⟩
    unfold assertDynamic Except.assert at hassert
    split at hassert
    · rename_i hdynamic
      simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using hdynamic
    · exact absurd hassert (by simp only [reduceCtorEq, not_false_eq_true])

lemma of_run_push {e s s' xs p} (h : Ninst.Run e s (push xs p) s') :
    Devm.PushBurn [xs.toB256] s s' := by
  rcases h with ⟨xl, _, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_push] at run
  split at run
  · simp only [Step.run_ofExecution, reduceCtorEq, and_false] at run
  · simp only [Step.run_ofExecution] at run
    exact Devm.pushBurn_of_run run.2.symm

/-- A successful `push` run, as the executable equation the `Hinv` instance
proofs consume.  This is where the driver's step-outcome shape is unwound, once,
for every push-shaped instance. -/
lemma Ninst.run_push_eq {e : Sevm} {s s' : Devm} {xs : Bytes} {le : xs.length ≤ 32}
    (h : Ninst.Run e s (.push xs le) s') :
    (do let d ← chargeGas (if xs = [] then gBase else gVerylow) s
        d.push xs.toB256) = .ok s' := by
  rcases h with ⟨xl, -, pc, run⟩
  simp only [Ninst.StepRun, Ninst.step_push] at run
  split at run
  · simp only [Step.run_ofExecution, reduceCtorEq, and_false] at run
  · simp only [Step.run_ofExecution] at run
    exact run.2.symm


lemma of_run_pushB256 {e s s' x} (h : Ninst.Run e s (pushB256 x) s') :
    Devm.PushBurn [x] s s' := by
  have h' := of_run_push h
  rwa [Bytes.toB256_sig, B256.toB256_toBytes] at h'

lemma of_run_pop {e : Sevm} {s s' : Devm} (h : Ninst.Run e s pop s') :
    ∃ x, Devm.PopBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  simp only [Functor.mapRev, Functor.map, Except.map] at h1
  rcases hp : Devm.pop s with _ | ⟨x, s₂⟩ <;> simp only [hp, reduceCtorEq, Except.ok.injEq] at h1
  subst h1
  exact ⟨x, Devm.popBurn_of_pop_of_burn (Devm.pop_of_pop hp) (Devm.burn_of_chargeGas h2)⟩

lemma of_run_dup {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (dup n) s') :
    ∃ x, s.stack[n.val]? = some x ∧ Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i x hx
    refine ⟨x, ?_, Devm.pushBurn_of_burn_of_push hb (Devm.push_of_push h2)⟩
    rw [hb.stack]; exact hx

lemma of_run_swap {e : Sevm} {s s' : Devm} {n : Fin 16} (h : Ninst.Run e s (swap n) s') :
    Jaune.List.swap s.stack n.val = some s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · rename_i stk hstk
    injection h2 with eq; subst eq
    rw [hb.stack]; exact hstk

lemma of_run_caller {e : Sevm} {s s' : Devm} (h : Ninst.Run e s caller s') :
    Devm.PushBurn [e.caller.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_callvalue {e : Sevm} {s s' : Devm} (h : Ninst.Run e s callvalue s') :
    Devm.PushBurn [e.value] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- Value-carrying inversion for `CALLDATASIZE`. -/
lemma of_run_calldatasize {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s calldatasize s') :
    Devm.PushBurn [e.data.length.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- Value-carrying inversion for `CODESIZE`.  Constructor decoders compare the
complete creation-code image, not merely the compiled executable prefix. -/
lemma of_run_codesize {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s codesize s') :
    Devm.PushBurn [e.code.size.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

lemma of_run_mstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  refine ⟨x, v, ?_⟩
  have hp := (Devm.pop_append p1 p2).stack
  rw [← eq]
  rw [show (Devm.memWrite s₃ i v.toBytes).stack = s₃.stack from rfl, ← hb.stack]
  exact hp

lemma Devm.pop_of_popN {n : Nat} {devm devm' : Devm} {l : List B256}
    (hp : devm.popN n = Except.ok (l, devm')) :
    l.length = n ∧ Devm.Pop l devm devm' := by
  induction n generalizing devm l with
  | zero =>
    rw [Devm.popN_def] at hp
    injection hp with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    refine ⟨rfl, ?_⟩
    constructor <;> simp only [Stack.Pop, Split, nil_append, Devm.Rels.eq]
  | succ n ih =>
    rw [Devm.popN_def] at hp
    rcases Except.bind_eq_ok hp with ⟨⟨x, devm1⟩, hp1, hp2⟩
    rcases Except.bind_eq_ok hp2 with ⟨⟨xs, devm2⟩, hp3, hp4⟩
    injection hp4 with eq
    injection eq with eq1 eq2
    subst eq1; subst eq2
    rcases ih hp3 with ⟨h_len, h_pop⟩
    refine ⟨by simp only [length_cons, h_len], Devm.pop_append (Devm.pop_of_pop hp1) h_pop⟩

lemma of_run_sstore {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  cases hsg : e.benvStat.rules.stateGas
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
      have hp := (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2)).stack
      have hb := Devm.burn_of_chargeGas h7
      have h_s₃ : s₃.stack = s₂.stack := by
        injection h4 with eq
        repeat' split at eq
        all_goals injection eq with eq _; subst eq; rfl
      have h_s₄ : s₄.stack = s₃.stack := by
        injection h6 with eq; rw [← eq]
        rfl
      injection h9 with eq
      refine ⟨x, y, ?_⟩
      rw [← eq]
      show Stack.Pop [x, y] s.stack s₅.stack
      rw [← hb.stack, h_s₄, h_s₃]
      exact hp
  · -- Amsterdam: static check first, state-gas second dimension.
    simp only [hsg] at run
    rcases Except.bind_eq_ok run with ⟨_, h0, run₁⟩
    rcases Except.bind_eq_ok run₁ with ⟨⟨x, s₁⟩, h1, run₂⟩
    rcases Except.bind_eq_ok run₂ with ⟨⟨y, s₂⟩, h2, run₃⟩
    rcases Except.bind_eq_ok run₃ with ⟨_, h3, run₄⟩
    rcases Except.bind_eq_ok run₄ with ⟨s₃, hchg, run₅⟩
    rcases Except.bind_eq_ok run₅ with ⟨s₄, hstg, h9⟩
    have hp := (Devm.pop_append (Devm.pop_of_pop h1) (Devm.pop_of_pop h2)).stack
    have hstg_st : s₃.stack = s₄.stack := (Devm.chargeStateGas_stack hstg).symm
    have hmid : s₂.stack = s₄.stack := by
      have e1 := (Devm.burn_of_chargeGas hchg).stack
      have e2 := hstg_st
      rw [← e2, ← e1]
      simp only [Devm.creditStateGasRefund, Mach.creditStateGasRefund,
        Devm.withRefundCounter, Devm.balReadStorage, Devm.setMach_stack]
      try split <;> (try split) <;> rfl
    injection h9 with eq
    refine ⟨x, y, ?_⟩
    rw [← eq]
    show Stack.Pop [x, y] s.stack s₄.stack
    rw [← hmid]
    exact hp

/-- `calldatacopy` writes *the calldata slice named by its operands* into memory.

The value-carrying form, and the piece (1b) of the arc needs: the bytes written
are `e.data.sliceD y.toNat z.toNat 0`, a function of `e.data` and the popped
operands alone. `d` is the state the instruction reaches after popping its three
operands and charging, so the equation says the whole effect on `d` is this one
write.

Two things this deliberately does *not* say, because Blanc has no vocabulary for
either yet (see the module note at `Sevm.dataWord`): that `d`'s memory agrees
with `s`'s, and what a subsequent `mload` of the written range yields. Both need
a `Mem.read`/`Mem.write` algebra that neither repository has. -/
lemma of_run_calldatacopy_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z d, Stack.Pop [x, y, z] s.stack (Devm.stack d) ∧
      s' = Devm.memWrite d x.toNat (e.data.sliceD y.toNat z.toNat 0) := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  refine ⟨x, y, z, s₄, ?_, eq.symm⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← hb.stack]
  exact hp

lemma of_run_calldatacopy {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack := by
  rcases of_run_calldatacopy_val h with ⟨x, y, z, d, hp, rfl⟩
  exact ⟨x, y, z, by rw [Devm.memWrite_stack]; exact hp⟩

lemma of_run_singleton {e s i s'} (h : Line.Run e s [i] s') : Ninst.Run e s i s' := by
  rcases Line.of_run_cons h with ⟨_, hrun, hnil⟩
  cases hnil; exact hrun

/-- `calldataload` pops an offset and pushes *the calldata word at it*.

The value-carrying form, and the point at which Blanc stops discarding what the
calldata says. `Rinst.runCore .calldataload` pushes
`Bytes.toB256 (e.data.sliceD start.toNat 32 0)`, which is `Sevm.dataWord e x` by
definition; the value-forgetting `of_run_calldataload` below is now literally
this statement with the pushed word quantified away, which is all a safety
invariant ever needed and all any existing consumer asks for.

Because `Sevm.dataWord` zero-pads (`List.sliceD`'s default), this holds for
calldata of every length — no well-formedness premise appears or is available. -/
lemma of_run_calldataload_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldataload s') :
    ∃ x, Stack.Diff [x] [Sevm.dataWord e x] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  have hpop := Devm.pop_of_pop h1
  have hb := Devm.burn_of_chargeGas h2
  have hpush : Devm.Push [Sevm.dataWord e si] s₂ s' := Devm.push_of_push run₂
  refine ⟨si, s₁.stack, hpop.stack, ?_⟩
  rw [show s₁.stack = s₂.stack from hb.stack]
  exact hpush.stack

/-- The value-forgetting form. Statement unchanged; its ~75 consumers across
`Solvent.lean` and `Conserved.lean` see exactly what they always did, and the
pop/charge/push destructuring is now done once, in the strong form above. -/
lemma of_run_calldataload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s calldataload s') :
    ∃ x y, Stack.Diff [x] [y] s.stack s'.stack := by
  rcases of_run_calldataload_val h with ⟨x, hd⟩
  exact ⟨x, _, hd⟩

lemma Devm.memRead_stack (devm : Devm) (i n : Nat) :
    (devm.memRead i n).2.stack = devm.stack := rfl

lemma of_run_keccak256 {e : Sevm} {s s' : Devm} (h : Ninst.Run e s keccak256 s') :
    ∃ x y z, Stack.Diff [x, y] [z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨s₃, h3, run₃⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  have hb := Devm.burn_of_chargeGas h3
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] (s₃.memRead mi sz).2 s' :=
    ⟨_, Devm.push_of_push run₃⟩
  refine ⟨x, y, val, s₂.stack, (Devm.pop_append p1 p2).stack, ?_⟩
  rw [show s₂.stack = s₃.stack from hb.stack, ← Devm.memRead_stack s₃ mi sz]
  exact hpush.stack

lemma of_run_log {e : Sevm} {s s' : Devm} {n : Fin 5} (h : Ninst.Run e s (log n) s') :
    ∃ zs, zs.length = n.val + 2 ∧ Stack.Pop zs s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨h_len, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases h_mem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_s₅ : s₅.stack = s₄.stack := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]; rfl
  refine ⟨x :: y :: topics, by simp only [length_cons, h_len], ?_⟩
  have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
  rw [← eq]
  show Stack.Pop (x :: y :: topics) s.stack s₅.stack
  rw [h_s₅, ← hb.stack]
  exact hp

lemma of_run_address {e : Sevm} {s s' : Devm} (h : Ninst.Run e s address s') :
    Devm.PushBurn [e.currentTarget.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- `SELFBALANCE` pushes the target balance, on the stack, on every fork
(including one whose rules record the account read).  Consumers route
through `prefix_of_push_stack`. -/
lemma of_run_selfbalance_stack {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s selfbalance s') :
    Stack.Push [s.getBal e.currentTarget] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  split at run
  ·
    rcases Except.bind_eq_ok run with ⟨d1, hgas, hpush⟩
    have hp := (Devm.push_of_push hpush).stack
    rw [Devm.balReadAccount_stack] at hp
    rw [← (Devm.burn_of_chargeGas hgas).stack] at hp
    have hval : d1.getBal e.currentTarget = s.getBal e.currentTarget :=
      chargeGas_getBal_eq hgas _
    rw [hval] at hp
    exact hp
  · cases run

lemma of_run_returndatasize {e : Sevm} {s s' : Devm} (h : Ninst.Run e s returndatasize s') :
    ∃ x, Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact ⟨_, Devm.pushBurn_of_pushItem run⟩

lemma of_run_gas {e : Sevm} {s s' : Devm} (h : Ninst.Run e s gas s') :
    ∃ x, Devm.PushBurn [x] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  exact ⟨_, Devm.pushBurn_of_burn_of_push (Devm.burn_of_chargeGas h1) (Devm.push_of_push h2)⟩

lemma of_run_mload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mload s') :
    ∃ x y, Stack.Diff [x] [y] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, hpop⟩
  have hb := Devm.burn_of_chargeGas h2
  obtain ⟨val, hpush⟩ : ∃ val, Devm.Push [val] (s₂.memRead si 32).2 s' :=
    ⟨_, Devm.push_of_push run₂⟩
  refine ⟨x, val, s₁.stack, hpop.stack, ?_⟩
  rw [show s₁.stack = s₂.stack from hb.stack, ← Devm.memRead_stack s₂ si 32]
  exact hpush.stack

lemma of_run_returndatacopy {e : Sevm} {s s' : Devm} (h : Ninst.Run e s returndatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popToNat h3 with ⟨z, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  refine ⟨x, y, z, ?_⟩
  split at h5
  · cases h5
  · injection h5 with eq
    have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq]
    show Stack.Pop [x, y, z] s.stack s₄.stack
    rw [← hb.stack]
    exact hp

/-- On the successful path the CALL-family return pushes the status flag onto
the parent's stack; incorporating the child and the memory write leave the
stack alone.  The stack-side companion of `Resume.call_state`, needed by a
caller that continues executing after the call returns.  It lives here, below
`Devm.push_of_push`, rather than beside its `state` sibling. -/
lemma Resume.call_stack {parent child : Devm} {oi os : Nat} {sf : Devm}
    (h : (Resume.call parent oi os).run (.ok child) = .ok sf) :
    ∃ b, sf.stack = b :: parent.stack := by
  have key : ∀ d : Devm, d.stack = parent.stack → ∀ v : B256,
      (Devm.push v d >>= fun d' =>
        (.ok (d'.memWrite oi (child.output.take os)) : Execution)) = .ok sf →
      ∃ b, sf.stack = b :: parent.stack := by
    intro d hd v hh
    rcases hp : Devm.push v d with e | evm2 <;> rw [hp] at hh
    · cases hh
    · injection hh with hh
      subst hh
      refine ⟨v, ?_⟩
      have h_push := (Devm.push_of_push hp).stack
      show evm2.stack = _
      rw [h_push, hd]
      rfl
  unfold Resume.run liftToExecution at h
  dsimp only [bind, Except.bind] at h
  split at h
  · exact key (incorporateChildOnError parent child child.output) rfl 0 h
  · exact key (incorporateChildOnSuccess parent child child.output) rfl 1 h

lemma Stack.swapCore_of_swap {n} {xxs yys : Stack} (h : Swap n xxs yys) :
    ∃ x y xs ys, xxs = x :: xs ∧ yys = y :: ys ∧ SwapCore x y n xs ys := by
  cases xxs; cases h; cases yys; cases h; refine ⟨_, _, _, _, rfl, rfl, h⟩

lemma Stack.swapCore_zero {x y s} : SwapCore x y 0 (y :: s) (x :: s) := by simp only [SwapCore,
  and_self]

lemma Stack.swapCore_succ {n x y z s s'} :
    SwapCore x z n s s' → SwapCore x z (n + 1) (y :: s) (y :: s') := by simp only [SwapCore,
      true_and, imp_self]

lemma Stack.swapCore_getElem_set {x y : B256} {n : Nat} {xs xs' : Stack}
    (h : SwapCore x y n xs xs') (t : Stack) :
    (xs ++ t)[n]? = some y ∧ (xs ++ t).set n x = xs' ++ t := by
  induction n generalizing xs xs' with
  | zero =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hx, hy, hl⟩
    subst hx; subst hy; subst hl
    constructor <;> rfl
  | succ n ih =>
    cases xs; cases h; cases xs'; cases h
    rcases h with ⟨hz, h⟩
    subst hz
    rcases ih h with ⟨h1, h2⟩
    constructor
    · simpa only [cons_append, getElem?_cons_succ] using h1
    · simp only [List.cons_append, List.set_cons_succ]
      rw [h2]

lemma Stack.prefix_of_swap {n} {xs xs' stk stk' : Stack} :
    Swap n xs xs' → Jaune.List.swap stk n = some stk' → (xs <<+ stk) → (xs' <<+ stk') := by
  intro h0 h1 h2
  rcases swapCore_of_swap h0 with ⟨x, y, xs₀, ys₀, hxs, hys, hc⟩
  subst hxs; subst hys
  rcases h2 with ⟨t, h2⟩
  rw [show stk = (x :: xs₀) ++ t from h2] at h1
  rcases swapCore_getElem_set hc t with ⟨hget, hset⟩
  simp only [List.cons_append, Jaune.List.swap, hget, hset] at h1
  injection h1 with h1
  refine ⟨t, ?_⟩
  rw [← h1]
  rfl

lemma Stack.nth_getElem {n : Nat} {x : B256} {xs ys : Stack}
    (h : Nth n x xs) (h' : xs <<+ ys) : ys[n]? = some x := by
  revert h'
  induction h generalizing ys with
  | head z zs =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (z :: zs) ++ t from h']; rfl
  | tail m z w zs h ih =>
    intro h'
    rcases h' with ⟨t, h'⟩
    rw [show ys = (w :: zs) ++ t from h']
    simp only [List.cons_append, List.getElem?_cons_succ]
    exact ih ⟨t, rfl⟩

lemma prefix_of_diffBurn_one (v : B256 → B256) {x xs} {s s' : Devm} :
    (∃ x', Devm.DiffBurn [x'] [v x'] s s') →
    (x :: xs <<+ s.stack) → (v x :: xs <<+ s'.stack) := by show_prefix_one

lemma prefix_of_diffBurn_two (v : B256 → B256 → B256) {x y xs} {s s' : Devm} :
    (∃ x' y', Devm.DiffBurn [x', y'] [v x' y'] s s') →
    (x :: y :: xs <<+ s.stack) → (v x y :: xs <<+ s'.stack) := by show_prefix_two

lemma prefix_of_not {e} {x xs} {s s' : Devm} :
    Ninst.Run e s not s' → (x :: xs <<+ s.stack) → ((~~~ x) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (~~~ ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_iszero {e} {x xs} {s s' : Devm} :
    Ninst.Run e s iszero s' → (x :: xs <<+ s.stack) → ((x =? 0) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_one (· =? 0) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyUnary run

lemma prefix_of_eq {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s eq s' → (x :: y :: xs <<+ s.stack) → ((x =? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.eqCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_lt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s lt s' → (x :: y :: xs <<+ s.stack) → ((x <? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.ltCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_gt {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s gt s' → (x :: y :: xs <<+ s.stack) → ((x >? y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.gtCheck ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_shl {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shl s' → (x :: y :: xs <<+ s.stack) → (y <<< x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y <<< x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  split at run
  · exact Devm.diffBurn_of_applyBinary run
  · cases run

lemma prefix_of_shr {e} {x y : B256} {xs} {s s' : Devm} :
    Ninst.Run e s shr s' → (x :: y :: xs <<+ s.stack) → (y >>> x.toNat :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (fun x y => y >>> x.toNat) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  split at run
  · exact Devm.diffBurn_of_applyBinary run
  · cases run

lemma prefix_of_or {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s or s' → (x :: y :: xs <<+ s.stack) → ((x ||| y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.or ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

/-- Bitwise conjunction on EVM words is commutative. -/
theorem B256.and_comm (x y : B256) : x &&& y = y &&& x := by
  rcases x with ⟨⟨xh0, xh1⟩, ⟨xl0, xl1⟩⟩
  rcases y with ⟨⟨yh0, yh1⟩, ⟨yl0, yl1⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.and_comm _ _

/-- Bitwise exclusive-or on EVM words is commutative. -/
theorem B256.xor_comm (x y : B256) : x ^^^ y = y ^^^ x := by
  rcases x with ⟨⟨xh0, xh1⟩, ⟨xl0, xl1⟩⟩
  rcases y with ⟨⟨yh0, yh1⟩, ⟨yl0, yl1⟩⟩
  apply Prod.ext <;> apply Prod.ext <;> exact UInt64.xor_comm _ _

/-- Reapplying the same bitwise mask does not change an EVM word. -/
theorem B256.and_idem_right (x mask : B256) :
    (x &&& mask) &&& mask = x &&& mask := by
  rcases x with ⟨xh, xl⟩
  rcases mask with ⟨mh, ml⟩
  change ⟨(xh &&& mh) &&& mh, (xl &&& ml) &&& ml⟩ =
    (⟨xh &&& mh, xl &&& ml⟩ : B256)
  apply Prod.ext
  · rcases xh with ⟨xh0, xh1⟩
    rcases mh with ⟨mh0, mh1⟩
    change ⟨(xh0 &&& mh0) &&& mh0, (xh1 &&& mh1) &&& mh1⟩ =
      (⟨xh0 &&& mh0, xh1 &&& mh1⟩ : B128)
    apply Prod.ext
    · change (xh0 &&& mh0) &&& mh0 = xh0 &&& mh0
      rw [UInt64.and_assoc, UInt64.and_self]
    · change (xh1 &&& mh1) &&& mh1 = xh1 &&& mh1
      rw [UInt64.and_assoc, UInt64.and_self]
  · rcases xl with ⟨xl0, xl1⟩
    rcases ml with ⟨ml0, ml1⟩
    change ⟨(xl0 &&& ml0) &&& ml0, (xl1 &&& ml1) &&& ml1⟩ =
      (⟨xl0 &&& ml0, xl1 &&& ml1⟩ : B128)
    apply Prod.ext
    · change (xl0 &&& ml0) &&& ml0 = xl0 &&& ml0
      rw [UInt64.and_assoc, UInt64.and_self]
    · change (xl1 &&& ml1) &&& ml1 = xl1 &&& ml1
      rw [UInt64.and_assoc, UInt64.and_self]

/-- `XOR` replaces the two known stack heads by their exclusive-or. -/
lemma prefix_of_xor {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s xor s' → (x :: y :: xs <<+ s.stack) →
      ((x ^^^ y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.xor ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_and {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s and s' → (x :: y :: xs <<+ s.stack) → ((x &&& y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two B256.and ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_add {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s add s' → (x :: y :: xs <<+ s.stack) → ((x + y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· + ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_sub {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sub s' → (x :: y :: xs <<+ s.stack) → ((x - y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· - ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_mul {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mul s' → (x :: y :: xs <<+ s.stack) → ((x * y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· * ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_div {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s div s' → (x :: y :: xs <<+ s.stack) → ((x / y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· / ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_mod {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mod s' → (x :: y :: xs <<+ s.stack) → ((x % y) :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_two (· % ·) ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyBinary run

lemma prefix_of_push {xs ys} {s s' : Devm} :
    Devm.PushBurn xs s s' → (ys <<+ s.stack) → ((xs ++ ys) <<+ s'.stack) :=
  λ h0 h1 => append_pref h0.stack h1

/-- Stack-only variant of `prefix_of_push` for producers whose run records
reads (`SELFBALANCE`), where the full `PushBurn` relation is false. -/
lemma prefix_of_push_stack {xs ys} {s s' : Devm} :
    Stack.Push xs s.stack s'.stack → (ys <<+ s.stack) →
      ((xs ++ ys) <<+ s'.stack) :=
  λ h0 h1 => append_pref h0 h1

/-- `TIMESTAMP` pushes the current block time above any known stack prefix. -/
lemma prefix_of_timestamp {e : Sevm} {s s' : Devm} {xs : Stack}
    (hp : xs <<+ s.stack) (h : Ninst.Run e s timestamp s') :
    e.benvStat.time :: xs <<+ s'.stack := by
  change Ninst.Run e s (.reg .timestamp) s' at h
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact prefix_of_push (Devm.pushBurn_of_pushItem run) hp

/-- `DUP n` at a stack whose top `n + 1` words are already known: the word it
pushes is the one the walk knows sits at index `n`.

The value-carrying `DUP`.  Every existing walk re-derives this inline —
`of_run_dup`, then `Stack.nth_getElem` to pin the anonymous word, then
`prefix_of_push` — which is three steps and a `subst` per `DUP`, and `flashLoan`
alone has nine.  The `Stack.Nth` premise is discharged by `show_nth`. -/
lemma prefix_of_dup_val {e : Sevm} {s s' : Devm} {n : Fin 16} {x : B256} {xs : Stack}
    (h : Ninst.Run e s (dup n) s') (hnth : Stack.Nth n.val x xs) (hp : xs <<+ s.stack) :
    x :: xs <<+ s'.stack := by
  rcases of_run_dup h with ⟨y, hy, pb⟩
  rw [Stack.nth_getElem hnth hp] at hy
  injection hy with hy
  subst hy
  exact prefix_of_push pb hp

lemma prefix_of_pop {y : B256} {xs} {s s' : Devm} :
    (∃ x, Devm.PopBurn [x] s s') → (y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h h'; rcases h with ⟨x, hx⟩
  have h_eq : y = x :=
    (List.of_cons_pref_of_cons_pref h' (pref_of_split hx.stack)).left
  rw [h_eq] at h'
  exact of_append_pref hx.stack h'

lemma prefix_of_mstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s mstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_mstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_sstore {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s sstore s' → (x :: y :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_sstore h0 with ⟨x', y', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact of_append_pref h2 h1

lemma prefix_of_calldatacopy {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s calldatacopy s' → (x :: y :: z :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_calldatacopy h0 with ⟨x', y', z', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- Value-carrying `prefix_of_calldataload`: the word left on the stack is the
calldata word at the offset that was there before. Modelled on
`prefix_of_sload`, which already carries its value this way. -/
lemma prefix_of_calldataload_val {e} {x xs} {s s' : Devm} :
    Ninst.Run e s calldataload s' → (x :: xs <<+ s.stack) →
    (Sevm.dataWord e x :: xs <<+ s'.stack) := by
  intro h0 h1
  rcases of_run_calldataload_val h0 with ⟨x', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  exact append_pref h3 (of_append_pref h2 h1)

lemma prefix_of_calldataload {e} {x xs} {s s' : Devm} :
    Ninst.Run e s calldataload s' → (x :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack :=
  fun h0 h1 => ⟨_, prefix_of_calldataload_val h0 h1⟩

lemma prefix_of_keccak256 {e} {x y xs} {s s' : Devm} :
    Ninst.Run e s keccak256 s' → (x :: y :: xs <<+ s.stack) → ∃ z, z :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_keccak256 h0 with ⟨x', y', z', stk, h2, h3⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, h⟩
  clear h; rw [hx, hy] at h1
  exact ⟨z', append_pref h3 (of_append_pref h2 h1)⟩

/-- Value-carrying `prefix_of_cdl`: `cdl n` leaves the calldata word at byte
offset `n` on top of the stack. -/
lemma prefix_of_cdl_val {e n xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (cdl n) s' →
    (Sevm.dataWord e n :: xs <<+ s'.stack) := by
  intro h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s₁, h_push, h_rest⟩
  rcases Line.of_run_cons h_rest with ⟨s₂, h_cdl, h_nil⟩
  cases h_nil
  have h1 : n :: xs <<+ s₁.stack := prefix_of_push (of_run_pushB256 h_push) h_pfx
  exact prefix_of_calldataload_val h_cdl h1

lemma prefix_of_cdl {e n xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (cdl n) s' → ∃ z, z :: xs <<+ s'.stack :=
  fun h_pfx h_run => ⟨_, prefix_of_cdl_val h_pfx h_run⟩

/-- The `of_arg` the decoding layer reads through: running `arg k` leaves the
`k`-th head word of the argument area on the stack.

`arg k` is `cdl (32 * k + 4)` and `Sevm.argWord e k` is `Sevm.dataWord e
(32 * k + 4)`, both by definition, so this is `prefix_of_cdl_val` at a
definitional instance rather than a new argument. Head-word access, not ABI
decoding: for a dynamic argument the word delivered here is the tail's offset
(see `arg`'s note (1) and `forwardArgTail`). -/
lemma prefix_of_arg {e k xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s (arg k) s' →
    (Sevm.argWord e k :: xs <<+ s'.stack) :=
  prefix_of_cdl_val

/-- `EXTCODESIZE` at a known stack top, with the exact code-size word read
from the instruction's input state.  Address warming may change the state
metadata, but memory is untouched. -/
lemma prefix_of_extcodesize_val
    {e : Sevm} {s r : Devm} {x : B256} {xs : Stack}
    (hp : x :: xs <<+ s.stack)
    (run : Ninst.Run e s Ninst.extcodesize r) :
    ((s.getCode x.toAdr).size.toB256 :: xs <<+ r.stack) ∧
      s.memory = r.memory := by
  rcases of_run_reg run with ⟨pc, hrun⟩
  simp only [Rinst.run, Rinst.runCore] at hrun
  rcases Except.bind_eq_ok hrun with ⟨⟨adr, d1⟩, hpopAdr, hrun⟩
  rw [Devm.popToAdr_def] at hpopAdr
  dsimp only [Functor.mapRev, Functor.map, Except.map] at hpopAdr
  rcases hpop : Devm.pop s with _ | ⟨word, d0⟩ <;>
    simp only [hpop, reduceCtorEq, Except.ok.injEq] at hpopAdr
  rcases hpopAdr with ⟨rfl, rfl⟩
  have hpop' := Devm.pop_of_pop hpop
  have hx : x = word :=
    (List.of_cons_pref_of_cons_pref hp
      (pref_of_split hpop'.stack)).left
  subst word
  have htail : xs <<+ d0.stack := of_append_pref hpop'.stack hp
  cases haccess : e.benvStat.rules.access with
  | eip2929 =>
    simp only [haccess] at hrun
    split at hrun
    · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
      have hst : s.state = d2.state :=
        hpop'.state.trans (Devm.burn_of_chargeGas hgas).state
      have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
        unfold Devm.getCode Devm.getAcct
        rw [hst]
      refine ⟨?_, ?_⟩
      · rw [← hcode]
        exact append_pref (Devm.push_of_push hpush).stack
          (by rw [Devm.balReadAccount_stack, ← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
      · exact hpop'.memory.trans
          ((Devm.burn_of_chargeGas hgas).memory.trans
            (Devm.push_of_push hpush).memory)
    · rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
      have hst : s.state = d2.state :=
        hpop'.state.trans
          ((show d0.state = (addAccessedAddress d0 x.toAdr).state from rfl).trans
            (Devm.burn_of_chargeGas hgas).state)
      have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
        unfold Devm.getCode Devm.getAcct
        rw [hst]
      refine ⟨?_, ?_⟩
      · rw [← hcode]
        exact append_pref (Devm.push_of_push hpush).stack
          (by rw [Devm.balReadAccount_stack, ← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
      · exact hpop'.memory.trans
          ((show d0.memory = (addAccessedAddress d0 x.toAdr).memory from rfl).trans
            ((Devm.burn_of_chargeGas hgas).memory.trans
              (Devm.push_of_push hpush).memory))

  | flat gas =>
    simp only [haccess] at hrun
    rcases Except.bind_eq_ok hrun with ⟨d2, hgas, hpush⟩
    have hst : s.state = d2.state :=
      hpop'.state.trans (Devm.burn_of_chargeGas hgas).state
    have hcode : d2.getCode x.toAdr = s.getCode x.toAdr := by
      unfold Devm.getCode Devm.getAcct
      rw [hst]
    refine ⟨?_, ?_⟩
    · rw [← hcode]
      exact append_pref (Devm.push_of_push hpush).stack
        (by rw [Devm.balReadAccount_stack, ← (Devm.burn_of_chargeGas hgas).stack]; exact htail)
    · exact hpop'.memory.trans
        ((Devm.burn_of_chargeGas hgas).memory.trans
          (Devm.push_of_push hpush).memory)
/-! ### Reading a described calldata layout

The bridge between `Sevm.dataWord` — what the contract's `calldataload` actually
yields — and a calldata *described* as an explicit concatenation, which is how
`abiCallWithTail` states a canonical encoding. Without this the encoding
definition and the reader would be two unrelated pieces of syntax and the
decoding predicate would carry no information. -/

/-- The word at `idx` of a calldata that has `pre` before it and a whole word
`w` at it. Note `post` is unconstrained: nothing about the rest of the calldata
is needed, which is what lets the head words be read one at a time. -/
lemma dataWord_of_append {e : Sevm} {idx : B256} {pre post : Bytes} {w : B256}
    (hlen : idx.toNat = pre.length)
    (hdata : e.data = pre ++ (B256.toBytes w ++ post)) :
    Sevm.dataWord e idx = w := by
  simp only [Sevm.dataWord, hdata, List.sliceD]
  rw [List.drop_length_append' hlen,
      List.takeD_eq_take _ (by simp only [length_append, B256.length_toBytes,
        le_add_iff_nonneg_right, _root_.zero_le]),
      List.take_length_append' (B256.length_toBytes w).symm, B256.toB256_toBytes]

/-- `fsig` leaves the calldata's function selector on the stack.

The entry route's first fact, and the one Step 2 of the arc composes with
dispatch reachability: `dispatchWith` assumes the selector is already on top of
the stack, and until now nothing said *which* word that was. Note that
`prefix_of_shr` was already value-carrying — only the calldata inversions were
not, which is why this fact was previously unavailable. -/
lemma prefix_of_fsig {e xs} {s s' : Devm} :
    (xs <<+ s.stack) → Line.Run e s fsig s' → (Sevm.selector e :: xs <<+ s'.stack) := by
  intro h_pfx h_run
  rcases of_run_append (cdl 0) h_run with ⟨s₁, h_cdl, h_shr⟩
  have h1 : Sevm.dataWord e 0 :: xs <<+ s₁.stack := prefix_of_cdl_val h_pfx h_cdl
  rcases Line.of_run_cons h_shr with ⟨s₂, h_push, h_rest⟩
  rcases Line.of_run_cons h_rest with ⟨s₃, h_op, h_nil⟩
  cases h_nil
  exact prefix_of_shr h_op (prefix_of_push (of_run_pushB256 h_push) h1)

lemma abiSelectorBytes_length (sel : B256) : (abiSelectorBytes sel).length = 4 := by
  simp only [abiSelectorBytes, length_drop, B256.length_toBytes, reduceSub]

private lemma UInt64.high_concat32 (x y : UInt32) :
    ((((x.toUInt64 <<< 32) ||| y.toUInt64) >>> 32).toUInt32) = x := by
  rw [← UInt32.toNat_inj]
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo]
  have widen (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  rw [widen, widen, n32]
  have hx : x.toNat <<< 32 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have := UInt32.toNat_lt x
    norm_num only at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 32 (UInt32.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt32.toNat_lt x)]

private lemma UInt64.low_concat32 (x y : UInt32) :
    (((x.toUInt64 <<< 32) ||| y.toUInt64).toUInt32) = y := by
  rw [← UInt32.toNat_inj]
  rw [UInt64.toNat_toUInt32]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo]
  have widen (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  rw [widen, widen, n32]
  have hx : x.toNat <<< 32 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    have := UInt32.toNat_lt x
    norm_num only at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt32.toNat_lt y), Nat.zero_or]

private lemma UInt32.high_concat16 (x y : UInt16) :
    ((((x.toUInt32 <<< 16) ||| y.toUInt32) >>> 16).toUInt16) = x := by
  rw [← UInt16.toNat_inj]
  rw [UInt32.toNat_toUInt16, UInt32.toNat_shiftRight]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft_lo]
  have widen (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  have n16 : UInt32.toNat 16 % 32 = 16 := rfl
  rw [widen, widen, n16]
  have hx : x.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := UInt16.toNat_lt x
    norm_num only at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 16 (UInt16.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt16.toNat_lt x)]

private lemma UInt32.low_concat16 (x y : UInt16) :
    (((x.toUInt32 <<< 16) ||| y.toUInt32).toUInt16) = y := by
  rw [← UInt16.toNat_inj]
  rw [UInt32.toNat_toUInt16]
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft_lo]
  have widen (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  have n16 : UInt32.toNat 16 % 32 = 16 := rfl
  rw [widen, widen, n16]
  have hx : x.toNat <<< 16 < 2 ^ 32 := by
    rw [Nat.shiftLeft_eq]
    have := UInt16.toNat_lt x
    norm_num only at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt16.toNat_lt y), Nat.zero_or]

private lemma UInt16.high_concat8 (x y : UInt8) :
    ((((x.toUInt16 <<< 8) ||| y.toUInt16) >>> 8).toUInt8) = x := by
  rw [← UInt8.toNat_inj]
  rw [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight]
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft_lo]
  have widen (z : UInt8) : z.toUInt16.toNat = z.toNat := rfl
  have n8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [widen, widen, n8]
  have hx : x.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    have := UInt8.toNat_lt x
    norm_num only at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.shiftRight_or_distrib,
    Nat.shiftLeft_shiftRight,
    Nat.shiftRight_eq_zero y.toNat 8 (UInt8.toNat_lt y), Nat.or_zero,
    Nat.mod_eq_of_lt (UInt8.toNat_lt x)]

private lemma UInt16.low_concat8 (x y : UInt8) :
    (((x.toUInt16 <<< 8) ||| y.toUInt16).toUInt8) = y := by
  rw [← UInt8.toNat_inj]
  rw [UInt16.toNat_toUInt8]
  simp only [UInt16.toNat_or, UInt16.toNat_shiftLeft_lo]
  have widen (z : UInt8) : z.toUInt16.toNat = z.toNat := rfl
  have n8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [widen, widen, n8]
  have hx : x.toNat <<< 8 < 2 ^ 16 := by
    rw [Nat.shiftLeft_eq]
    have := UInt8.toNat_lt x
    norm_num only at this ⊢
    omega
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt hx, Nat.or_mod_two_pow]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mul_mod_right,
    Nat.mod_eq_of_lt (UInt8.toNat_lt y), Nat.zero_or]

/-- Encoding eight bytes as a limb and decoding it again is exact. -/
private lemma UInt64.toBytes_ofBytes (a b c d e f g h : UInt8) :
    (UInt64.ofBytes a b c d e f g h).toBytes = [a, b, c, d, e, f, g, h] := by
  rw [UInt64.ofBytes_eq_halves]
  simp only [UInt64.toBytes, UInt64.high_concat32, UInt64.low_concat32,
    UInt32.toBytes]
  rw [UInt32.ofBytes_eq_halves, UInt32.ofBytes_eq_halves]
  simp only [UInt32.high_concat16, UInt32.low_concat16, UInt16.toBytes,
    UInt16.ofBytes, UInt16.high_concat8, UInt16.low_concat8]
  simp only [cons_append, nil_append]

/-- The 32-byte codec is an exact round trip, in the concrete shape used by
`Bytes.toBytes_toB256_of_length`. -/
private lemma Bytes.toBytes_toB256_32
    (a00 a01 a02 a03 a04 a05 a06 a07
     a08 a09 a10 a11 a12 a13 a14 a15
     a16 a17 a18 a19 a20 a21 a22 a23
     a24 a25 a26 a27 a28 a29 a30 a31 : UInt8) :
    (Bytes.toB256
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15,
       a16, a17, a18, a19, a20, a21, a22, a23,
       a24, a25, a26, a27, a28, a29, a30, a31]).toBytes =
      [a00, a01, a02, a03, a04, a05, a06, a07,
       a08, a09, a10, a11, a12, a13, a14, a15,
       a16, a17, a18, a19, a20, a21, a22, a23,
       a24, a25, a26, a27, a28, a29, a30, a31] := by
  simp only [Bytes.toB256]
  rw [Bytes.toB256_go_eight_cons, Bytes.toB256_go_eight_cons,
      Bytes.toB256_go_eight_cons, Bytes.toB256_go_eight_cons]
  simp only [Bytes.toB256.go, B256.toBytes, B128.toBytes, List.append_assoc,
    UInt64.toBytes_ofBytes]
  simp only [cons_append, nil_append]

/-- `Bytes.toB256` loses no information on an exact word. -/
lemma Bytes.toBytes_toB256_of_length {xs : Bytes} (h : xs.length = 32) :
    (Bytes.toB256 xs).toBytes = xs := by
  rcases xs with _ | ⟨a00, xs⟩
  · simp only [length_nil, OfNat.zero_ne_ofNat] at h
  rcases xs with _ | ⟨a01, xs⟩
  · simp only [length_cons, length_nil, zero_add, OfNat.one_ne_ofNat] at h
  rcases xs with _ | ⟨a02, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a03, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a04, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a05, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a06, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a07, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a08, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a09, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a10, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a11, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a12, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a13, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a14, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a15, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a16, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a17, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a18, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a19, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a20, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a21, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a22, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a23, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a24, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a25, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a26, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a27, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a28, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a29, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a30, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  rcases xs with _ | ⟨a31, xs⟩
  · simp only [length_cons, length_nil, zero_add, reduceAdd, reduceEqDiff] at h
  cases xs with
  | nil =>
      simpa only using
        (Bytes.toBytes_toB256_32 a00 a01 a02 a03 a04 a05 a06 a07 a08 a09 a10 a11 a12 a13 a14 a15 a16
          a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31)
  | cons a32 xs => simp only [length_cons, reduceEqDiff] at h

private lemma Bytes.toB256_uint32_toBytes (x : UInt32) :
    Bytes.toB256 x.toBytes = x.toB256 := by
  have highZero : (x.toUInt64 >>> 32).toUInt32 = 0 := by
    rw [← UInt32.toNat_inj, UInt64.toNat_toUInt32,
      UInt64.toNat_shiftRight]
    change (x.toNat >>> 32) % 4294967296 = 0
    rw [Nat.shiftRight_eq_zero _ _ (UInt32.toNat_lt x)]
  have roundtrip := B256.toB256_toBytes
    (⟨⟨(0 : UInt64), 0⟩, ⟨0, x.toUInt64⟩⟩ : B256)
  change Bytes.toB256 x.toBytes =
    (⟨⟨(0 : UInt64), 0⟩, ⟨0, x.toUInt64⟩⟩ : B256)
  simpa only [UInt32.toBytes, UInt16.toBytes, UInt32.toUInt8_toUInt16, cons_append, nil_append,
    B256.toBytes, B128.toBytes, UInt64.toBytes, UInt64.zero_shiftRight, UInt64.toUInt32_ofNat,
    UInt32.zero_shiftRight, UInt32.toUInt16_ofNat, UInt16.zero_shiftRight, UInt16.toUInt8_ofNat,
    highZero, UInt32.toUInt32_toUInt64, Bytes.toB256_zero_cons] using roundtrip

/-- Shifting a word down by 224 bits is its first four big-endian bytes,
repacked as a `B256`. -/
lemma shiftRight_224_eq_toB256_take_four (x : B256) :
    x >>> 224 = Bytes.toB256 (x.toBytes.take 4) := by
  rcases x with ⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩
  have firstFour :
      (B256.toBytes (⟨⟨x3, x2⟩, ⟨x1, x0⟩⟩ : B256)).take 4 =
        (x3 >>> 32).toUInt32.toBytes := by
    simp only [B256.toBytes, B128.toBytes, UInt64.toBytes]
    simp only [List.append_assoc]
    rw [List.take_length_append' (UInt32.length_toBytes _).symm]
  rw [firstFour, Bytes.toB256_uint32_toBytes]
  change B256.shiftRight (⟨⟨_, _⟩, ⟨_, _⟩⟩ : B256) 224 = _
  simp only [B256.shiftRight]
  change (⟨0, B128.shiftRight ⟨_, _⟩ 96⟩ : B256) = _
  simp only [B128.shiftRight]
  dsimp only [B128]
  norm_num only
  simp only [ite_true, ite_false]
  congr 3
  have hlt : (x3 >>> 32).toNat < 4294967296 := by
    rw [UInt64.toNat_shiftRight]
    change x3.toNat >>> 32 < 4294967296
    rw [Nat.shiftRight_eq_div_pow]
    norm_num only
    have hx := UInt64.toNat_lt x3
    omega
  rw [← UInt64.toNat_inj]
  change (x3 >>> 32).toNat = (x3 >>> 32).toUInt32.toNat
  rw [UInt64.toUInt32_toNat, Nat.mod_eq_of_lt hlt]

/-- Taking a shorter prefix after a padded take is the shorter padded take. -/
lemma List.take_takeD_of_le {alpha} (xs : List alpha) (m n : Nat)
    (default : alpha) (le : m ≤ n) :
    (List.takeD n xs default).take m = List.takeD m xs default := by
  induction m generalizing n xs with
  | zero => rfl
  | succ m ih =>
      cases n with
      | zero => omega
      | succ n =>
          cases xs with
          | nil =>
              simp only [List.takeD, List.tail, List.take, List.cons.injEq]
              exact ⟨trivial, ih [] n (by omega)⟩
          | cons x xs =>
              simp only [List.takeD, List.tail, List.take, List.cons.injEq]
              exact ⟨trivial, ih xs n (by omega)⟩

/-- `Sevm.selector` is exactly the first four calldata bytes, padded on the
right with zeros when calldata is short. -/
theorem Sevm.selector_eq_toB256_takeD_four (sevm : Sevm) :
    Sevm.selector sevm = Bytes.toB256 (sevm.data.takeD 4 0) := by
  let word := sevm.data.sliceD 0 32 0
  have wordLength : word.length = 32 := List.takeD_length _ _ _
  have roundtrip : (Bytes.toB256 word).toBytes = word :=
    Bytes.toBytes_toB256_of_length wordLength
  have firstFour :
      (Bytes.toB256 word).toBytes.take 4 = sevm.data.takeD 4 0 := by
    rw [roundtrip]
    unfold word
    simp only [List.sliceD, List.drop_zero]
    exact List.take_takeD_of_le sevm.data 4 32 0 (by omega)
  rw [Sevm.selector, Sevm.dataWord]
  change Bytes.toB256 word >>> 224 = _
  rw [shiftRight_224_eq_toB256_take_four, firstFour]

/-! The three head words and the offset word of a `flashLoan`-shaped call.

`flashLoan(address,address,uint256,bytes)` is three static heads then one
dynamic tail, so these four are the whole head area. Together they are what
makes `Sevm.DecodesCallWithTail` a *specification*: they say the contract's own
`arg 0`, `arg 1`, `arg 2` and `arg 3` recover exactly the arguments the encoding
was built from, which is the identity fixed decision 2 demands and the falsifier
for the encoding definition itself. -/

/-- The encoding's head area, right-associated so each head word can be read off
by `dataWord_of_append` after re-associating the prefix. -/
lemma decodes_split {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    e.data = abiSelectorBytes sel ++ (B256.toBytes a ++ (B256.toBytes b ++
      (B256.toBytes c ++ (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data)))) := by
  simpa only [Sevm.DecodesCallWithTail, abiCallWithTail, map_cons, map_nil, flatten_cons,
    flatten_nil, append_nil, length_cons, length_nil, zero_add, reduceAdd, reduceMul,
    append_assoc] using h

lemma argWord_zero_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) : Sevm.argWord e 0 = a :=
  dataWord_of_append (by rw [abiSelectorBytes_length]; rfl) (decodes_split h)

lemma argWord_one_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) : Sevm.argWord e 1 = b := by
  have hd : e.data = (abiSelectorBytes sel ++ B256.toBytes a) ++ (B256.toBytes b ++
      (B256.toBytes c ++ (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data))) := by
    rw [List.append_assoc]; exact decodes_split h
  exact dataWord_of_append
    (by rw [List.length_append, abiSelectorBytes_length, B256.length_toBytes]; rfl) hd

lemma argWord_two_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) : Sevm.argWord e 2 = c := by
  have hd : e.data = (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b) ++
      (B256.toBytes c ++ (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data)) := by
    rw [List.append_assoc, List.append_assoc]; exact decodes_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, abiSelectorBytes_length,
        B256.length_toBytes, B256.length_toBytes]; rfl) hd

/-- The offset word is `0x80`, and this is proved rather than assumed: it is the
one head word whose value the encoding's *shape* fixes. -/
lemma argWord_three_of_decodes {e : Sevm} {sel a b c : B256} {data : Bytes}
    (h : Sevm.DecodesCallWithTail e sel [a, b, c] data) :
    Sevm.argWord e 3 = Nat.toB256 128 := by
  have hd : e.data =
      (abiSelectorBytes sel ++ B256.toBytes a ++ B256.toBytes b ++ B256.toBytes c) ++
      (B256.toBytes (Nat.toB256 128) ++ abiBytesTail data) := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc]; exact decodes_split h
  exact dataWord_of_append
    (by rw [List.length_append, List.length_append, List.length_append,
        abiSelectorBytes_length, B256.length_toBytes, B256.length_toBytes,
        B256.length_toBytes]; rfl) hd

lemma of_run_sload {e : Sevm} {s s' : Devm} (h : Ninst.Run e s sload s') :
    ∃ x, Stack.Diff [x] [Devm.getStorVal s e.currentTarget x] s.stack s'.stack := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s₁⟩, h1, run₁⟩
  have hpop := Devm.pop_of_pop h1
  have e1 : Devm.getStor s = Devm.getStor s₁ := Devm.pop_getStor_eq h1
  refine ⟨key, s₁.stack, hpop.stack, ?_⟩
  suffices H : ∀ (d : Devm) (c : Nat),
      Devm.getStor s₁ = Devm.getStor d → s₁.stack = d.stack →
      (chargeGas c d >>= fun next => Devm.push
        (Devm.getStorVal (Devm.balReadStorage e.benvStat.rules e.currentTarget key next) e.currentTarget key)
        (Devm.balReadStorage e.benvStat.rules e.currentTarget key next)) = .ok s' →
      Stack.Push [Devm.getStorVal s e.currentTarget key] s₁.stack s'.stack by
    cases haccess : e.benvStat.rules.access with
    | eip2929 =>
      simp only [haccess] at run₁
      split at run₁
      · exact H s₁ gasWarmAccess rfl rfl run₁
      · exact H (addAccessedStorageKey s₁ e.currentTarget key) gasColdSload
          (@addAccessedStorageKey_getStor s₁ e.currentTarget key).symm rfl run₁
    | flat gas =>
      simp only [haccess] at run₁
      exact H s₁ gas.sload rfl rfl run₁
  intro d c hgs hst run'
  rcases Except.bind_eq_ok run' with ⟨s₂, h2, run₂⟩
  have hpush := Devm.push_of_push run₂
  have hstk : d.stack = s₂.stack := (Devm.burn_of_chargeGas h2).stack
  have e2 : Devm.getStor d = Devm.getStor s₂ := chargeGas_getStor_eq h2
  have hval : Devm.getStorVal
      (Devm.balReadStorage e.benvStat.rules e.currentTarget key s₂)
      e.currentTarget key = Devm.getStorVal s e.currentTarget key := by
    rw [Devm.balReadStorage_getStorVal]
    show (Devm.getStor s₂ e.currentTarget).get key =
      (Devm.getStor s e.currentTarget).get key
    rw [← e2, ← hgs, ← e1]
  rw [hst, hstk, ← hval]
  exact hpush.stack

lemma prefix_of_sload {e x xs} {s s' : Devm} :
    Ninst.Run e s sload s' → (x :: xs <<+ s.stack) →
    ∃ y, (y :: xs <<+ s'.stack) ∧ y = Devm.getStorVal s e.currentTarget x := by
  intro h0 h1
  rcases of_run_sload h0 with ⟨x', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  exact ⟨_, append_pref h3 (of_append_pref h2 h1), rfl⟩

/-- A successful `SLOAD` emits no log entries. -/
lemma of_run_sload_logs {e : Sevm} {s s' : Devm}
    (run : Ninst.Run e s sload s') : s.logs = s'.logs := by
  rcases of_run_reg run with ⟨_pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨key, s1⟩, popRun, tailRun⟩
  have popLogs := (Devm.pop_of_pop popRun).logs
  suffices preserve : ∀ (d : Devm) (cost : Nat),
      s1.logs = d.logs →
      (chargeGas cost d >>=
        fun next => Devm.push
          (Devm.getStorVal (Devm.balReadStorage e.benvStat.rules e.currentTarget key next) e.currentTarget key)
          (Devm.balReadStorage e.benvStat.rules e.currentTarget key next)) = .ok s' →
      s1.logs = s'.logs by
    refine popLogs.trans ?_
    cases haccess : e.benvStat.rules.access with
    | eip2929 =>
      simp only [haccess] at tailRun
      split at tailRun
      · exact preserve s1 gasWarmAccess rfl tailRun
      · exact preserve (addAccessedStorageKey s1 e.currentTarget key)
          gasColdSload rfl tailRun
    | flat gas =>
      simp only [haccess] at tailRun
      exact preserve s1 gas.sload rfl tailRun
  intro d cost logsEq tailRun
  rcases Except.bind_eq_ok tailRun with ⟨charged, chargeRun, pushRun⟩
  exact (logsEq.trans (Devm.burn_of_chargeGas chargeRun).logs).trans
    (Devm.balReadStorage_logs.symm.trans (Devm.push_of_push pushRun).logs)

lemma prefix_of_mload {e x xs} {s s' : Devm} :
    Ninst.Run e s mload s' → (x :: xs <<+ s.stack) → ∃ y, y :: xs <<+ s'.stack := by
  intro h0 h1
  rcases of_run_mload h0 with ⟨x', y', stk, h2, h3⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  rw [hx] at h1
  exact ⟨y', append_pref h3 (of_append_pref h2 h1)⟩

lemma prefix_of_returndatacopy {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s returndatacopy s' → (x :: y :: z :: xs <<+ s.stack) → (xs <<+ s'.stack) := by
  intros h0 h1
  rcases of_run_returndatacopy h0 with ⟨x', y', z', h2⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, _⟩
  rw [hx, hy, hz] at h1
  exact of_append_pref h2 h1

/-- `mstoreAt` consumes the top of the stack and touches memory only. -/
lemma prefix_of_mstoreAt {e : Sevm} {s s' : Devm} {k x xs}
    (h : Line.Run e s (mstoreAt k) s') (hp : x :: xs <<+ s.stack) : xs <<+ s'.stack := by
  rcases Line.of_run_cons h with ⟨u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨u2, qm, hnil⟩
  cases hnil
  exact prefix_of_mstore qm (prefix_of_push (of_run_pushB256 qp) hp)

/-- `returnDataShorterThan` pushes one flag. -/
lemma of_returnDataShorterThan {e : Sevm} {s s' : Devm} {n : B256} {xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (returnDataShorterThan n) s') :
    ∃ y, y :: xs <<+ s'.stack := by
  simp only [returnDataShorterThan] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : n :: xs <<+ u1.stack := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  rcases of_run_returndatasize q2 with ⟨rds, pb2⟩
  have hp2 : rds :: n :: xs <<+ u2.stack := prefix_of_push pb2 hp1
  rcases Line.of_run_cons h with ⟨u3, q3, hnil⟩
  cases hnil
  exact ⟨_, prefix_of_lt q3 hp2⟩

/-- `checkReturnDataHead` copies the head word into memory, reads it back, and
pushes one comparison flag. -/
lemma of_checkReturnDataHead {e : Sevm} {s s' : Devm} {w m : B256} {xs}
    (hp : xs <<+ s.stack) (h : Line.Run e s (checkReturnDataHead w m) s') :
    ∃ y, y :: xs <<+ s'.stack := by
  simp only [checkReturnDataHead, pushList, List.map] at h
  rcases Line.of_run_cons h with ⟨u1, q1, h⟩
  have hp1 : (32 : B256) :: xs <<+ u1.stack := prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons h with ⟨u2, q2, h⟩
  have hp2 : (0 : B256) :: (32 : B256) :: xs <<+ u2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons h with ⟨u3, q3, h⟩
  have hp3 : (m * 32) :: (0 : B256) :: (32 : B256) :: xs <<+ u3.stack :=
    prefix_of_push (of_run_pushB256 q3) hp2
  rcases Line.of_run_cons h with ⟨u4, q4, h⟩
  have hp4 : xs <<+ u4.stack := prefix_of_returndatacopy q4 hp3
  rcases Line.of_run_cons h with ⟨u5, q5, h⟩
  have hp5 : (m * 32) :: xs <<+ u5.stack := prefix_of_push (of_run_pushB256 q5) hp4
  rcases Line.of_run_cons h with ⟨u6, q6, h⟩
  rcases prefix_of_mload q6 hp5 with ⟨head, hp6⟩
  rcases Line.of_run_cons h with ⟨u7, q7, h⟩
  have hp7 : w :: head :: xs <<+ u7.stack := prefix_of_push (of_run_pushB256 q7) hp6
  rcases Line.of_run_cons h with ⟨u8, q8, hnil⟩
  cases hnil
  exact ⟨_, prefix_of_eq q8 hp7⟩

lemma Line.spx_scheme {e s' i l xs xs' ys}
    (h : ∀ s0 s1, Ninst.Run e s0 i s1 → (xs <<+ s0.stack) → (xs' <<+ s1.stack))
    (h' : ∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (i :: l) s' → (ys <<+ s'.stack) := by
  intros s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h' s_mid (h _ _ h_head h_pfx) h_tail

lemma Line.spx_push {e : Sevm} {s' l bs p xs ys} :
    (∀ s : Devm, (bs.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (push bs p :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_push h_head) h_pfx

lemma Line.spx_pushB256 {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (pushB256 x :: l) s' → (ys <<+ s'.stack)) := by
  intros h_next s h_pfx h_run
  rcases Line.of_run_cons h_run with ⟨s_mid, h_head, h_tail⟩
  apply h_next s_mid _ h_tail
  apply prefix_of_push (of_run_pushB256 h_head) h_pfx

lemma Line.spx_mstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (mstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_mstore

lemma Line.spx_sstore {e : Sevm} {s' l x y xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sstore :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sstore

lemma Line.spx_dup {e s' l xs ys} {n : Fin 16} (x) :
    Stack.Nth n.val x xs →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (dup n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_nth; apply Line.spx_scheme
  intros s0 s1 h_step h_pfx
  rcases of_run_dup h_step with ⟨w, h_get, h_pb⟩
  rw [Stack.nth_getElem h_nth h_pfx] at h_get
  injection h_get with h_get
  rw [h_get]
  apply prefix_of_push h_pb h_pfx

lemma Line.spx_log (zs : Stack) {e s' l xs ys} {n : Fin 5} :
    zs.length = n.val + 2 →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (zs ++ xs <<+ s.stack) → Line.Run e s (log n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_len; apply Line.spx_scheme
  intros s₀ s₁ h_step h_pfx
  rcases of_run_log h_step with ⟨zs', h_len', h_pop⟩
  have h_zs : (zs <<+ s₀.stack) := @pref_trans _ zs (zs ++ xs) _ ⟨xs, rfl⟩ h_pfx
  have h_zs' : (zs' <<+ s₀.stack) := pref_of_split h_pop
  cases List.pref_unique (Eq.trans h_len h_len'.symm) h_zs h_zs'
  exact of_append_pref h_pop h_pfx

lemma Line.spx_swap (xs') {e s' l xs ys} {n : Fin 16} :
    Stack.Swap n.val xs xs' →
    (∀ s : Devm, (xs' <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (swap n :: l) s' → (ys <<+ s'.stack)) := by
  intro h_swap; apply Line.spx_scheme
  intros s0 s1 h_step
  exact Stack.prefix_of_swap h_swap (of_run_swap h_step)

lemma Line.spx_iszero {e s' l} {x} {xs ys} :
    (∀ s : Devm, ((x =? 0) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (iszero :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_iszero

lemma Line.spx_pop {e : Sevm} {s' l x xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (pop :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step
  exact prefix_of_pop (of_run_pop h_step)

lemma Line.spx_eq {e s' l x y xs ys} :
    (∀ s : Devm, ((x =? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (eq :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_eq

lemma Line.spx_lt {e s' l x y xs ys} :
    (∀ s : Devm, ((x <? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (lt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_lt

lemma Line.spx_gt {e s' l x y xs ys} :
    (∀ s : Devm, ((x >? y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (gt :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_gt

lemma Line.spx_sub {e s' l x y xs ys} :
    (∀ s : Devm, ((x - y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (sub :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_sub

lemma Line.spx_not {e s' l x xs ys} :
    (∀ s : Devm, (~~~ x :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: xs <<+ s.stack) → Line.Run e s (not :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_not

lemma Line.spx_or {e s' l x y xs ys} :
    (∀ s : Devm, ((x ||| y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (or :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_or

lemma Line.spx_and {e s' l x y xs ys} :
    (∀ s : Devm, ((x &&& y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (and :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_and

lemma Line.spx_shl {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y <<< x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shl :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shl

lemma Line.spx_shr {e s' l} {x y : B256} {xs ys} :
    (∀ s : Devm, (y >>> x.toNat :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (shr :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_shr

lemma Line.spx_add {e s' l x y xs ys} :
    (∀ s : Devm, ((x + y) :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: xs <<+ s.stack) → Line.Run e s (add :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_add

lemma Line.spx_caller {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.caller.toB256 :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (caller :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_caller h_step) h_pfx

lemma Line.spx_callvalue {e : Sevm} {s' l xs ys} :
    (∀ s : Devm, (e.value :: xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s (callvalue :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intros s0 s1 h_step h_pfx
  apply prefix_of_push (of_run_callvalue h_step) h_pfx

lemma Line.spx_calldatacopy {e : Sevm} {s' l x y z xs ys} :
    (∀ s : Devm, (xs <<+ s.stack) → Line.Run e s l s' → (ys <<+ s'.stack)) →
    (∀ s : Devm, (x :: y :: z :: xs <<+ s.stack) → Line.Run e s (calldatacopy :: l) s' → (ys <<+ s'.stack)) := by
  apply Line.spx_scheme; intro s0 s1; apply prefix_of_calldatacopy

lemma Line.spx_unwrap {e xs} {s' : Devm} :
    ∀ s : Devm, (xs <<+ s.stack) → Line.Run e s [] s' → (xs <<+ s'.stack) := by
  intros _ h0 h1; cases h1; apply h0


/-- `logWith 2 0 1` pops the topic triple and the window pair. -/
lemma of_logWith201 {e : Sevm} {s s' : Devm} {ev z w : B256} {xs}
    (hp : ev :: z :: w :: xs <<+ s.stack) (h : Line.Run e s (logWith 2 0 1) s') :
    xs <<+ s'.stack := by
  generalize_line_prefix


/-- `MSTORE` writes *the word it popped* at *the offset it popped*.

The value-carrying companion of `of_run_mstore`, and the first Blanc lemma whose
conclusion names `Devm.memory` at all. -/
lemma of_run_mstore_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mstore s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat y.toBytes := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  have hmem : s.memory = s₃.memory := (p1.memory.trans p2.memory).trans hb.memory
  refine ⟨x, v, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 p2).stack
    rw [← eq, show (Devm.memWrite s₃ x.toNat v.toBytes).stack = s₃.stack from rfl,
      ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- `MSTORE8` writes the low byte of the word it popped at the offset it
popped.  This is the byte-store companion of `of_run_mstore_val`. -/
lemma of_run_mstore8_val {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s mstore8 s') :
    ∃ x y, Stack.Pop [x, y] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat [y.2.2.toUInt8] := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨i, s₁⟩, h1, run'⟩
  rcases Except.bind_eq_ok run' with ⟨⟨v, s₂⟩, h2, run''⟩
  rcases Except.bind_eq_ok run'' with ⟨s₃, h3, h4⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have p2 := Devm.pop_of_pop h2
  have hb := Devm.burn_of_chargeGas h3
  injection h4 with eq
  have hmem : s.memory = s₃.memory :=
    (p1.memory.trans p2.memory).trans hb.memory
  refine ⟨x, v, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 p2).stack
    rw [← eq,
      show (Devm.memWrite s₃ x.toNat [v.2.2.toUInt8]).stack =
        s₃.stack from rfl,
      ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- `CODECOPY` writes the exact code-image slice named by its three operands at
the popped destination offset.  This is the creation-code companion of
`of_run_calldatacopy_mem`. -/
lemma of_run_codecopy_mem {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s codecopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack ∧
      s'.memory = s.memory.write x.toNat
        (e.code.sliceD y.toNat z.toNat (Linst.toUInt8 .stop)) := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨ci, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  injection h5 with eq
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  refine ⟨x, y, z, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq,
      show (Devm.memWrite s₄ x.toNat _).stack = s₄.stack from rfl,
      ← hb.stack]
    exact hp
  · rw [← eq, hmem]
    rfl

/-- `LOG` only *extends* memory: it reads a window and records it, and the
backing array is untouched.  That is enough to carry both `Mem.Wf` and a
`Mem.Reads` image across the mint's `Transfer` event. -/
lemma of_run_log_mem {e : Sevm} {s s' : Devm} {n : Fin 5}
    (h : Ninst.Run e s (log n) s') :
    ∃ mi sz, s'.memory = s.memory.extend mi sz := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat h1 with ⟨x, p1⟩
  rcases Devm.pop_of_popToNat h2 with ⟨y, p2⟩
  rcases Devm.pop_of_popN h3 with ⟨_, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  refine ⟨mi, sz, ?_⟩
  rcases h_mem : Devm.memRead s₄ mi sz with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_s₅ : s₅.memory = s₄.memory.extend mi sz := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read mi sz with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]
    show mem = _
    have hm2 : mem = (s₄.memory.read mi sz).2 := by rw [h_read]
    rw [hm2]
    rfl
  rw [← eq]
  show s₅.memory = _
  rw [h_s₅, hmem]

/-- `MSTORE` at a *known* stack top: the value-carrying companion of
`prefix_of_mstore`, with the popped operands pinned to the words the walk
already knows are there. -/
lemma prefix_of_mstore_val {e} {x y xs} {s s' : Devm}
    (h0 : Ninst.Run e s mstore s') (h1 : x :: y :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧ s'.memory = s.memory.write x.toNat y.toBytes := by
  rcases of_run_mstore_val h0 with ⟨x', y', h2, hm⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2) with ⟨hx, hy, -⟩
  refine ⟨?_, by rw [hx, hy]; exact hm⟩
  rw [hx, hy] at h1
  exact of_append_pref h2 h1

/-- `mstoreAt k` writes the stack top into memory word `k`.

The `Line`-level form, and the one every `storeCallbackHead`-shaped fragment
composes: `(k * 32).toNat` is the byte offset the compiled `PUSH` supplies, and
`B256.toBytes` is the machine's own 32-byte big-endian encoding. -/
lemma of_run_mstoreAt_val {e : Sevm} {s s' : Devm} {k x xs}
    (h : Line.Run e s (mstoreAt k) s') (hp : x :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧ s'.memory = s.memory.write (k * 32).toNat x.toBytes := by
  rcases Line.of_run_cons h with ⟨u, qp, h'⟩
  rcases Line.of_run_cons h' with ⟨u2, qm, hnil⟩
  cases hnil
  have hpb := of_run_pushB256 qp
  rcases prefix_of_mstore_val qm (prefix_of_push hpb hp) with ⟨hs, hm⟩
  exact ⟨hs, by rw [hm, ← hpb.memory]⟩

/-- `RETURNDATASIZE` pushes the length of the last call's return data. -/
lemma of_run_returndatasize_val {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s returndatasize s') :
    Devm.PushBurn [s.returnData.length.toB256] s s' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.pushBurn_of_pushItem run

/-- `RETURNDATACOPY` writes *the returndata slice named by its operands* at
*the offset it popped* — and it got there without overrunning the returndata,
because an overrun is an exceptional halt, not a failed test (the reason
`returnDataShorterThan` must be branched on first). -/
lemma of_run_returndatacopy_val {e : Sevm} {s s' : Devm}
    (h : Ninst.Run e s returndatacopy s') :
    ∃ x y z, Stack.Pop [x, y, z] s.stack s'.stack ∧
      y.toNat + z.toNat ≤ s.returnData.length ∧
      s'.memory
        = s.memory.write x.toNat (s.returnData.sliceD y.toNat z.toNat 0) ∧
      s'.returnData = s.returnData := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨di, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨sz, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, h5⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popToNat_val h3 with ⟨z, p3, rfl⟩
  have hb := Devm.burn_of_chargeGas h4
  have hrd : s.returnData = s₄.returnData :=
    ((p1.returnData.trans p2.returnData).trans p3.returnData).trans hb.returnData
  have hmem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  split at h5
  · cases h5
  · rename_i hbound
    injection h5 with eq
    refine ⟨x, y, z, ?_, ?_, ?_, ?_⟩
    · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
      rw [← eq, show (Devm.memWrite s₄ x.toNat _).stack = s₄.stack from rfl,
        ← hb.stack]
      exact hp
    · rw [hrd]
      omega
    · rw [← eq, hmem, hrd]
      rfl
    · rw [← eq, hrd]
      rfl

/-- `RETURNDATACOPY` at a *known* stack top. -/
lemma prefix_of_returndatacopy_val {e} {x y z xs} {s s' : Devm}
    (h0 : Ninst.Run e s returndatacopy s') (h1 : x :: y :: z :: xs <<+ s.stack) :
    (xs <<+ s'.stack) ∧
      y.toNat + z.toNat ≤ s.returnData.length ∧
      s'.memory
        = s.memory.write x.toNat (s.returnData.sliceD y.toNat z.toNat 0) ∧
      s'.returnData = s.returnData := by
  rcases of_run_returndatacopy_val h0 with ⟨x', y', z', h2, hle, hm, hrd⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, hpf, hpf'⟩
  rcases List.of_cons_pref_of_cons_pref hpf hpf' with ⟨hz, -⟩
  rw [hx, hy, hz] at h1 ⊢
  exact ⟨of_append_pref h2 h1, hle, hm, hrd⟩

/-- The value a `Devm`-level memory read returns is the `Mem`-level one. -/
lemma Devm.memRead_fst (d : Devm) (i n : Nat) :
    (d.memRead i n).1 = (d.memory.read i n).1 := by
  unfold Devm.memRead
  rcases d.memory.read i n with ⟨val, mem⟩
  rfl

/-- Value-carrying inversion for `LOG`: besides the popped stack words, expose
the exact topics and the log entry appended from the pre-instruction memory.

The earlier `of_run_log` is intentionally the value-forgetting stack theorem;
this companion is the shared seam used by contract proofs that specify events
as part of their public behavior. -/
lemma of_run_log_val {e : Sevm} {s s' : Devm} {n : Fin 5}
    (h : Ninst.Run e s (log n) s') :
    ∃ mi sz topics,
      topics.length = n.val ∧
      Stack.Pop (mi :: sz :: topics) s.stack s'.stack ∧
      s'.logs =
        s.logs ++
          [⟨e.currentTarget, topics,
            (s.memory.read mi.toNat sz.toNat).1⟩] := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨mi, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨⟨sz, s₂⟩, h2, run₂⟩
  rcases Except.bind_eq_ok run₂ with ⟨⟨topics, s₃⟩, h3, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₄, h4, run₄⟩
  rcases Except.bind_eq_ok run₄ with ⟨_, h5, run₅⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  rcases Devm.pop_of_popToNat_val h2 with ⟨y, p2, rfl⟩
  rcases Devm.pop_of_popN h3 with ⟨h_len, p3⟩
  have hb := Devm.burn_of_chargeGas h4
  rcases h_mem : Devm.memRead s₄ x.toNat y.toNat with ⟨data, s₅⟩
  rw [h_mem] at run₅
  injection run₅ with eq
  have h_pre_mem : s.memory = s₄.memory :=
    ((p1.memory.trans p2.memory).trans p3.memory).trans hb.memory
  have h_data : data = (s.memory.read x.toNat y.toNat).1 := by
    have hd := congrArg Prod.fst h_mem
    simp only [Devm.memRead_fst] at hd
    rw [h_pre_mem]
    exact hd.symm
  have h_mem_logs : s₄.logs = s₅.logs := by
    simp only [Devm.memRead] at h_mem
    rcases h_read : s₄.memory.read x.toNat y.toNat with ⟨val, mem⟩
    rw [h_read] at h_mem
    injection h_mem with _ h_devm
    rw [← h_devm]
    rfl
  have h_pre_logs : s.logs = s₅.logs :=
    (((p1.logs.trans p2.logs).trans p3.logs).trans hb.logs).trans h_mem_logs
  refine ⟨x, y, topics, h_len, ?_, ?_⟩
  · have hp := (Devm.pop_append p1 (Devm.pop_append p2 p3)).stack
    rw [← eq]
    show Stack.Pop (x :: y :: topics) s.stack s₅.stack
    have h_s₅_stack : s₅.stack = s₄.stack := by
      simp only [Devm.memRead] at h_mem
      rcases h_read : s₄.memory.read x.toNat y.toNat with ⟨val, mem⟩
      rw [h_read] at h_mem
      injection h_mem with _ h_devm
      rw [← h_devm]
      rfl
    rw [h_s₅_stack, ← hb.stack]
    exact hp
  · rw [← eq]
    show s₅.logs ++ [⟨e.currentTarget, topics, data⟩] =
      s.logs ++
        [⟨e.currentTarget, topics, (s.memory.read x.toNat y.toNat).1⟩]
    rw [← h_pre_logs, h_data]

/-- `MLOAD` pushes *the word at the offset it popped*, and only extends
memory.  The value-carrying companion of `of_run_mload`. -/
lemma of_run_mload_val {e : Sevm} {s s' : Devm} (h : Ninst.Run e s mload s') :
    ∃ x, Stack.Diff [x] [Bytes.toB256 (s.memory.read x.toNat 32).1]
        s.stack s'.stack ∧
      s'.memory = s.memory.extend x.toNat 32 ∧
      s'.returnData = s.returnData := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨si, s₁⟩, h1, run₁⟩
  rcases Except.bind_eq_ok run₁ with ⟨s₂, h2, run₂⟩
  rcases Devm.pop_of_popToNat_val h1 with ⟨x, p1, rfl⟩
  have hb := Devm.burn_of_chargeGas h2
  have hpush := Devm.push_of_push run₂
  have hmem : s.memory = s₂.memory := p1.memory.trans hb.memory
  have hrd : s.returnData = s₂.returnData := p1.returnData.trans hb.returnData
  refine ⟨x, ⟨s₁.stack, p1.stack, ?_⟩, ?_, ?_⟩
  · have hstk := hpush.stack
    rw [show (s₂.memRead x.toNat 32).2.stack = s₂.stack from rfl,
      ← hb.stack] at hstk
    rw [show (s₂.memRead x.toNat 32).1 = (s.memory.read x.toNat 32).1 from by
      rw [Devm.memRead_fst, hmem]] at hstk
    exact hstk
  · have hm := hpush.memory
    rw [show (s₂.memRead x.toNat 32).2.memory = s₂.memory.extend x.toNat 32 from
      rfl] at hm
    rw [← hm, ← hmem]
  · rw [← hpush.returnData]
    show s₂.returnData = s.returnData
    exact hrd.symm

/-- `MLOAD` at a *known* stack top against a known memory image: the pushed
word is the image's word at that offset, and the image survives the
extension. -/
lemma prefix_of_mload_val {e} {x : B256} {xs bs} {s s' : Devm}
    (h0 : Ninst.Run e s mload s') (h1 : x :: xs <<+ s.stack)
    (hr : Mem.Reads s.memory bs) :
    (Bytes.toB256 (bs.sliceD x.toNat 32 0) :: xs <<+ s'.stack) ∧
      s'.memory = s.memory.extend x.toNat 32 ∧
      s'.returnData = s.returnData := by
  rcases of_run_mload_val h0 with ⟨x', ⟨stk, h2, h3⟩, hm, hrd⟩
  have hx : x = x' := (List.of_cons_pref_of_cons_pref h1 (pref_of_split h2)).left
  subst hx
  rw [Mem.Reads.read hr x.toNat 32] at h3
  exact ⟨append_pref h3 (of_append_pref h2 h1), hm, hrd⟩

/-- **`(len + 31) & ~31` is `ceil32 len`**, as a `Nat`. -/
lemma B256.toNat_ceil32 {len : Nat} (h : 31 + len < 2 ^ 256) :
    ((~~~ (31 : B256)) &&& (31 + Nat.toB256 len)).toNat = ceil32 len := by
  have hy : ((31 : B256) + Nat.toB256 len).toNat = 31 + len := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt (by omega : len < 2 ^ 256),
      show B256.toNat 31 = 31 from rfl, Nat.lo_eq_of_lt h]
  rw [B256.toNat_and, show (~~~ (31 : B256)).toNat = 2 ^ 256 - 32 from rfl,
    Nat.and_comm, hy, Nat.and_mask32 h, ceil32_eq_mul]

/-! ### The weak form of a partial-correctness theorem: settles with some error

`exec` is Jaune's total function into `Execution := Except (EvmError × Devm)
Devm`, so it is defined on every `Evm`.  A statement of the form "no `.ok`
outcome exists" therefore already implies the positive claim "this call
settles with *some* error" — the case `exec` did not take is the only one
left.  This is the error-genre plan's E-A: the generic bridge, contract-
agnostic and mentioning no `Func`, `Prog`, or contract of Blanc's. -/

end Blanc
