import Blanc.Lift.CursorCuts
import Blanc.Lift.Exact
import Blanc.ExecDeterminism
import Blanc.LockExclusion

/-!
# Exact-state forward cuts of an actual certificate cursor

`Blanc/Lift/CursorCuts.lean` advances a checked cursor through an actual
successful raw suffix, but its conclusions keep only the loose `RunWith`,
`Jinst.Run` and `ConfStep` facts, whose jump frames forget the exact gas.
This module pins the complete actual state at a later cursor.

The pinned state is computed by a gas-exact synthetic run of a *cut* tree:
`SFunc.CutAt fs tgt f f'` follows one inline path of `f` to the subtree `tgt`,
replaces `tgt` by `.last .stop`, and turns every arm the path does not take
into `.undefined` (so the synthetic run cannot take it). A `.branchTo` the
path takes is inlined from `fs`. `cursor_cut_exact` then derives, from the
actual successful derivation alone, the node at `tgt`, its frame-entry-free
span and its complete dynamic state, including gas and world metadata: the
synthetic run's halting state. The usual `rx_*` walk kit proves that
synthetic run. `cursor_callNext_exact` crosses one internal call edge, and
`Exec.Deriv.ExecFreeUntil.eq_of_execAt` identifies two frame-entry-free
cuts that both decode a frame-entering instruction.
-/

namespace Blanc.Lift

open Jaune

/-! ## Exact frames are functional -/

/-- An actual primitive step agrees with a compiled step from the same state. -/
theorem ninstRun_eq_of_runCompiled {sevm : Sevm} {s s₁ s₂ : Devm} {n : Ninst}
    (actual : Ninst.Run sevm s n s₁) (compiled : Ninst.RunCompiled sevm s n s₂) :
    s₁ = s₂ := by
  obtain ⟨xl, filled, pc, step⟩ := actual
  obtain ⟨xl', filled', step'⟩ := compiled
  exact Except.ok.inj (Step.Run.unique_of_filled filled filled' step (step' pc)).2

/-- Two exact pops of equally many words with one charge reach one state. -/
theorem popBurnBy_eq_of_length {xs ys : List B256} {cost : Nat} {a b b' : Devm}
    (left : Devm.PopBurnBy xs cost a b) (right : Devm.PopBurnBy ys cost a b')
    (length : xs.length = ys.length) : b = b' := by
  have stackLeft : a.stack = xs ++ b.stack := left.stack
  have stackRight : a.stack = ys ++ b'.stack := right.stack
  have gasLeft : a.gasLeft = b.gasLeft + cost := left.gasLeft
  have gasRight : a.gasLeft = b'.gasLeft + cost := right.gasLeft
  exact Blanc.Devm.eq_of_proj (List.append_inj (stackLeft.symm.trans stackRight) length).2
    (left.memory.symm.trans right.memory) (by omega)
    (left.logs.symm.trans right.logs) (left.refundCounter.symm.trans right.refundCounter)
    (left.output.symm.trans right.output)
    (left.accountsToDelete.symm.trans right.accountsToDelete)
    (left.returnData.symm.trans right.returnData) (left.error.symm.trans right.error)
    (left.accessedAddresses.symm.trans right.accessedAddresses)
    (left.accessedStorageKeys.symm.trans right.accessedStorageKeys)
    (left.state.symm.trans right.state)
    (left.createdAccounts.symm.trans right.createdAccounts)
    (left.transientStorage.symm.trans right.transientStorage)
    (left.stateGas.symm.trans right.stateGas)
    (left.accountReads.symm.trans right.accountReads)
    (left.storageReads.symm.trans right.storageReads)

/-- Two exact burns of one charge reach one state. -/
theorem burnBy_eq {cost : Nat} {a b b' : Devm}
    (left : Devm.BurnBy cost a b) (right : Devm.BurnBy cost a b') : b = b' := by
  have gasLeft : a.gasLeft = b.gasLeft + cost := left.gasLeft
  have gasRight : a.gasLeft = b'.gasLeft + cost := right.gasLeft
  exact Blanc.Devm.eq_of_proj (left.stack.symm.trans right.stack)
    (left.memory.symm.trans right.memory) (by omega)
    (left.logs.symm.trans right.logs) (left.refundCounter.symm.trans right.refundCounter)
    (left.output.symm.trans right.output)
    (left.accountsToDelete.symm.trans right.accountsToDelete)
    (left.returnData.symm.trans right.returnData) (left.error.symm.trans right.error)
    (left.accessedAddresses.symm.trans right.accessedAddresses)
    (left.accessedStorageKeys.symm.trans right.accessedStorageKeys)
    (left.state.symm.trans right.state)
    (left.createdAccounts.symm.trans right.createdAccounts)
    (left.transientStorage.symm.trans right.transientStorage)
    (left.stateGas.symm.trans right.stateGas)
    (left.accountReads.symm.trans right.accountReads)
    (left.storageReads.symm.trans right.storageReads)

/-! ## Inverting one stateful synthetic step by node kind -/

section ConfStepKinds

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}
  {d d' : Devm} {f f' g : SFunc} {K K' : List SFunc} {k : Nat}

theorem ConfStep.of_dest (h : ConfStep P fs sevm ⟨d, .dest f, K⟩ ⟨d', f', K'⟩) :
    Devm.Burn d d' ∧ f' = f := by
  cases h with
  | dest burn => exact ⟨burn, rfl⟩

theorem ConfStep.of_branch (h : ConfStep P fs sevm ⟨d, .branch f g, K⟩ ⟨d', f', K'⟩) :
    (∃ t, Devm.PopBurn [t, 0] d d' ∧ f' = f) ∨
      (∃ t w, w ≠ 0 ∧ Devm.PopBurn [t, w] d d' ∧ f' = g) := by
  cases h with
  | zero t pop => exact Or.inl ⟨t, pop, rfl⟩
  | succ t w nonzero pop => exact Or.inr ⟨t, w, nonzero, pop, rfl⟩

theorem ConfStep.of_branchTo (h : ConfStep P fs sevm ⟨d, .branchTo f k, K⟩ ⟨d', f', K'⟩) :
    (∃ t, Devm.PopBurn [t, 0] d d' ∧ f' = f) ∨
      (∃ t w, w ≠ 0 ∧ fs[k]? = some f' ∧ Devm.PopBurn [t, w] d d') := by
  cases h with
  | toZero t pop => exact Or.inl ⟨t, pop, rfl⟩
  | toSucc t w nonzero entry pop => exact Or.inr ⟨t, w, nonzero, entry, pop⟩

theorem ConfStep.of_callNext (h : ConfStep P fs sevm ⟨d, .callNext k f, K⟩ ⟨d', f', K'⟩) :
    ∃ t, fs[k]? = some f' ∧ Devm.PopBurn [t] d d' := by
  cases h with
  | call t entry pop => exact ⟨t, entry, pop⟩

end ConfStepKinds

/-! ## Decoded jump bytes under checked control nodes -/

section CheckedJumps

variable {code : ByteArray} {c : Cert} {F : Exec.Deriv} {κ : Cursor}
  {f g : SFunc} {k : Nat}

theorem CursorOK.jumpdestAt_of_dest (ok : CursorOK code c F κ) (tree : κ.f = .dest f) :
    Jinst.At F.sevm.code F.pc .jumpdest := by
  have check := ok.check
  rw [tree] at check
  rw [ok.code_eq, ok.pc_eq]
  apply byteAt_jinst_at
  simp only [checkNode, Bool.and_eq_true, beq_iff_eq] at check
  exact check.1

theorem CursorOK.jumpiAt_of_branch (ok : CursorOK code c F κ) (tree : κ.f = .branch f g) :
    Jinst.At F.sevm.code F.pc .jumpi := by
  have check := ok.check
  rw [tree] at check
  rw [ok.code_eq, ok.pc_eq]
  apply byteAt_jinst_at
  simp only [checkNode] at check
  split at check
  · simp only [Bool.and_eq_true, beq_iff_eq] at check
    exact check.1.1
  · cases check

theorem CursorOK.jumpiAt_of_branchTo (ok : CursorOK code c F κ) (tree : κ.f = .branchTo f k) :
    Jinst.At F.sevm.code F.pc .jumpi := by
  have check := ok.check
  rw [tree] at check
  rw [ok.code_eq, ok.pc_eq]
  apply byteAt_jinst_at
  simp only [checkNode] at check
  split at check
  · simp only [Bool.and_eq_true, beq_iff_eq] at check
    exact check.1.1.1.1
  · cases check

theorem CursorOK.jumpAt_of_callNext (ok : CursorOK code c F κ) (tree : κ.f = .callNext k f) :
    Jinst.At F.sevm.code F.pc .jump := by
  have check := ok.check
  rw [tree] at check
  rw [ok.code_eq, ok.pc_eq]
  apply byteAt_jinst_at
  simp only [checkNode] at check
  split at check
  · simp only [Bool.and_eq_true, beq_iff_eq] at check
    exact check.1.1.1
  · cases check

end CheckedJumps

/-! ## Cut trees -/

/-- `SFunc.CutAt fs tgt f f'`: `f'` is `f` along one path to the subtree `tgt`,
which becomes `.last .stop`. Untaken arms become `.undefined`, a taken
`.branchTo` is inlined from `fs` as a jumping `.branch`, and no instruction
on the path enters a frame. -/
inductive SFunc.CutAt (fs : List SFunc) (tgt : SFunc) : SFunc → SFunc → Prop
  | here : SFunc.CutAt fs tgt tgt (.last .stop)
  | next {n : Ninst} {f f' : SFunc} :
    (∀ x : Xinst, n ≠ .exec x) → SFunc.CutAt fs tgt f f' →
    SFunc.CutAt fs tgt (.next n f) (.next n f')
  | dest {f f' : SFunc} :
    SFunc.CutAt fs tgt f f' → SFunc.CutAt fs tgt (.dest f) (.dest f')
  | zero {f f' g : SFunc} :
    SFunc.CutAt fs tgt f f' → SFunc.CutAt fs tgt (.branch f g) (.branch f' .undefined)
  | succ {f g g' : SFunc} :
    SFunc.CutAt fs tgt g g' → SFunc.CutAt fs tgt (.branch f g) (.branch .undefined g')
  | toZero {f f' : SFunc} {k : Nat} :
    SFunc.CutAt fs tgt f f' → SFunc.CutAt fs tgt (.branchTo f k) (.branch f' .undefined)
  | toSucc {f g g' : SFunc} {k : Nat} :
    fs[k]? = some g → SFunc.CutAt fs tgt g g' →
    SFunc.CutAt fs tgt (.branchTo f k) (.branch .undefined g')

/-- A successful actual frame at a checked cursor reaches the cut subtree.
Its frame-entry-free span, unchanged static environment and outcome, cursor,
and complete dynamic state are derived from the actual derivation; the state
is the halting state of the gas-exact synthetic run of the cut tree. -/
theorem cursor_cut_exact {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {fs' : List SFunc} {tgt f f' : SFunc}
    (cut : SFunc.CutAt c.prog tgt f f') :
    ∀ {F : Exec.Deriv} {κ : Cursor} {post s : Devm},
      CursorOK code c F κ → κ.f = f → F.exn = .ok post →
      CoveredFork F.sevm.benvStat.fork →
      SFunc.RunExact fs' F.sevm F.devm f' (.halted s) →
      ∃ (N : Exec.Deriv) (κ' : Cursor),
        Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
        CursorOK code c N κ' ∧ κ'.f = tgt ∧ N.devm = s := by
  induction cut with
  | here =>
    intro F κ post s ok tree success fork run
    cases run with
    | last stop =>
      have self : Linst.Run F.sevm F.devm .stop (.ok F.devm) := rfl
      exact ⟨F, κ, .refl F, rfl, rfl, ok, tree, (Except.ok.inj (stop.symm.trans self)).symm⟩
  | @next n f f' free cut ih =>
    intro F κ post s ok tree success fork run
    obtain ⟨N, κ', edge, _, primitive, synthetic, _, placed⟩ :=
      cursor_next_forward checked ok tree success fork
    cases run with
    | next compiled rest =>
      have state := ninstRun_eq_of_runCompiled primitive.toRun compiled
      have nextTree : κ'.f = f := by
        rcases κ with ⟨body, pc, a, m, K⟩
        dsimp only at tree
        subst body
        cases synthetic
        rfl
      have nextSevm : N.sevm = F.sevm := Cursor.parentStep_sevm edge
      have nextExn : N.exn = F.exn := by cases edge <;> rfl
      have nextFork : CoveredFork N.sevm.benvStat.fork := by rw [nextSevm]; exact fork
      have nextRun : SFunc.RunExact fs' N.sevm N.devm f' (.halted s) := by
        rw [nextSevm, state]; exact rest
      obtain ⟨E, κ'', span, sameSevm, sameExn, endOk, endTree, endState⟩ :=
        ih placed nextTree (nextExn.trans success) nextFork nextRun
      have decoded := ok.ninstAt_of_next tree
      have headFree : ∀ x : Xinst, ¬ Ninst.At F.sevm.code F.pc (.exec x) := by
        intro x atExec
        exact free x (Inst.next.inj (Option.some.inj (decoded.symm.trans atExec)))
      exact ⟨E, κ'', (Exec.Deriv.ExecFreeUntil.ofStep edge headFree).trans span,
        sameSevm.trans nextSevm, sameExn.trans nextExn, endOk, endTree, endState⟩
  | @dest f f' cut ih =>
    intro F κ post s ok tree success fork run
    have instruction := ok.jumpdestAt_of_dest tree
    obtain ⟨N, κ', edge, jumped, _, stateful, placed⟩ :=
      cursor_jinst_forward checked ok instruction success fork
    have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        ⟨F.devm, .dest f, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
      rw [← tree]; exact stateful
    obtain ⟨burn, nextTree⟩ := ConfStep.of_dest step
    cases run with
    | dest burnBy rest =>
      have state := burnBy_eq
        (Devm.BurnBy.of_burn burn (Devm.gasLeft_of_jumpdest_run jumped)) burnBy
      have nextSevm : N.sevm = F.sevm := Cursor.parentStep_sevm edge
      have nextExn : N.exn = F.exn := by cases edge <;> rfl
      have nextFork : CoveredFork N.sevm.benvStat.fork := by rw [nextSevm]; exact fork
      have nextRun : SFunc.RunExact fs' N.sevm N.devm f' (.halted s) := by
        rw [nextSevm, state]; exact rest
      obtain ⟨E, κ'', span, sameSevm, sameExn, endOk, endTree, endState⟩ :=
        ih placed nextTree (nextExn.trans success) nextFork nextRun
      exact ⟨E, κ'', (Exec.Deriv.ExecFreeUntil.ofStep edge
          (Blanc.Jinst.At.not_exec instruction)).trans span,
        sameSevm.trans nextSevm, sameExn.trans nextExn, endOk, endTree, endState⟩
  | @zero f f' g cut ih =>
    intro F κ post s ok tree success fork run
    have instruction := ok.jumpiAt_of_branch tree
    obtain ⟨N, κ', edge, jumped, _, stateful, placed⟩ :=
      cursor_jinst_forward checked ok instruction success fork
    have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        ⟨F.devm, .branch f g, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
      rw [← tree]; exact stateful
    cases run with
    | succ _ _ _ _ rest => cases rest
    | zero d pop rest =>
      rcases ConfStep.of_branch step with ⟨t, actual, nextTree⟩ | ⟨t, w, nonzero, actual, _⟩
      · have state := popBurnBy_eq_of_length
          (Devm.PopBurnBy.of_popBurn actual (Devm.gasLeft_of_jumpi_run jumped)) pop rfl
        have nextSevm : N.sevm = F.sevm := Cursor.parentStep_sevm edge
        have nextExn : N.exn = F.exn := by cases edge <;> rfl
        have nextFork : CoveredFork N.sevm.benvStat.fork := by rw [nextSevm]; exact fork
        have nextRun : SFunc.RunExact fs' N.sevm N.devm f' (.halted s) := by
          rw [nextSevm, state]; exact rest
        obtain ⟨E, κ'', span, sameSevm, sameExn, endOk, endTree, endState⟩ :=
          ih placed nextTree (nextExn.trans success) nextFork nextRun
        exact ⟨E, κ'', (Exec.Deriv.ExecFreeUntil.ofStep edge
            (Blanc.Jinst.At.not_exec instruction)).trans span,
          sameSevm.trans nextSevm, sameExn.trans nextExn, endOk, endTree, endState⟩
      · have actualStack : F.devm.stack = [t, w] ++ N.devm.stack := actual.stack
        have syntheticStack : F.devm.stack = [d, 0] ++ _ := pop.stack
        rw [actualStack] at syntheticStack
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at syntheticStack
        exact (nonzero syntheticStack.2.1).elim
  | @succ f g g' cut ih =>
    intro F κ post s ok tree success fork run
    have instruction := ok.jumpiAt_of_branch tree
    obtain ⟨N, κ', edge, jumped, _, stateful, placed⟩ :=
      cursor_jinst_forward checked ok instruction success fork
    have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        ⟨F.devm, .branch f g, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
      rw [← tree]; exact stateful
    cases run with
    | zero _ _ rest => cases rest
    | succ d w nonzero pop rest =>
      rcases ConfStep.of_branch step with ⟨t, actual, _⟩ | ⟨t, w', _, actual, nextTree⟩
      · have actualStack : F.devm.stack = [t, 0] ++ N.devm.stack := actual.stack
        have syntheticStack : F.devm.stack = [d, w] ++ _ := pop.stack
        rw [actualStack] at syntheticStack
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at syntheticStack
        exact (nonzero syntheticStack.2.1.symm).elim
      · have state := popBurnBy_eq_of_length
          (Devm.PopBurnBy.of_popBurn actual (Devm.gasLeft_of_jumpi_run jumped)) pop rfl
        have nextSevm : N.sevm = F.sevm := Cursor.parentStep_sevm edge
        have nextExn : N.exn = F.exn := by cases edge <;> rfl
        have nextFork : CoveredFork N.sevm.benvStat.fork := by rw [nextSevm]; exact fork
        have nextRun : SFunc.RunExact fs' N.sevm N.devm g' (.halted s) := by
          rw [nextSevm, state]; exact rest
        obtain ⟨E, κ'', span, sameSevm, sameExn, endOk, endTree, endState⟩ :=
          ih placed nextTree (nextExn.trans success) nextFork nextRun
        exact ⟨E, κ'', (Exec.Deriv.ExecFreeUntil.ofStep edge
            (Blanc.Jinst.At.not_exec instruction)).trans span,
          sameSevm.trans nextSevm, sameExn.trans nextExn, endOk, endTree, endState⟩
  | @toZero f f' k cut ih =>
    intro F κ post s ok tree success fork run
    have instruction := ok.jumpiAt_of_branchTo tree
    obtain ⟨N, κ', edge, jumped, _, stateful, placed⟩ :=
      cursor_jinst_forward checked ok instruction success fork
    have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        ⟨F.devm, .branchTo f k, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
      rw [← tree]; exact stateful
    cases run with
    | succ _ _ _ _ rest => cases rest
    | zero d pop rest =>
      rcases ConfStep.of_branchTo step with ⟨t, actual, nextTree⟩ | ⟨t, w, nonzero, _, actual⟩
      · have state := popBurnBy_eq_of_length
          (Devm.PopBurnBy.of_popBurn actual (Devm.gasLeft_of_jumpi_run jumped)) pop rfl
        have nextSevm : N.sevm = F.sevm := Cursor.parentStep_sevm edge
        have nextExn : N.exn = F.exn := by cases edge <;> rfl
        have nextFork : CoveredFork N.sevm.benvStat.fork := by rw [nextSevm]; exact fork
        have nextRun : SFunc.RunExact fs' N.sevm N.devm f' (.halted s) := by
          rw [nextSevm, state]; exact rest
        obtain ⟨E, κ'', span, sameSevm, sameExn, endOk, endTree, endState⟩ :=
          ih placed nextTree (nextExn.trans success) nextFork nextRun
        exact ⟨E, κ'', (Exec.Deriv.ExecFreeUntil.ofStep edge
            (Blanc.Jinst.At.not_exec instruction)).trans span,
          sameSevm.trans nextSevm, sameExn.trans nextExn, endOk, endTree, endState⟩
      · have actualStack : F.devm.stack = [t, w] ++ N.devm.stack := actual.stack
        have syntheticStack : F.devm.stack = [d, 0] ++ _ := pop.stack
        rw [actualStack] at syntheticStack
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at syntheticStack
        exact (nonzero syntheticStack.2.1).elim
  | @toSucc f g g' k entry cut ih =>
    intro F κ post s ok tree success fork run
    have instruction := ok.jumpiAt_of_branchTo tree
    obtain ⟨N, κ', edge, jumped, _, stateful, placed⟩ :=
      cursor_jinst_forward checked ok instruction success fork
    have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
        ⟨F.devm, .branchTo f k, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
      rw [← tree]; exact stateful
    cases run with
    | zero _ _ rest => cases rest
    | succ d w nonzero pop rest =>
      rcases ConfStep.of_branchTo step with ⟨t, actual, _⟩ | ⟨t, w', _, actualEntry, actual⟩
      · have actualStack : F.devm.stack = [t, 0] ++ N.devm.stack := actual.stack
        have syntheticStack : F.devm.stack = [d, w] ++ _ := pop.stack
        rw [actualStack] at syntheticStack
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at syntheticStack
        exact (nonzero syntheticStack.2.1.symm).elim
      · have nextTree : κ'.f = g := Option.some.inj (actualEntry.symm.trans entry)
        have state := popBurnBy_eq_of_length
          (Devm.PopBurnBy.of_popBurn actual (Devm.gasLeft_of_jumpi_run jumped)) pop rfl
        have nextSevm : N.sevm = F.sevm := Cursor.parentStep_sevm edge
        have nextExn : N.exn = F.exn := by cases edge <;> rfl
        have nextFork : CoveredFork N.sevm.benvStat.fork := by rw [nextSevm]; exact fork
        have nextRun : SFunc.RunExact fs' N.sevm N.devm g' (.halted s) := by
          rw [nextSevm, state]; exact rest
        obtain ⟨E, κ'', span, sameSevm, sameExn, endOk, endTree, endState⟩ :=
          ih placed nextTree (nextExn.trans success) nextFork nextRun
        exact ⟨E, κ'', (Exec.Deriv.ExecFreeUntil.ofStep edge
            (Blanc.Jinst.At.not_exec instruction)).trans span,
          sameSevm.trans nextSevm, sameExn.trans nextExn, endOk, endTree, endState⟩

/-- A successful actual frame at a checked internal call enters the callee
entry with the exact state of the call's one-word pop and `gMid` charge. -/
theorem cursor_callNext_exact {code : ByteArray} {c : Cert}
    (checked : Cert.check code c = true) {F : Exec.Deriv} {κ : Cursor}
    (ok : CursorOK code c F κ) {k : Nat} {f : SFunc} (tree : κ.f = .callNext k f)
    {post : Devm} (success : F.exn = .ok post) (fork : CoveredFork F.sevm.benvStat.fork)
    {d : B256} {s : Devm} (pop : Devm.PopBurnBy [d] gMid F.devm s) :
    ∃ (N : Exec.Deriv) (κ' : Cursor),
      Exec.Deriv.ExecFreeUntil F N ∧ N.sevm = F.sevm ∧ N.exn = F.exn ∧
      CursorOK code c N κ' ∧ c.prog[k]? = some κ'.f ∧ N.devm = s := by
  have instruction := ok.jumpAt_of_callNext tree
  obtain ⟨N, κ', edge, jumped, _, stateful, placed⟩ :=
    cursor_jinst_forward checked ok instruction success fork
  have step : ConfStep (Ninst.RunWith (Cursor.DescOf F)) c.prog F.sevm
      ⟨F.devm, .callNext k f, κ.K.map Cont.f⟩ ⟨N.devm, κ'.f, κ'.K.map Cont.f⟩ := by
    rw [← tree]; exact stateful
  obtain ⟨t, entry, actual⟩ := ConfStep.of_callNext step
  have state := popBurnBy_eq_of_length
    (Devm.PopBurnBy.of_popBurn actual (Devm.gasLeft_of_jump_run jumped)) pop rfl
  exact ⟨N, κ', Exec.Deriv.ExecFreeUntil.ofStep edge (Blanc.Jinst.At.not_exec instruction),
    Cursor.parentStep_sevm edge, by cases edge <;> rfl, placed, entry, state⟩

end Blanc.Lift

namespace Blanc

/-- Two frame-entry-free spans from one node that both end at a decoded
frame-entering instruction end at the same node. -/
theorem Exec.Deriv.ExecFreeUntil.eq_of_execAt {root left right : Exec.Deriv}
    (leftFree : Exec.Deriv.ExecFreeUntil root left)
    (rightFree : Exec.Deriv.ExecFreeUntil root right) {x y : Jaune.Xinst}
    (leftAt : Jaune.Ninst.At left.sevm.code left.pc (.exec x))
    (rightAt : Jaune.Ninst.At right.sevm.code right.pc (.exec y)) : left = right :=
  Exec.Deriv.ParentPrefix.antisymm
    ((leftFree.2 right rightFree.1).resolve_right fun clean => clean y rightAt)
    ((rightFree.2 left leftFree.1).resolve_right fun clean => clean x leftAt)

end Blanc
