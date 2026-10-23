import Blanc.Lift.HistCursorReturn
import Blanc.Lift.CursorGasCall
import Blanc.Lift.CursorBalanceReply

/-!
# Historical GAS-to-call and call-reply cursor forwarders

`CursorStateAt.gasCall`, `CursorStateAt.returnWord` and `CursorStateAt.callFlag` contain no call
semantics of their own: they forward `CoveredFork` to the cursor cuts, which read only
`rules.stateGas = none`. The `…H` forms take that fact alone through `HistCursorCuts` and
`HistCursorReturn`; each `_covered` form recovers the modern statement verbatim.

Nothing here mentions a contract.
-/

namespace Blanc.Lift
open Jaune

/-- `CursorStateAt.gasCall` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.gasCallH {code : ByteArray} {c : Cert}
    {root start : Exec.Deriv} {b post : Devm} {S : List B256}
    {M : Mem} {K : List SFunc} {x : Xinst} {tail : SFunc}
    (cut : CursorStateAt code c start (.next (.reg .gas) (.next (.exec x) tail)) b S M K)
    (checked : Cert.check code c = true) (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (hsg : start.sevm.benvStat.rules.stateGas = none) :
    ∃ (step : CallOccurrenceStep root x) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil start step.occurrence.node ∧
      step.occurrence.node.sevm = start.sevm ∧
      step.occurrence.node.exn = start.exn ∧
      step.occurrence.node.devm = St b (gas.toB256 :: S) M gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) start.sevm
        step.occurrence.node.devm (.exec x) step.returned.devm ∧
      CursorOK code c step.returned cursor ∧ cursor.f = tail ∧
      cursor.K.map Cont.f = K := by
  obtain ⟨call, κ, _, _, sameSevm, sameExn, placed, tree, line, sameK, free⟩ :=
    cursor_nexts_line_cont_free_forwardH checked cut.placed [.reg .gas]
      (.next (.exec x) tail) cut.tree (cut.exn_eq.trans success)
      (cut.sevm_eq ▸ hsg)
  obtain ⟨g, state⟩ := cut.state
  rw [cut.sevm_eq, state] at line
  obtain ⟨_, primitive, line⟩ := Line.of_run_cons line
  cases line
  obtain ⟨gas, callState⟩ := ri_gas_remaining primitive
  have gap := cut.free.trans (free (by
    intro n member y equal
    simp only [List.mem_singleton, equal, reduceCtorEq] at member))
  have env := sameSevm.trans cut.sevm_eq
  have outcome := sameExn.trans cut.exn_eq
  obtain ⟨step, cursor, nodeEq, _, primitiveCall, synthetic, _, returned⟩ :=
    cursor_next_call_occurrence_forwardH checked (reached.trans gap.1) placed tree
      (outcome.trans success) (env ▸ hsg)
  have nextShape : cursor.f = tail ∧ cursor.K = κ.K := by
    rcases κ with ⟨f, pc, a, m, pending⟩
    dsimp only at tree
    subst f
    cases synthetic
    exact ⟨rfl, rfl⟩
  refine ⟨step, cursor, gas, ?_, ?_, ?_, ?_, ?_, returned, nextShape.1, ?_⟩
  · rw [nodeEq]; exact gap
  · rw [nodeEq]; exact env
  · rw [nodeEq]; exact outcome
  · rw [nodeEq]; exact callState
  · simpa only [nodeEq, env] using primitiveCall
  · rw [nextShape.2, sameK]; exact cut.continuations

theorem CursorStateAt.gasCallH_covered {code : ByteArray} {c : Cert}
    {root start : Exec.Deriv} {b post : Devm} {S : List B256}
    {M : Mem} {K : List SFunc} {x : Xinst} {tail : SFunc}
    (cut : CursorStateAt code c start (.next (.reg .gas) (.next (.exec x) tail)) b S M K)
    (checked : Cert.check code c = true) (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root x) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil start step.occurrence.node ∧
      step.occurrence.node.sevm = start.sevm ∧
      step.occurrence.node.exn = start.exn ∧
      step.occurrence.node.devm = St b (gas.toB256 :: S) M gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) start.sevm
        step.occurrence.node.devm (.exec x) step.returned.devm ∧
      CursorOK code c step.returned cursor ∧ cursor.f = tail ∧
      cursor.K.map Cont.f = K :=
  cut.gasCallH checked reached success fork.rules_stateGas_none

/-- `CursorStateAt.returnWord` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.returnWordH {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {returnTree shortTree decodeTree tail : SFunc} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {a x y z p : B256} {n : Nat}
    (cut : CursorStateAt code c start returnTree b (a :: x :: y :: z :: R) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : returnTree = .dest ((returnWordGuardLine destination le).foldr
      SFunc.next (.branch shortTree decodeTree)))
    (decode : decodeTree = .dest (.next (.reg .pop) (.next (.reg .mload) tail)))
    (mem : PtrMem p n M) (fit : p.toNat + 32 ≤ n)
    (bound : b.returnData.length < 2 ^ 256) (noShort : shortTree.noOk = true) :
    32 ≤ b.returnData.length ∧
      Nonempty (CursorStateAt code c start tail b
        (Bytes.toB256 (M.read p.toNat 32).1 :: R) M K) := by
  obtain ⟨G, state⟩ := cut.state
  obtain ⟨outcome, source⟩ := cut.placed.sourceRunH checked
    (cut.exn_eq.trans success) (cut.sevm_eq ▸ hsg)
  rw [cut.tree, state, cut.sevm_eq] at source
  have source' := SFunc.runP_iff_runCutP_nil.mp source
  have width := (returnWidthGuard_invP destination le shape
    (fun step => step.toRun) mem bound noShort source').1
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.destH checked success hsg
  obtain ⟨guard⟩ := opened.lineH checked success hsg
    (returnWordGuardLine destination le) rfl
    (by
      intro ni member xi equal; subst ni
      simp only [returnWordGuardLine, returnWidthCompareLine, List.mem_append,
        List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := Bytes.toB256 destination ::
      B256.eqCheck (B256.ltCheck b.returnData.length.toB256 32) 0 ::
      b.returnData.length.toB256 :: p :: R) (M' := M) (by
      intro gas d line
      dsimp only [returnWordGuardLine] at line
      obtain ⟨_, pops, line⟩ := of_run_append
        [.reg .pop, .reg .pop, .reg .pop, .reg .pop] line
      obtain ⟨_, step, pops⟩ := Line.of_run_cons pops; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, pops⟩ := Line.of_run_cons pops; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, pops⟩ := Line.of_run_cons pops; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, pops⟩ := Line.of_run_cons pops; obtain ⟨_, rfl⟩ := ri_pop step
      cases pops
      obtain ⟨_, comparison, line⟩ := of_run_append returnWidthCompareLine line
      obtain ⟨_, compared⟩ := returnWidthCompareLine_inv mem comparison
      rw [compared] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      exact ri_push step)
  have ltZero : B256.ltCheck b.returnData.length.toB256 32 = 0 := by
    rw [B256.ltCheck, ite_eq_right]
    rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt bound]
    change ¬ b.returnData.length < 32
    omega
  have condition : B256.eqCheck (B256.ltCheck b.returnData.length.toB256 32) 0 = 1 := by
    rw [ltZero]
    decide
  rw [condition] at guard
  obtain ⟨decoder⟩ := guard.branchSuccH checked success hsg (by decide : (1 : B256) ≠ 0)
  rw [decode] at decoder
  obtain ⟨entry⟩ := decoder.destH checked success hsg
  obtain ⟨loaded⟩ := entry.lineH checked success hsg [.reg .pop, .reg .mload] rfl
    (by intro ni member xi equal; subst ni; simp only [List.mem_cons,
      List.not_mem_nil, reduceCtorEq, or_self] at member)
    (b' := b) (S' := Bytes.toB256 (M.read p.toNat 32).1 :: R) (M' := M) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      obtain ⟨gas', state⟩ := ri_mload step
      rw [mem.read_self fit] at state
      exact ⟨gas', state⟩)
  exact ⟨width, ⟨loaded⟩⟩

theorem CursorStateAt.returnWordH_covered {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {returnTree shortTree decodeTree tail : SFunc} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {a x y z p : B256} {n : Nat}
    (cut : CursorStateAt code c start returnTree b (a :: x :: y :: z :: R) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : returnTree = .dest ((returnWordGuardLine destination le).foldr
      SFunc.next (.branch shortTree decodeTree)))
    (decode : decodeTree = .dest (.next (.reg .pop) (.next (.reg .mload) tail)))
    (mem : PtrMem p n M) (fit : p.toNat + 32 ≤ n)
    (bound : b.returnData.length < 2 ^ 256) (noShort : shortTree.noOk = true) :
    32 ≤ b.returnData.length ∧
      Nonempty (CursorStateAt code c start tail b
        (Bytes.toB256 (M.read p.toNat 32).1 :: R) M K) :=
  cut.returnWordH checked success fork.rules_stateGas_none destination le shape decode mem fit
    bound noShort

/-- `CursorStateAt.callFlag` from `rules.stateGas = none` alone. -/
theorem CursorStateAt.callFlagH {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f failedTree returnTree : SFunc} {b post : Devm} {R : List B256}
    {M : Mem} {K : List SFunc} {flag a x y : B256}
    (cut : CursorStateAt code c start f b (flag :: a :: x :: y :: R) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (hsg : start.sevm.benvStat.rules.stateGas = none)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : f = (callFlagGuardLine destination le).foldr SFunc.next
      (.branch failedTree returnTree))
    (flag01 : flag = 0 ∨ flag = 1) (noFail : failedTree.noOk = true) :
    flag = 1 ∧
      Nonempty (CursorStateAt code c start returnTree b (0 :: a :: x :: y :: R) M K) := by
  have one : flag = 1 := by
    obtain ⟨G, state⟩ := cut.state
    obtain ⟨outcome, source⟩ := cut.placed.sourceRunH checked
      (cut.exn_eq.trans success) (cut.sevm_eq ▸ hsg)
    rw [cut.tree, state, cut.sevm_eq] at source
    simp only [shape] at source
    have run := SFunc.runP_iff_runCutP_nil.mp source
    dsimp only [callFlagGuardLine, List.foldr] at run
    obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero step.toRun
    obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl step.toRun
    obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero step.toRun
    obtain ⟨_, step, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push step.toRun
    rcases ric_branchP run with ⟨_, _, failed⟩ | ⟨accepted, _, _⟩
    · exact (failed.false_of_noOk noFail).elim
    · have zeroFlag : B256.eqCheck flag 0 = 0 := eq_zero_of_iszero_ne_zero accepted
      rcases flag01 with zero | one
      · rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zeroFlag
        exact ((by decide : (1 : B256) ≠ 0) zeroFlag).elim
      · exact one
  refine ⟨one, ?_⟩
  rw [one] at cut
  obtain ⟨guard⟩ := cut.lineH checked success hsg (callFlagGuardLine destination le) shape
    (by
      intro ni member xi equal; subst ni
      simp only [callFlagGuardLine, List.mem_cons, List.not_mem_nil, reduceCtorEq,
        or_self] at member)
    (b' := b) (S' := Bytes.toB256 destination :: 1 :: 0 :: a :: x :: y :: R) (M' := M) (by
      intro gas d line
      dsimp only [callFlagGuardLine] at line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_dup rfl step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_iszero step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨gas', state⟩ := ri_push step
      cases line
      exact ⟨gas', by simpa only [show B256.eqCheck 1 0 = 0 from by decide,
        show B256.eqCheck 0 0 = 1 from by decide] using state⟩)
  exact guard.branchSuccH checked success hsg (by decide : (1 : B256) ≠ 0)

theorem CursorStateAt.callFlagH_covered {code : ByteArray} {c : Cert} {start : Exec.Deriv}
    {f failedTree returnTree : SFunc} {b post : Devm} {R : List B256}
    {M : Mem} {K : List SFunc} {flag a x y : B256}
    (cut : CursorStateAt code c start f b (flag :: a :: x :: y :: R) M K)
    (checked : Cert.check code c = true) (success : start.exn = .ok post)
    (fork : CoveredFork start.sevm.benvStat.fork)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : f = (callFlagGuardLine destination le).foldr SFunc.next
      (.branch failedTree returnTree))
    (flag01 : flag = 0 ∨ flag = 1) (noFail : failedTree.noOk = true) :
    flag = 1 ∧
      Nonempty (CursorStateAt code c start returnTree b (0 :: a :: x :: y :: R) M K) :=
  cut.callFlagH checked success fork.rules_stateGas_none destination le shape flag01 noFail

end Blanc.Lift
