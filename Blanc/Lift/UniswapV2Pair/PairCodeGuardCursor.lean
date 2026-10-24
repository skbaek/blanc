import Blanc.Lift.HistCursorReturn
import Blanc.Lift.CursorSourceRun
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.SyncWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

private theorem pair_code_guard_compare_cursor_stateH {start : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {token : B256} {K : List SFunc} {f tail : SFunc}
    (cut : CursorStateAt code cert start f b (token :: S) M K)
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : f = syncCodeGuardLine.foldr SFunc.next (.next (.push destination le) tail)) :
    Nonempty (CursorStateAt code cert start tail (accountAccessH start.sevm b token.toAdr)
      (Bytes.toB256 destination ::
        B256.eqCheck (B256.eqCheck (b.getCode token.toAdr).size.toB256 0) 0 ::
        B256.eqCheck (b.getCode token.toAdr).size.toB256 0 :: S) M K) := by
  obtain ⟨compared⟩ := cut.lineH cert_check success stateGas syncCodeGuardLine shape
    (by intro n member x equal; subst n
        simp only [syncCodeGuardLine, List.mem_cons, List.not_mem_nil,
          reduceCtorEq, or_self] at member)
    (syncCodeGuardLine_invH bal)
  obtain ⟨guard⟩ := compared.lineH cert_check success stateGas [.push destination le] rfl
    (by intro n member x equal; subst n
        simp only [List.mem_singleton, reduceCtorEq] at member)
    (by intro gas d line
        obtain ⟨_, step, line⟩ := Line.of_run_cons line
        cases line
        exact ri_push step)
  exact ⟨guard⟩


theorem pair_code_guard_cursor_stateH {start : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {token : B256} {K : List SFunc}
    {f failed callTree : SFunc}
    (cut : CursorStateAt code cert start f b (token :: S) M K)
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : f = syncCodeGuardLine.foldr SFunc.next
      (.next (.push destination le) (.branch failed callTree)))
    (noFail : failed.noOk = true) :
    (b.getCode token.toAdr).size.toB256 ≠ 0 ∧
      Nonempty (CursorStateAt code cert start callTree
        (accountAccessH start.sevm b token.toAdr) (0 :: S) M K) := by
  obtain ⟨guard⟩ := pair_code_guard_compare_cursor_stateH cut success stateGas bal destination le shape
  obtain ⟨G, state⟩ := guard.state
  obtain ⟨outcome, source⟩ := guard.placed.sourceRunH cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact stateGas)
  rw [guard.tree, state, guard.sevm_eq] at source
  rcases ric_branchP (SFunc.runP_iff_runCutP_nil.mp source) with
    ⟨_, _, failure⟩ | ⟨accepted, _, tail⟩
  · exact (failure.false_of_noOk noFail).elim
  · have zero := eq_zero_of_iszero_ne_zero accepted
    have nonzero : (b.getCode token.toAdr).size.toB256 ≠ 0 := by
      intro empty
      rw [empty, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
      exact (by decide : (1 : B256) ≠ 0) zero
    rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at guard
    exact ⟨nonzero, guard.branchSuccH cert_check success stateGas (by decide)⟩

/-- The supplied actual Pair code guard derives code presence from its own
successful branch and preserves the full warmed state and continuations. -/
theorem pair_code_guard_cursor_state {start : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {token : B256} {K : List SFunc}
    {f failed callTree : SFunc}
    (cut : CursorStateAt code cert start f b (token :: S) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : f = syncCodeGuardLine.foldr SFunc.next
      (.next (.push destination le) (.branch failed callTree)))
    (noFail : failed.noOk = true) :
    (b.getCode token.toAdr).size.toB256 ≠ 0 ∧
      Nonempty (CursorStateAt code cert start callTree
        (temporalAccountAccessBase b token.toAdr) (0 :: S) M K) := by
  simpa only [accountAccessH_of_eip2929 fork.rules_access] using
    pair_code_guard_cursor_stateH cut success fork.rules_stateGas_none fork.rules_bal_none destination le shape noFail


theorem pair_code_guard_to_cursor_stateH {start : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {token : B256} {K : List SFunc}
    {f failed callTree : SFunc} {k : Nat}
    (cut : CursorStateAt code cert start f b (token :: S) M K)
    (success : start.exn = .ok post) (stateGas : start.sevm.benvStat.rules.stateGas = none)
    (bal : start.sevm.benvStat.rules.bal = none)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : f = syncCodeGuardLine.foldr SFunc.next
      (.next (.push destination le) (.branchTo failed k)))
    (noFail : failed.noOk = true) (lookup : cert.prog[k]? = some callTree) :
    (b.getCode token.toAdr).size.toB256 ≠ 0 ∧
      Nonempty (CursorStateAt code cert start callTree
        (accountAccessH start.sevm b token.toAdr) (0 :: S) M K) := by
  obtain ⟨guard⟩ := pair_code_guard_compare_cursor_stateH cut success stateGas bal destination le shape
  obtain ⟨G, state⟩ := guard.state
  obtain ⟨outcome, source⟩ := guard.placed.sourceRunH cert_check
    (guard.exn_eq.trans success) (by rw [guard.sevm_eq]; exact stateGas)
  rw [guard.tree, state, guard.sevm_eq] at source
  have accepted : B256.eqCheck (B256.eqCheck (b.getCode token.toAdr).size.toB256 0) 0 ≠ 0 := by
    cases SFunc.runP_iff_runCutP_nil.mp source with
    | toZero _ pop body =>
      exact (body.false_of_noOk noFail).elim
    | toSucc _ _ nonzero _ _ pop body =>
      exact (St.of_pop2 pop).2.1 ▸ nonzero
  have zero := eq_zero_of_iszero_ne_zero accepted
  have nonzero : (b.getCode token.toAdr).size.toB256 ≠ 0 := by
    intro empty
    rw [empty, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at zero
    exact (by decide : (1 : B256) ≠ 0) zero
  rw [zero, show B256.eqCheck (0 : B256) 0 = 1 from by decide] at guard
  exact ⟨nonzero, guard.toSuccH cert_check success stateGas (by decide) lookup⟩

/-- A referenced code guard reaches its actual checked entry and preserves the
complete warmed state; successful execution supplies its own code-presence fact. -/
theorem pair_code_guard_to_cursor_state {start : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {token : B256} {K : List SFunc}
    {f failed callTree : SFunc} {k : Nat}
    (cut : CursorStateAt code cert start f b (token :: S) M K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (destination : Bytes) (le : destination.length ≤ 32)
    (shape : f = syncCodeGuardLine.foldr SFunc.next
      (.next (.push destination le) (.branchTo failed k)))
    (noFail : failed.noOk = true) (lookup : cert.prog[k]? = some callTree) :
    (b.getCode token.toAdr).size.toB256 ≠ 0 ∧
      Nonempty (CursorStateAt code cert start callTree
        (temporalAccountAccessBase b token.toAdr) (0 :: S) M K) := by
  simpa only [accountAccessH_of_eip2929 fork.rules_access] using
    pair_code_guard_to_cursor_stateH cut success fork.rules_stateGas_none fork.rules_bal_none destination le shape noFail lookup


end Blanc.Lift.UniswapV2Pair
