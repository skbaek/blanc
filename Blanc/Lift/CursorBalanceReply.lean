import Blanc.Lift.CursorSourceRun
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.StaticCallGuard

/-! Actual checked return-width guards and physical word decoding. -/

namespace Blanc.Lift
open Jaune

def returnWordGuardLine (destination : Bytes) (le : destination.length ≤ 32) : List Ninst :=
  [.reg .pop, .reg .pop, .reg .pop, .reg .pop] ++
    returnWidthCompareLine ++ [.push destination le]

/-- The same actual successful suffix proves its returndata width and advances
through the checked width guard and physical memory decoder. -/
theorem CursorStateAt.returnWord {code : ByteArray} {c : Cert} {start : Exec.Deriv}
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
        (Bytes.toB256 (M.read p.toNat 32).1 :: R) M K) := by
  obtain ⟨G, state⟩ := cut.state
  obtain ⟨outcome, source⟩ := cut.placed.sourceRun checked
    (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
  rw [cut.tree, state, cut.sevm_eq] at source
  have source' := SFunc.runP_iff_runCutP_nil.mp source
  have width := (returnWidthGuard_invP destination le shape
    (fun step => step.toRun) mem bound noShort source').1
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest checked success fork
  obtain ⟨guard⟩ := opened.line checked success fork
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
  obtain ⟨decoder⟩ := guard.branchSucc checked success fork (by decide : (1 : B256) ≠ 0)
  rw [decode] at decoder
  obtain ⟨entry⟩ := decoder.dest checked success fork
  obtain ⟨loaded⟩ := entry.line checked success fork [.reg .pop, .reg .mload] rfl
    (by intro ni member xi equal; subst ni; simp at member)
    (b' := b) (S' := Bytes.toB256 (M.read p.toNat 32).1 :: R) (M' := M) (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line; obtain ⟨_, rfl⟩ := ri_pop step
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      obtain ⟨gas', state⟩ := ri_mload step
      rw [mem.read_self fit] at state
      exact ⟨gas', state⟩)
  exact ⟨width, ⟨loaded⟩⟩


def callFlagGuardLine (destination : Bytes) (le : destination.length ≤ 32) : List Ninst :=
  [.reg .iszero, .reg (.dup 0), .reg .iszero, .push destination le]

/-- Successful execution of the supplied actual reply suffix forces its real
flag to one and reaches the checked success continuation in that same frame. -/
theorem CursorStateAt.callFlag {code : ByteArray} {c : Cert} {start : Exec.Deriv}
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
      Nonempty (CursorStateAt code c start returnTree b (0 :: a :: x :: y :: R) M K) := by
  have one : flag = 1 := by
    obtain ⟨G, state⟩ := cut.state
    obtain ⟨outcome, source⟩ := cut.placed.sourceRun checked
      (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
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
  obtain ⟨guard⟩ := cut.line checked success fork (callFlagGuardLine destination le) shape
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
  exact guard.branchSucc checked success fork (by decide : (1 : B256) ≠ 0)

end Blanc.Lift
