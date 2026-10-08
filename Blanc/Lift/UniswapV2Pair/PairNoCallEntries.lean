import Blanc.Lift.UniswapV2Pair.PairDispatchCursor
import Blanc.Lift.CursorNoExecSuffix

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Literal rows of the Pair dispatcher used by the call-free entries. -/
inductive PairNoCallComparison
  | at002b | at0036 | at0041

def PairNoCallComparison.bytes : PairNoCallComparison → List UInt8
  | .at002b => [0xba, 0x9a, 0x7a, 0x56]
  | .at0036 | .at0041 => [0xd2, 0x12, 0x20, 0xa7]

def PairNoCallComparison.target : PairNoCallComparison → List UInt8
  | .at002b => [0x00, 0x97]
  | .at0036 => [0x00, 0x71]
  | .at0041 => [0x05, 0xda]

def PairNoCallComparison.op : PairNoCallComparison → Rinst
  | .at0041 => .eq
  | _ => .gt

def PairNoCallComparison.line (q : PairNoCallComparison) : List Ninst :=
  [.reg (.dup 0), .push q.bytes (by cases q <;> decide),
   .reg q.op, .push q.target (by cases q <;> decide)]

def PairNoCallComparison.tail : PairNoCallComparison → SFunc
  | .at002b => .branch t_0036_c0 t_0097_c0
  | .at0036 => .branch t_0041_c0 t_0071_c0
  | .at0041 => .branchTo t_004c_c0 75

def PairNoCallComparison.body (q : PairNoCallComparison) : SFunc :=
  q.line.foldr SFunc.next q.tail

def PairNoCallComparison.compute (q : PairNoCallComparison) (sel : B256) : B256 :=
  match q with
  | .at0041 => B256.eqCheck (Bytes.toB256 q.bytes) sel
  | _ => B256.gtCheck (Bytes.toB256 q.bytes) sel

/-- Each literal row retains the selector, memory and complete world. -/
theorem PairNoCallComparison.line_inv {sevm : Sevm} {b d : Devm}
    {S : List B256} {M : Mem} {G : Nat} (q : PairNoCallComparison) (sel : B256)
    (run : Line.Run sevm (St b (sel :: S) M G) q.line d) :
    ∃ G', d = St b (Bytes.toB256 q.target :: q.compute sel :: sel :: S) M G' := by
  cases q <;> dsimp only [PairNoCallComparison.line, PairNoCallComparison.bytes,
    PairNoCallComparison.target, PairNoCallComparison.op, PairNoCallComparison.compute] at run ⊢
  all_goals
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_dup rfl step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨_, rfl⟩ := ri_push step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    first
    | obtain ⟨_, rfl⟩ := ri_gt step
    | obtain ⟨_, rfl⟩ := ri_eq step
    obtain ⟨_, step, run⟩ := Line.of_run_cons run
    obtain ⟨gas, state⟩ := ri_push step
    cases run
    exact ⟨gas, state⟩

/-- The literal comparison is traversed on the original checked cursor. -/
theorem PairNoCallComparison.cut {root : Exec.Deriv} {b post : Devm}
    {S : List B256} {M : Mem} {K : List SFunc} (q : PairNoCallComparison) (sel : B256)
    (cut : CursorStateAt code cert root q.body b (sel :: S) M K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    Nonempty (CursorStateAt code cert root q.tail b
      (Bytes.toB256 q.target :: q.compute sel :: sel :: S) M K) := by
  apply cut.line cert_check success fork q.line rfl
  · intro n member x equal
    subst n
    cases q <;> simp only [PairNoCallComparison.line, PairNoCallComparison.op, List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self] at member
  · exact q.line_inv sel

/-- The actual successful token1 selector reaches its selected function with
an empty continuation stack after a frame-free original-root prefix. -/
theorem token1_noCall_entry {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd21220a7)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    Nonempty (CursorStateAt code cert
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
      t_05da_c75 b [0xd21220a7] getterInitMemory []) := by
  obtain ⟨first⟩ := pair_dispatch_comparison_cursor_state codeEq fork selector (by decide) run
  obtain ⟨guard⟩ := PairNoCallComparison.at002b.cut 0xd21220a7 first rfl fork
  change CursorStateAt code cert _ (.branch t_0036_c0 t_0097_c0) b
    (0x97 :: 0 :: [0xd21220a7]) getterInitMemory [] at guard
  obtain ⟨second⟩ := guard.branchZero cert_check rfl fork
  obtain ⟨guard⟩ := PairNoCallComparison.at0036.cut 0xd21220a7 second rfl fork
  change CursorStateAt code cert _ (.branch t_0041_c0 t_0071_c0) b
    (0x71 :: 0 :: [0xd21220a7]) getterInitMemory [] at guard
  obtain ⟨third⟩ := guard.branchZero cert_check rfl fork
  obtain ⟨guard⟩ := PairNoCallComparison.at0041.cut 0xd21220a7 third rfl fork
  change CursorStateAt code cert _ (.branchTo t_004c_c0 75) b
    (0x5da :: 1 :: [0xd21220a7]) getterInitMemory [] at guard
  exact guard.toSucc cert_check rfl fork (by decide) rfl

/-- Every original same-frame token1 occurrence is free of external instructions.
The certificate covers the real selected suffix and its empty continuation stack. -/
theorem token1_root_noExec {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xd21220a7)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∀ N, Exec.Deriv.ParentPrefix ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ N →
      ∀ x, ¬ Ninst.At N.sevm.code N.pc (.exec x) := by
  obtain ⟨cut⟩ := token1_noCall_entry codeEq fork selector run
  have suffix := cut.placed.noExecSuffix cert_check (cut.sevm_eq ▸ fork)
    (E := [28]) (by decide) (by rw [cut.tree]; decide)
    (by rw [cut.continuations]; simp only [List.not_mem_nil, false_implies, implies_true])
  intro N reached x decoded
  rcases cut.free.2 N reached with after | clean
  · exact suffix N after x decoded
  · exact clean x decoded

end Blanc.Lift.UniswapV2Pair
