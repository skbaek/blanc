import Blanc.Lift.UniswapV2Pair.SwapCanonical
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.ExactWalkSolc

/-! Forward (gas-exact) component schedule of the swap entry: the PC0 guards, the selector
dispatch to `t_01be_c99` and the ABI wrapper up to the body's internal call, and the wrapper's
`STOP`. Given an exact run of the body `t_0683_c54` from the decoded entry stack (the forward
environment), the original bytes run from pc zero with an exact gas charge, and that run
satisfies the canonical swap frame. The body's own forward walk (lock, reserves, transfers,
callback, balance queries, pricing check, update, logs, unlock) is not constructed here: it
is the premise. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The literal swap PC0 guard and selector path: 166 gas before `t_01be_c99`. -/
theorem swapDispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (body : SFunc.RunExact cert.prog sevm
      (St b [0x022c0d9f] getterInitMemory G) t_01be_c99 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 166)) t_0000_c0 o := by
  rw [show G + 166 = (G + 103) + 63 by omega]
  refine getterString_guards_exact value size ?_
  unfold t_001a_c0
  apply rx_push (w := 0) rfl (by decide)
  apply rx_calldataload (by decide)
  apply rx_push (w := 224) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_shr (v := 0x022c0d9f) selector (by decide)
  apply rx_dup1 (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x00f9) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_00f9_c0
  apply rx_dest
  apply rx_dup1 (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x0166) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_0166_c0
  apply rx_dest
  apply rx_dup1 (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x095ea7b3) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_gt (v := 1) (by decide) (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_push (w := 0x0197) rfl (by simp only [List.length_cons,List.length_nil]; decide)
  apply rx_branch_succ (by decide : (1 : B256) ≠ 0)
  unfold t_0197_c0
  apply rx_dest
  exact cmp_hit (tgt := t_01be_c99) rfl rfl body

/-- One straight-line forward step of the swap walks: a jump destination, push, dup, swap, pop,
calldata read, or arithmetic/comparison over the concrete stack. -/
macro "swap_rx" : tactic => `(tactic| first
  | apply rx_dest
  | apply rx_push rfl (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_dup rfl (by simp only [List.length_cons, List.length_nil]; decide)
  | (apply rx_swap rfl; dsimp only [List.set])
  | apply rx_pop
  | apply rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_add (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_sub (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_lt rfl (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_gt rfl (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_iszero rfl (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_and rfl (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_or rfl (by simp only [List.length_cons, List.length_nil]; decide)
  | apply rx_mul rfl (by simp only [List.length_cons, List.length_nil]; decide))

theorem swap_iszero_lt {x y : B256} (h : y.toNat ≤ x.toNat) :
    B256.eqCheck (B256.ltCheck x y) 0 ≠ 0 := by
  have zero : B256.ltCheck x y = 0 := by
    have notLt : ¬ x < y := by
      rw [B256.lt_iff_toNat_lt_toNat]
      omega
    unfold B256.ltCheck
    simp only [notLt, ite_false]
  rw [zero]
  decide

theorem swap_gt_zero {x y : B256} (h : x.toNat ≤ y.toNat) : B256.gtCheck x y = 0 := by
  have notGt : ¬ x > y := by
    change ¬ y < x
    rw [B256.lt_iff_toNat_lt_toNat]
    omega
  unfold B256.gtCheck
  simp only [notGt, ite_false]

theorem swap_iszero_gt {x y : B256} (h : x.toNat ≤ y.toNat) :
    B256.eqCheck (B256.gtCheck x y) 0 ≠ 0 := by
  rw [swap_gt_zero h]
  decide

/-- The ABI wrapper `t_01be..t_024c`: under the four literal guards it decodes the entry and
calls the body with `swapBodyStack`; the wrapper's own instructions cost 279 gas. -/
theorem swapAbi_exact {sevm : Sevm} {b post : Devm} {G : Nat} {o : Outcome}
    (guards : SwapAbiGuards sevm)
    (callee : SFunc.RunExact cert.prog sevm
      (St b (swapBodyStack sevm) getterInitMemory G) t_0683_c54 (.returned post))
    (tail : SFunc.RunExact cert.prog sevm post t_0257_c99 o) :
    SFunc.RunExact cert.prog sevm (St b [0x022c0d9f] getterInitMemory (G + 279)) t_01be_c99 o := by
  unfold t_01be_c99
  repeat swap_rx
  refine rx_branch_succ (swap_iszero_lt guards.args) ?_
  unfold t_01d4_c99
  repeat swap_rx
  refine rx_branch_succ ?_ ?_
  · rw [show Bytes.toB256 [4] + Bytes.toB256 [96] = (100 : B256) from by decide]
    exact swap_iszero_gt guards.offset
  unfold t_0218_c99
  repeat swap_rx
  refine rx_branch_succ ?_ ?_
  · rw [show Bytes.toB256 [4] + Bytes.toB256 [96] = (100 : B256) from by decide]
    exact swap_iszero_gt guards.head
  unfold t_022a_c99
  repeat swap_rx
  refine rx_branch_succ ?_ ?_
  · have mulOne : ∀ x : B256, x * 1 = x := by
      intro x
      apply B256.toNat_inj
      rw [B256.toNat_mul, show (1 : B256).toNat = 1 from rfl, Nat.mul_one,
        Nat.lo_eq_of_lt x.toNat_lt]
    rw [show Bytes.toB256 [4] + Bytes.toB256 [96] = (100 : B256) from by decide,
      show Bytes.toB256 [1] = (1 : B256) from rfl, mulOne,
      show B256.gtCheck (Sevm.dataWord sevm (Bytes.toB256 [4] + Sevm.dataWord sevm 100))
        (Bytes.toB256 [1, 0, 0, 0, 0]) = 0 from swap_gt_zero guards.length,
      show B256.gtCheck (Bytes.toB256 [32] + (Bytes.toB256 [4] + Sevm.dataWord sevm 100) +
        Sevm.dataWord sevm (Bytes.toB256 [4] + Sevm.dataWord sevm 100))
        (Bytes.toB256 [4] + (Nat.toB256 (List.length sevm.data) - Bytes.toB256 [4])) = 0
        from swap_gt_zero guards.tail]
    decide
  unfold t_024c_c99
  repeat swap_rx
  exact rx_callRet rfl callee tail

/-- PC0 to the wrapper `STOP`: 446 gas around an exact body run. -/
theorem swapPc0_exact {sevm : Sevm} {b x : Devm} {R : List B256} {M : Mem} {G g : Nat}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    (body : SFunc.RunExact cert.prog sevm (St b (swapBodyStack sevm) getterInitMemory G)
      t_0683_c54 (.returned (St x R M (g + 1)))) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 279 + 166)) t_0000_c0
      (.halted (St x R M g)) := by
  refine swapDispatch_exact value size selector (swapAbi_exact guards body ?_)
  unfold t_0257_c99
  exact rx_dest rx_stop

/-- **Swap forward component schedule.** Given the forward environment of the swap body (an
exact run of `t_0683_c54` from the decoded entry stack, returning with at least the wrapper's
`STOP` gas), together with the nonpayable, size and selector guards and the four literal ABI
guards, a successful pc-zero run of the original bytes exists with the exact initial gas
`G + 445`, ending in the body's returned world with its residual gas. That same run satisfies
the canonical swap frame with foreign storage (`swap_bytecode_exact_consumes_own`) under
trace-local HASH-T over its own trace universe. This is a component schedule: it constructs
the dispatch and wrapper and consumes the body run as a premise; it does not construct the
body (the reachable-state gas theorem stays original-host work).
CROSS-HOST: conditional on `SwapCallReplyShort`. -/
theorem swap_bytecode_forward_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b x : Devm} {R : List B256} {M : Mem} {G g : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    (body : SFunc.RunExact cert.prog sevm (St b (swapBodyStack sevm) getterInitMemory G)
      t_0683_c54 (.returned (St x R M (g + 1)))) :
    ∃ run : Exec 0 sevm (St b [] Mem.empty (G + 279 + 166)) (.ok (St x R M g)),
      (WriterInj (WriterExtend K
          (swapTraceKeys ⟨0, sevm, St b [] Mem.empty (G + 279 + 166), _, run⟩)) →
        WriterApart (WriterExtend K
          (swapTraceKeys ⟨0, sevm, St b [] Mem.empty (G + 279 + 166), _, run⟩)) →
        SwapCallReplyShort ⟨0, sevm, St b [] Mem.empty (G + 279 + 166), _, run⟩ sevm →
        (∀ a, a ≠ sevm.currentTarget → (swapPrefixWorld sevm b).getStor a = b.getStor a) ∧
        SwapCanonicalBody
          (fun d => ∀ a, a ≠ sevm.currentTarget → (St x R M g).getStor a = d.getStor a)
          K current invocation run) := by
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok codeEq fork
    ⟨t_0000_c0, rfl, swapPc0_exact value size selector guards body⟩
  exact ⟨run, fun inj apart short =>
    swap_bytecode_exact_consumes_own invocation rep sem image installed freshOutput codeEq fork
      selector run inj apart short⟩

end Blanc.Lift.UniswapV2Pair
