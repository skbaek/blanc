import Blanc.Lift.UniswapV2Pair.SwapCanonical
import Blanc.Lift.UniswapV2Pair.GetterStringWalk
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.UniswapV2Pair.SwapForwardFront
import Blanc.Lift.UniswapV2Pair.SwapForwardBack

/-! Forward (gas-exact) schedule of the swap entry: the PC0 guards, the selector dispatch to
`t_01be_c99`, the ABI wrapper up to the body's internal call and the wrapper's `STOP`, around
the body's own forward run (`swapBody_exact`: the front half to the join, `SwapForwardFront`,
and the back half to the return, `SwapForwardBack`). The callee frames (token transfers,
callback, balance queries) are forward-environment premises; the moved-pointer `_safeTransfer`
helper is `safeTransfer_dynamic_forward` (the CALL reply bound is derived from the actual
68-byte `CALL`). The original bytes run from pc zero
with an exact gas charge, and that run satisfies the canonical swap frame. -/
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

/-- **Forward swap body.** The front half (`swapBody_front_exact`: lock prefix, both optional
transfers, conditional callback) joined at `t_09c3_c5` to the back half (`swapBack_exact`:
both balance queries, inputs, `K` check, `_update`, `Swap` log, unlock): the actual body runs
from its entry with the decoded stack and the PC0 memory to its return, with the closed
charge `swapPrefixGas` over the front environment's transfer-branch gas, ending at the back
environment's world and memory with residual exactly `G`. The join gas is the back half's
entry gas `back.gas`.
The `_safeTransfer` helper is `safeTransfer_dynamic_forward`. -/
theorem swapBody_exact {K : WriterKey → Prop} {st : State}
    {sevm : Sevm} {b d0 d1 dC : Devm} {cg0 cg1 cgC G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (rep : WriterRep K (b.getStor sevm.currentTarget) st)
    (unlocked : st.unlocked = 1) (nonstatic : sevm.isStatic = false)
    (output : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0)
    (liquidity0 : (swapAmount0Out sevm).toNat < st.reserve0.val)
    (liquidity1 : (swapAmount1Out sevm).toNat < st.reserve1.val)
    (to0 : swapRecipient sevm ≠ st.token0) (to1 : swapRecipient sevm ≠ st.token1)
    (guards : SwapAbiGuards sevm)
    (back : SwapBackForwardEnv sevm (swapFrontCutWorld sevm b d0 d1 dC)
      (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
      (swapFrontPtr sevm d0 d1) (swapCutWords sevm st) 0x257 [0x022c0d9f] G)
    (front : SwapFrontForwardEnv sevm b st d0 d1 dC cg0 cg1 cgC back.gas) :
    SFunc.RunExact cert.prog sevm
      (St b (swapBodyStack sevm) getterInitMemory
        (swapFrontTransferGas sevm b d0 d1 cg0 cg1 cgC back.gas +
          swapPrefixGas sevm b (swapAmount0Out sevm)))
      t_0683_c54 (.returned (St back.post [0x022c0d9f] back.memory G)) := by
  obtain ⟨mem, lower, width, _, run⟩ := swapBody_front_exact fork rep unlocked nonstatic
    output liquidity0 liquidity1 to0 to1 guards front
  exact run _ (swapBack_exact fork mem lower width (by decide) back)

/-- **Swap forward schedule from pc zero.** From the nonpayable, size and selector guards, the
four literal ABI guards, the finite entry storage with the source guards of `startTyped`, and
the forward environments of both halves of the body (the token transfers and callback for the
front, the two `balanceOf` queries and the primitive guards for the back), a successful
pc-zero run of the original bytes exists with the exact initial gas
`swapFrontTransferGas … back.gas + swapPrefixGas … + 445`, ending in the back half's world
and memory with the residual `g`. That same run satisfies the canonical swap frame with foreign
storage (`swap_bytecode_exact_consumes_own`) under trace-local HASH-T over its own trace
universe. The callee frames are forward-environment premises (ENV class): this is a
conditional universal construction, not an existential execution for arbitrary callees.
The `_safeTransfer` helper is `safeTransfer_dynamic_forward`. -/
theorem swap_bytecode_forward_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b d0 d1 dC : Devm} {cg0 cg1 cgC g : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f) (guards : SwapAbiGuards sevm)
    (unlocked : current.state.unlocked = 1) (nonstatic : sevm.isStatic = false)
    (output : swapAmount0Out sevm ≠ 0 ∨ swapAmount1Out sevm ≠ 0)
    (liquidity0 : (swapAmount0Out sevm).toNat < current.state.reserve0.val)
    (liquidity1 : (swapAmount1Out sevm).toNat < current.state.reserve1.val)
    (to0 : swapRecipient sevm ≠ current.state.token0)
    (to1 : swapRecipient sevm ≠ current.state.token1)
    (back : SwapBackForwardEnv sevm (swapFrontCutWorld sevm b d0 d1 dC)
      (swapFrontCutMem sevm d0 d1 dC) (swapFrontCutMem sevm d0 d1 dC).size
      (swapFrontPtr sevm d0 d1) (swapCutWords sevm current.state) 0x257 [0x022c0d9f] (g + 1))
    (front : SwapFrontForwardEnv sevm b current.state d0 d1 dC cg0 cg1 cgC back.gas) :
    let G := swapFrontTransferGas sevm b d0 d1 cg0 cg1 cgC back.gas +
      swapPrefixGas sevm b (swapAmount0Out sevm)
    ∃ run : Exec 0 sevm (St b [] Mem.empty (G + 279 + 166))
        (.ok (St back.post [0x022c0d9f] back.memory g)),
      (WriterInj (WriterExtend K
          (swapTraceKeys ⟨0, sevm, St b [] Mem.empty (G + 279 + 166), _, run⟩)) →
        WriterApart (WriterExtend K
          (swapTraceKeys ⟨0, sevm, St b [] Mem.empty (G + 279 + 166), _, run⟩)) →
        (∀ a, a ≠ sevm.currentTarget → (swapPrefixWorld sevm b).getStor a = b.getStor a) ∧
        SwapCanonicalBody
          (fun d => ∀ a, a ≠ sevm.currentTarget →
            (St back.post [0x022c0d9f] back.memory g).getStor a = d.getStor a)
          K current invocation run) := by
  intro G
  have body := swapBody_exact fork rep unlocked nonstatic output liquidity0 liquidity1
    to0 to1 guards back front
  obtain ⟨run⟩ := lift_exact cert_check jumps_ok codeEq fork
    ⟨t_0000_c0, rfl, swapPc0_exact value size selector guards body⟩
  exact ⟨run, fun inj apart =>
    swap_bytecode_exact_consumes_own invocation rep sem image installed freshOutput codeEq fork
      selector run inj apart⟩

end Blanc.Lift.UniswapV2Pair
