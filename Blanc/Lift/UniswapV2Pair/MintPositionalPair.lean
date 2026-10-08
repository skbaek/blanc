import Blanc.Lift.UniswapV2Pair.MintPositional
import Blanc.Lift.UniswapV2Pair.MintPositionalReply
import Blanc.Lift.UniswapV2Pair.MintPositionalSecond

/-! Consecutive actual Mint balance calls and their full replies. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem MintBalanceOccurrence.returned_sevm {root start : Exec.Deriv}
    {site : MintBalanceSite} {b : Devm} {token : B256} {S : List B256}
    {M : Mem} {K : List SFunc}
    (r : MintBalanceOccurrence root start site b token S M K) :
    r.call.returned.sevm = start.sevm :=
  (Cursor.parentStep_sevm r.call.edge).trans r.sevm_eq

theorem MintBalanceOccurrence.returned_exn {root start : Exec.Deriv}
    {site : MintBalanceSite} {b : Devm} {token : B256} {S : List B256}
    {M : Mem} {K : List SFunc}
    (r : MintBalanceOccurrence root start site b token S M K) :
    r.call.returned.exn = start.exn := by
  have same : r.call.returned.exn = r.call.occurrence.node.exn :=
    by
      have edge := r.call.edge
      generalize original : r.call.occurrence.node = F at edge ⊢
      generalize returned : r.call.returned = N at edge ⊢
      cases edge <;> rfl
  exact same.trans r.exn_eq

/-- The complete reply is classified at this original occurrence's actual
returned parent, with no replacement call or answer witness. -/
theorem MintBalanceOccurrence.reply {root start : Exec.Deriv}
    {site : MintBalanceSite} {b : Devm} {token : B256} {S : List B256}
    {M : Mem} {K : List SFunc}
    (r : MintBalanceOccurrence root start site b token S M K)
    (fork : CoveredFork start.sevm.benvStat.fork) :
    ∃ flag out, StaticCallPost b r.call.returned.devm S M 128 36 128 32 flag out ∧
      out.length < 2 ^ 256 ∧
      (flag = 1 → StaticAnswered start.sevm b token.toAdr (M.read 128 36).1 out) := by
  have actual := r.primitive.toRun
  rw [r.input] at actual
  exact ri_staticcall_bounded fork actual

private theorem mint_balance_after_call_shape (site : MintBalanceSite) :
    site.afterCallTree = (callFlagGuardLine
      (match site with | .first => [0x11,0x22] | .second => [0x11,0xc5])
      (by cases site <;> (change (2 : Nat) ≤ 32; decide))).foldr SFunc.next
      (.branch (match site with | .first => t_1119_c41 | .second => t_11bc_c41)
        site.returnTree) := by cases site <;> rfl

/-- Checked decoding of the output selected by the supplied actual call. -/
theorem mint_balance_occurrence_decode {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {token a x y : B256}
    (site : MintBalanceSite)
    (r : MintBalanceOccurrence root start site b token (a :: x :: y :: R)
      (balanceRequestMemory M start.sevm.currentTarget) K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (mem : PtrMem 128 192 (balanceRequestMemory M start.sevm.currentTarget)) :
    ∃ out, StaticCallPost b r.call.returned.devm (a :: x :: y :: R)
        (balanceRequestMemory M start.sevm.currentTarget) 128 36 128 32 1 out ∧
      out.length < 2 ^ 256 ∧ 32 ≤ out.length ∧
      StaticAnswered start.sevm b token.toAdr
        (ExternalOperation.encode (.balanceOf start.sevm.currentTarget)) out ∧
      Nonempty (CursorStateAt code cert r.call.returned site.afterDecodeTree
        r.call.returned.devm (Bytes.toB256 (out.take 32) :: R)
        (balanceReplyMemory M start.sevm.currentTarget out) K) := by
  obtain ⟨flag, out, reply, bound, answered⟩ := r.reply fork
  have returnedEnv := r.returned_sevm
  have state := reply.eq_St
  change r.call.returned.devm = St r.call.returned.devm
    (flag :: a :: x :: y :: R) (balanceReplyMemory M start.sevm.currentTarget out)
    r.call.returned.devm.gasLeft at state
  let cut : CursorStateAt code cert r.call.returned site.afterCallTree
      r.call.returned.devm (flag :: a :: x :: y :: R)
      (balanceReplyMemory M r.call.returned.sevm.currentTarget out) K :=
    ⟨r.call.returned, r.cursor, .refl _, rfl, rfl, r.placed, r.tree,
      ⟨r.call.returned.devm.gasLeft, by rw [returnedEnv]; exact state⟩, r.continuations⟩
  obtain ⟨one, width, decoded⟩ := mint_balance_reply_cursor_state
    (start := r.call.returned) (b := r.call.returned.devm) (post := post)
    (f := site.afterCallTree) (R := R) (M := M) (K := K)
    (flag := flag) (a := a) (x := x) (y := y) (out := out) site cut
    (mint_balance_after_call_shape site)
    (r.returned_exn.trans success) (by rw [returnedEnv]; exact fork) reply.flag reply.returnData bound
    (by rw [returnedEnv]; exact mem) wf
  subst flag
  have answer := answered rfl
  rw [balanceRequestMemory_read wf start.sevm.currentTarget] at answer
  rw [returnedEnv] at decoded
  exact ⟨out, reply, bound, width, answer, decoded⟩

/-- Mint's second actual instruction follows the first actual reply. The
between-call span starts at that same returned node and contains no exec. -/
theorem mint_second_occurrence_of_first {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {token r1 r0 toWord extρ : B256}
    (first : MintBalanceOccurrence root start .first b token
      (164 :: 0x70a08231 :: token :: 0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M start.sevm.currentTarget) K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (mem : PtrMem 128 192 (balanceRequestMemory M start.sevm.currentTarget)) :
    ∃ out, StaticCallPost b first.call.returned.devm
        (164 :: 0x70a08231 :: token :: 0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M start.sevm.currentTarget) 128 36 128 32 1 out ∧
      out.length < 2 ^ 256 ∧ 32 ≤ out.length ∧
      StaticAnswered start.sevm b token.toAdr
        (ExternalOperation.encode (.balanceOf start.sevm.currentTarget)) out ∧
      let returned := first.call.returned
      let token1 := (returned.devm.getStorVal returned.sevm.currentTarget 7).toAdr.toB256
      ((temporalAccountAccessBase (afterSload returned.sevm returned.devm 7)
        token1.toAdr).getCode token1.toAdr).size.toB256 ≠ 0 ∧
      Nonempty (MintBalanceOccurrence root returned .second
        (temporalAccountAccessBase (afterSload returned.sevm returned.devm 7) token1.toAdr)
        token1
        (164 :: 0x70a08231 :: token1 :: 0 :: Bytes.toB256 (out.take 32) ::
          r1 :: r0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory (balanceReplyMemory M start.sevm.currentTarget out)
          returned.sevm.currentTarget) K) := by
  obtain ⟨out, reply, bound, width, answer, decoded⟩ :=
    mint_balance_occurrence_decode .first first success fork wf mem
  obtain ⟨decoded⟩ := decoded
  have returnedEnv := first.returned_sevm
  have decoded' : CursorStateAt code cert first.call.returned
      MintBalanceSite.first.afterDecodeTree first.call.returned.devm
      (Bytes.toB256 (out.take 32) :: 0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R)
      (balanceReplyMemory M first.call.returned.sevm.currentTarget out) K := by
    simpa only [returnedEnv] using decoded
  have returnedSuccess := first.returned_exn.trans success
  have returnedFork : CoveredFork first.call.returned.sevm.benvStat.fork := by
    rw [returnedEnv]; exact fork
  have nonzero := mint_second_code_guard decoded' returnedSuccess returnedFork
    (balanceReplyMemory_ptr out (by rw [returnedEnv]; exact mem))
  obtain ⟨request⟩ := mint_second_guard_cursor_state decoded' returnedSuccess returnedFork
    (balanceReplyMemory_ptr out (by rw [returnedEnv]; exact mem))
  obtain ⟨second⟩ := mint_balance_occurrence_of_request_cursor .second request
    (first.call.sameFrame.snoc first.call.edge) returnedSuccess returnedFork
  refine ⟨out, reply, bound, width, answer, ?_, ?_⟩
  · simpa only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state] using nonzero
  · simpa only [returnedEnv] using (Nonempty.intro second)

end Blanc.Lift.UniswapV2Pair
