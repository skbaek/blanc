import Blanc.Lift.UniswapV2Pair.MintPositionalPair
import Blanc.Lift.UniswapV2Pair.MintPositionalFee

/-! Mint's third original call after both exact physical balance replies. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The third call begins after the supplied second actual reply. Both checked
subtractions and fee preparation belong to that same original parent path. -/
theorem mint_fee_occurrence_of_second {root start : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {token b0 r1 r0 toWord extρ : B256}
    (second : MintBalanceOccurrence root start .second b token
      (164 :: 0x70a08231 :: token :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M start.sevm.currentTarget) K)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork)
    (wf : Mem.Wf M)
    (mem : PtrMem 128 192 (balanceRequestMemory M start.sevm.currentTarget))
    (bound0 : r0.toNat < 2 ^ 112) (bound1 : r1.toNat < 2 ^ 112) :
    ∃ out, StaticCallPost b second.call.returned.devm
        (164 :: 0x70a08231 :: token :: 0 :: b0 :: r1 :: r0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M start.sevm.currentTarget) 128 36 128 32 1 out ∧
      out.length < 2 ^ 256 ∧ 32 ≤ out.length ∧
      StaticAnswered start.sevm b token.toAdr
        (ExternalOperation.encode (.balanceOf start.sevm.currentTarget)) out ∧
      r0 ≤ b0 ∧ r1 ≤ Bytes.toB256 (out.take 32) ∧
      let returned := second.call.returned
      let factory := feeFactoryWord returned.sevm returned.devm
      Nonempty (MintFeeOccurrence root returned
        (feeFactoryCallWorld returned.sevm returned.devm) factory
        (132 :: 0x017e7e58 :: factory :: 0 :: 0 :: r1 :: r0 :: 0x1233 ::
          mintFeeLocals (Bytes.toB256 (out.take 32) - r1) (b0 - r0)
            (Bytes.toB256 (out.take 32)) b0 r1 r0 toWord extρ R)
        (feeRequestMemory (balanceReplyMemory M start.sevm.currentTarget out))
        (t_1233_c41 :: K)) := by
  obtain ⟨out, reply, bound, width, answer, decoded⟩ :=
    mint_balance_occurrence_decode .second second success fork wf mem
  obtain ⟨decoded⟩ := decoded
  have returnedEnv := second.returned_sevm
  have returnedSuccess := second.returned_exn.trans success
  have returnedFork : CoveredFork second.call.returned.sevm.benvStat.fork := by
    rw [returnedEnv]; exact fork
  obtain ⟨cover0, cover1, callee⟩ := mint_amounts_fee_cursor_state decoded
    returnedSuccess returnedFork bound0 bound1
  obtain ⟨callee⟩ := callee
  obtain ⟨fee⟩ := mint_fee_occurrence_of_callee callee
    (second.call.sameFrame.snoc second.call.edge) returnedSuccess returnedFork
    (balanceReplyMemory_ptr out mem)
  exact ⟨out, reply, bound, width, answer, cover0, cover1, ⟨fee⟩⟩

end Blanc.Lift.UniswapV2Pair
