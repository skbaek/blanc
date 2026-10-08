import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalObservation
import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalRequest
import Blanc.Lift.UniswapV2Pair.PairCodeGuardCursor
import Blanc.Lift.CursorNoExecSuffix

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnFiveCalls.finalRequestMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) : Mem :=
  skimRequestMemory r.finalMemory r.finalPointer sevm.currentTarget

def BurnFiveCalls.finalLocals {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) (balance0 : B256) : List B256 :=
  (r.four.three.pricedLocals r.four.pricing).set 4 balance0

/-- Seven ordered actual positions in the original Burn parent, with both
physical token replies, final answers and no external suffix retained. -/
structure BurnSevenCalls (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  five : BurnFiveCalls root sevm b
  second_bound : five.second.returned.devm.returnData.length < 2 ^ 160
  second_accepted : five.second.returned.devm.returnData = [] ∨
    (32 ≤ five.second.returned.devm.returnData.length ∧
      Bytes.toB256 (five.second.returned.devm.returnData.sliceD 0 32 0) ≠ 0)
  second_decoded : CursorStateAt code cert five.second.returned t_16a3_c13
    five.second.returned.devm (five.four.three.pricedLocals five.four.pricing)
    five.finalMemory [t_053d_c83]
  final0 : BurnFinalObservation root five.second.returned .first
    (temporalAccountAccessBase five.second.returned.devm
      (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
    (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff)
    five.finalPointer (five.four.three.pricedLocals five.four.pricing)
    five.finalRequestMemory [t_053d_c83]
  final1 : BurnFinalObservation root final0.call.returned .second
    (temporalAccountAccessBase final0.call.returned.devm
      (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
    (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff)
    five.finalPointer (five.finalLocals (Bytes.toB256 (final0.out.take 32)))
    (skimRequestMemory (burnBalanceReplyMemory five.finalRequestMemory five.finalPointer final0.out)
      five.finalPointer sevm.currentTarget) [t_053d_c83]
  suffix : ∀ N, Exec.Deriv.ParentPrefix final1.call.returned N → ∀ x,
    ¬ Ninst.At N.sevm.code N.pc (.exec x)

/-- Successful execution of the checked original Burn bytecode fixes all
seven actual calls, their own replies and ordered gaps. No desired mapping,
model success, payout equality, guard or cursor endpoint is a premise. -/
theorem burn_seven_occurrences_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnSevenCalls root sevm b) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨r⟩ := burn_five_occurrences_of_success codeEq fork selector run
  obtain ⟨_, _, _, secondBound, secondAccepted, ⟨decoded⟩⟩ := r.actualReply rfl fork
  have reached5 := r.second.sameFrame.snoc r.second.edge
  have env5 : r.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.second.edge).trans r.sevm_eq
  have success5 : r.second.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached5
  have fork5 : CoveredFork r.second.returned.sevm.benvStat.fork := by rw [env5]; exact fork
  obtain ⟨n, pointer⟩ := r.finalMem
  have bounds := burnFinalPointer_bounds r.first_bound secondBound
  change 96 ≤ r.finalPointer.toNat ∧ r.finalPointer.toNat + 1024 < 2 ^ 256 at bounds
  obtain ⟨prepared0⟩ := burn_final_first_preparation_cursor_state
    (by simpa only [BurnThreeCalls.pricedLocals] using decoded) success5 fork5
    (PtrWord.of_ptrMem pointer) bounds.1 bounds.2
  rw [env5] at prepared0
  obtain ⟨code0, ⟨guard0⟩⟩ := pair_code_guard_cursor_state prepared0 success5 fork5
    [0x17,0x0f] (by decide) rfl (by decide)
  have memory0 := burnBalanceRequest_memoryLayout (pair := sevm.currentTarget)
    pointer bounds.1 bounds.2
  obtain ⟨observation0⟩ := burn_final_observation_of_request_cursor .first guard0
    reached5 success5 fork5 memory0.1 bounds.1 memory0.2
    (by simpa only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state] using code0)
    (by rw [env5]; exact skimRequestMemory_read pointer.wf bounds.2)
  have reached6 := observation0.call.sameFrame.snoc observation0.call.edge
  have env6 : observation0.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm observation0.call.edge).trans (observation0.sevm_eq.trans env5)
  have success6 : observation0.call.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached6
  have fork6 : CoveredFork observation0.call.returned.sevm.benvStat.fork := by rw [env6]; exact fork
  obtain ⟨prepared1⟩ := burn_final_second_preparation_cursor_state
    (by simpa only [BurnThreeCalls.pricedLocals] using observation0.decoded)
    success6 fork6 (PtrWord.of_ptrMem observation0.pointer) bounds.1 bounds.2
  rw [env6] at prepared1
  obtain ⟨code1, ⟨guard1⟩⟩ := pair_code_guard_cursor_state prepared1 success6 fork6
    [0x17,0xab] (by decide) rfl (by decide)
  have memory1 := burnBalanceRequest_memoryLayout (pair := sevm.currentTarget)
    observation0.pointer bounds.1 bounds.2
  obtain ⟨observation1⟩ := burn_final_observation_of_request_cursor .second guard1
    reached6 success6 fork6 memory1.1 bounds.1 memory1.2
    (by simpa only [Devm.getCode, Devm.getAcct, temporalAccountAccessBase_state] using code1)
    (by rw [env6]; exact skimRequestMemory_read observation0.pointer.wf bounds.2)
  have env7 : observation1.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm observation1.call.edge).trans (observation1.sevm_eq.trans env6)
  have suffix := observation1.placed.noExecSuffix cert_check (by rw [env7]; exact fork)
    (E := [9,14,18,19,20,21,22,58,60,65,66]) (by decide)
    (by rw [observation1.tree]; decide)
    (by intro f member
        rw [observation1.continuations] at member
        simp only [List.mem_singleton] at member
        subst f
        decide)
  refine ⟨{
    five := r
    second_bound := secondBound
    second_accepted := secondAccepted
    second_decoded := decoded
    final0 := observation0
    final1 := ?_
    suffix := ?_ }⟩
  · simpa only [BurnFiveCalls.finalLocals, BurnFiveCalls.finalRequestMemory, BurnThreeCalls.pricedLocals,
      burnPricedLocals, List.set] using observation1
  · exact suffix

end Blanc.Lift.UniswapV2Pair
