import Blanc.Lift.HistCursorReturn
import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalObservation
import Blanc.Lift.UniswapV2Pair.BurnPositionalFinalRequest
import Blanc.Lift.UniswapV2Pair.PairCodeGuardCursor
import Blanc.Lift.CursorNoExecSuffix

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def BurnFiveCalls.finalRequestMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) : Mem :=
  skimRequestMemory r.finalMemory r.finalPointer sevm.currentTarget

def BurnFiveCallsH.finalRequestMemory {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) : Mem :=
  skimRequestMemory r.finalMemory r.finalPointer sevm.currentTarget

def BurnFiveCalls.finalLocals {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (r : BurnFiveCalls root sevm b) (balance0 : B256) : List B256 :=
  (r.four.three.pricedLocals r.four.pricing).set 4 balance0

def BurnFiveCallsH.finalLocals {root : Exec.Deriv} {sevm : Sevm} {b : Devm} {w : BurnSchedule}
    (r : BurnFiveCallsH root sevm b w) (balance0 : B256) : List B256 :=
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

structure BurnSevenCallsH (root : Exec.Deriv) (sevm : Sevm) (b : Devm) (w : BurnSchedule) where
  five : BurnFiveCallsH root sevm b w
  second_bound : five.second.returned.devm.returnData.length < 2 ^ 160
  second_accepted : five.second.returned.devm.returnData = [] ∨
    (32 ≤ five.second.returned.devm.returnData.length ∧
      Bytes.toB256 (five.second.returned.devm.returnData.sliceD 0 32 0) ≠ 0)
  second_decoded : CursorStateAt code cert five.second.returned t_16a3_c13
    five.second.returned.devm (five.four.three.pricedLocals five.four.pricing)
    five.finalMemory [t_053d_c83]
  final0 : BurnFinalObservationH root five.second.returned .first
    (w.acc five.second.returned.devm
      (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
    (burnInitialToken0 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff)
    five.finalPointer (five.four.three.pricedLocals five.four.pricing)
    five.finalRequestMemory [t_053d_c83]
  final1 : BurnFinalObservationH root final0.call.returned .second
    (w.acc final0.call.returned.devm
      (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr)
    (burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff)
    five.finalPointer (five.finalLocals (Bytes.toB256 (final0.out.take 32)))
    (skimRequestMemory (burnBalanceReplyMemory five.finalRequestMemory five.finalPointer final0.out)
      five.finalPointer sevm.currentTarget) [t_053d_c83]
  suffix : ∀ N, Exec.Deriv.ParentPrefix final1.call.returned N → ∀ x,
    ¬ Ninst.At N.sevm.code N.pc (.exec x)

/-- On a covered fork, `BurnSevenCallsH` gives the modern `BurnSevenCalls` with the same fields. -/
def BurnSevenCallsH.toCovered {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnSevenCallsH root sevm b BurnSchedule.modern) :
    BurnSevenCalls root sevm b where
  five := h.five.toCovered fork
  second_bound := h.second_bound
  second_accepted := h.second_accepted
  second_decoded := by
    rw [BurnFiveCallsH.finalMemory_toCovered fork]
    exact h.second_decoded
  final0 := h.final0.toCovered (by
    show CoveredFork h.five.second.returned.sevm.benvStat.fork
    rw [(Cursor.parentStep_sevm h.five.second.edge).trans h.five.sevm_eq]; exact fork)
  final1 := h.final1.toCovered (by
    show CoveredFork h.final0.call.returned.sevm.benvStat.fork
    rw [(Cursor.parentStep_sevm h.final0.call.edge).trans (h.final0.sevm_eq.trans
      ((Cursor.parentStep_sevm h.five.second.edge).trans h.five.sevm_eq))]; exact fork)
  suffix := h.suffix

theorem burn_seven_occurrences_of_successH {sevm : Sevm} {b post : Devm} {w : BurnSchedule} {G : Nat}
    (worlds : BurnScheduleH sevm w) (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnSevenCallsH root sevm b w) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  rcases w with ⟨FB, FC, acc⟩
  obtain ⟨hFB, hFC, hacc⟩ := worlds
  subst hacc
  obtain ⟨r⟩ := burn_five_occurrences_of_successH ⟨hFB, hFC, rfl⟩ codeEq stateGas bal selector run
  obtain ⟨_, _, _, secondBound, secondAccepted, ⟨decoded⟩⟩ := r.actualReply rfl stateGas
  have reached5 := r.second.sameFrame.snoc r.second.edge
  have env5 : r.second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm r.second.edge).trans r.sevm_eq
  have success5 : r.second.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached5
  have fork5 : r.second.returned.sevm.benvStat.rules.stateGas = none ∧ r.second.returned.sevm.benvStat.rules.bal = none := by rw [env5]; exact ⟨stateGas, bal⟩
  obtain ⟨n, pointer⟩ := r.finalMem
  have bounds := burnFinalPointer_bounds r.first_bound secondBound
  change 96 ≤ r.finalPointer.toNat ∧ r.finalPointer.toNat + 1024 < 2 ^ 256 at bounds
  obtain ⟨prepared0⟩ := burn_final_first_preparation_cursor_stateH
    (by simpa only [BurnThreeCallsH.pricedLocals] using decoded) success5 fork5.1
    (PtrWord.of_ptrMem pointer) bounds.1 bounds.2
  rw [env5] at prepared0
  obtain ⟨code0, ⟨guard0⟩⟩ := pair_code_guard_cursor_stateH prepared0 success5 fork5.1 fork5.2
    [0x17,0x0f] (by decide) rfl (by decide)
  have memory0 := burnBalanceRequest_memoryLayout (pair := sevm.currentTarget)
    pointer bounds.1 bounds.2
  obtain ⟨observation0⟩ := burn_final_observation_of_request_cursorH .first guard0
    reached5 success5 fork5.1 memory0.1 bounds.1 memory0.2
    (by simpa only [Devm.getCode, Devm.getAcct, accountAccessH_state] using code0)
    (by rw [env5]; exact skimRequestMemory_read pointer.wf bounds.2)
  rw [env5] at observation0
  have reached6 := observation0.call.sameFrame.snoc observation0.call.edge
  have env6 : observation0.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm observation0.call.edge).trans (observation0.sevm_eq.trans env5)
  have success6 : observation0.call.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq reached6
  have fork6 : observation0.call.returned.sevm.benvStat.rules.stateGas = none ∧ observation0.call.returned.sevm.benvStat.rules.bal = none := by rw [env6]; exact ⟨stateGas, bal⟩
  obtain ⟨prepared1⟩ := burn_final_second_preparation_cursor_stateH
    (by simpa only [BurnThreeCallsH.pricedLocals] using observation0.decoded)
    success6 fork6.1 (PtrWord.of_ptrMem observation0.pointer) bounds.1 bounds.2
  rw [env6] at prepared1
  obtain ⟨code1, ⟨guard1⟩⟩ := pair_code_guard_cursor_stateH prepared1 success6 fork6.1 fork6.2
    [0x17,0xab] (by decide) rfl (by decide)
  have memory1 := burnBalanceRequest_memoryLayout (pair := sevm.currentTarget)
    observation0.pointer bounds.1 bounds.2
  obtain ⟨observation1⟩ := burn_final_observation_of_request_cursorH .second guard1
    reached6 success6 fork6.1 memory1.1 bounds.1 memory1.2
    (by simpa only [Devm.getCode, Devm.getAcct, accountAccessH_state] using code1)
    (by rw [env6]; exact skimRequestMemory_read observation0.pointer.wf bounds.2)
  rw [env6] at observation1
  have env7 : observation1.call.returned.sevm = sevm :=
    (Cursor.parentStep_sevm observation1.call.edge).trans (observation1.sevm_eq.trans env6)
  have suffix := observation1.placed.noExecSuffixH cert_check (by rw [env7]; exact stateGas)
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
  · simpa only [BurnFiveCallsH.finalLocals, BurnFiveCallsH.finalRequestMemory, BurnThreeCallsH.pricedLocals,
      burnPricedLocals, List.set] using observation1
  · exact suffix


end Blanc.Lift.UniswapV2Pair
