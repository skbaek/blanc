import Blanc.Lift.UniswapV2Pair.BurnPositionalBalances
import Blanc.Lift.UniswapV2Pair.BurnPositionalFee
import Blanc.Lift.UniswapV2Pair.PairFeeObservation

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def burnInitialReserve0 (sevm : Sevm) (b : Devm) : B256 :=
  reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8)

def burnInitialReserve1 (sevm : Sevm) (b : Devm) : B256 :=
  reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8)

def burnInitialReplyMemory (sevm : Sevm) (out0 out1 : Bytes) : Mem :=
  balanceReplyMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
    sevm.currentTarget out1

/-- The two actual initial slots and physical replies beneath one original root.
The second input retains the full world returned by the first instruction. -/
structure BurnInitialPair (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  first : CallOccurrenceStep root .staticcall
  second : CallOccurrenceStep root .staticcall
  gas0 : Nat
  gas1 : Nat
  out0 : Bytes
  out1 : Bytes
  first_gap : Exec.Deriv.ExecFreeUntil root first.occurrence.node
  first_input : first.occurrence.node.devm = burnFirstCallInput sevm
    (burnInitialReserveWorld sevm b) [0x89afcb44] getterInitMemory gas0
    (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b)
    (Sevm.dataWord sevm 4).toAdr.toB256 0x053d
  first_reply : StaticCallPost (burnInitialWorld0 sevm b) first.returned.devm
    (164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
    (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 36 128 32 1 out0
  first_width : 32 ≤ out0.length
  first_bound : out0.length < 2 ^ 256
  first_decoded : CursorStateAt code cert first.returned BurnInitialBalanceSite.first.afterDecodeTree
    first.returned.devm (Bytes.toB256 (out0.take 32) :: burnInitialTail0 sevm b)
    (balanceReplyMemory getterInitMemory sevm.currentTarget out0) [t_053d_c83]
  first_guard : ((burnInitialWorld0 sevm b).getCode (burnInitialToken0 sevm b).toAdr).size.toB256 ≠ 0
  second_gap : Exec.Deriv.ExecFreeUntil first.returned second.occurrence.node
  second_sevm : second.occurrence.node.sevm = sevm
  second_input : second.occurrence.node.devm =
    burnInitialSecondInput sevm b first.returned.devm out0 gas1
  second_reply : StaticCallPost
    (temporalAccountAccessBase first.returned.devm (burnInitialTarget1 sevm b).toAdr)
    second.returned.devm
    (164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
    (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
      sevm.currentTarget) 128 36 128 32 1 out1
  second_width : 32 ≤ out1.length
  second_bound : out1.length < 2 ^ 256
  second_guard : (first.returned.devm.getCode (burnInitialTarget1 sevm b).toAdr).size.toB256 ≠ 0
  decoded : CursorStateAt code cert second.returned BurnInitialBalanceSite.second.afterDecodeTree
    second.returned.devm (Bytes.toB256 (out1.take 32) :: burnInitialTail1 sevm b out0)
    (burnInitialReplyMemory sevm out0 out1) [t_053d_c83]

structure BurnInitialPairH (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  first : CallOccurrenceStep root .staticcall
  second : CallOccurrenceStep root .staticcall
  gas0 : Nat
  gas1 : Nat
  out0 : Bytes
  out1 : Bytes
  first_gap : Exec.Deriv.ExecFreeUntil root first.occurrence.node
  first_input : first.occurrence.node.devm = burnFirstCallInputH sevm
    (burnInitialReserveWorldH sevm b) [0x89afcb44] getterInitMemory gas0
    (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b)
    (Sevm.dataWord sevm 4).toAdr.toB256 0x053d
  first_reply : StaticCallPost (burnInitialWorld0H sevm b) first.returned.devm
    (164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
    (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 36 128 32 1 out0
  first_width : 32 ≤ out0.length
  first_bound : out0.length < 2 ^ 256
  first_decoded : CursorStateAt code cert first.returned BurnInitialBalanceSite.first.afterDecodeTree
    first.returned.devm (Bytes.toB256 (out0.take 32) :: burnInitialTail0 sevm b)
    (balanceReplyMemory getterInitMemory sevm.currentTarget out0) [t_053d_c83]
  first_guard : ((burnInitialWorld0H sevm b).getCode (burnInitialToken0 sevm b).toAdr).size.toB256 ≠ 0
  second_gap : Exec.Deriv.ExecFreeUntil first.returned second.occurrence.node
  second_sevm : second.occurrence.node.sevm = sevm
  second_input : second.occurrence.node.devm =
    burnInitialSecondInputH sevm b first.returned.devm out0 gas1
  second_reply : StaticCallPost
    (accountAccessH sevm first.returned.devm (burnInitialTarget1 sevm b).toAdr)
    second.returned.devm
    (164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
    (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
      sevm.currentTarget) 128 36 128 32 1 out1
  second_width : 32 ≤ out1.length
  second_bound : out1.length < 2 ^ 256
  second_guard : (first.returned.devm.getCode (burnInitialTarget1 sevm b).toAdr).size.toB256 ≠ 0
  decoded : CursorStateAt code cert second.returned BurnInitialBalanceSite.second.afterDecodeTree
    second.returned.devm (Bytes.toB256 (out1.take 32) :: burnInitialTail1 sevm b out0)
    (burnInitialReplyMemory sevm out0 out1) [t_053d_c83]

/-- On a covered fork, `BurnInitialPairH` gives the modern `BurnInitialPair` with the same fields. -/
def BurnInitialPairH.toCovered {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnInitialPairH root sevm b) :
    BurnInitialPair root sevm b where
  first := h.first
  second := h.second
  gas0 := h.gas0
  gas1 := h.gas1
  out0 := h.out0
  out1 := h.out1
  first_gap := h.first_gap
  first_input := by simpa only [burnFirstCallInputH_of_covered fork, burnInitialReserveWorldH_of_covered fork] using h.first_input
  first_reply := by simpa only [burnInitialWorld0H_of_covered fork] using h.first_reply
  first_width := h.first_width
  first_bound := h.first_bound
  first_decoded := h.first_decoded
  first_guard := by simpa only [burnInitialWorld0H_of_covered fork] using h.first_guard
  second_gap := h.second_gap
  second_sevm := h.second_sevm
  second_input := by simpa only [burnInitialSecondInputH_of_covered fork] using h.second_input
  second_reply := by simpa only [accountAccessH_of_eip2929 fork.rules_access] using h.second_reply
  second_width := h.second_width
  second_bound := h.second_bound
  second_guard := h.second_guard
  decoded := h.decoded

/-- On a covered fork, the modern `BurnInitialPair` gives `BurnInitialPairH` with the same fields. -/
def BurnInitialPair.toH {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnInitialPair root sevm b) :
    BurnInitialPairH root sevm b where
  first := h.first
  second := h.second
  gas0 := h.gas0
  gas1 := h.gas1
  out0 := h.out0
  out1 := h.out1
  first_gap := h.first_gap
  first_input := by simpa only [burnFirstCallInputH_of_covered fork, burnInitialReserveWorldH_of_covered fork] using h.first_input
  first_reply := by simpa only [burnInitialWorld0H_of_covered fork] using h.first_reply
  first_width := h.first_width
  first_bound := h.first_bound
  first_decoded := h.first_decoded
  first_guard := by simpa only [burnInitialWorld0H_of_covered fork] using h.first_guard
  second_gap := h.second_gap
  second_sevm := h.second_sevm
  second_input := by simpa only [burnInitialSecondInputH_of_covered fork] using h.second_input
  second_reply := by simpa only [accountAccessH_of_eip2929 fork.rules_access] using h.second_reply
  second_width := h.second_width
  second_bound := h.second_bound
  second_guard := h.second_guard
  decoded := h.decoded

/-- The Burn call worlds that depend on the access schedule: the LP-balance load before the
factory call (`FB`), the factory call world (`FC`), both as functions of the returned node's
environment and world, and the final balance calls' account access (`acc`). -/
structure BurnSchedule where
  FB : Sevm → Devm → Devm
  FC : Sevm → Devm → Devm
  acc : Devm → Adr → Devm

/-- The factory call world of the Burn fee observation. -/
abbrev burnFeeCallWorldOf (s : Sevm) (d : Devm) : Devm :=
  feeFactoryCallWorld s (feeBurnWorld s d)

abbrev burnFeeCallWorldOfH (s : Sevm) (d : Devm) : Devm :=
  feeFactoryCallWorldH s (feeBurnWorldH s d)

/-- The modern Burn call worlds. -/
abbrev BurnSchedule.modern : BurnSchedule := ⟨feeBurnWorld, burnFeeCallWorldOf, temporalAccountAccessBase⟩

/-- The historical Burn call worlds at the frame environment `sevm`. -/
abbrev BurnSchedule.historical (sevm : Sevm) : BurnSchedule :=
  ⟨feeBurnWorldH, burnFeeCallWorldOfH, accountAccessH sevm⟩

/-- `w` gives the historical call worlds for frames running at `sevm`. -/
def BurnScheduleH (sevm : Sevm) (w : BurnSchedule) : Prop :=
  (∀ s d, s = sevm → w.FB s d = feeBurnWorldH s d) ∧
    (∀ s d, s = sevm → w.FC s d = burnFeeCallWorldOfH s d) ∧
    w.acc = accountAccessH sevm

theorem BurnScheduleH.historical (sevm : Sevm) : BurnScheduleH sevm (BurnSchedule.historical sevm) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, rfl⟩

theorem BurnScheduleH.of_covered {sevm : Sevm} (fork : CoveredFork sevm.benvStat.fork) :
    BurnScheduleH sevm BurnSchedule.modern :=
  ⟨fun s d same => by subst same; exact (feeBurnWorldH_of_covered fork).symm,
    fun s d same => by
      subst same
      show feeFactoryCallWorld s (feeBurnWorld s d) = feeFactoryCallWorldH s (feeBurnWorldH s d)
      rw [feeBurnWorldH_of_covered fork, feeFactoryCallWorldH_of_covered fork],
    by
      funext d a
      exact (accountAccessH_of_eip2929 fork.rules_access).symm⟩

/-- Both balance observations and the factory reply retain their actual original
slots. The factory request starts from the second returned world and sampled LP
balance, and its checked continuation retains the Burn caller. -/
structure BurnThreeCalls (root : Exec.Deriv) (sevm : Sevm) (b : Devm) where
  initial : BurnInitialPair root sevm b
  fee : PairFeeObservation root initial.second.returned
    (feeBurnWorld initial.second.returned.sevm initial.second.returned.devm)
    (feeBurnMemory (burnInitialReplyMemory sevm initial.out0 initial.out1)
      initial.second.returned.sevm.currentTarget)
    (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b) 0x15e2
    (burnFeeLocals (feeBurnLiquidity initial.second.returned.sevm initial.second.returned.devm)
      (Bytes.toB256 (initial.out1.take 32)) (Bytes.toB256 (initial.out0.take 32))
      (burnInitialToken1 sevm b) (burnInitialToken0 sevm b)
      (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x053d [0x89afcb44])
    [t_15e2_c37, t_053d_c83]

/-- `BurnThreeCalls` over the historical initial pair, generic in the call worlds `w`. -/
structure BurnThreeCallsH (root : Exec.Deriv) (sevm : Sevm) (b : Devm) (w : BurnSchedule) where
  worlds : BurnScheduleH sevm w
  initial : BurnInitialPairH root sevm b
  fee : PairFeeObservationH root initial.second.returned
    (w.FB initial.second.returned.sevm initial.second.returned.devm)
    (w.FC initial.second.returned.sevm initial.second.returned.devm)
    (feeBurnMemory (burnInitialReplyMemory sevm initial.out0 initial.out1)
      initial.second.returned.sevm.currentTarget)
    (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b) 0x15e2
    (burnFeeLocals (feeBurnLiquidity initial.second.returned.sevm initial.second.returned.devm)
      (Bytes.toB256 (initial.out1.take 32)) (Bytes.toB256 (initial.out0.take 32))
      (burnInitialToken1 sevm b) (burnInitialToken0 sevm b)
      (burnInitialReserve1 sevm b) (burnInitialReserve0 sevm b)
      (Sevm.dataWord sevm 4).toAdr.toB256 0x053d [0x89afcb44])
    [t_15e2_c37, t_053d_c83]

theorem BurnInitialPairH.returned_sevm {root : Exec.Deriv} {sevm : Sevm} {b : Devm}
    (h : BurnInitialPairH root sevm b) : h.second.returned.sevm = sevm :=
  (Cursor.parentStep_sevm h.second.edge).trans h.second_sevm

/-- At the modern call worlds and on a covered fork, `BurnThreeCallsH` gives the modern
`BurnThreeCalls` with the same fields. -/
def BurnThreeCallsH.toCovered {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnThreeCallsH root sevm b BurnSchedule.modern) :
    BurnThreeCalls root sevm b where
  initial := h.initial.toCovered fork
  fee := h.fee.toCovered (by
    show CoveredFork h.initial.second.returned.sevm.benvStat.fork
    rw [h.initial.returned_sevm]; exact fork)

/-- On a covered fork, the modern `BurnThreeCalls` gives `BurnThreeCallsH` at the modern
call worlds. -/
def BurnThreeCalls.toH {sevm : Sevm} {root : Exec.Deriv} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) (h : BurnThreeCalls root sevm b) :
    BurnThreeCallsH root sevm b BurnSchedule.modern where
  worlds := BurnScheduleH.of_covered fork
  initial := h.initial.toH fork
  fee := by
    have f : CoveredFork h.initial.second.returned.sevm.benvStat.fork := by
      rw [(Cursor.parentStep_sevm h.initial.second.edge).trans h.initial.second_sevm]; exact fork
    have x := h.fee.toH f
    exact x

theorem burn_three_occurrences_of_successH {sevm : Sevm} {b post : Devm} {G : Nat}
    {w : BurnSchedule} (worlds : BurnScheduleH sevm w) (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnThreeCallsH root sevm b w) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨first, second, cursor1, gas0, gas1, out0, out1,
    gap0, input0, reply0, width0, bound0, gap1, env1, outcome1, input1,
    primitive1, placed1, tree1, cont1, reply1, width1, bound1, ⟨decoded⟩,
    ⟨decoded0⟩, guard0, guard1⟩ :=
    burn_initial_occurrences_of_successH codeEq stateGas bal selector run
  let initial : BurnInitialPairH root sevm b :=
    ⟨first, second, gas0, gas1, out0, out1, gap0, input0, reply0, width0, bound0,
      decoded0, guard0, gap1, env1, input1, reply1, width1, bound1, guard1, decoded⟩
  have envRet : second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm second.edge).trans env1
  have successRet : second.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq (second.sameFrame.snoc second.edge)
  have forkRet : second.returned.sevm.benvStat.rules.stateGas = none ∧ second.returned.sevm.benvStat.rules.bal = none := by
    rw [envRet]; exact ⟨stateGas, bal⟩
  have mem := balanceReplyMemory_ptr out1
    (balanceRequestMemory_ptr
      (balanceReplyMemory_ptr out0
        (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)) sevm.currentTarget)
  obtain ⟨callee⟩ := burn_fee_caller_cursor_stateH
    (R := [0x89afcb44]) (K := [t_053d_c83])
    (b1 := Bytes.toB256 (out1.take 32)) (discarded := 0)
    (b0 := Bytes.toB256 (out0.take 32))
    (token1 := burnInitialToken1 sevm b) (token0 := burnInitialToken0 sevm b)
    (r1 := burnInitialReserve1 sevm b) (r0 := burnInitialReserve0 sevm b)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) (extρ := 0x053d)
    decoded successRet forkRet.1 forkRet.2 mem
  have callWorld : w.FC second.returned.sevm second.returned.devm =
      feeFactoryCallWorldH second.returned.sevm (w.FB second.returned.sevm second.returned.devm) := by
    rw [worlds.2.1 _ _ envRet, worlds.1 _ _ envRet]
  rw [← worlds.1 _ _ envRet] at callee
  obtain ⟨fee⟩ := pair_fee_observation_of_calleeH callWorld callee
    (second.sameFrame.snoc second.edge) successRet forkRet.1 forkRet.2
    (feeBurnMemory_ptr mem second.returned.sevm.currentTarget)
  exact ⟨⟨worlds, initial, fee⟩⟩

/-- Original deployed Burn success selects its first three external instructions
and their replies, with no externally supplied occurrence or fee result. -/
theorem burn_three_occurrences_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnThreeCalls root sevm b) := by
  obtain ⟨h⟩ := burn_three_occurrences_of_successH (BurnScheduleH.of_covered fork) codeEq
    fork.rules_stateGas_none fork.rules_bal_none selector run
  exact ⟨h.toCovered fork⟩


end Blanc.Lift.UniswapV2Pair
