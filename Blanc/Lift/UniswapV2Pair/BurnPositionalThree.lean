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
  decoded : CursorStateAt code cert second.returned BurnInitialBalanceSite.second.afterDecodeTree
    second.returned.devm (Bytes.toB256 (out1.take 32) :: burnInitialTail1 sevm b out0)
    (burnInitialReplyMemory sevm out0 out1) [t_053d_c83]

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

/-- Original deployed Burn success selects its first three external instructions
and their replies, with no externally supplied occurrence or fee result. -/
theorem burn_three_occurrences_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    Nonempty (BurnThreeCalls root sevm b) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨first, second, cursor1, gas0, gas1, out0, out1,
    gap0, input0, reply0, width0, bound0, gap1, env1, outcome1, input1,
    primitive1, placed1, tree1, cont1, reply1, width1, bound1, ⟨decoded⟩⟩ :=
    burn_initial_occurrences_of_success codeEq fork selector run
  let initial : BurnInitialPair root sevm b :=
    ⟨first, second, gas0, gas1, out0, out1, gap0, input0, reply0, width0, bound0,
      gap1, env1, input1, reply1, width1, bound1, decoded⟩
  have envRet : second.returned.sevm = sevm :=
    (Cursor.parentStep_sevm second.edge).trans env1
  have successRet : second.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq (second.sameFrame.snoc second.edge)
  have forkRet : CoveredFork second.returned.sevm.benvStat.fork := by
    rw [envRet]; exact fork
  have mem := balanceReplyMemory_ptr out1
    (balanceRequestMemory_ptr
      (balanceReplyMemory_ptr out0
        (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)) sevm.currentTarget)
  obtain ⟨callee⟩ := burn_fee_caller_cursor_state
    (R := [0x89afcb44]) (K := [t_053d_c83])
    (b1 := Bytes.toB256 (out1.take 32)) (discarded := 0)
    (b0 := Bytes.toB256 (out0.take 32))
    (token1 := burnInitialToken1 sevm b) (token0 := burnInitialToken0 sevm b)
    (r1 := burnInitialReserve1 sevm b) (r0 := burnInitialReserve0 sevm b)
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) (extρ := 0x053d)
    decoded successRet forkRet mem
  obtain ⟨fee⟩ := pair_fee_observation_of_callee callee
    (second.sameFrame.snoc second.edge) successRet forkRet
    (feeBurnMemory_ptr mem second.returned.sevm.currentTarget)
  exact ⟨⟨initial, fee⟩⟩

end Blanc.Lift.UniswapV2Pair
