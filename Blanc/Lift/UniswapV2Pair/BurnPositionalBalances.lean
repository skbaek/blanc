import Blanc.Lift.UniswapV2Pair.BurnPositional
import Blanc.Lift.UniswapV2Pair.BurnPositionalReply
import Blanc.Lift.UniswapV2Pair.BurnPositionalSecond
import Blanc.ExecutionModelAccounting

/-! Actual initial Burn balance occurrences from public successful execution. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune


def burnInitialReserveWorld (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (burnLockedWorld sevm b) 8

def burnInitialReserveWorldH (sevm : Sevm) (b : Devm) : Devm :=
  afterSloadH sevm (burnLockedWorldH sevm b) 8

theorem burnInitialReserveWorldH_of_covered {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) :
    burnInitialReserveWorldH sevm b = burnInitialReserveWorld sevm b := by
  unfold burnInitialReserveWorldH burnInitialReserveWorld
  simp only [burnLockedWorldH_of_covered fork, afterSloadH_of_eip2929 fork.rules_access]

/-- The historical reserve world stores the same words as the modern one. -/
theorem burnInitialReserveWorldH_getStorVal (sevm : Sevm) (b : Devm) (k : B256) :
    (burnInitialReserveWorldH sevm b).getStorVal sevm.currentTarget k =
      (burnInitialReserveWorld sevm b).getStorVal sevm.currentTarget k := by
  unfold burnInitialReserveWorldH burnInitialReserveWorld
  rw [getStorVal_afterSloadH, getStorVal_afterSload, burnLockedWorldH_getStorVal]

def burnInitialToken0 (sevm : Sevm) (b : Devm) : B256 :=
  0xffffffffffffffffffffffffffffffffffffffff &&&
    (burnInitialReserveWorld sevm b).getStorVal sevm.currentTarget 6

def burnInitialToken1 (sevm : Sevm) (b : Devm) : B256 :=
  0xffffffffffffffffffffffffffffffffffffffff &&&
    (afterSload sevm (burnInitialReserveWorld sevm b) 6).getStorVal sevm.currentTarget 7

def burnInitialWorld0 (sevm : Sevm) (b : Devm) : Devm :=
  temporalAccountAccessBase (burnTokensWorld sevm (burnInitialReserveWorld sevm b))
    (burnInitialToken0 sevm b).toAdr

def burnInitialWorld0H (sevm : Sevm) (b : Devm) : Devm :=
  accountAccessH sevm (burnTokensWorldH sevm (burnInitialReserveWorldH sevm b))
    (burnInitialToken0 sevm b).toAdr

theorem burnInitialWorld0H_of_covered {sevm : Sevm} {b : Devm}
    (fork : CoveredFork sevm.benvStat.fork) :
    burnInitialWorld0H sevm b = burnInitialWorld0 sevm b := by
  unfold burnInitialWorld0H burnInitialWorld0
  simp only [burnInitialReserveWorldH_of_covered fork, burnTokensWorldH_of_covered fork, accountAccessH_of_eip2929 fork.rules_access]

/-- The historical first request, with its cached token words read as the modern storage reads. -/
theorem burnFirstCallInputH_initial (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat)
    (r1 r0 toWord extρ : B256) :
    burnFirstCallInputH sevm (burnInitialReserveWorldH sevm b) R M G r1 r0 toWord extρ =
      St (accountAccessH sevm (burnTokensWorldH sevm (burnInitialReserveWorldH sevm b))
          (burnInitialToken0 sevm b).toAdr)
        (G.toB256 :: burnInitialToken0 sevm b :: 128 :: 36 :: 128 :: 32 :: 164 :: 0x70a08231 ::
          burnInitialToken0 sevm b :: 0 :: burnInitialToken1 sevm b :: burnInitialToken0 sevm b ::
          r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
        (balanceRequestMemory M sevm.currentTarget) G := by
  have t0 : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&& (burnInitialReserveWorldH sevm b).getStorVal sevm.currentTarget 6 =
      burnInitialToken0 sevm b := by
    rw [burnInitialReserveWorldH_getStorVal]; rfl
  have t1 : (0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
      (afterSloadH sevm (burnInitialReserveWorldH sevm b) 6).getStorVal sevm.currentTarget 7 =
      burnInitialToken1 sevm b := by
    rw [getStorVal_afterSloadH, burnInitialReserveWorldH_getStorVal, burnInitialToken1,
      getStorVal_afterSload]
  simp only [burnFirstCallInputH, t0, t1]

def burnInitialTail0 (sevm : Sevm) (b : Devm) : List B256 :=
  [0, burnInitialToken1 sevm b, burnInitialToken0 sevm b,
    reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8),
    reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8),
    0, 0, (Sevm.dataWord sevm 4).toAdr.toB256, 0x053d, 0x89afcb44]

theorem burn_first_observation_of_successH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat) (out : Bytes),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = sevm ∧ step.occurrence.node.exn = .ok post ∧
      step.occurrence.node.devm = burnFirstCallInputH sevm (burnInitialReserveWorldH sevm b)
        [0x89afcb44] getterInitMemory gas
        (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (Sevm.dataWord sevm 4).toAdr.toB256 0x053d ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnFirstAfterCallTree ∧ cursor.K.map Cont.f = [t_053d_c83] ∧
      StaticCallPost (burnInitialWorld0H sevm b) step.returned.devm
        (164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 36 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      StaticAnsweredH sevm (burnInitialWorld0H sevm b) (burnInitialToken0 sevm b).toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out ∧
      Nonempty (CursorStateAt code cert step.returned BurnInitialBalanceSite.first.afterDecodeTree
        step.returned.devm (Bytes.toB256 (out.take 32) :: burnInitialTail0 sevm b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget out) [t_053d_c83]) := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨step, cursor, gas, gap, env, outcome, input, primitive, placed, tree, conts⟩ :=
    burn_first_occurrence_of_successH codeEq stateGas bal selector run
  simp only [burnLockedWorldH_getStorVal] at input
  have envRet : step.returned.sevm = sevm := (Cursor.parentStep_sevm step.edge).trans env
  have successRet : step.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq (step.sameFrame.snoc step.edge)
  have call : Ninst.Run sevm
      (St (burnInitialWorld0H sevm b)
        (gas.toB256 :: burnInitialToken0 sevm b :: 128 :: 36 :: 128 :: 32 ::
          164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) gas)
      (.exec .staticcall) step.returned.devm := by
    simpa only [input, burnFirstCallInputH, burnInitialWorld0H, burnInitialToken0,
      burnInitialToken1, burnInitialTail0, burnInitialReserveWorldH, burnInitialReserveWorld,
      getStorVal_afterSloadH, getStorVal_afterSload, burnLockedWorldH_getStorVal] using primitive.toRun
  obtain ⟨flag, out, reply, bound, answered⟩ := ri_staticcall_boundedH stateGas call
  have mem := balanceReplyMemory_ptr out
    (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)
  have actualReply : StaticCallPost (burnInitialWorld0H sevm b) step.returned.devm
      (164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
      (balanceRequestMemory getterInitMemory step.returned.sevm.currentTarget)
      128 36 128 32 flag out := by rw [envRet]; exact reply
  obtain ⟨one, long, decoded⟩ := burn_initial_actual_reply_cursorH .first placed tree
    successRet (by rw [envRet]; exact stateGas) actualReply
    (by rw [envRet]; exact mem) bound
  rw [envRet, conts,
    balanceReplyMemory_word getterInitMemory_ptr.wf sevm.currentTarget out long] at decoded
  have accepted : StaticAnsweredH sevm (burnInitialWorld0H sevm b)
      (burnInitialToken0 sevm b).toAdr
      (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out := by
    have accepted := answered one
    change StaticAnsweredH sevm (burnInitialWorld0H sevm b) (burnInitialToken0 sevm b).toAdr
      ((balanceRequestMemory getterInitMemory sevm.currentTarget).read 128 36).1 out at accepted
    rw [balanceRequestMemory_read getterInitMemory_ptr.wf] at accepted
    exact accepted
  rw [one] at reply
  exact ⟨step, cursor, gas, out, gap, env, outcome, input, primitive, placed, tree, conts,
    reply, long, bound, accepted, decoded⟩

/-- The first decoded observation is attached to the actual original-root
occurrence and its actual returned parent, including the physical reply. -/
theorem burn_first_observation_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat) (out : Bytes),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = sevm ∧ step.occurrence.node.exn = .ok post ∧
      step.occurrence.node.devm = burnFirstCallInput sevm (burnInitialReserveWorld sevm b)
        [0x89afcb44] getterInitMemory gas
        (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (Sevm.dataWord sevm 4).toAdr.toB256 0x053d ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnFirstAfterCallTree ∧ cursor.K.map Cont.f = [t_053d_c83] ∧
      StaticCallPost (burnInitialWorld0 sevm b) step.returned.devm
        (164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 36 128 32 1 out ∧
      32 ≤ out.length ∧ out.length < 2 ^ 256 ∧
      StaticAnswered sevm (burnInitialWorld0 sevm b) (burnInitialToken0 sevm b).toAdr
        (ExternalOperation.encode (.balanceOf sevm.currentTarget)) out ∧
      Nonempty (CursorStateAt code cert step.returned BurnInitialBalanceSite.first.afterDecodeTree
        step.returned.devm (Bytes.toB256 (out.take 32) :: burnInitialTail0 sevm b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget out) [t_053d_c83]) := by
  simpa only [burnFirstCallInputH_of_covered fork, burnInitialReserveWorldH_of_covered fork, burnInitialWorld0H_of_covered fork, burnLockedWorldH_of_covered fork, StaticAnsweredH_iff_of_covered fork] using
    burn_first_observation_of_successH codeEq fork.rules_stateGas_none fork.rules_bal_none selector run



def burnInitialTarget1 (sevm : Sevm) (b : Devm) : B256 :=
  burnInitialToken1 sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff

def burnInitialTail1 (sevm : Sevm) (b : Devm) (out0 : Bytes) : List B256 :=
  0 :: Bytes.toB256 (out0.take 32) :: (burnInitialTail0 sevm b).tail

def burnInitialSecondInput (sevm : Sevm) (b returned0 : Devm) (out0 : Bytes)
    (gas : Nat) : Devm :=
  St (temporalAccountAccessBase returned0 (burnInitialTarget1 sevm b).toAdr)
    (gas.toB256 :: burnInitialTarget1 sevm b :: 128 :: 36 :: 128 :: 32 ::
      164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
    (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
      sevm.currentTarget) gas

def burnInitialSecondInputH (sevm : Sevm) (b returned0 : Devm) (out0 : Bytes)
    (gas : Nat) : Devm :=
  St (accountAccessH sevm returned0 (burnInitialTarget1 sevm b).toAdr)
    (gas.toB256 :: burnInitialTarget1 sevm b :: 128 :: 36 :: 128 :: 32 ::
      164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
    (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
      sevm.currentTarget) gas

theorem burnInitialSecondInputH_of_covered {sevm : Sevm} {b returned0 : Devm} {out0 : Bytes} {gas : Nat}
    (fork : CoveredFork sevm.benvStat.fork) :
    burnInitialSecondInputH sevm b returned0 out0 gas = burnInitialSecondInput sevm b returned0 out0 gas := by
  unfold burnInitialSecondInputH burnInitialSecondInput
  simp only [accountAccessH_of_eip2929 fork.rules_access]

theorem burn_initial_occurrences_of_successH {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (stateGas : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (first second : CallOccurrenceStep root .staticcall)
      (cursor1 : Cursor) (gas0 gas1 : Nat) (out0 out1 : Bytes),
      Exec.Deriv.ExecFreeUntil root first.occurrence.node ∧
      first.occurrence.node.devm = burnFirstCallInputH sevm (burnInitialReserveWorldH sevm b)
        [0x89afcb44] getterInitMemory gas0
        (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (Sevm.dataWord sevm 4).toAdr.toB256 0x053d ∧
      StaticCallPost (burnInitialWorld0H sevm b) first.returned.devm
        (164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      Exec.Deriv.ExecFreeUntil first.returned second.occurrence.node ∧
      second.occurrence.node.sevm = sevm ∧ second.occurrence.node.exn = .ok post ∧
      second.occurrence.node.devm = burnInitialSecondInputH sevm b first.returned.devm out0 gas1 ∧
      Ninst.RunWith (Cursor.DescOf second.occurrence.node) sevm
        second.occurrence.node.devm (.exec .staticcall) second.returned.devm ∧
      CursorOK code cert second.returned cursor1 ∧
      cursor1.f = burnSecondAfterCallTree ∧ cursor1.K.map Cont.f = [t_053d_c83] ∧
      StaticCallPost (accountAccessH sevm first.returned.devm (burnInitialTarget1 sevm b).toAdr)
        second.returned.devm
        (164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
          sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      Nonempty (CursorStateAt code cert second.returned BurnInitialBalanceSite.second.afterDecodeTree
        second.returned.devm (Bytes.toB256 (out1.take 32) :: burnInitialTail1 sevm b out0)
        (balanceReplyMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
          sevm.currentTarget out1) [t_053d_c83]) ∧
      Nonempty (CursorStateAt code cert first.returned BurnInitialBalanceSite.first.afterDecodeTree
        first.returned.devm (Bytes.toB256 (out0.take 32) :: burnInitialTail0 sevm b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget out0) [t_053d_c83]) ∧
      ((burnInitialWorld0H sevm b).getCode (burnInitialToken0 sevm b).toAdr).size.toB256 ≠ 0 ∧
      (first.returned.devm.getCode (burnInitialTarget1 sevm b).toAdr).size.toB256 ≠ 0 := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨first, cursor0, gas0, out0, gap0, env0, outcome0, input0, primitive0,
    placed0, tree0, cont0, reply0, long0, bound0, answered0, ⟨decoded0⟩⟩ :=
    burn_first_observation_of_successH codeEq stateGas bal selector run
  have envRet0 : first.returned.sevm = sevm := (Cursor.parentStep_sevm first.edge).trans env0
  have successRet0 : first.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq (first.sameFrame.snoc first.edge)
  have mem0 := balanceReplyMemory_ptr out0
    (balanceRequestMemory_ptr getterInitMemory_ptr sevm.currentTarget)
  have decoded0' : CursorStateAt code cert first.returned BurnInitialBalanceSite.first.afterDecodeTree
      first.returned.devm (Bytes.toB256 (out0.take 32) :: burnInitialTail0 sevm b)
      (balanceReplyMemory getterInitMemory first.returned.sevm.currentTarget out0) [t_053d_c83] := by
    rw [envRet0]
    exact decoded0
  obtain ⟨code1, ⟨request1⟩⟩ := burn_second_guard_cursor_dataH
    (R := [0x89afcb44]) (b0 := Bytes.toB256 (out0.take 32))
    (token1 := burnInitialToken1 sevm b) (token0 := burnInitialToken0 sevm b)
    (r1 := reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (r0 := reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
    (toWord := (Sevm.dataWord sevm 4).toAdr.toB256) (extρ := 0x053d)
    decoded0' successRet0 (by rw [envRet0]; exact stateGas) (by rw [envRet0]; exact bal) (by rw [envRet0]; exact mem0)
  obtain ⟨second, cursor1, gas1, gap1, env1, outcome1, input1, primitive1,
    placed1, tree1, cont1⟩ := burn_second_call_of_request_cursorH request1
    (first.sameFrame.snoc first.edge) successRet0 (by rw [envRet0]; exact stateGas)
  have env1' : second.occurrence.node.sevm = sevm := env1.trans envRet0
  have outcome1' : second.occurrence.node.exn = .ok post := outcome1.trans successRet0
  have envRet1 : second.returned.sevm = sevm := (Cursor.parentStep_sevm second.edge).trans env1'
  have successRet1 : second.returned.exn = .ok post :=
    Blanc.Exec.Deriv.ParentPrefix.exn_eq (second.sameFrame.snoc second.edge)
  rw [envRet0] at input1 primitive1
  have input1' : second.occurrence.node.devm =
      burnInitialSecondInputH sevm b first.returned.devm out0 gas1 := input1
  have call1 : Ninst.Run sevm
      (St (accountAccessH sevm first.returned.devm (burnInitialTarget1 sevm b).toAdr)
        (gas1.toB256 :: burnInitialTarget1 sevm b :: 128 :: 36 :: 128 :: 32 ::
          164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
          sevm.currentTarget) gas1) (.exec .staticcall) second.returned.devm := by
    rw [input1'] at primitive1
    exact primitive1.toRun
  obtain ⟨flag1, out1, reply1, bound1, _⟩ := ri_staticcall_boundedH stateGas call1
  have mem1 := balanceReplyMemory_ptr out1 (balanceRequestMemory_ptr mem0 sevm.currentTarget)
  have actualReply1 : StaticCallPost
      (accountAccessH sevm first.returned.devm (burnInitialTarget1 sevm b).toAdr)
      second.returned.devm
      (164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
      (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
        second.returned.sevm.currentTarget) 128 36 128 32 flag1 out1 := by
    rw [envRet1]
    exact reply1
  obtain ⟨one1, long1, decoded1⟩ := burn_initial_actual_reply_cursorH .second placed1 tree1
    successRet1 (by rw [envRet1]; exact stateGas) actualReply1
    (by rw [envRet1]; exact mem1) bound1
  rw [envRet1, cont1, balanceReplyMemory_word mem0.wf sevm.currentTarget out1 long1] at decoded1
  rw [one1] at reply1
  obtain ⟨_, _, _, _, _, code0⟩ := burn_prefix_guards_of_successH codeEq stateGas bal selector run
  have code0' : ((burnInitialWorld0H sevm b).getCode (burnInitialToken0 sevm b).toAdr).size.toB256 ≠ 0 := by
    simpa only [burnInitialWorld0H, burnInitialToken0, burnInitialReserveWorldH,
      burnInitialReserveWorld, getStorVal_afterSloadH, getStorVal_afterSload,
      burnLockedWorldH_getStorVal, Devm.getCode, Devm.getAcct, accountAccessH_state] using code0
  refine ⟨first, second, cursor1, gas0, gas1, out0, out1, gap0, input0, reply0,
    long0, bound0, gap1, env1', outcome1', input1', ?_, placed1, tree1, cont1,
    reply1, long1, bound1, decoded1, ⟨decoded0⟩, code0', code1⟩
  exact primitive1

/-- Both initial observations are actual positions in the supplied original
Burn execution. The second request uses the first actual reply and returned
world, and the intervening prefix contains no external instruction. -/
theorem burn_initial_occurrences_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (first second : CallOccurrenceStep root .staticcall)
      (cursor1 : Cursor) (gas0 gas1 : Nat) (out0 out1 : Bytes),
      Exec.Deriv.ExecFreeUntil root first.occurrence.node ∧
      first.occurrence.node.devm = burnFirstCallInput sevm (burnInitialReserveWorld sevm b)
        [0x89afcb44] getterInitMemory gas0
        (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (Sevm.dataWord sevm 4).toAdr.toB256 0x053d ∧
      StaticCallPost (burnInitialWorld0 sevm b) first.returned.devm
        (164 :: 0x70a08231 :: burnInitialToken0 sevm b :: burnInitialTail0 sevm b)
        (balanceRequestMemory getterInitMemory sevm.currentTarget) 128 36 128 32 1 out0 ∧
      32 ≤ out0.length ∧ out0.length < 2 ^ 256 ∧
      Exec.Deriv.ExecFreeUntil first.returned second.occurrence.node ∧
      second.occurrence.node.sevm = sevm ∧ second.occurrence.node.exn = .ok post ∧
      second.occurrence.node.devm = burnInitialSecondInput sevm b first.returned.devm out0 gas1 ∧
      Ninst.RunWith (Cursor.DescOf second.occurrence.node) sevm
        second.occurrence.node.devm (.exec .staticcall) second.returned.devm ∧
      CursorOK code cert second.returned cursor1 ∧
      cursor1.f = burnSecondAfterCallTree ∧ cursor1.K.map Cont.f = [t_053d_c83] ∧
      StaticCallPost (temporalAccountAccessBase first.returned.devm (burnInitialTarget1 sevm b).toAdr)
        second.returned.devm
        (164 :: 0x70a08231 :: burnInitialTarget1 sevm b :: burnInitialTail1 sevm b out0)
        (balanceRequestMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
          sevm.currentTarget) 128 36 128 32 1 out1 ∧
      32 ≤ out1.length ∧ out1.length < 2 ^ 256 ∧
      Nonempty (CursorStateAt code cert second.returned BurnInitialBalanceSite.second.afterDecodeTree
        second.returned.devm (Bytes.toB256 (out1.take 32) :: burnInitialTail1 sevm b out0)
        (balanceReplyMemory (balanceReplyMemory getterInitMemory sevm.currentTarget out0)
          sevm.currentTarget out1) [t_053d_c83]) ∧
      Nonempty (CursorStateAt code cert first.returned BurnInitialBalanceSite.first.afterDecodeTree
        first.returned.devm (Bytes.toB256 (out0.take 32) :: burnInitialTail0 sevm b)
        (balanceReplyMemory getterInitMemory sevm.currentTarget out0) [t_053d_c83]) ∧
      ((burnInitialWorld0 sevm b).getCode (burnInitialToken0 sevm b).toAdr).size.toB256 ≠ 0 ∧
      (first.returned.devm.getCode (burnInitialTarget1 sevm b).toAdr).size.toB256 ≠ 0 := by
  simpa only [burnFirstCallInputH_of_covered fork, burnInitialReserveWorldH_of_covered fork, burnInitialSecondInputH_of_covered fork, burnInitialWorld0H_of_covered fork, burnLockedWorldH_of_covered fork, accountAccessH_of_eip2929 fork.rules_access] using
    burn_initial_occurrences_of_successH codeEq fork.rules_stateGas_none fork.rules_bal_none selector run


end Blanc.Lift.UniswapV2Pair
