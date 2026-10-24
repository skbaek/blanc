import Blanc.Lift.HistCursorCalls
import Blanc.Lift.UniswapV2Pair.SkimPositionalPrefix
import Blanc.Lift.UniswapV2Pair.PairCodeGuardCursor
import Blanc.Lift.CursorGasCall

namespace Blanc.Lift.UniswapV2Pair
open Jaune

def skimFirstBalanceRest (sevm : Sevm) (b : Devm) (toWord : B256)
    (R : List B256) : List B256 :=
  164 :: 0x70a08231 :: skimToken0 sevm b :: skimReserve0 sevm b ::
    0x1a26 :: toWord :: skimToken0 sevm b :: 0x1a2b :: skimToken1 sevm b ::
    skimToken0 sevm b :: toWord :: R

def skimFirstAfterCallTree : SFunc :=
  .next (.reg .iszero) (.next (.reg (.dup 0)) (.next (.reg .iszero)
    (.next (.push [0x1a, 0x02] (by decide)) (.branch t_19f9_c34 t_1a02_c34))))

theorem skim_first_guard_cursor_stateH {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {toWord : B256}
    (cut : CursorStateAt code cert root t_194f_c34 (afterSloadH root.sevm b 12)
      (toWord :: R) getterInitMemory [])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) :
    root.sevm.isStatic = false ∧
    ((skimCachedWorldH root.sevm b).getCode (skimToken0 root.sevm b).toAdr).size.toB256 ≠ 0 ∧
    Nonempty (CursorStateAt code cert root t_19ee_c34
      (accountAccessH root.sevm (skimCachedWorldH root.sevm b) (skimToken0 root.sevm b).toAdr)
      (0 :: skimToken0 root.sevm b :: 128 :: 36 :: 128 :: 32 ::
        skimFirstBalanceRest root.sevm b toWord R)
      (balanceRequestMemory getterInitMemory root.sevm.currentTarget) []) := by
  obtain ⟨G, state⟩ := cut.state
  obtain ⟨outcome, source⟩ := cut.placed.sourceRunH cert_check
    (cut.exn_eq.trans success) (by rw [cut.sevm_eq]; exact stateGas)
  rw [cut.tree, state, cut.sevm_eq] at source
  have nonstatic := (skimFirstHalf_invH stateGas bal getterInitMemory_ptr
    (SFunc.runP_iff_runCutP_nil.mp source)).1
  obtain ⟨opened⟩ := cut.destH cert_check success stateGas
  obtain ⟨request⟩ := opened.lineH cert_check success stateGas skimFirstLine (by rfl)
    (by
      intro n member x equal; subst n
      simp only [skimFirstLine, List.mem_cons, List.not_mem_nil,
        reduceCtorEq, or_self] at member)
    (b' := skimCachedWorldH root.sevm b)
    (S' := skimToken0 root.sevm b :: skimToken0 root.sevm b :: 128 :: 36 :: 128 :: 32 ::
      skimFirstBalanceRest root.sevm b toWord R)
    (M' := balanceRequestMemory getterInitMemory root.sevm.currentTarget)
    (by intro gas d line; exact (skimFirstLine_invH stateGas bal getterInitMemory_ptr line).2)
  obtain ⟨codeGuard, entered⟩ := pair_code_guard_cursor_stateH request success stateGas bal
    [0x19, 0xee] (by decide) rfl (by decide : t_19ea_c34.noOk = true)
  exact ⟨nonstatic, codeGuard, entered⟩


theorem skim_first_call_of_prefixH {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {toWord : B256}
    (cut : CursorStateAt code cert root t_194f_c34 (afterSloadH root.sevm b 12)
      (toWord :: R) getterInitMemory [])
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none) :
    root.sevm.isStatic = false ∧
    ((skimCachedWorldH root.sevm b).getCode (skimToken0 root.sevm b).toAdr).size.toB256 ≠ 0 ∧
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = root.sevm ∧ step.occurrence.node.exn = root.exn ∧
      step.occurrence.node.devm = St
        (accountAccessH root.sevm (skimCachedWorldH root.sevm b) (skimToken0 root.sevm b).toAdr)
        (gas.toB256 :: skimToken0 root.sevm b :: 128 :: 36 :: 128 :: 32 ::
          skimFirstBalanceRest root.sevm b toWord R)
        (balanceRequestMemory getterInitMemory root.sevm.currentTarget) gas ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) root.sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧ cursor.f = skimFirstAfterCallTree ∧
      cursor.K.map Cont.f = [] := by
  obtain ⟨nonstatic, codeGuard, ⟨guarded⟩⟩ := skim_first_guard_cursor_stateH cut success stateGas bal
  obtain ⟨opened⟩ := guarded.destH cert_check success stateGas
  obtain ⟨ready⟩ := opened.lineH cert_check success stateGas [.reg .pop] rfl
    (by intro n member x equal; subst n
        simp only [List.mem_singleton, reduceCtorEq] at member)
    (by intro gas d line
        obtain ⟨_, step, line⟩ := Line.of_run_cons line
        cases line
        exact ri_pop step)
  exact ⟨nonstatic, codeGuard, ready.gasCallH cert_check (.refl root) success stateGas⟩


end Blanc.Lift.UniswapV2Pair
