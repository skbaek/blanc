import Blanc.Lift.UniswapV2Pair.BurnPositionalCuts
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.CursorOccurrence
import Blanc.Lift.CursorGasCall
import Blanc.Lift.UniswapV2Pair.BurnPositionalInv

/-! Actual Burn call positions in the checked original-bytecode execution. -/

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- GAS and the first STATICCALL use the supplied actual request cursor.
The word supplied as call gas equals the actual successor's remaining gas. -/
theorem burn_first_call_of_request_cursor {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {r1 r0 toWord extρ : B256} {K : List SFunc}
    (cut : CursorStateAt code cert root t_14fb_c37
      (temporalAccountAccessBase (burnTokensWorld root.sevm b)
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6).toAdr)
      (0 :: ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6) :: 128 :: 36 :: 128 :: 32 :: 164 ::
        0x70a08231 :: ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6) :: 0 ::
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          (afterSload root.sevm b 6).getStorVal root.sevm.currentTarget 7) ::
        ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&&
          b.getStorVal root.sevm.currentTarget 6) ::
        r1 :: r0 :: 0 :: 0 :: toWord :: extρ :: R)
      (balanceRequestMemory M root.sevm.currentTarget) K)
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork) :
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = root.sevm ∧
      step.occurrence.node.exn = root.exn ∧
      step.occurrence.node.devm = burnFirstCallInput root.sevm b R M gas r1 r0 toWord extρ ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) root.sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnFirstAfterCallTree ∧ cursor.K.map Cont.f = K := by
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨beforeGas⟩ := opened.line cert_check success fork [.reg .pop] (by rfl)
    (by intro n member x equal; simp only [List.mem_singleton, equal, reduceCtorEq] at member)
    (by
      intro g d line
      obtain ⟨_, pop, tail⟩ := Line.of_run_cons line
      obtain ⟨g', state⟩ := ri_pop pop
      cases tail
      exact ⟨g', state⟩)
  simpa only [burnFirstCallInput] using
    beforeGas.gasCall (x := .staticcall) (tail := burnFirstAfterCallTree)
      cert_check (.refl root) success fork

/-- A successful public Burn execution produces its first original-bytecode
balance STATICCALL, exact request, filled actual slot and returned cursor.
All prefix guards and residual gas are derived from this supplied execution. -/
theorem burn_first_occurrence_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    ∃ (step : CallOccurrenceStep root .staticcall) (cursor : Cursor) (gas : Nat),
      Exec.Deriv.ExecFreeUntil root step.occurrence.node ∧
      step.occurrence.node.sevm = sevm ∧
      step.occurrence.node.exn = .ok post ∧
      step.occurrence.node.devm = burnFirstCallInput sevm
        (afterSload sevm (burnLockedWorld sevm b) 8) [0x89afcb44] getterInitMemory gas
        (reserve1Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (reserve0Read ((burnLockedWorld sevm b).getStorVal sevm.currentTarget 8))
        (Sevm.dataWord sevm 4).toAdr.toB256 0x053d ∧
      Ninst.RunWith (Cursor.DescOf step.occurrence.node) sevm
        step.occurrence.node.devm (.exec .staticcall) step.returned.devm ∧
      CursorOK code cert step.returned cursor ∧
      cursor.f = burnFirstAfterCallTree ∧ cursor.K.map Cont.f = [t_053d_c83] := by
  let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
  obtain ⟨_, _, abiSize, unlocked, _, nonzero⟩ :=
    burn_prefix_guards_of_success codeEq fork selector run
  obtain ⟨publicEntry⟩ := burn_public_cursor_state codeEq fork selector run
  obtain ⟨entry⟩ := burn_abi_cursor_state publicEntry rfl fork abiSize
  obtain ⟨reserveEntry⟩ := burn_lock_cursor_state entry rfl fork unlocked
  obtain ⟨requestEntry⟩ := burn_reserves_cursor_state reserveEntry rfl fork
  obtain ⟨request⟩ := burn_first_guard_cursor_state requestEntry rfl fork
    getterInitMemory_ptr nonzero
  exact burn_first_call_of_request_cursor request rfl fork

end Blanc.Lift.UniswapV2Pair
