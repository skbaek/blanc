import Blanc.Lift.CursorGasCall
import Blanc.Lift.UniswapV2Pair.PairReservesCursor
import Blanc.Lift.UniswapV2Pair.MintPositionalInv
import Blanc.Lift.UniswapV2Pair.MintPositionalRequest

/-! Actual same-root Mint external instructions and their original slots. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def MintBalanceSite.afterCallTree (site : MintBalanceSite) : SFunc :=
  match site.callTree with
  | .dest (.next _ (.next _ (.next _ tail))) => tail
  | _ => .undefined

/-- One Mint balance call at its actual cursor and same supplied root. -/
structure MintBalanceOccurrence (root start : Exec.Deriv) (site : MintBalanceSite)
    (b : Devm) (token : B256) (S : List B256) (M : Mem) (K : List SFunc) where
  call : CallOccurrenceStep root .staticcall
  cursor : Cursor
  gas : Nat
  free : Exec.Deriv.ExecFreeUntil start call.occurrence.node
  sevm_eq : call.occurrence.node.sevm = start.sevm
  exn_eq : call.occurrence.node.exn = start.exn
  input : call.occurrence.node.devm = St b
    (gas.toB256 :: token :: 128 :: 36 :: 128 :: 32 :: S) M gas
  primitive : Ninst.RunWith (Cursor.DescOf call.occurrence.node) start.sevm
    call.occurrence.node.devm (.exec .staticcall) call.returned.devm
  placed : CursorOK code cert call.returned cursor
  tree : cursor.f = site.afterCallTree
  continuations : cursor.K.map Cont.f = K

/-- GAS uses the actual remaining gas before this actual filled STATICCALL slot. -/
theorem mint_balance_occurrence_of_request_cursor {root start : Exec.Deriv}
    {b post : Devm} {R : List B256} {M : Mem} {z token a x y : B256} {K : List SFunc}
    (site : MintBalanceSite)
    (cut : CursorStateAt code cert start site.callTree b
      (z :: token :: 128 :: 36 :: 128 :: 32 :: a :: x :: y :: R) M K)
    (reached : Exec.Deriv.ParentPrefix root start)
    (success : start.exn = .ok post) (fork : CoveredFork start.sevm.benvStat.fork) :
    Nonempty (MintBalanceOccurrence root start site b token (a :: x :: y :: R) M K) := by
  have shape : site.callTree = .dest (.next (.reg .pop)
    (.next (.reg .gas) (.next (.exec .staticcall) site.afterCallTree))) := by cases site <;> rfl
  rw [shape] at cut
  obtain ⟨opened⟩ := cut.dest cert_check success fork
  obtain ⟨beforeGas⟩ := opened.line cert_check success fork [.reg .pop] rfl
    (by intro n member xi equal; subst n; simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at member)
    (by
      intro gas d line
      obtain ⟨_, step, line⟩ := Line.of_run_cons line
      cases line
      exact ri_pop step)
  obtain ⟨call, cursor, gas, free, env, outcome, input, primitive, placed, tree, K⟩ :=
    beforeGas.gasCall cert_check reached success fork
  exact ⟨⟨call, cursor, gas, free, env, outcome, input, primitive, placed, tree, K⟩⟩

/-- The successful original Mint root produces its first actual balance call.
The complete request state and original slot are selected by that same execution. -/
theorem mint_first_occurrence_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    let root : Exec.Deriv := ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩
    let reserveWorld := afterSload sevm (mintLockedWorld sevm b) 8
    let token := (reserveWorld.getStorVal sevm.currentTarget 6).toAdr.toB256
    Nonempty (MintBalanceOccurrence root root .first
      (temporalAccountAccessBase (afterSload sevm reserveWorld 6) token.toAdr) token
      (164 :: 0x70a08231 :: token :: 0 ::
        reserve1Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
        reserve0Read ((mintLockedWorld sevm b).getStorVal sevm.currentTarget 8) ::
        0 :: (Sevm.dataWord sevm 4).toAdr.toB256 :: 0x039b :: [0x6a627842])
      (balanceRequestMemory getterInitMemory sevm.currentTarget) [t_039b_c86]) := by
  obtain ⟨_, _, abi, unlocked, _⟩ := mint_prefix_guards_of_success codeEq fork selector run
  obtain ⟨entry⟩ := mint_public_cursor_state codeEq fork selector run
  obtain ⟨internal⟩ := mint_abi_cursor_state entry rfl fork abi
  obtain ⟨reserves⟩ := mint_lock_cursor_state internal rfl fork unlocked
  obtain ⟨requestEntry⟩ := pair_reserves_cursor_state reserves rfl fork
  obtain ⟨request⟩ := mint_first_guard_cursor_state requestEntry rfl fork getterInitMemory_ptr
  exact mint_balance_occurrence_of_request_cursor .first request (.refl _) rfl fork

end Blanc.Lift.UniswapV2Pair
