import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.UniswapV2Pair.LPBurnCore

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The actual LP burn returns through its original caller with the sequential
storage/log world derived by entry63, without a storage-representation premise. -/
theorem pair_lp_burn_cursor_state {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {caller : SFunc}
    {fromWord value ρ : B256}
    (cut : CursorStateAt code cert root t_2992_c63 b
      (value :: fromWord :: ρ :: R) M (caller :: K))
    (success : root.exn = .ok post) (fork : CoveredFork root.sevm.benvStat.fork)
    (mem : PtrMem 128 192 M) :
    root.sevm.isStatic = false ∧ value ≤ lpBurnBalanceWord root.sevm b fromWord ∧
      value ≤ lpBurnSupplyWord root.sevm
        (afterSload root.sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord root.sevm b fromWord - value) ∧
      ∃ residual, Nonempty (CursorStateAt code cert root caller
        (lpBurnPost root.sevm b R M fromWord value residual) R
        (lpBurnPost root.sevm b R M fromWord value residual).memory K) := by
  obtain ⟨returned, cursor, gap, env, outcome, placed, tree, conts, run⟩ :=
    cut.placed.quietReturn cert_check (cut.exn_eq.trans success) (cut.sevm_eq ▸ fork)
      (E := [9, 18, 59]) (caller := caller) (K := K) (by decide) (by decide)
      (by rw [cut.tree]; decide) (by rw [cut.tree]; decide) cut.continuations
  obtain ⟨gas, state⟩ := cut.state
  rw [cut.sevm_eq, cut.tree, state] at run
  obtain ⟨nonstatic, balance, supply, residual, result⟩ := lpBurn63_inv fork mem run
  have full : returned.devm = lpBurnPost root.sevm b R M fromWord value residual :=
    Outcome.returned.inj result
  have machine : returned.devm = St
      (lpBurnPost root.sevm b R M fromWord value residual) R
      (lpBurnPost root.sevm b R M fromWord value residual).memory residual := by
    rw [full]
    exact St.self rfl rfl
  exact ⟨nonstatic, balance, supply, residual,
    ⟨⟨returned, cursor, cut.free.trans gap, env.trans cut.sevm_eq,
      outcome.trans cut.exn_eq, placed, tree, ⟨residual, machine⟩, conts⟩⟩⟩

end Blanc.Lift.UniswapV2Pair
