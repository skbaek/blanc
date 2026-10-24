import Blanc.Lift.HistCursorReturn
import Blanc.Lift.CursorQuietReturn
import Blanc.Lift.CursorStateCuts
import Blanc.Lift.UniswapV2Pair.Check
import Blanc.Lift.UniswapV2Pair.LPBurnCore
import Blanc.Lift.UniswapV2Pair.LPMintCore

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem pairLPBurnPost_ptrH {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {fromWord value : B256} {G : Nat} (mem : PtrMem 128 192 M) :
    PtrMem 128 192 (lpBurnPostH sevm b R M fromWord value G).memory := by
  simpa only [lpBurnPostH, lpBurnBalancePostH, lpBurnSupplyPostH, St.memory, lpMintMemory] using
    lpMintMemory_ptr (lpMintScratch_ptr mem fromWord) fromWord value

theorem pair_lp_burn_cursor_stateH {root : Exec.Deriv} {b post : Devm}
    {R : List B256} {M : Mem} {K : List SFunc} {caller : SFunc}
    {fromWord value ρ : B256}
    (cut : CursorStateAt code cert root t_2992_c63 b
      (value :: fromWord :: ρ :: R) M (caller :: K))
    (success : root.exn = .ok post) (stateGas : root.sevm.benvStat.rules.stateGas = none)
    (bal : root.sevm.benvStat.rules.bal = none)
    (mem : PtrMem 128 192 M) :
    root.sevm.isStatic = false ∧ value ≤ lpBurnBalanceWord root.sevm b fromWord ∧
      value ≤ lpBurnSupplyWordH root.sevm
        (afterSloadH root.sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord root.sevm b fromWord - value) ∧
      ∃ residual, Nonempty (CursorStateAt code cert root caller
        (lpBurnPostH root.sevm b R M fromWord value residual) R
        (lpBurnPostH root.sevm b R M fromWord value residual).memory K) := by
  obtain ⟨returned, cursor, gap, env, outcome, placed, tree, conts, run⟩ :=
    cut.placed.quietReturnH cert_check (cut.exn_eq.trans success) (cut.sevm_eq ▸ stateGas)
      (E := [9, 18, 59]) (caller := caller) (K := K) (by decide) (by decide)
      (by rw [cut.tree]; decide) (by rw [cut.tree]; decide) cut.continuations
  obtain ⟨gas, state⟩ := cut.state
  rw [cut.sevm_eq, cut.tree, state] at run
  obtain ⟨nonstatic, balance, supply, residual, result⟩ := lpBurn63_invH stateGas bal mem run
  have full : returned.devm = lpBurnPostH root.sevm b R M fromWord value residual :=
    Outcome.returned.inj result
  have machine : returned.devm = St
      (lpBurnPostH root.sevm b R M fromWord value residual) R
      (lpBurnPostH root.sevm b R M fromWord value residual).memory residual := by
    rw [full]
    exact St.self rfl rfl
  exact ⟨nonstatic, balance, supply, residual,
    ⟨⟨returned, cursor, cut.free.trans gap, env.trans cut.sevm_eq,
      outcome.trans cut.exn_eq, placed, tree, ⟨residual, machine⟩, conts⟩⟩⟩


end Blanc.Lift.UniswapV2Pair
