import Blanc.Lift.SystemExecution.HistoryStorage.SystemWalk
import Blanc.Lift.SystemCallAmsterdam
import Blanc.Lift.WalkKit

namespace Blanc.Lift.HistoryStorage.Totality
open Jaune Blanc.Lift
open Blanc.Lift.SystemExecution.HistoryStorage

local notation "A" => amsterdamStateGasRules

/-- Amsterdam system execution starts with the actual prepared access records. -/
def base (benv : Benv) : Devm := systemCallBase (systemMsg benv)
def cost (benv : Benv) : Nat :=
  sstoreCostA A (systemSevm benv) (base benv) (systemKey benv) (systemValue benv)
def post (benv : Benv) : Devm :=
  St (afterSstoreA A (systemSevm benv) (base benv) (systemKey benv) (systemValue benv)) [] .empty
    (systemTransactionGas - (43 + cost benv))

private theorem ready {benv : Benv} (hf : benv.stat.fork = .amsterdam) :
    Ready (systemSevm benv) (base benv) [systemKey benv] where
  error := systemCallBase_error _
  refund := by rw [base, systemCallBase_refundCounter]
  spill := (systemCallBase_stateGas hf).1
  reservoir := by
    change _ ≤ (systemCallBase (systemMsg benv)).stateGas.left
    unfold systemMsg
    rw [(systemCallBase_stateGas hf).2]
    change 1 * amsterdamStateGasRules.storageSet ≤ amsterdamStateGasRules.systemReservoir
    decide
  clean := fun k _ => systemCallBase_orig rfl _ k

/-- The one-store system path with its exact regular-gas charge. -/
private theorem root_runA {benv : Benv} {G : Nat} (hf : benv.stat.fork = .amsterdam)
    (hg : gCallStipend < G) :
    SFunc.RunExact prog (systemSevm benv) (St (base benv) [] .empty (G + cost benv + 43))
      t_0000_c0 (.halted (St (afterSstoreA A (systemSevm benv) (base benv)
        (systemKey benv) (systemValue benv)) [] .empty G)) := by
  wrun!
  simp only [show (systemSevm benv).caller = systemAddress from rfl, B256.eqCheck]
  apply rx_branch_succ (by decide)
  wrun! 1
  refine rx_push0 (amsterdam_push0 hf) (by decide) ?_
  wrun!
  change SFunc.RunExact prog (systemSevm benv)
    (St (base benv) [systemKey benv, systemValue benv] .empty (G + cost benv)) _ _
  exact rx_sstoreR (amsterdam_stateGas hf) rfl (ready hf) (by omega) Blanc.Lift.rx_stop

/-- The actual Amsterdam system frame halts after its single ring-buffer write. -/
theorem system_exec {benv : Benv} (hf : benv.stat.fork = .amsterdam) :
    exec ⟨0, systemSevm benv, base benv⟩ = .ok (post benv) := by
  have hc : cost benv ≤ 12100 := sstoreCostA_le A _ _ _ _
  let G := systemTransactionGas - (43 + cost benv)
  have hg : gCallStipend < G := by change 2300 < 30000000 - (43 + cost benv); omega
  have hrun := root_runA hf hg
  have heq : G + cost benv + 43 = systemTransactionGas := by change 30000000 - (43 + cost benv) + cost benv + 43 = 30000000; omega
  rw [heq] at hrun
  have hentry : St (base benv) [] .empty systemTransactionGas = base benv := systemCallBase_St
  rw [hentry] at hrun
  apply (exec_iff_exec_eq _ _ _ _).mp
  apply lift_exact_noExec cert_check jumps_ok (by rfl) (progNoExec_of_all (by decide +kernel))
  exact ⟨t_0000_c0, prog_root, hrun⟩

/-- The call exposes the exact state update and the regular-gas bound. -/
theorem call_ok {benv : Benv} (hf : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode historyStorageAddress = historyStorageCode) :
    ∃ out, processUncheckedSystemTransaction benv historyStorageAddress
        (benv.stat.blockHashes.getLast?.getD 0).toBytes =
        .ok (benv.state.setStorVal historyStorageAddress (systemKey benv) (systemValue benv), out) ∧
      out.gasLeft ≤ systemTransactionGas ∧ systemTransactionGas - out.gasLeft ≤ 15000 := by
  have r := (ready hf).sstore (by simp only [List.not_mem_nil, not_false_eq_true]) (systemValue benv)
  have clean : (post benv).error = none := r.error
  have nonneg : 0 ≤ (post benv).refundCounter := r.refund
  have call := processSystemTransaction_amsterdam_of_exec hf installed
    (systemContracts_nondelegated member) (by decide) (system_exec hf) clean nonneg
  have hs : (post benv).state = benv.state.setStorVal historyStorageAddress (systemKey benv) (systemValue benv) := by
    rw [post, St_state, afterSstoreA_state]
    rfl
  refine ⟨systemCallOutputA (systemMsg benv) (post benv), ?_, ?_, ?_⟩
  · unfold processUncheckedSystemTransaction
    rw [installed, ← hs]
    exact call
  · change 30000000 - (43 + cost benv) ≤ 30000000
    omega
  · have hc : cost benv ≤ 12100 := sstoreCostA_le A _ _ _ _
    change 30000000 - (30000000 - (43 + cost benv)) ≤ 15000
    omega
end Blanc.Lift.HistoryStorage.Totality
