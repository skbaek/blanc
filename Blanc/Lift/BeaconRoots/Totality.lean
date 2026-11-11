import Blanc.Lift.SystemExecution.BeaconRoots.SystemWalk
import Blanc.Lift.SystemCallAmsterdam
import Blanc.Lift.WalkKit

namespace Blanc.Lift.BeaconRoots.Totality
open Jaune Blanc.Lift
open Blanc.Lift.SystemExecution.BeaconRoots
local notation "A" => amsterdamStateGasRules

/-- The actual Amsterdam prepared base. -/
def base (benv : Benv) : Devm := systemCallBase (systemMsg benv)
/-- The base after writing the timestamp tag. -/
def mid (benv : Benv) : Devm :=
  afterSstoreA A (systemSevm benv) (base benv) (systemKey benv) benv.stat.time
/-- The two actual regular storage charges. -/
def cost1 (benv : Benv) : Nat :=
  sstoreCostA A (systemSevm benv) (base benv) (systemKey benv) benv.stat.time
def cost2 (benv : Benv) : Nat :=
  sstoreCostA A (systemSevm benv) (mid benv) (systemRootKey benv) (systemValue benv)
def post (benv : Benv) : Devm :=
  St (afterSstoreA A (systemSevm benv) (mid benv) (systemRootKey benv) (systemValue benv)) [] .empty
    (systemTransactionGas - (51 + cost1 benv + cost2 benv))

private theorem ready {benv : Benv} (hf : benv.stat.fork = .amsterdam) :
    Ready (systemSevm benv) (base benv) [systemKey benv, systemRootKey benv] where
  error := systemCallBase_error _
  refund := by rw [base, systemCallBase_refundCounter]
  spill := (systemCallBase_stateGas hf).1
  reservoir := by
    change _ ≤ (systemCallBase (systemMsg benv)).stateGas.left
    unfold systemMsg
    rw [(systemCallBase_stateGas hf).2]
    change 2 * amsterdamStateGasRules.storageSet ≤ amsterdamStateGasRules.systemReservoir
    decide
  clean := fun k _ => systemCallBase_orig rfl _ k

private theorem ready_mid {benv : Benv} (hf : benv.stat.fork = .amsterdam) :
    Ready (systemSevm benv) (mid benv) [systemRootKey benv] :=
  (ready hf).sstore (by simpa only [List.mem_singleton] using systemKey_ne benv) benv.stat.time

/-- The certified two-store path at Amsterdam, with exact regular gas. -/
private theorem root_runA {benv : Benv} {G : Nat} (hf : benv.stat.fork = .amsterdam)
    (hg : gCallStipend < G) :
    SFunc.RunExact prog (systemSevm benv)
      (St (base benv) [] .empty (G + cost1 benv + cost2 benv + 51)) t_0000_c0
      (.halted (St (afterSstoreA A (systemSevm benv) (mid benv)
        (systemRootKey benv) (systemValue benv)) [] .empty G)) := by
  wrun!
  simp only [show (systemSevm benv).caller = systemAddress from rfl, B256.eqCheck]
  apply rx_branch_succ (by decide)
  wrun!
  change SFunc.RunExact prog (systemSevm benv)
    (St (base benv) [systemKey benv, benv.stat.time, systemKey benv] .empty
      (G + cost1 benv + cost2 benv + 14)) _ _
  rw [show G + cost1 benv + cost2 benv + 14 = G + cost2 benv + 14 + cost1 benv by omega]
  refine rx_sstoreR (amsterdam_stateGas hf) rfl (ready hf) (by omega) ?_
  refine rx_push0 (amsterdam_push0 hf) (by wroom) ?_
  wrun!
  change SFunc.RunExact prog (systemSevm benv)
    (St (mid benv) [systemRootKey benv, systemValue benv] .empty (G + cost2 benv)) _ _
  exact rx_sstoreR (amsterdam_stateGas hf) rfl (ready_mid hf) (by omega) Blanc.Lift.rx_stop

/-- The actual Amsterdam system frame halts after writing the tag and root. -/
theorem system_exec {benv : Benv} (hf : benv.stat.fork = .amsterdam) :
    exec ⟨0, systemSevm benv, base benv⟩ = .ok (post benv) := by
  have hc1 : cost1 benv ≤ 12100 := sstoreCostA_le A _ _ _ _
  have hc2 : cost2 benv ≤ 12100 := sstoreCostA_le A _ _ _ _
  let G := systemTransactionGas - (51 + cost1 benv + cost2 benv)
  have hg : gCallStipend < G := by change 2300 < 30000000 - (51 + cost1 benv + cost2 benv); omega
  have hrun := root_runA hf hg
  have heq : G + cost1 benv + cost2 benv + 51 = systemTransactionGas := by
    change 30000000 - (51 + cost1 benv + cost2 benv) + cost1 benv + cost2 benv + 51 = 30000000
    omega
  rw [heq] at hrun
  have hentry : St (base benv) [] .empty systemTransactionGas = base benv := systemCallBase_St
  rw [hentry] at hrun
  apply (exec_iff_exec_eq _ _ _ _).mp
  apply lift_exact_noExec cert_check jumps_ok (by rfl) (progNoExec_of_all (by decide +kernel))
  exact ⟨t_0000_c0, prog_root, hrun⟩

/-- The Amsterdam call writes exactly its two ring-buffer slots within the frozen bound. -/
theorem call_ok {benv : Benv} (hf : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode beaconRootsAddress = beaconRootsCode) :
    ∃ out, processUncheckedSystemTransaction benv beaconRootsAddress benv.stat.parentBeaconBlockRoot.toBytes =
        .ok ((benv.state.setStorVal beaconRootsAddress (systemKey benv) benv.stat.time).setStorVal
          beaconRootsAddress (systemRootKey benv) (systemValue benv), out) ∧
      out.gasLeft ≤ systemTransactionGas ∧ systemTransactionGas - out.gasLeft ≤ 30000 := by
  have r := (ready_mid hf).sstore (by simp only [List.not_mem_nil, not_false_eq_true]) (systemValue benv)
  have clean : (post benv).error = none := r.error
  have nonneg : 0 ≤ (post benv).refundCounter := r.refund
  have call := processSystemTransaction_amsterdam_of_exec hf installed
    (systemContracts_nondelegated member) (by decide) (system_exec hf) clean nonneg
  have hs : (post benv).state =
      (benv.state.setStorVal beaconRootsAddress (systemKey benv) benv.stat.time).setStorVal
        beaconRootsAddress (systemRootKey benv) (systemValue benv) := by
    rw [post, St_state, afterSstoreA_state, mid, afterSstoreA_state]
    rfl
  refine ⟨systemCallOutputA (systemMsg benv) (post benv), ?_, ?_, ?_⟩
  · unfold processUncheckedSystemTransaction
    rw [installed, ← hs]
    exact call
  · change 30000000 - (51 + cost1 benv + cost2 benv) ≤ 30000000
    omega
  · have hc1 : cost1 benv ≤ 12100 := sstoreCostA_le A _ _ _ _
    have hc2 : cost2 benv ≤ 12100 := sstoreCostA_le A _ _ _ _
    change 30000000 - (30000000 - (51 + cost1 benv + cost2 benv)) ≤ 30000
    omega
end Blanc.Lift.BeaconRoots.Totality
