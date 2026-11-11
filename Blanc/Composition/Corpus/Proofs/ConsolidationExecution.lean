import Blanc.Composition.Corpus.Freeze.ConsolidationExecution
import Blanc.ExecutionKeptBalSilent

/-!
# EIP-7251: settled-frame classification and kept value

Exact inhabitants of the frozen C-S2 and C-S6 cells. The successful frame inversions supply the
three cases, including unconditional dequeue output and log preservation. The balance-silent
certificate and the shared kept-history accounting cover every committed call's incoming value.
-/

namespace Blanc.Corpus.Proofs.Consolidation

open Jaune Blanc
open Blanc.Composition.ConsolidationRequestPublic
open Blanc.Corpus.Freeze.Consolidation

/-- **C-S2.** Every settled frame in a covered kept history has exactly one of the frozen effects. -/
theorem c_s2 : C_S2 := by
  intro cfg start final blocks kept code covered b hb f hf
  have member := Lift.ConsolidationRequest.member
  obtain ⟨-, nondelegating, nonempty⟩ := systemContracts_facts _ member
  obtain ⟨orig, entry⟩ := kept.entry_in code nonempty nondelegating b hb f hf
  have fork : CoveredFork f.sevm.benvStat.fork := by
    rw [entry.benvStat]
    exact covered b hb
  have exec : Exec 0 f.sevm f.pre (.ok f.post) := by
    rw [← entry.pc]
    cases f with
    | mk pc sevm pre out run committed =>
        cases out with
        | error err => simp only [Execution.commits, Bool.false_eq_true] at committed
        | ok post => exact run
  by_cases caller : f.sevm.caller = systemAddress
  · obtain ⟨dynamic, state, output, logs⟩ :=
      Lift.ConsolidationRequest.exec_system_frame entry.code fork entry.stack entry.memoryWf caller exec
    exact .dequeue caller dynamic (by rw [state, entry.target]) (by rw [output, entry.target]) logs
  · rcases Lift.ConsolidationRequest.exec_user_frame entry.code fork entry.stack entry.memorySize
        entry.memoryWf entry.dataLength caller exec with ⟨i, w, law⟩ | ⟨i, w, empty, read⟩
    · have quote := law.quote
      rw [entry.target] at quote
      refine .submission caller law.length law.dynamic (by rw [← entry.target]; exact law.active)
        (by rw [quotedFee_of_run quote]; exact law.covered)
        (by rw [← entry.target]; exact law.storage)
        (fun a ha => law.otherStorage a (by rw [entry.target]; exact ha)) law.balance
        (by rw [law.logs, entry.target]; rfl) law.output
    · have quote := read.quote
      rw [entry.target] at quote
      refine .feeRead caller empty read.value (by rw [← entry.target]; exact read.active) ?_
        read.storage read.balance read.logs
      rw [quotedFee_of_run quote, toB256_toNat]
      exact read.output

/-- **C-S6.** The final balance covers the starting balance plus every committed submission, and
indeed every kept call, under the frozen sender and arithmetic premises. -/
theorem c_s6 : C_S6 := by
  intro cfg start final blocks kept code _covered senders roots credits
  have member := Lift.ConsolidationRequest.member
  have closed : Lift.BalSilentSet Lift.SystemExecution.ConsolidationRequest.cert.prog
      [0, 1, 2, 3, 4, 5, 6] = true := by
    decide +kernel
  have allValue := kept.systemContract_bal_covers member
    Lift.SystemExecution.ConsolidationRequest.cert_check
    Lift.SystemExecution.ConsolidationRequest.Amsterdam.sysPath.noExec closed
    (by decide : 0 ∈ ([0, 1, 2, 3, 4, 5, 6] : List Nat)) code senders roots credits
  refine ⟨?_, allValue⟩
  exact Nat.le_trans (Nat.add_le_add_left
    (sum_map_filter_le (blocks.flatMap (KeptBlock.keptAt addr))
      (fun f => decide (f.sevm.caller ≠ systemAddress ∧ f.sevm.data.length = 96))
      (fun f => f.sevm.value.toNat)) _) allValue

end Blanc.Corpus.Proofs.Consolidation
