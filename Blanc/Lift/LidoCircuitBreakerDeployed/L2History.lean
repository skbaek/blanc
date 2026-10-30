import Blanc.Lift.LidoCircuitBreakerDeployed.History
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceAdmission
import Blanc.Lift.LidoCircuitBreakerDeployed.Reentry

/-!
# L2 at a committed `registerPauser(t, 0)` frame with a good entry

`l2_registerPauser_zero` (`L2Frame.lean`) is a statement about one frame: it takes fresh
entry, the selector and calldata word, `EntryAt lidoA` at the frame's entry, the installed
code, and a `RegistryWitness` of the frame's entry storage.  `l2_of_entryGood` reads all of
them from `EntryGood` for the Lido accounting carrier (pc zero, the covered fork, the installed
code, fresh entry and `EntryAt lidoA`, and the entry invariant `RegInv`).  For
settlement-committed non-static frames after the actual deployment, `lido_remove_repairs`
(`DeploymentHistory.lean`) obtains that `EntryGood` from the mid-history entry accounting
`MidHistoryTraceIn.entryGood_settled` and the Lido spawn obligation, including reentry from
`pause`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace

/-- A byte array whose list is the deployed image is the deployed code. -/
theorem eq_code_of_image {b : ByteArray} (h : some b.toList = lidoSpec.sem.image) :
    b = code := by
  have h' : b.toList = code.toList := Option.some.inj h
  cases hb : b with
  | mk d =>
    cases hk : code with
    | mk d' =>
      rw [hb, hk, ByteArray.toList_eq_toList_data, ByteArray.toList_eq_toList_data] at h'
      exact congrArg ByteArray.mk (Array.toList_inj.mp h')

/-- L2 at one committed `registerPauser(t, 0)` frame whose entry is good for the Lido
accounting carrier. -/
theorem l2_of_entryGood {ca : Adr} (frame : Exec.Frame)
    (good : ExecutionAccountingReplay.EntryGood ca lidoSpec.sem (lidoFrameEntry lidoA) (fun s => RegInv s) frame)
    (target : frame.sevm.currentTarget = ca)
    (hsig : Sevm.dataWord frame.sevm 0 >>> 224 = selector "registerPauser" [.address, .address])
    (hnp0 : Sevm.dataWord frame.sevm 36 = 0) :
    ∃ entries, RegistryWitness (solRegistryStorage (Devm.getStor frame.pre ca)) entries ∧
      L2Post entries (Sevm.dataWord frame.sevm 4) (Devm.getStor frame.post ca) ∧
      RegistryWitness (solRegistryStorage (Devm.getStor frame.post ca))
        (removedEntries entries (Sevm.dataWord frame.sevm 4)) := by
  obtain ⟨hpc, fork, installed, ⟨hfresh, -, hA⟩, ⟨entries, hwit⟩⟩ := good
  obtain ⟨pc, sevm, pre, out, run, committed⟩ := frame
  dsimp only at hpc fork installed hfresh hA hwit target hsig hnp0 ⊢
  subst hpc
  subst target
  cases out with
  | error e => simp only [Execution.commits, Bool.false_eq_true] at committed
  | ok post =>
    have hinstalled : Devm.getCode pre sevm.currentTarget = code := eq_code_of_image installed.1
    have hcode : sevm.code = Devm.getCode pre sevm.currentTarget := by
      rw [hinstalled]
      exact eq_code_of_image (installed.2 rfl).1
    exact ⟨entries, hwit,
      l2_registerPauser_zero_witness fork hinstalled hcode hfresh hsig hA hwit hnp0 run⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
