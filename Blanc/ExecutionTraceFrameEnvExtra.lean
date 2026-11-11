import Blanc.ExecutionMessageGas
import Blanc.ExecutionTraceCalldata
import Blanc.ExecutionTransactionGas
import Blanc.ExecutionTraceSystemCode
import Blanc.ExecutionCodeAt
import Blanc.Lift.CallerProvenance
import Blanc.ExecutionTraceEntry
import Blanc.ExecutionTraceCodeAt
import Blanc.ExecutionTraceFrameEnv

/-!
# Generic environment discharge for per-frame walk premises

Frame walks and contract frame theorems take premises about the frame's entry that a configured
history determines without any per-frame assumption, or with only trace-local ones.  This module
discharges three of them once, for every contract:

* **Entry gas fits a word** (`ConfiguredHistoryTrace.gas_bound`,
  `ConfiguredHistoryTrace.frameAdmitted_gas`).  Frame walks start from `pre.gasMeasure < 2 ^ 256`.
  Inside one execution no entered frame starts with more gas than the execution's root
  (`Exec.rawFrameRoots_gas_le`: a spawn passes `frame.inner.gas < pre.gasMeasure`,
  `Evm.step_gasBound`; the child starts with exactly that, `Frame.enter_run_gasMeasure`; the parent
  resumes with no more than it had).  A message's root frame starts with the message grant
  (delegation and code resolution keep it); a transaction's grant is below `tx.gas`, which
  `checkTransaction` keeps below the block gas limit, which header validation keeps below `2 ^ 63`
  (`ConfiguredBlockTrace.header_gasLimit_lt`); a system message's grant is `systemTransactionGas`.
  So every raw frame of a configured history starts with `gasMeasure < 2 ^ 64`.
* **Children keep the code at an address no CREATE frame targets**
  (`Exec.childFrames_codeAt_keep`), from `Exec.codeAt_avoid` on each committed direct child.
* **System frames never target a contract whose code differs in size from every canonical
  system code** (`not_mem_systemTargets_of_size`, `ConfiguredHistoryTrace.system_ne_of_size`),
  hoisted from a contract-specific proof and stated generically.
-/

namespace Blanc

open Jaune

/-! ## Direct children keep the code at an address no CREATE frame targets -/

namespace ExecutionTrace

/-! ## From retained slots to whole histories -/

/-- An address whose installed code has a size no canonical system code has is not a system
address. -/
theorem not_mem_systemTargets_of_size {w : State} {ca : Adr} {c : ByteArray}
    (installed : w.getCode ca = c) (system : SystemCodeInstalled w)
    (size : ∀ p ∈ systemContracts, p.2.size ≠ c.size) :
    ca ∉ systemTargets := by
  intro hmem
  have hsize : ∀ p ∈ systemContracts, p.1 = ca → False := by
    intro p hp hca
    have h := system p hp
    rw [hca, installed] at h
    exact size p hp (congrArg ByteArray.size h).symm
  simp only [systemTargets, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · exact hsize (beaconRootsAddress, beaconRootsCode) (by simp only [systemContracts,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_or]) rfl
  · exact hsize (historyStorageAddress, historyStorageCode) (by simp only [systemContracts,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, true_or, or_true]) rfl
  · exact hsize (withdrawalRequestPredeployAddress, withdrawalRequestCode)
      (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        true_or, or_true]) rfl
  · exact hsize (consolidationRequestPredeployAddress, consolidationRequestCode)
      (by simp only [systemContracts, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        or_true]) rfl

/-! ## The raw frames of a history are closed under descent

Every frame a raw frame enters is itself a raw frame of the history.  So a trace-local premise over
`trace.rawFrames` (such as "no CREATE frame targets `a`") covers every frame below a given raw
frame, which is what per-frame consumers like `Exec.childFrames_codeAt_keep` need. -/

end ExecutionTrace

end Blanc
