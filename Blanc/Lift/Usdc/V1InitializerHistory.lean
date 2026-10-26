import Blanc.Lift.Usdc.InitV1KeyBounds
import Blanc.Lift.Usdc.ImplV1.Check
import Blanc.ExecutionStagedRootFacts
import Blanc.ExecutionHistoryCellProvenance

/-! V1 initializer exclusion at actual raw-history stores, for any frame outcome. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- The actual initializer prefix avoids the implementation slot, including old-tail clears. -/
theorem v1Initializer_store_ne_implSlot {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = ImplV1.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (fresh : Exec.FreshEntry root.sevm root.devm)
    (gas : root.devm.gasMeasure < 2 ^ 256)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Sevm.selector root.sevm = 0x3357162b)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨T, reach, atStore, machine⟩ := Reach.sstoreNode_pot ImplV1.cert_check
    pc code hsg fresh.1 fresh.2 gas chain decoded
  exact InitV1KeyBounds.initV1_reach_ne_implSlot_concrete
    (fun h => StepIn.toRun h) selected reach atStore write.key write.value rest
    (machine ▸ stack)

/-- History admission supplies freshness, the gas bound and state-gas capability itself. -/
theorem ConfiguredHistoryTraceIn.v1Initializer_write_ne_implSlot
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = ImplV1.code)
    (selected : Sevm.selector node.sevm = 0x3357162b)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, fresh, gas⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  rw [same] at code selected
  exact v1Initializer_store_ne_implSlot pc code hsg fresh gas chain selected found

end Blanc.Lift.Usdc
