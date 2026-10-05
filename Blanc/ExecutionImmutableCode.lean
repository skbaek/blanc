import Blanc.ExecutionTraceAdmission
import Blanc.ExecutionBodyPrefixAdmission
import Blanc.StorageOnlySpec

/-! Nonempty, nondelegating installed code survives actual configured execution.
The ordinary admitted ladder supplies the transport; no address exclusions or
contract-specific frame-entry premises are required. -/

namespace Blanc.ExecutionTrace

open Jaune

private theorem bytes_eq_of_image {actual code : ByteArray}
    (image : some actual.toList = some code.toList) : actual = code := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj image

private def immutableSem (code : ByteArray) (nonempty : code.toList ≠ [])
    (nondelegating : ¬ isValidDelegation code) : CodeSem where
  image := some code.toList
  Run := fun _ _ _ => True
  correct := fun _ _ => trivial
  ne_nil := by
    intro l image
    exact (Option.some.inj image) ▸ nonempty
  not_delegation := by
    intro actual image
    exact bytes_eq_of_image image ▸ nondelegating

private def immutableSpec (code : ByteArray) (nonempty : code.toList ≠ [])
    (nondelegating : ¬ isValidDelegation code) : ContractSpecSem :=
  ContractSpecSem.ofStorageOnly (immutableSem code nonempty nondelegating) (fun _ => True)

private theorem immutableSpec_preserves (code : ByteArray) (nonempty : code.toList ≠ [])
    (nondelegating : ¬ isValidDelegation code) (address : Adr) :
    (immutableSpec code nonempty nondelegating).PreservesAdmitted address (fun _ _ => True) := by
  intro sevm pre post fork run admitted image wf inv
  exact ⟨trivial, trivial⟩

/-- Exact code identity at the opening and protocol message boundaries of the
next actual block. All admission and resource facts come from that trace. -/
theorem ConfiguredHistoryTrace.block_code_boundaries
    {cfg : ChainConfig} {checkpoint pre post : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint pre)
    (block : ConfiguredBlockTrace cfg pre post) (address : Adr) (code : ByteArray)
    (nonempty : code.toList ≠ []) (nondelegating : ¬ isValidDelegation code)
    (installed : checkpoint.state.getCode address = code) :
    pre.state.getCode address = code ∧
    block.bodyTrace.beaconState.getCode address = code ∧
    block.bodyTrace.requestBenv.state.getCode address = code ∧
    block.bodyTrace.requests.withdrawalState.getCode address = code := by
  let spec := immutableSpec code nonempty nondelegating
  have preserves := immutableSpec_preserves code nonempty nondelegating address
  have admitted : (ConfiguredHistoryTrace.step history block).FrameAdmitted
      address (fun _ _ => True) := by
    apply ((ConfiguredHistoryTrace.step history block).frameAdmitted_iff_rawFrames
      address (fun _ _ => True)).2
    intro root member target
    exact trivial
  have initial : spec.StateInv address checkpoint.state := by
    refine ⟨?_, trivial, trivial⟩
    change some (checkpoint.state.getCode address).toList = some code.toList
    rw [installed]
  have opening := history.stateInv_admitted_sem preserves admitted.1 initial
  have openingInv : spec.BenvInv address (initBenv block.fork pre block.block.header) :=
    ⟨opening, block.not_mem_openingCreatedAccounts address⟩
  have beacon := block.bodyTrace.beacon.stateInv_and_sum_le_admitted_sem
    preserves block.covered admitted.2.beacon openingInv
  have request := block.bodyTrace.requestBenvInv_admitted_sem
    preserves block.covered admitted.2 block.openingBound openingInv
  have withdrawal := block.bodyTrace.requests.withdrawal.stateInv_and_sum_le_admitted_sem
    preserves (block.bodyTrace.requestBenv_covered block.covered)
    admitted.2.requests.withdrawal request
  exact ⟨bytes_eq_of_image opening.code, bytes_eq_of_image beacon.1.code,
    bytes_eq_of_image request.state.code, bytes_eq_of_image withdrawal.1.code⟩

end Blanc.ExecutionTrace
