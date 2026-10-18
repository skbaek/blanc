import Blanc.Lift.Usdc.HistorySlots
import Blanc.ExecutionHistoryAdmission
import Blanc.StorageOnlySpec

/-!
# USDC at the end of a configured history (U9c)

The USDC analogue of `weth9_history_footprint_universe`, as far as USDC's laws reach: the three
runtimes and the implementation slot at the history's end (`UsdcInstalled`), the admin word
unchanged (`usdc_history_end_installed`), and the footprint ledger over the history's key universe good, with that universe
injective and apart from the fixed slots.

* the codes: a certified image is a trivially preserved storage-only invariant
  (`ConfiguredHistoryTrace.stateInv_admitted_sem`);
* the implementation and admin slots: `usdc_history_slots`;
* the ledger: `usdc_history_frames_of`'s end `SlotInv`.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.Token

/-- A certified code image at the checkpoint is at the history's end. -/
theorem history_end_codeImage (sem : CodeSem) (a : Adr) {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode a).toList = sem.image) :
    some (future.state.getCode a).toList = sem.image :=
  (tr.stateInv_admitted_sem (c := ContractSpecSem.ofStorageOnly sem (fun _ => True))
    (entry := fun _ _ => True) (fun _ _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
    ((tr.frameAdmitted_iff_rawFrames a _).2 fun _ _ _ => trivial)
    ⟨installed, trivial, trivial⟩).code

/-- **USDC installed at the history's end, the admin word unchanged.** -/
theorem usdc_history_end_installed {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    UsdcInstalled P future.state ∧ adminOf future.state P = adminOf checkpoint.state P := by
  obtain ⟨-, slot, admin⟩ := usdc_history_slots tr hist
  have inst := hist.1
  exact ⟨⟨history_end_codeImage proxySem P tr inst.proxy,
    history_end_codeImage implSem usdcImpl tr inst.impl,
    history_end_codeImage libSem usdcLib tr inst.lib, slot, inst.implApart, inst.libApart⟩, admin⟩

/-- **USDC at the history's end** (`usdc_history_end_core`): installed, the admin word unchanged,
the history's key universe injective and apart from the fixed slots, and its ledger good at the
end.  `FootInv`'s support half needs a storage-locality law (decision usdc-history-end-split). -/
theorem usdc_history_end_core {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : UsdcHist P K₀ tr) :
    UsdcInstalled P future.state ∧ adminOf future.state P = adminOf checkpoint.state P ∧
      SlotFootprint.Inj Key.slot (historyKeyUniverse P tr K₀) ∧
      SlotFootprint.Apart Key.slot fixedSlots (historyKeyUniverse P tr K₀) ∧
      (ledger (historyKeyUniverse P tr K₀) (future.state.getStor P)).Good := by
  have ext := hist.2.2.1.extend hist.2.2.2
  obtain ⟨inst, admin⟩ := usdc_history_end_installed tr hist
  exact ⟨inst, admin, ext.inj, ext.apart, (usdc_history_frames_of impl_signed_law tr hist).2.2.2.1⟩

end Blanc.Lift.Usdc
