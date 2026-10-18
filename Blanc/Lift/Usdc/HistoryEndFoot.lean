import Blanc.Lift.Usdc.HistoryEnd

/-!
# USDC's footprint at the end of a configured history (U6s)

The USDC analogue of `weth9_history_footprint_universe` at the predecessor's WETH9 standard:
`usdc_history_end` adds `FootInv`'s support half to `usdc_history_end_core` (installed, admin,
`Inj`, `Apart`, ledger good).  The support comes from the slot ladder's end invariant
(`usdc_history_frames_of`): `SlotInv` carries `Support` over the history's key universe, because
every family law (`ImplStepLaw`) writes the proxy's storage only at fixed slots and at the slots of
the frame's keys (`frameKeys`), which the universe contains, the library writes nothing, and
`rescueERC20` and the proxy's own frames keep the storage outside their children.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift.Token

/-- **USDC at the history's end**: the three runtimes and the implementation slot installed, the
footprint invariant over the history's key universe, and the admin word unchanged. -/
theorem usdc_history_end {P : Adr} {K₀ : Usdc.Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} (tr : ConfiguredHistoryTrace cfg checkpoint future)
    (hist : Usdc.UsdcHist P K₀ tr) :
    Usdc.UsdcInstalled P future.state ∧
      Usdc.FootInv (Usdc.historyKeyUniverse P tr K₀) (future.state.getStor P) ∧
      Usdc.adminOf future.state P = Usdc.adminOf checkpoint.state P := by
  obtain ⟨inst, admin, inj, apart, good⟩ := usdc_history_end_core tr hist
  exact ⟨inst, ⟨(usdc_history_frames_of impl_signed_law tr hist).2.2.2.2, inj, apart, good⟩, admin⟩

end Blanc.Lift.Usdc
