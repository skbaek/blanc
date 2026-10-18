import Blanc.Lift.Usdc.Hist
import Blanc.Lift.Usdc.FootprintLedger

/-!
# USDC's support-free checkpoint premises (twin of `Hist.lean`)

`UsdcHistF P K₀ tr` is the support-free twin of `UsdcHist`: the installed codes at the
checkpoint, the governance premise F2, the support-free footprint over `K₀` at the
checkpoint (`FootCoreL`), and HASH-T over the keys the history touches.  `FootCoreL` is the
Lift-level twin of `Blanc.Composition.UsdcToken.FootCore`
(`Blanc/Composition/UsdcTokenLive.lean:23-33`): that module lives at Composition layer (it
imports `Blanc.Composition.UniswapV2PairUsdcWeth9LegsFacts`), which `Hist.lean` cannot import,
so the three fields (`inj`, `apart`, `good`) are repeated here.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.ExecutionTrace

/-- The support-free footprint: the tracked keys' slots injective and apart from the fixed
slots, and the ledger good.  `FootInv` without its support half. -/
structure FootCoreL (K : Key → Prop) (s : Stor) : Prop where
  inj : SlotFootprint.Inj Key.slot K
  apart : SlotFootprint.Apart Key.slot fixedSlots K
  good : (ledger K s).Good

/-- **Touching fresh keys extends the support-free footprint.**  `inj`/`apart` extend by the
shared `Inj.extend`/`Apart.extend`; `Good` reads only slots 8 and 18 (`ledger_good_congr`),
which the extension leaves alone. -/
theorem FootCoreL.extend {K : Key → Prop} {s : Stor} (h : FootCoreL K s) {ks : List Key}
    (fresh : KeysFresh K ks) : FootCoreL (SlotFootprint.extendBy K ks) s :=
  ⟨h.inj.extend fresh, h.apart.extend fresh, ledger_good_congr h.good rfl rfl⟩

/-- USDC's support-free trace-local premises: installed codes at the checkpoint, F2, the
support-free footprint over `K₀` at the checkpoint, and HASH-T over the keys the history
touches. -/
def UsdcHistF (P : Adr) (K₀ : Key → Prop) {cfg : ChainConfig} {checkpoint future : BlockChain}
    (tr : ConfiguredHistoryTrace cfg checkpoint future) : Prop :=
  UsdcInstalled P checkpoint.state ∧ UsdcGovernance P tr ∧
    FootCoreL K₀ (checkpoint.state.getStor P) ∧ KeysFresh K₀ (historyTouchedKeys P tr)

/-- Every `UsdcHist` checkpoint is a support-free checkpoint: the twin proof reads only
`inj`/`apart`/`good` of the checkpoint `FootInv`. -/
theorem UsdcHist.toUsdcHistF {P : Adr} {K₀ : Key → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {tr : ConfiguredHistoryTrace cfg checkpoint future}
    (h : UsdcHist P K₀ tr) : UsdcHistF P K₀ tr := by
  obtain ⟨installed, gov, foot, fresh⟩ := h
  exact ⟨installed, gov, ⟨foot.inj, foot.apart, foot.good⟩, fresh⟩

end Blanc.Lift.Usdc
