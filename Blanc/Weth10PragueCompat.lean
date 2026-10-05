import Blanc.Weth10AnyOrder

/-!
Thin compatibility corollaries for the historical Prague-only WETH10 API.

The generic theorem remains the proof owner in every case.  This module is the
only public specialization layer that names `ChainConfig.pragueOnly`; current
mainnet clients should import `Blanc.Weth10Mainnet` instead.
-/

namespace Blanc

open Jaune

namespace Weth10

/-! ## Legacy fixed-Prague entry points -/

theorem chain_preserves_stable
    (dp : DeployParams) (ca : Adr) (ch ch' : BlockChain)
    (hreach : BlockChain.Reach ch ch')
    (hstable : Stable dp ca ch.state) :
    Stable dp ca ch'.state := by
  have hbacked : (backedSpec weth10 dp).StateInv ca ch.state :=
    ⟨hstable.code, hstable.sumNof, hstable.backed⟩
  have hflash : (flashExactSpec dp 0).StateInv ca ch.state :=
    ⟨hstable.code, trivial, hstable.flashZero⟩
  have hbacked' := ContractSpec.chain_preserves_inv ca
    (backedSpec_preserves dp ca) ch ch' hreach hbacked
  have hflash' := ContractSpec.chain_preserves_inv ca
    (flashExactSpec_preserves dp ca 0) ch ch' hreach hflash
  exact ⟨hbacked'.code, hbacked'.side, hbacked'.inv, hflash'.inv⟩

/-! ## Named Prague-only corollaries -/

end Weth10

end Blanc
