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

abbrev PragueDeploymentRoot
    (chainId : UInt64) (base deployed : BlockChain)
    (dp : DeployParams) (ca : Adr) : Prop :=
  DeploymentRoot (ChainConfig.pragueOnly chainId) base deployed dp ca

/-- A Prague-only schedule selects only the covered Prague fork. -/
private theorem pragueOnly_covered (chainId : UInt64) :
    ∀ t f, (ChainConfig.pragueOnly chainId).forkAt t = .ok f → CoveredFork f := by
  intro t f h
  rw [ChainConfig.pragueOnly_forkAt] at h
  cases h
  exact CoveredFork.prague

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
