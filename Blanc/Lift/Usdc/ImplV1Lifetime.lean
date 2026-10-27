import Blanc.ExecutionInstalledCertCuts
import Blanc.Lift.Usdc.ProxyContextCodes
import Blanc.Lift.Usdc.ProxyCreation.ConstantsCheck

/-!
# V1 runtime from its creation transaction to the original pre-C22 cut

These are internal composition lemmas. `constructorOutput` is the still-missing
actual V1 constructor producer's settled installed-runtime output. It is not
an adopted environmental premise, fetched code observation or new anchor.

The actual creation cut, intervening whole-block history and C22 cut are retained
by the existing selected-domain carriers. Their identification with the original
historical execution remains a separate producer obligation. No full-history
binding, origin result or final P1/L5 completion is claimed here.
-/

namespace Blanc.Lift.Usdc.ImplV1Lifetime

open Jaune Blanc.ExecutionTrace

/-- Existing checked V1 runtime facts, packaged for common code transport. -/
theorem installedCert : InstalledCert ImplV1.code := by
  exact ⟨⟨ImplV1.cert, ImplV1.cert_check, ImplV1.cert_callOnly,
    ImplV1.cert_noSelfdestruct⟩, ImplV1.code_not_delegation,
    toList_ne_nil_of_size_ne_zero (Nat.ne_of_gt ImplV1.code_size_pos)⟩

/-- Internal composition to the original pre-C22 position. `constructorOutput`
is the still-missing settled output of the actual V1 constructor producer;
none of the supplied execution witnesses is asserted to be origin-bound here. -/
theorem code_before_c22_of_creation_cut
    {F : Fork → Prop} {cfg : ChainConfig}
    {origin created cPre cPost : BlockChain}
    (creation : ConfiguredBlockTraceIn F cfg origin created) {i : Nat}
    (creationCut : creation.bodyTrace.transactions.TxSplit i)
    (between : ConfiguredHistoryTraceIn F cfg created cPre)
    (cBlock : ConfiguredBlockTraceIn F cfg cPre cPost)
    (cCut : cBlock.bodyTrace.transactions.TxSplit 22)
    (capabilities : BodyStageCapabilities F)
    (constructorOutput : creationCut.afterBenv.state.getCode
      ProxyCreation.initialImplementation.toAdr = ImplV1.code) :
    cCut.benv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code := by
  have mid := (MidHistoryTraceIn.tail creation creationCut).append between
  exact mid.code_before_txSplit_of_installedCert installedCert cBlock cCut capabilities
    constructorOutput

/-- The same internal composition through the actual C22 transaction, every
outcome. The source constructor output remains an unfulfilled producer result. -/
theorem code_after_c22_of_creation_cut
    {F : Fork → Prop} {cfg : ChainConfig}
    {origin created cPre cPost : BlockChain}
    (creation : ConfiguredBlockTraceIn F cfg origin created) {i : Nat}
    (creationCut : creation.bodyTrace.transactions.TxSplit i)
    (between : ConfiguredHistoryTraceIn F cfg created cPre)
    (cBlock : ConfiguredBlockTraceIn F cfg cPre cPost)
    (cCut : cBlock.bodyTrace.transactions.TxSplit 22)
    (capabilities : BodyStageCapabilities F)
    (constructorOutput : creationCut.afterBenv.state.getCode
      ProxyCreation.initialImplementation.toAdr = ImplV1.code) :
    cCut.afterBenv.state.getCode ProxyCreation.initialImplementation.toAdr = ImplV1.code := by
  have beforeCode := code_before_c22_of_creation_cut creation creationCut between
    cBlock cCut capabilities constructorOutput
  have hsg : cCut.benv.stat.rules.stateGas = none := by
    change cCut.afterBenv.stat.rules.stateGas = none
    rw [cBlock.txSplit_stat cCut]
    exact capabilities.stateGas_none cBlock.forkIn
  exact (cCut.head.noDel_of_installedCert ImplV1.cert_check ImplV1.cert_callOnly
    ImplV1.cert_noSelfdestruct installedCert.notDelegation installedCert.nonempty hsg
    beforeCode (cBlock.txSplit_notCreated cCut _)).2.2

end Blanc.Lift.Usdc.ImplV1Lifetime
