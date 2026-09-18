-- ProrataWethVaultPairReplay.lean : the pair core replay corollary.

import Blanc.Composition.ProrataWethVaultPairVaultSegment
import Blanc.Composition.ProrataWethVaultPairWethSegment
import Blanc.Composition.ProrataWethVaultWithdrawPayout
import Blanc.Composition.ProrataWethVaultWithdrawLocator

namespace Blanc.Composition.ProrataWethVault

open Jaune

theorem Exec.corePairReplay (vault : Adr) :
    Exec.Fa (Exec.Wkn wethAccount Blanc.weth
      (fun pc sevm pre out _ => Exec.CorePairReplay vault pc sevm pre out)) :=
  Exec.corePairReplay_of_segments (vaultFramePairSegment vault)
    (wethFramePairSegment vault)
    (fun run hcode ht hd hc hs hp hf => wethWithdrawAcceptedPayoutAt_body run hcode ht hd hc hs hp hf)

end Blanc.Composition.ProrataWethVault
