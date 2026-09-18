-- ProrataWethVaultPairReplay.lean : the pair core replay corollary.

import Blanc.Composition.ProrataWethVaultPairVaultSegment
import Blanc.Composition.ProrataWethVaultPairWethSegment
import Blanc.Composition.ProrataWethVaultWithdrawPayout

namespace Blanc.Composition.ProrataWethVault

open Jaune

theorem Exec.corePairReplay (vault : Adr) :
    Exec.Fa (Exec.Wkn wethAccount Blanc.weth
      (fun pc sevm pre out _ => Exec.CorePairReplay vault pc sevm pre out)) :=
  Exec.corePairReplay_of_segments (vaultFramePairSegment vault)
    (wethFramePairSegment vault) wethWithdrawAcceptedPayout

end Blanc.Composition.ProrataWethVault
