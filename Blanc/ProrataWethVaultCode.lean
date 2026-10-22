-- GENERATED FILE: scripts/gen-prorata-weth-vault-code.lean
-- Public runtime and compiler witness; byte chunks have one upstream owner.
import Blanc.ProrataWethVaultCodeData
import Blanc.ProrataWethVaultCodeProof3

namespace Blanc
open Jaune

/-- The 17481-byte compiled EVM runtime. -/
def prorataWethVaultCode : Bytes :=
  prorataWethVaultCodeChunk0 ++
    prorataWethVaultCodeChunk1 ++
    prorataWethVaultCodeChunk2 ++
    prorataWethVaultCodeChunk3 ++
    prorataWethVaultCodeChunk4 ++
    prorataWethVaultCodeChunk5 ++
    prorataWethVaultCodeChunk6 ++
    prorataWethVaultCodeChunk7 ++
    prorataWethVaultCodeChunk8 ++
    prorataWethVaultCodeChunk9 ++
    prorataWethVaultCodeChunk10 ++
    prorataWethVaultCodeChunk11 ++
    prorataWethVaultCodeChunk12 ++
    prorataWethVaultCodeChunk13 ++
    prorataWethVaultCodeChunk14 ++
    prorataWethVaultCodeChunk15 ++
    prorataWethVaultCodeChunk16 ++
    prorataWethVaultCodeChunk17 ++
    prorataWethVaultCodeChunk18 ++
    prorataWethVaultCodeChunk19 ++
    prorataWethVaultCodeChunk20 ++
    prorataWethVaultCodeChunk21 ++
    prorataWethVaultCodeChunk22 ++
    prorataWethVaultCodeChunk23 ++
    prorataWethVaultCodeChunk24 ++
    prorataWethVaultCodeChunk25 ++
    prorataWethVaultCodeChunk26 ++
    prorataWethVaultCodeChunk27 ++
    prorataWethVaultCodeChunk28 ++
    prorataWethVaultCodeChunk29 ++
    prorataWethVaultCodeChunk30 ++
    prorataWethVaultCodeChunk31 ++
    prorataWethVaultCodeChunk32 ++
    prorataWethVaultCodeChunk33 ++
    prorataWethVaultCodeChunk34 ++
    prorataWethVaultCodeChunk35 ++
    prorataWethVaultCodeChunk36 ++
    prorataWethVaultCodeChunk37 ++
    prorataWethVaultCodeChunk38 ++
    prorataWethVaultCodeChunk39 ++
    prorataWethVaultCodeChunk40 ++
    prorataWethVaultCodeChunk41 ++
    prorataWethVaultCodeChunk42 ++
    prorataWethVaultCodeChunk43 ++
    prorataWethVaultCodeChunk44 ++
    prorataWethVaultCodeChunk45 ++
    prorataWethVaultCodeChunk46 ++
    prorataWethVaultCodeChunk47 ++
    prorataWethVaultCodeChunk48 ++
    prorataWethVaultCodeChunk49 ++
    prorataWethVaultCodeChunk50 ++
    prorataWethVaultCodeChunk51 ++
    prorataWethVaultCodeChunk52 ++
    prorataWethVaultCodeChunk53 ++
    prorataWethVaultCodeChunk54 ++
    prorataWethVaultCodeChunk55 ++
    prorataWethVaultCodeChunk56 ++
    prorataWethVaultCodeChunk57 ++
    prorataWethVaultCodeChunk58 ++
    prorataWethVaultCodeChunk59 ++
    prorataWethVaultCodeChunk60 ++
    prorataWethVaultCodeChunk61 ++
    prorataWethVaultCodeChunk62 ++
    prorataWethVaultCodeChunk63 ++
    prorataWethVaultCodeChunk64 ++
    prorataWethVaultCodeChunk65 ++
    prorataWethVaultCodeChunk66 ++
    prorataWethVaultCodeChunk67 ++
    prorataWethVaultCodeChunk68

/-- Kernel-checked identity between the family program and committed bytes. -/
theorem prorataWethVaultCode_compile :
    Prog.compile ProrataWethVault.vault = some prorataWethVaultCode := by
  change Table.compile ProrataWethVaultCodeProof.vaultTable
    ProrataWethVaultCodeProof.vaultTable = some prorataWethVaultCode
  conv_lhs => arg 2; rw [ProrataWethVaultCodeProof.vaultTable_source]
  rw [ProrataWethVaultCodeProof.vaultEntries, ProrataWethVaultCodeProof.vaultTableTail0_compile]
  rw [ProrataWethVaultCodeProof.vaultFinalChunk_take]
  rfl

end Blanc
