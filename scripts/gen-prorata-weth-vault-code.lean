-- Generate the committed runtime literal for `ProrataWethVault.vault`.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-prorata-weth-vault-code.lean

import Blanc.ProrataWethVault

namespace Blanc

open Jaune

private def hexByte (b : UInt8) : String :=
  let ds := Nat.toDigits 16 b.toNat
  "0x" ++ (if ds.length == 1 then "0" ++ String.ofList ds else String.ofList ds)

private partial def chunks (n : Nat) (xs : List String) : List (List String) :=
  if xs.isEmpty then [] else xs.take n :: chunks n (xs.drop n)

private def renderByteChunk (index : Nat) (bytes : List String) : String :=
  let rows := chunks 12 bytes
  let body :=
    String.intercalate ",\n" (rows.map fun row => "   " ++ String.intercalate ", " row)
  "def prorataWethVaultCodeChunk" ++ toString index ++ " : Bytes :=\n" ++
    "  [" ++ (body.drop 3) ++ "]"

private def renderByteChunkAlias (index source : Nat) : String :=
  "def prorataWethVaultCodeChunk" ++ toString index ++ " : Bytes :=\n" ++
    "  prorataWethVaultCodeChunk" ++ toString source

private def renderByteChunkDef
    (indexedChunks : List (Nat × List String))
    (pair : Nat × List String) : String :=
  match indexedChunks.find? (fun earlier =>
      decide (earlier.fst < pair.fst) && earlier.snd == pair.snd) with
  | some earlier => renderByteChunkAlias pair.fst earlier.fst
  | none => renderByteChunk pair.fst pair.snd

private def renderData (bs : Bytes) : String :=
  let byteChunks := chunks 256 (bs.map hexByte)
  let indexedChunks := List.zip (List.range byteChunks.length) byteChunks
  let chunkDefs := String.intercalate "\n\n"
    (indexedChunks.map (renderByteChunkDef indexedChunks))
  String.intercalate "\n"
    [ "-- ProrataWethVaultCodeData.lean : the single generated vault byte-chunk owner."
    , "--"
    , "-- GENERATED FILE -- do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-prorata-weth-vault-code.lean"
    , ""
    , "import Blanc.ProrataWethVault"
    , ""
    , "namespace Blanc"
    , ""
    , "open Jaune"
    , ""
    , "-- Keep a declaration boundary after the last literal for the exact byte reader."
    , "section GeneratedByteChunks"
    , ""
    , chunkDefs
    , ""
    , "end GeneratedByteChunks"
    , ""
    , "end Blanc"
    , "" ]

private def renderProofPart (index : Nat) (proof : String) : String :=
  let predecessor := if index == 1 then "ProrataWethVaultCodeData"
    else "ProrataWethVaultCodeProof" ++ toString (index - 1)
  String.intercalate "\n"
    [ "-- GENERATED FILE: scripts/gen-prorata-weth-vault-code.lean"
    , "-- Maintained proof text: scripts/prorata-weth-vault-code-proof" ++
        toString index ++ ".lean.in"
    , "import Blanc." ++ predecessor
    , "import Blanc.CompiledShape"
    , ""
    , "namespace Blanc"
    , "open Jaune CompiledShape"
    , "open scoped CompiledShape"
    , "namespace ProrataWethVaultCodeProof"
    , ""
    , proof
    , "end ProrataWethVaultCodeProof"
    , "end Blanc"
    , "" ]

private def renderModule (bs : Bytes) : String :=
  let byteChunks := chunks 256 (bs.map hexByte)
  let joinedChunks := String.intercalate " ++\n    "
    ((List.range byteChunks.length).map fun index =>
      "prorataWethVaultCodeChunk" ++ toString index)
  String.intercalate "\n"
    [ "-- GENERATED FILE: scripts/gen-prorata-weth-vault-code.lean"
    , "-- Public runtime and compiler witness; byte chunks have one upstream owner."
    , "import Blanc.ProrataWethVaultCodeData"
    , "import Blanc.ProrataWethVaultCodeProof3"
    , ""
    , "namespace Blanc"
    , "open Jaune"
    , ""
    , "/-- The " ++ toString bs.length ++ "-byte compiled EVM runtime. -/"
    , "def prorataWethVaultCode : Bytes :="
    , "  " ++ joinedChunks ]
  ++ "\n\n"
  ++ String.intercalate "\n"
    [ "/-- Kernel-checked identity between the family program and committed bytes. -/"
    , "theorem prorataWethVaultCode_compile :"
    , "    Prog.compile ProrataWethVault.vault = some prorataWethVaultCode := by"
    , "  change Table.compile ProrataWethVaultCodeProof.vaultTable"
    , "    ProrataWethVaultCodeProof.vaultTable = some prorataWethVaultCode"
    , "  conv_lhs => arg 2; rw [ProrataWethVaultCodeProof.vaultTable_source]"
    , "  rw [ProrataWethVaultCodeProof.vaultEntries, ProrataWethVaultCodeProof.vaultTableTail0_compile]"
    , "  rw [ProrataWethVaultCodeProof.vaultFinalChunk_take]"
    , "  rfl"
    , ""
    , "end Blanc"
    , "" ]

private def outPath : System.FilePath :=
  "Blanc" / "ProrataWethVaultCode.lean"

#eval show IO Unit from do
  match Prog.compile ProrataWethVault.vault with
  | none =>
      throw (IO.userError
        "Prog.compile ProrataWethVault.vault = none -- refusing to generate")
  | some bs => do
      IO.FS.writeFile ("Blanc" / "ProrataWethVaultCodeData.lean") (renderData bs)
      for index in [1, 2, 3] do
        let proof ← IO.FS.readFile
          ("scripts" / s!"prorata-weth-vault-code-proof{index}.lean.in")
        IO.FS.writeFile ("Blanc" / s!"ProrataWethVaultCodeProof{index}.lean")
          (renderProofPart index proof)
      IO.FS.writeFile outPath (renderModule bs)
      IO.println s!"wrote vault data, three proof parts and {outPath} ({bs.length} bytes)"

end Blanc
