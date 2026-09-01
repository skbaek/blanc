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
  "private def prorataWethVaultCodeChunk" ++ toString index ++ " : Bytes :=\n" ++
    "  [" ++ (body.drop 3) ++ "]"

private def renderByteChunkAlias (index source : Nat) : String :=
  "private def prorataWethVaultCodeChunk" ++ toString index ++ " : Bytes :=\n" ++
    "  prorataWethVaultCodeChunk" ++ toString source

private def renderByteChunkDef
    (indexedChunks : List (Nat × List String))
    (pair : Nat × List String) : String :=
  match indexedChunks.find? (fun earlier =>
      decide (earlier.fst < pair.fst) && earlier.snd == pair.snd) with
  | some earlier => renderByteChunkAlias pair.fst earlier.fst
  | none => renderByteChunk pair.fst pair.snd

private def renderModule (bs : Bytes) : String :=
  let byteChunks := chunks 256 (bs.map hexByte)
  let indexedChunks := List.zip (List.range byteChunks.length) byteChunks
  let chunkDefs := String.intercalate "\n\n"
    (indexedChunks.map (renderByteChunkDef indexedChunks))
  let joinedChunks := String.intercalate " ++\n    "
    (indexedChunks.map fun pair => "prorataWethVaultCodeChunk" ++ toString pair.fst)
  String.intercalate "\n"
    [ "-- ProrataWethVaultCode.lean : compiled runtime bytecode for the"
    , "-- full-width ERC-4626 vault over exact Blanc WETH."
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
    , chunkDefs
    , ""
    , "/-- The " ++ toString bs.length ++ "-byte compiled EVM runtime. -/"
    , "def prorataWethVaultCode : Bytes :="
    , "  " ++ joinedChunks ]
  ++ "\n\n"
  ++ String.intercalate "\n"
    [ "/-- Kernel-checked identity between the family program and committed bytes. -/"
    , "theorem prorataWethVaultCode_compile :"
    , "    Prog.compile ProrataWethVault.vault = some prorataWethVaultCode := by"
    , "  decide +kernel"
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
      IO.FS.writeFile outPath (renderModule bs)
      IO.println s!"wrote {outPath} ({bs.length} bytes)"

end Blanc
