-- gen-drip-creation-code.lean : sole writer for
-- `Blanc/DripCreationCode.lean`.
--
-- Run from the repository root with the repository-prescribed Lean runtime.
-- It evaluates the two-pass DRIP constructor artifact and emits the complete
-- creation-literal module; no creation byte is transcribed by hand.

import Blanc.DripDeploy

namespace Blanc.Drip

open Jaune

private def hexByte (b : UInt8) : String :=
  let digits := Nat.toDigits 16 b.toNat
  "0x" ++
    (if digits.length == 1 then
      "0" ++ String.ofList digits
    else
      String.ofList digits)

private partial def chunks (n : Nat) (xs : List String) : List (List String) :=
  if xs.isEmpty then [] else xs.take n :: chunks n (xs.drop n)

private def renderModule (bytes : Bytes) : String :=
  let rows := chunks 12 (bytes.map hexByte)
  let body :=
    String.intercalate ",\n"
      (rows.map fun row => "   " ++ String.intercalate ", " row)
  let size := bytes.length
  let headroom := pragueCodeLimits.maxInitCodeSize - size
  String.intercalate "\n"
    [ "-- DripCreationCode.lean : compiler-generated DRIP creation literal."
    , "--"
    , "-- GENERATED FILE — do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-drip-creation-code.lean"
    , "--"
    , "-- The byte list is emitted from Drip.creationCode, whose prefix is"
    , "-- tied to Drip.constructorProgram by constructorInitPrefix_compile."
    , ""
    , "import Blanc.DripDeploy"
    , ""
    , "namespace Blanc.Drip"
    , ""
    , "open Jaune"
    , ""
    , "/-- The " ++ toString size ++ "-byte exact DRIP creation artifact. -/"
    , "def creationCodeLiteral : Bytes :="
    , "  [" ++ body.drop 3 ]
  ++ "]\n\n"
  ++ String.intercalate "\n"
    [ "/-- Kernel-checked identity between the committed literal and the"
    , "two-pass compiler-derived creation artifact. -/"
    , "theorem creationCode_eq_literal : creationCode = creationCodeLiteral := by"
    , "  decide +kernel"
    , ""
    , "theorem creationCodeLiteral_length : creationCodeLiteral.length = " ++
        toString size ++ " := by"
    , "  decide +kernel"
    , ""
    , "theorem creationCodeLiteral_eip3860 :"
    , "    creationCodeLiteral.length <= eip3860InitcodeLimit := by"
    , "  rw [creationCodeLiteral_length, eip3860InitcodeLimit_exact]"
    , "  decide"
    , ""
    , "theorem creationCodeLiteral_headroom :"
    , "    eip3860InitcodeLimit - creationCodeLiteral.length = " ++
        toString headroom ++ " := by"
    , "  rw [creationCodeLiteral_length, eip3860InitcodeLimit_exact]"
    , ""
    , "end Blanc.Drip"
    , "" ]

private def outPath : System.FilePath := "Blanc" / "DripCreationCode.lean"

#eval show IO Unit from do
  IO.FS.writeFile outPath (renderModule creationCode)
  IO.println s!"wrote {outPath} ({creationCode.length} bytes)"

end Blanc.Drip
