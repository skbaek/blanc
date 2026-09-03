-- gen-drip-code.lean : sole writer for `Blanc/DripCode.lean`.
--
-- Run from the repository root with the repository-prescribed Lean runtime.
-- It evaluates Blanc's compiler and emits the complete runtime-literal module;
-- no byte in that module is transcribed by hand.

import Blanc.Drip

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
  let headroom := pragueCodeLimits.maxCodeSize - size
  String.intercalate "\n"
    [ "-- DripCode.lean : compiler-generated DRIP runtime literal and witness."
    , "--"
    , "-- GENERATED FILE — do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-drip-code.lean"
    , "--"
    , "-- The byte list is emitted directly by `Prog.compile Drip.runtime`."
    , ""
    , "import Blanc.Drip"
    , ""
    , "namespace Blanc.Drip"
    , ""
    , "open Jaune"
    , ""
    , "/-- The " ++ toString size ++ "-byte EVM runtime emitted for DRIP. -/"
    , "def code : Bytes :="
    , "  [" ++ body.drop 3 ]
  ++ "]\n\n"
  ++ String.intercalate "\n"
    [ "/-- Kernel-checked compiler witness tying every byte-level theorem to"
    , "the committed literal above. -/"
    , "theorem code_compile : Prog.compile runtime = some code := by"
    , "  decide +kernel"
    , ""
    , "def compiledSelectors : List B256 := funcs.map Prod.fst"
    , ""
    , "theorem compiledSelectors_eq_selectors : compiledSelectors = selectors := by"
    , "  rfl"
    , ""
    , "def codeSize : Nat := code.length"
    , ""
    , "def eip170RuntimeLimit : Nat := pragueCodeLimits.maxCodeSize"
    , ""
    , "def codeHeadroom : Nat := eip170RuntimeLimit - codeSize"
    , ""
    , "theorem codeSize_exact : codeSize = " ++ toString size ++ " := by"
    , "  decide +kernel"
    , ""
    , "theorem eip170RuntimeLimit_exact : eip170RuntimeLimit = 24576 := by"
    , "  rfl"
    , ""
    , "theorem code_eip170 : codeSize <= eip170RuntimeLimit := by"
    , "  rw [codeSize_exact, eip170RuntimeLimit_exact]"
    , "  decide"
    , ""
    , "theorem codeHeadroom_exact : codeHeadroom = " ++ toString headroom ++ " := by"
    , "  unfold codeHeadroom"
    , "  rw [codeSize_exact, eip170RuntimeLimit_exact]"
    , ""
    , "end Blanc.Drip"
    , "" ]

private def outPath : System.FilePath := "Blanc" / "DripCode.lean"

#eval show IO Unit from do
  match Prog.compile runtime with
  | none =>
      throw (IO.userError "Prog.compile Drip.runtime = none — refusing to generate")
  | some bytes => do
      IO.FS.writeFile outPath (renderModule bytes)
      IO.println s!"wrote {outPath} ({bytes.length} bytes)"

end Blanc.Drip
