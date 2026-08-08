-- gen-weth10-template.lean : generate the zero-parameter runtime literal.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-weth10-template.lean

import Blanc.Weth10

namespace Blanc.Weth10

open Jaune

private def hexByte (b : UInt8) : String :=
  let ds := Nat.toDigits 16 b.toNat
  "0x" ++ (if ds.length == 1 then "0" ++ String.ofList ds else String.ofList ds)

private partial def chunks (n : Nat) (xs : List String) : List (List String) :=
  if xs.isEmpty then [] else xs.take n :: chunks n (xs.drop n)

private def renderModule (bs : Bytes) : String :=
  let rows := chunks 12 (bs.map hexByte)
  let body :=
    String.intercalate ",\n" (rows.map fun row => "   " ++ String.intercalate ", " row)
  String.intercalate "\n"
    [ "-- Weth10TemplateCode.lean : zero-parameter runtime template literal."
    , "--"
    , "-- GENERATED FILE — do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-weth10-template.lean"
    , ""
    , "import Blanc.Weth10"
    , ""
    , "namespace Blanc.Weth10"
    , ""
    , "open Jaune"
    , ""
    , "/-- The " ++ toString bs.length ++ "-byte zero-parameter member of the runtime"
    , "family, committed as a literal.  `Blanc/Weth10Deploy.lean` defines"
    , "`weth10RuntimeTemplate` as this literal and re-establishes the identity with"
    , "`weth10Code ⟨0, 0⟩` by a kernel-checked witness, so kernel-side computation"
    , "over the template (lengths, slices, token folds) runs on a literal byte list"
    , "instead of re-evaluating `Prog.compile` at every proof that touches it. -/"
    , "def weth10TemplateCode : Bytes :="
    , "  [" ++ (body.drop 3) ]
  ++ "]\n\n"
  ++ String.intercalate "\n"
    [ "end Blanc.Weth10"
    , "" ]

private def outPath : System.FilePath := "Blanc" / "Weth10TemplateCode.lean"

#eval show IO Unit from do
  match Prog.compile (weth10 (⟨0, 0⟩ : DeployParams)) with
  | some base => do
      if base.length != 6313 then
        throw (IO.userError s!"zero-parameter runtime length {base.length} ≠ 6313")
      IO.FS.writeFile outPath (renderModule base)
      IO.println s!"wrote {outPath} ({base.length} bytes)"
  | none =>
      throw (IO.userError "Prog.compile WETH10 ⟨0, 0⟩ = none")

end Blanc.Weth10
