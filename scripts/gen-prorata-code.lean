-- gen-prorata-code.lean : the named generator for `Blanc/ProrataCode.lean`.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-prorata-code.lean
--
-- It evaluates Blanc's own compiler on `Blanc.Prorata.prorata` and writes the
-- complete module `Blanc/ProrataCode.lean` — header, byte literal, and witness
-- theorem. The literal is therefore never transcribed by hand; regenerating
-- must leave the working tree clean (`git diff --exit-code Blanc/ProrataCode.lean`).
--
-- A sibling of `scripts/gen-fmint-code.lean` and `scripts/gen-weth-code.lean`,
-- deliberately kept a separate script rather than a parameterised one: each
-- generator names exactly one program and writes exactly one file, so a
-- regeneration can never touch another contract's committed bytes.

import Blanc.Prorata

namespace Blanc

open Jaune

/-- Two-digit `0x`-prefixed hex for one byte. -/
private def hexByte (b : UInt8) : String :=
  let ds := Nat.toDigits 16 b.toNat
  "0x" ++ (if ds.length == 1 then "0" ++ String.ofList ds else String.ofList ds)

private partial def chunks (n : Nat) (xs : List String) : List (List String) :=
  if xs.isEmpty then [] else xs.take n :: chunks n (xs.drop n)

/-- The generated module text for a compiled program's bytes. -/
private def renderModule (bs : Bytes) : String :=
  let rows := chunks 12 (bs.map hexByte)
  let body :=
    String.intercalate ",\n" (rows.map fun row => "   " ++ String.intercalate ", " row)
  String.intercalate "\n"
    [ "-- ProrataCode.lean : the compiled runtime bytecode of the PRORATA contract,"
    , "-- and the witness theorem that Blanc's compiler really produces it."
    , "--"
    , "-- GENERATED FILE — do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-prorata-code.lean"
    , "--"
    , "-- The literal below is the output of `Prog.compile Prorata.prorata`, emitted"
    , "-- by the compiler itself; `prorataCode_compile` is what makes that claim"
    , "-- checkable, and it is audited by scripts/AxiomCheck.lean via"
    , "-- scripts/check.sh."
    , ""
    , "import Blanc.Prorata"
    , ""
    , "namespace Blanc"
    , ""
    , "open Jaune"
    , ""
    , "/-- The " ++ toString bs.length ++ "-byte EVM runtime bytecode Blanc's compiler emits for"
    , "`Prorata.prorata`. -/"
    , "def prorataCode : Bytes :="
    , "  [" ++ (body.drop 3) ]
  ++ "]\n\n"
  ++ String.intercalate "\n"
    [ "/-- **The compile witness.** Every PRORATA statement at compiled-bytes"
    , "altitude hypothesises `some code = Prog.compile Prorata.prorata`, so without"
    , "this equation each of them could be discharged vacuously. This equation is"
    , "what keeps all of them about the bytes below rather than about nothing."
    , ""
    , "`decide +kernel` evaluates the compiler in the kernel — no elaboration option"
    , "is raised, and nothing is added to the trusted base (in particular this is"
    , "not a native evaluation shortcut). -/"
    , "theorem prorataCode_compile : Prog.compile Prorata.prorata = some prorataCode := by"
    , "  decide +kernel"
    , ""
    , "end Blanc"
    , "" ]

private def outPath : System.FilePath := "Blanc" / "ProrataCode.lean"

#eval show IO Unit from do
  match Prog.compile Prorata.prorata with
  | none =>
      throw (IO.userError "Prog.compile Prorata.prorata = none — refusing to generate")
  | some bs => do
      IO.FS.writeFile outPath (renderModule bs)
      IO.println s!"wrote {outPath} ({bs.length} bytes)"

end Blanc
