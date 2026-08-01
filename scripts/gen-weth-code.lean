-- gen-weth-code.lean : the named generator for `Blanc/WethCode.lean`.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-weth-code.lean
--
-- It evaluates Blanc's own compiler on `Blanc.weth` and writes the complete
-- module `Blanc/WethCode.lean` — header, byte literal, and witness theorem.
-- The literal is therefore never transcribed by hand; regenerating must leave
-- the working tree clean (`git diff --exit-code Blanc/WethCode.lean`).

import Blanc.Weth

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
    [ "-- WethCode.lean : the compiled runtime bytecode of the WETH contract, and"
    , "-- the witness theorem that Blanc's compiler really produces it."
    , "--"
    , "-- GENERATED FILE — do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-weth-code.lean"
    , "--"
    , "-- The literal below is the output of `Prog.compile weth`, emitted by the"
    , "-- compiler itself; `wethCode_compile` is what makes that claim checkable,"
    , "-- and it is audited by scripts/AxiomCheck.lean via scripts/check.sh."
    , ""
    , "import Blanc.Weth"
    , ""
    , "namespace Blanc"
    , ""
    , "open Jaune"
    , ""
    , "/-- The " ++ toString bs.length ++ "-byte EVM runtime bytecode Blanc's compiler emits for `weth`. -/"
    , "def wethCode : Bytes :="
    , "  [" ++ (body.drop 3) ]
  ++ "]\n\n"
  ++ String.intercalate "\n"
    [ "/-- **The compile witness.** Blanc's seven headline solvency theorems all"
    , "hypothesise `some code = Prog.compile weth`; without this equation every one"
    , "of them could be vacuously true. `decide +kernel` evaluates the compiler in"
    , "the kernel — no elaboration option is raised, and nothing is added to the"
    , "trusted base (in particular this is *not* `native_decide`). -/"
    , "theorem wethCode_compile : Prog.compile weth = some wethCode := by"
    , "  decide +kernel"
    , ""
    , "end Blanc"
    , "" ]

private def outPath : System.FilePath := "Blanc" / "WethCode.lean"

#eval show IO Unit from do
  match Prog.compile weth with
  | none =>
      throw (IO.userError "Prog.compile weth = none — refusing to generate")
  | some bs => do
      IO.FS.writeFile outPath (renderModule bs)
      IO.println s!"wrote {outPath} ({bs.length} bytes)"

end Blanc
