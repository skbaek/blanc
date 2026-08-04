-- gen-fmint-code.lean : the named generator for `Blanc/FmintCode.lean`.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-fmint-code.lean
--
-- It evaluates Blanc's own compiler on `Blanc.Fmint.fmint` and writes the
-- complete module `Blanc/FmintCode.lean` — header, byte literal, and witness
-- theorem. The literal is therefore never transcribed by hand; regenerating
-- must leave the working tree clean (`git diff --exit-code Blanc/FmintCode.lean`).
--
-- The sibling of `scripts/gen-weth-code.lean`, deliberately kept a separate
-- script rather than a parameterised one: each generator names exactly one
-- program and writes exactly one file, so a regeneration can never touch the
-- other contract's committed bytes. That is the property the WETH tripwire
-- relies on.

import Blanc.Fmint

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
    [ "-- FmintCode.lean : the compiled runtime bytecode of the fmint contract,"
    , "-- and the witness theorem that Blanc's compiler really produces it."
    , "--"
    , "-- GENERATED FILE — do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-fmint-code.lean"
    , "--"
    , "-- The literal below is the output of `Prog.compile Fmint.fmint`, emitted by"
    , "-- the compiler itself; `fmintCode_compile` is what makes that claim"
    , "-- checkable, and it is audited by scripts/AxiomCheck.lean via"
    , "-- scripts/check.sh."
    , ""
    , "import Blanc.Fmint"
    , ""
    , "namespace Blanc"
    , ""
    , "open Jaune"
    , ""
    , "/-- The " ++ toString bs.length ++ "-byte EVM runtime bytecode Blanc's compiler emits for"
    , "`Fmint.fmint`. -/"
    , "def fmintCode : Bytes :="
    , "  [" ++ (body.drop 3) ]
  ++ "]\n\n"
  ++ String.intercalate "\n"
    [ "/-- **The compile witness.** Every statement in `Blanc/Flashmint.lean`"
    , "hypothesises `some code = Prog.compile Fmint.fmint`, so without this equation"
    , "each of them could be discharged vacuously. Those statements are still"
    , "statements — conservation is unproven, pending Arc B of"
    , "`~/plans/flashmint-proposal.md` — so the witness lands ahead of the proofs"
    , "that will need it rather than beside them."
    , ""
    , "`decide +kernel` evaluates the compiler in the kernel — no elaboration option"
    , "is raised, and nothing is added to the trusted base (in particular this is"
    , "*not* `native_decide`). -/"
    , "theorem fmintCode_compile : Prog.compile Fmint.fmint = some fmintCode := by"
    , "  decide +kernel"
    , ""
    , "end Blanc"
    , "" ]

private def outPath : System.FilePath := "Blanc" / "FmintCode.lean"

#eval show IO Unit from do
  match Prog.compile Fmint.fmint with
  | none =>
      throw (IO.userError "Prog.compile Fmint.fmint = none — refusing to generate")
  | some bs => do
      IO.FS.writeFile outPath (renderModule bs)
      IO.println s!"wrote {outPath} ({bs.length} bytes)"

end Blanc
