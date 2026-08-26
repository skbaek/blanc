-- gen-weth10-code.lean : generate the canonical WETH10 runtime artifact.
--
-- Run from the repository root:
--
--     lake env lean scripts/gen-weth10-code.lean

import Blanc.Weth10

namespace Blanc.Weth10

open Jaune

def mainnetDeployParams : DeployParams :=
  ⟨1, 0x9d6861d4de8c156e6b3155e3283174a7c6c86fd27c1ff43e1f05cc2d417fbb65⟩

private def hexByte (b : UInt8) : String :=
  let ds := Nat.toDigits 16 b.toNat
  "0x" ++ (if ds.length == 1 then "0" ++ String.ofList ds else String.ofList ds)

private partial def chunks (n : Nat) (xs : List String) : List (List String) :=
  if xs.isEmpty then [] else xs.take n :: chunks n (xs.drop n)

private def diffIndices : Nat → Bytes → Bytes → List Nat
  | _, [], [] => []
  | i, x :: xs, y :: ys =>
      (if x = y then [] else [i]) ++ diffIndices (i + 1) xs ys
  | _, _, _ => []

private def changedWordStarts (base changed : Bytes) : List Nat :=
  let ds := diffIndices 0 base changed
  ds.filter fun i => i = 0 || !(ds.contains (i - 1))

private def expectedChangedIndices (starts : List Nat) : List Nat :=
  starts.flatMap fun start => (List.range 32).map (start + ·)

private def renderNats (xs : List Nat) : String :=
  "[" ++ String.intercalate ", " (xs.map toString) ++ "]"

private def renderModule (bs : Bytes) (chainOffsets separatorOffsets : List Nat) : String :=
  let rows := chunks 12 (bs.map hexByte)
  let body :=
    String.intercalate ",\n" (rows.map fun row => "   " ++ String.intercalate ", " row)
  String.intercalate "\n"
    [ "-- Weth10Code.lean : parameterized compiled runtime and canonical artifact."
    , "--"
    , "-- GENERATED FILE — do not edit by hand. Regenerate with:"
    , "--"
    , "--     lake env lean scripts/gen-weth10-code.lean"
    , ""
    , "import Blanc.Weth10"
    , ""
    , "namespace Blanc.Weth10"
    , ""
    , "open Jaune"
    , ""
    , "/-- The runtime family. Fixed-width deployment words make every layout and"
    , "compiler guard independent of the concrete deployment parameters. -/"
    , "def weth10Code (dp : DeployParams) : Bytes :="
    , "  (Prog.compile (weth10 dp)).getD []"
    , ""
    , "/-- Universal compiler witness: compilation succeeds for every deployment. -/"
    , "theorem weth10Code_compile (dp : DeployParams) :"
    , "    Prog.compile (weth10 dp) = some (weth10Code dp) := by"
    , "  unfold weth10Code"
    , "  exact Prog.compile_eq_some_getD_of_compiles _ (weth10_compiles dp)"
    , ""
    , "/-- Parameters embedded by the locked mainnet deployment. -/"
    , "def mainnetDeployParams : DeployParams :="
    , "  ⟨1, 0x9d6861d4de8c156e6b3155e3283174a7c6c86fd27c1ff43e1f05cc2d417fbb65⟩"
    , ""
    , "/-- Byte offsets of the first byte of every fixed-width chain-ID word. -/"
    , "def deploymentChainIdWordOffsets : List Nat := " ++ renderNats chainOffsets
    , ""
    , "/-- Byte offsets of the first byte of every fixed-width cached-domain word. -/"
    , "def cachedDomainSeparatorWordOffsets : List Nat := " ++ renderNats separatorOffsets
    , ""
    , "/-- The " ++ toString bs.length ++ "-byte canonical mainnet-parameter runtime. -/"
    , "def weth10MainnetCode : Bytes :="
    , "  [" ++ (body.drop 3) ]
  ++ "]\n\n"
  ++ "end Blanc.Weth10\n"

private def outPath : System.FilePath := "Blanc" / "Weth10Code.lean"

#eval show IO Unit from do
  let zero : DeployParams := ⟨0, 0⟩
  let chainMarker : DeployParams := ⟨B256.max, 0⟩
  let separatorMarker : DeployParams := ⟨0, B256.max⟩
  match Prog.compile (weth10 mainnetDeployParams), Prog.compile (weth10 zero),
      Prog.compile (weth10 chainMarker), Prog.compile (weth10 separatorMarker) with
  | some bs, some base, some chainChanged, some separatorChanged => do
      if bs.length != base.length || base.length != chainChanged.length ||
          base.length != separatorChanged.length then
        throw (IO.userError "deployment parameters changed runtime length")
      let chainOffsets := changedWordStarts base chainChanged
      let separatorOffsets := changedWordStarts base separatorChanged
      let chainDiffs := diffIndices 0 base chainChanged
      let separatorDiffs := diffIndices 0 base separatorChanged
      if chainDiffs != expectedChangedIndices chainOffsets || chainOffsets.length != 3 then
        throw (IO.userError s!"unexpected chain-ID patch spans: {chainOffsets}")
      if separatorDiffs != expectedChangedIndices separatorOffsets ||
          separatorOffsets.length != 2 then
        throw (IO.userError s!"unexpected cached-domain patch spans: {separatorOffsets}")
      IO.FS.writeFile outPath (renderModule bs chainOffsets separatorOffsets)
      IO.println s!"wrote {outPath} ({bs.length} bytes; chain {chainOffsets}; domain {separatorOffsets})"
  | _, _, _, _ =>
      throw (IO.userError "Prog.compile WETH10 family = none")

end Blanc.Weth10
