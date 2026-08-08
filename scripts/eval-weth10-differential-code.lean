-- Emit the two concrete Blanc runtimes used by the WETH10 differential rig.
--
-- This is an evaluator, not a generated runtime owner.  The universal family
-- and its proof stay in `Blanc.Weth10Code`; this script merely gives the
-- independent Python/EELS harness exact bytes for two named parameter worlds.

import Blanc.Weth10

namespace Blanc.Weth10

open Jaune

def differentialSyntheticAddress : B256 :=
  0x0000000000000000000000000000000000000000000000000000000000001000

def differentialSyntheticChainId : B256 := 31337

def differentialSyntheticDomainSeparator : B256 :=
  0x1967b0678ebf880673e5717c2e034e403352644648cbf7f427c2d47faa9d4efb

def differentialSyntheticParams : DeployParams :=
  ⟨differentialSyntheticChainId, differentialSyntheticDomainSeparator⟩

def differentialMainnetParams : DeployParams :=
  ⟨1, 0x9d6861d4de8c156e6b3155e3283174a7c6c86fd27c1ff43e1f05cc2d417fbb65⟩

private def emit (label : String) (dp : DeployParams) : IO Unit := do
  match Prog.compile (weth10 dp) with
  | none => throw (IO.userError s!"{label}: WETH10 compilation failed")
  | some code => IO.println s!"{label} {code.length} {code.toHex}"

#eval show IO Unit from do
  emit "mainnet" differentialMainnetParams
  emit "synthetic" differentialSyntheticParams
  IO.println s!"synthetic-domain {differentialSyntheticDomainSeparator.toNat}"
  let selectors := (weth10Funcs differentialMainnetParams).map (fun row => row.1.toHex)
  IO.println s!"selectors {selectors.length} {String.intercalate "," selectors}"

end Blanc.Weth10
