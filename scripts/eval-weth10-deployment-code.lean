-- Emit the generic WETH10 initcode and two independently named expected
-- runtime members for the deployment fixture gate.

import Blanc.Weth10Deploy

namespace Blanc.Weth10

open Jaune

def deploymentFixtureMainnetAddress : Adr :=
  (0xf4BB2e28688e89fCcE3c0580D37d36A7672E8A9F : B256).toAdr

def deploymentFixtureSyntheticAddress : Adr :=
  (0x0000000000000000000000000000000000001000 : B256).toAdr

private def emitBytes (label : String) (code : Bytes) : IO Unit :=
  IO.println s!"{label} {code.length} {code.toHex}"

#eval show IO Unit from do
  emitBytes "initcode" weth10InitCode
  IO.println s!"prefix-length {weth10InitPrefix.length}"
  emitBytes "mainnet-runtime"
    (weth10Code (freshDeployParams 1 deploymentFixtureMainnetAddress))
  emitBytes "synthetic-runtime"
    (weth10Code
      (freshDeployParams 31337 deploymentFixtureSyntheticAddress))

end Blanc.Weth10
