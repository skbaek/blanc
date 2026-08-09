-- Emit the generic WETH10 initcode, three independently named expected
-- runtime members, and the exact nonempty system program used by the
-- canonical configured-transaction fixture.

import Blanc.Weth10DeploymentRoot

namespace Blanc.Weth10

open Jaune

def deploymentFixtureMainnetAddress : Adr :=
  (0xf4BB2e28688e89fCcE3c0580D37d36A7672E8A9F : B256).toAdr

def deploymentFixtureSyntheticAddress : Adr :=
  (0x0000000000000000000000000000000000001000 : B256).toAdr

/-- CREATE address independently derived by the fixture generator from
private key 29's sender and nonce zero. -/
def deploymentFixtureTransactionAddress : Adr :=
  (0xcf024a39b81692e3c25b9ceb8474dc6203d584d7 : B256).toAdr

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
  emitBytes "transaction-runtime"
    (weth10Code (freshDeployParams 1 deploymentFixtureTransactionAddress))
  emitBytes "system-code" ((Prog.compile deploymentSystemProgram).getD [])

end Blanc.Weth10
