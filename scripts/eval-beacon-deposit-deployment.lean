-- Emit the exact Blanc values consumed by the temporary BeaconDeposit
-- deployment control. This evaluator does not construct a theorem or own a
-- golden: the Python control independently pins artifact identities and
-- recomputes the constructor storage before executing pinned EELS.

import Blanc.BeaconDepositDeploymentRoot

namespace Blanc.BeaconDeposit

open Jaune

private def emitBytes (label : String) (value : Bytes) : IO Unit :=
  IO.println s!"{label} {value.length} {value.toHex}"

private def emitWord (label : String) (key value : B256) : IO Unit :=
  IO.println s!"{label} {key.toHex} {value.toHex}"

#eval show IO Unit from do
  emitBytes "creation" creationCode
  emitBytes "runtime" code
  emitBytes "system-code" ((Prog.compile deploymentSystemProgram).getD [])
  for index in List.range 31 do
    let height := index + 1
    emitWord "storage" (zeroHashSlot height)
      (zeroHash Bytes.sha256 height)
  IO.println s!"gas {constructorProgramGas} {constructorCodeDepositGas} {constructorCreateMessageGasAccounting}"
  IO.println s!"limits {eip170RuntimeLimit} {eip3860InitcodeLimit}"

end Blanc.BeaconDeposit
