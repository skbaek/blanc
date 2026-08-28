import Blanc.BeaconDepositDeploy

namespace Blanc.BeaconDeposit

open Jaune

private def emitBytes (label : String) (value : Bytes) : IO Unit :=
  IO.println s!"{label} {value.length} {value.toHex}"

private def selectorHex (value : B256) : String :=
  (abiSelectorBytes value).toHex

#eval show IO Unit from do
  emitBytes "runtime" code
  emitBytes "creation" creationCode
  let values := selectors.map selectorHex
  IO.println s!"selectors {values.length} {String.intercalate "," values}"

end Blanc.BeaconDeposit
