-- Emit the exact production values consumed by the finite Lido deployment
-- replay. This evaluator owns no bytes or semantic constants: every row is
-- read from the final deployment-root module family.

import Blanc.LidoCircuitBreakerDeploymentRoot

namespace Blanc.LidoCircuitBreaker

open Jaune

private def emitBytes (label : String) (value : Bytes) : IO Unit :=
  IO.println s!"{label} {value.length} {value.toHex}"

private def emitWord (label : String) (value : B256) : IO Unit :=
  IO.println s!"{label} {value.toHex}"

private def emitLog (value : Log) : IO Unit := do
  let topics := value.topics.map B256.toHex
  IO.println s!"log {value.address.toB256.toHex} {topics.length} {String.intercalate "," topics} {value.data.length} {value.data.toHex}"

#eval show IO Unit from do
  emitBytes "official-create" officialFullCreateInput
  emitBytes "official-runtime" (lidoCircuitBreakerCode officialParams)
  emitBytes "system-code" ((Prog.compile deploymentSystemProgram).getD [])
  emitWord "pause-slot" pauseDurationSlot
  emitWord "pause-value" officialConstructorArgs.initialPauseDuration
  emitWord "heartbeat-slot" heartbeatIntervalSlot
  emitWord "heartbeat-value"
    officialConstructorArgs.initialHeartbeatInterval
  for value in officialConstructorLogs 0 do
    emitLog value
  IO.println s!"gas {officialConstructorRequiredGas} {officialCodeDepositGas} {officialCreateMessageGasAccounting}"
  IO.println s!"limits {eip170RuntimeLimit} {eip3860InitcodeLimit}"

end Blanc.LidoCircuitBreaker
