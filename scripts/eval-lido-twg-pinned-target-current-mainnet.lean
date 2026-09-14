-- Emit the two exact compiler-owned runtimes consumed by the BPO2
-- CircuitBreaker × TriggerableWithdrawalsGateway replay.  This evaluator owns
-- no byte literal and proves nothing: the registered consumer treats its
-- output as model-boundary evidence only.

import Blanc.Composition.LidoCircuitBreakerTriggerableWithdrawalsGatewayControl

namespace Blanc.CurrentMainnet.LidoTwgPinnedTarget

open Jaune

private def emitBytes (label : String) (code : Bytes) : IO Unit :=
  IO.println s!"{label} {code.length} {code.toHex}"

#eval show IO Unit from do
  emitBytes "circuit-breaker-runtime"
    (LidoCircuitBreaker.lidoCircuitBreakerCode LidoCircuitBreaker.officialParams)
  emitBytes "gateway-runtime"
    (LidoTriggerableWithdrawalsGateway.lidoTwgCode
      Composition.LidoCircuitBreakerTwg.controlDeployParams)
  IO.println s!"gateway-locator {Composition.LidoCircuitBreakerTwg.controlDeployParams.locator.toHex}"

end Blanc.CurrentMainnet.LidoTwgPinnedTarget
