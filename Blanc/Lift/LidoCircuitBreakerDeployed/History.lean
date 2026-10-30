import Blanc.Lift.LidoCircuitBreakerDeployed.Pause
import Blanc.Lift.LidoCircuitBreakerDeployed.L2Frame
import Blanc.Lift.LidoCircuitBreakerDeployed.Corollaries

/-!
# The instantiated Lido writer specifications

`LidoWriterSpecsM lidoA` from the two writer walks, over the concrete per-frame premise `lidoA`,
and the state invariant from the raw-slot checkpoint form `RegistryZeroRaw`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker
open Blanc.ExecutionTrace
open scoped BigOperators

/-- Both Registry writers, with the concrete premise `lidoA`. -/
theorem lidoWriterSpecsM : LidoWriterSpecsM lidoA :=
  ⟨fun hfork hw hloc hA hmem hpre run =>
      registerPauser_wrapper_post hfork hw hloc hA hmem hpre run,
   fun hfork hcode hadm ih hw hloc hA hmem hpre run =>
      pause_wrapper_post hfork hcode hadm ih hw hloc hA hmem hpre run⟩

/-- The checkpoint premise in raw form gives the state invariant. -/
theorem stateInv_of_registryZeroRaw {ca : Adr} {w : Jaune.State}
    (hcode : some (w.getCode ca).toList = lidoSpec.sem.image)
    (hzero : RegistryZeroRaw (w.getStor ca)) : lidoSpec.StateInv ca w :=
  ⟨hcode, trivial, inv_of_registryZero (registryZero_of_raw hzero)⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
