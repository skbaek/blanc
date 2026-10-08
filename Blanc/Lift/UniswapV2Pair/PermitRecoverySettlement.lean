import Blanc.Lift.UniswapV2Pair.PermitPositional
import Blanc.Lift.UniswapV2Pair.SourceOccurrence

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The actual instruction reads the recovery request from its own memory. -/
theorem PermitCallOccurrence.request_image {root : Exec.Deriv} {b : Devm}
    (actual : PermitCallOccurrence root b) :
    (actual.call.occurrence.node.devm.memory.read (482 : B256).toNat (128 : B256).toNat).1 =
      ExternalOperation.encode (.recover (permitPublicDigest root.sevm b)
        (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)) := by
  rw [actual.beforeMemory]
  have request := (permitCallMemory_facts (sevm := root.sevm) (b := b)
    getterInitMemory_ptr (Mem.reads_data getterInitMemory) (permitOwner root.sevm)
    (permitSpender root.sevm) (permitValue root.sevm) (permitDeadline root.sevm)
    (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)).2.1
  change ((permitPublicCallMemory root.sevm b).read 482 128).1 =
    ExternalOperation.encode (.recover (permitPublicDigest root.sevm b)
      (permitV root.sevm) (permitR root.sevm) (permitS root.sevm)) at request
  simpa only [show (482 : B256).toNat = 482 from rfl,
    show (128 : B256).toNat = 128 from rfl] using request

end Blanc.Lift.UniswapV2Pair
