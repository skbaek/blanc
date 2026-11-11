import Blanc.ExecutionKeptFrames
import Blanc.ExecutionAccountingStoragePrefix

/-!
# Whole-storage replay of the actual kept-frame chain

The existing chain supplies every incoming storage boundary. A contract supplies only its
per-frame pure update law; the existing guarded replay then retains the exact fold and prefixes.
-/

namespace Blanc

open Jaune ExecutionAccountingReplay

/-- Convert the actual kept-frame storage chain to the existing guarded replay, without adding
an endpoint or prefix premise. -/
theorem KeptChain.storageReplay {a : Adr} {s t : Stor} {fs : List Exec.Frame}
    (chain : KeptChain a s fs t) (update : Stor → Exec.Frame → Stor)
    (each : ∀ f ∈ fs, Devm.getStor f.post a = update (Devm.getStor f.pre a) f) :
    GuardedStorageReplay update (fun incoming f => Devm.getStor f.pre a = incoming) s fs t := by
  revert each
  induction chain with
  | nil s =>
      intro _
      exact .nil s
  | @cons s t f rest starts tail ih =>
      intro each
      have post : Devm.getStor f.post a = update s f := by
        rw [← starts]
        exact each f List.mem_cons_self
      refine .cons starts ?_
      rw [← post]
      exact ih fun g hg => each g (List.mem_cons_of_mem _ hg)

end Blanc
