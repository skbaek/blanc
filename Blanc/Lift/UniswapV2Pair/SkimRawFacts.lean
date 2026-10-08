import Blanc.Lift.UniswapV2Pair.SkimSecondWalk

namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem skim_cached_getStor (sevm : Sevm) (b : Devm) :
    Devm.getStor (skimCachedWorld sevm b) sevm.currentTarget =
      (Devm.getStor b sevm.currentTarget).set 12 0 := by
  unfold skimCachedWorld syncLockedWorld
  rw [afterSload_getStor, afterSload_getStor, afterSload_getStor, afterSstore_getStor_self,
    afterSload_getStor]

theorem skim_cached_getCode (sevm : Sevm) (b : Devm) (a : Adr) :
    (skimCachedWorld sevm b).getCode a = b.getCode a := by
  unfold skimCachedWorld syncLockedWorld
  rw [afterSload_getCode, afterSload_getCode, afterSload_getCode, afterSstore_getCode,
    afterSload_getCode]

theorem skim_cached_output (sevm : Sevm) (b : Devm) :
    (skimCachedWorld sevm b).output = b.output := by
  unfold skimCachedWorld syncLockedWorld
  rw [afterSload_output, afterSload_output, afterSload_output, afterSstore_output,
    afterSload_output]

end Blanc.Lift.UniswapV2Pair
