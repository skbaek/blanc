import Blanc.LidoTriggerableWithdrawalsGateway
import Blanc.StaticStores

/-!
# Static exclusion for the TWG limit writer

The production `setLimitWrite` body begins with a long staging line followed
by `SSTORE`. Naming that exact prefix keeps the proof a bounded check and lets
a successful source run discharge its dynamic-frame premise.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

namespace LidoTriggerableWithdrawalsGateway

theorem setLimitWrite_storesOrHalts {fs : List Func} :
    StoresOrHalts fs setLimitWrite := by
  unfold setLimitWrite storePackedLimitWorkingWords
  stores_line (mloadWord 0 ++ mstoreAt 13 ++ mloadWord 2 ++ mstoreAt 6 ++
    mloadWord 1 ++ mstoreAt 7 ++ packFiveUint32Words 13 4 12 6 7 ++
    [pushB256 twrLimitPosition])
  exact StoresOrHalts.store

theorem setLimitWrite_isStatic_eq_false {fs : List Func} {e : Sevm}
    {s r : Devm} (run : Func.Run fs e s setLimitWrite r) :
    e.isStatic = false :=
  setLimitWrite_storesOrHalts.isStatic_eq_false run

end LidoTriggerableWithdrawalsGateway
end Blanc
