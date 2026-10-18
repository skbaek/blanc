import Blanc.CommonCore

/-! A code semantics that records only which bytes a frame runs.

`CodeSem.ofBytes c` is the code image `some c.toList` whose run relation says the frame runs `c`,
as `factorySem` and `pairSem` are built.  Its two side conditions are size facts, decided once
per runtime.  The three USDC runtimes (`proxySem`, `implSem`, `libSem`) are its instances. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc

/-- The certified image of the exact bytes `c`, with run relation `sevm.code = c`. -/
def CodeSem.ofBytes (c : ByteArray) (nonempty : c.size ≠ 0)
    (notDelegation : c.size ≠ eoaDelegatedCodeLength) : CodeSem where
  image := some c.toList
  Run sevm _ _ := sevm.code = c
  correct := by
    intro sevm pre post _ hcode
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj hcode
  ne_nil := by
    intro l hl hnil
    have hlen : c.data.toList.length = 0 := by
      rw [← ByteArray.toList_eq_toList_data, Option.some.inj hl, hnil, List.length_nil]
    apply nonempty
    show c.data.size = 0
    rwa [← Array.length_toList]
  not_delegation := by
    intro d hd hdel
    have hdata : d.data.toList = c.data.toList := by
      simpa only [ByteArray.toList_eq_toList_data] using Option.some.inj hd
    have hsize : d.size = c.size := by
      show d.data.size = c.data.size
      rw [← Array.length_toList, hdata, Array.length_toList]
    exact notDelegation (hsize ▸ hdel.1)

end Blanc.Lift.Usdc
