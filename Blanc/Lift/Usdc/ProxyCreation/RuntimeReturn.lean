import Blanc.Lift.Usdc.ProxyCreation.Cert
import Blanc.Lift.Deploy

/-!
# The original proxy constructor's returned runtime window

The registered return entry copies its executing code into symbolic memory
and halts with that exact window, retaining memory expansion in its charge.
-/

namespace Blanc.Lift.Usdc.ProxyCreation

open Jaune

/-- The registered runtime-return entry copies and returns the exact window
of its executing code, with its full memory-expansion charge. -/
theorem runtimeReturn_runExact
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (halign : M.size % 32 = 0) (hroom : S.length + 4 ≤ 1024) :
    SFunc.RunExact cert.prog sevm
      (St b S M (G + (calculateMemoryGasCost (memExtSize M.size 0 2186) -
        calculateMemoryGasCost M.size) + 226))
      t_0290_c3
      (.halted ((St b S (M.write 0 (sevm.code.sliceD 671 2186 (Linst.toUInt8 .stop))) G).withOutput (sevm.code.sliceD 671 2186 (Linst.toUInt8 .stop)))) := by
  have charge : gasCopy * ceilDiv 2186 32 + 19 = 226 := by decide
  have sizeNat : (2186 : B256).toNat = 2186 := by decide
  have offsetNat : (671 : B256).toNat = 671 := by decide
  simpa only [solcRuntimeReturn, t_0290_c3, Nat.add_assoc, charge, sizeNat, offsetNat] using
    (solcRuntimeReturn_runExact (fs := cert.prog) (sevm := sevm) (b := b)
      (S := S) (M := M) (G := G)
      (sizeHead := 0x08) (sizeTail := [0x8a])
      (offsetHead := 0x02) (offsetTail := [0x9f])
      (sizeBound := by decide) (offsetBound := by decide)
      (size := 2186) (offset := 671) (by decide) (by decide) (by decide) halign hroom)

end Blanc.Lift.Usdc.ProxyCreation
