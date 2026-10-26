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
  let window := sevm.code.sliceD 671 2186 (Linst.toUInt8 .stop)
  let copied := M.write 0 window
  have hlen : window.length = 2186 := ByteArray.length_sliceD _ _ _ _
  have hne : window ≠ [] := by
    intro hnil
    rw [hnil] at hlen
    cases hlen
  have hsize : copied.size = memExtSize M.size 0 2186 :=
    Mem.size_write_of_size rfl halign hlen
  have hmod : copied.size % 32 = 0 := by
    rw [hsize]
    exact memExtSize_mod_32 halign
  have hfit : 0 + 2186 ≤ copied.size := by
    have h := Mem.write_end_le_size M 0 hne
    simpa only [hlen] using h
  have hread : (copied.read 0 2186).1 = window := by
    change ((M.write 0 window).read 0 2186).1 = window
    rw [← hlen]
    exact Mem.read_write_zero M hne
  have hmem : (copied.read 0 2186).2 = copied :=
    Mem.read_snd_eq_self (memExtSize_of_le hmod hfit)
  have hpost : returnPost (St b (0 :: 2186 :: S) copied G) 0 2186 S =
      (St b S copied G).withOutput window := by
    change ((St b S copied G).withMemory (copied.read 0 2186).2).withOutput
      (copied.read 0 2186).1 = _
    rw [hmem, hread]
    rfl
  change SFunc.RunExact cert.prog sevm _ t_0290_c3
    (.halted ((St b S copied G).withOutput window))
  rw [← hpost]
  unfold t_0290_c3
  apply rx_dest
  apply rx_push (w := 2186) (by decide) (by omega)
  apply rx_dup (n := 0) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 671) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
  rw [show G + (calculateMemoryGasCost (memExtSize M.size 0 2186) -
      calculateMemoryGasCost M.size) + 213 =
      (G + 3) + ((calculateMemoryGasCost (memExtSize M.size 0 2186) -
        calculateMemoryGasCost M.size) + 210) by omega]
  refine rx_codecopy (G := G + 3)
    (c := (calculateMemoryGasCost (memExtSize M.size 0 2186) -
      calculateMemoryGasCost M.size) + 210) (M' := copied) ?_ ?_ ?_
  · rw [St.extCost_eq rfl]
    change 210 + (calculateMemoryGasCost (memExtSize M.size 0 2186) -
      calculateMemoryGasCost M.size) = _
    omega
  · rfl
  · apply rx_push (w := 0) (by decide) (by simp only [List.length_cons]; omega)
    exact rx_return_any rfl (Devm.extCost_zero_of_le hmod hfit)

end Blanc.Lift.Usdc.ProxyCreation
