import Blanc.Lift.SolcLibraryConstructor
import Blanc.Lift.Usdc.LibCreation.Check
import Blanc.Lift.Usdc.Lib.Check
import Blanc.Lift.Usdc.Constants

/-! Unadopted library-creation preview: exact certificate and runtime bindings.
No original transaction/history correspondence or production registration is asserted. -/

namespace Blanc.Lift.Usdc.LibCreation

open Jaune

/-- The checked entry is the shared library-constructor source pattern. -/
theorem entry_shape : t_0000_c0 =
    solcLibraryConstructor [0x06, 0xcd] [0x00, 0x26] (by decide) (by decide) := rfl

/-- The registered runtime's first instruction embeds the actual library address. -/
theorem runtime_head : Lib.code.sliceD 0 21 0 =
    [0x73] ++ usdcLib.toB256.toBytes.sliceD 12 20 0 := by
  decide +kernel

private theorem tail_drop : code.toList.drop 59 = Lib.code.toList.drop 21 := by
  simp only [ByteArray.toList_eq_toList_data]
  have checked : (code.data.toList.drop 59 == Lib.code.data.toList.drop 21) = true := by
    decide +kernel
  exact eq_of_beq checked

/-- The remaining runtime bytes are the unmodified creation-code window. -/
theorem runtime_tail : (code.sliceD 38 1741 0).sliceD 21 1720 0 =
    Lib.code.sliceD 21 1720 0 := by
  simp only [ByteArray.sliceD_eq]
  rw [Bytes.sliceD_sliceD_of_le _ 38 1741 21 1720 (by decide)]
  change (code.toList.drop 59).takeD 1720 0 = (Lib.code.toList.drop 21).takeD 1720 0
  exact congrArg (fun bs => bs.takeD 1720 0) tail_drop

/-- The actual source returns the registered runtime and leaves storage unchanged. -/
theorem constructor_effects {sevm : Sevm} {b post : Devm} {S : List B256} {G : Nat}
    (image : sevm.code = code) (target : sevm.currentTarget = usdcLib)
    (run : SFunc.Run cert.prog sevm (St b S Mem.empty G) t_0000_c0 (.halted post)) :
    post.getStor = b.getStor ∧ post.output = Lib.code.toList := by
  rw [entry_shape] at run
  obtain ⟨storage, output⟩ := solcLibraryConstructor_effects
    (size := 1741) (offset := 38) (by decide +kernel) (by decide +kernel)
    Mem.wf_empty Mem.reads_empty run
  change post.output = (solcLibraryPatchedImage
    (Bytes.writeAt [] 11 (sevm.code.sliceD 38 1741 0))
    sevm.currentTarget).sliceD 11 1741 0 at output
  rw [image, target] at output
  refine ⟨storage, output.trans ?_⟩
  rw [solcLibraryPatchedImage_window [] _ _ 1741 (by decide)
    (by rw [ByteArray.length_sliceD]), runtime_tail, ← runtime_head]
  simp only [ByteArray.sliceD_eq]
  rw [← List.sliceD_add Lib.code.toList 0 21 0 1720]
  apply Bytes.sliceD_zero_length
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

end Blanc.Lift.Usdc.LibCreation
