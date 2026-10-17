import Blanc.BytesWrite
import Blanc.Lift.Curve3Pool.Creation.Input

/-! The creation input's copy window is the registered runtime, by append rewriting: no kernel
comparison over the segment and no hash of the init code. -/

namespace Blanc.Lift.Curve3Pool.Creation

open Jaune

/-- The registered runtime's bytes. -/
abbrev runtime : List UInt8 := Blanc.Lift.Curve3Pool.code.data.toList

theorem runtime_length : runtime.length = 21199 := by decide +kernel

/-- **The copy window is the registered runtime**: `creation[488, 488 + 21199)` is
`Curve3Pool.code`. -/
theorem runtime_window : creationCode.sliceD 488 21199 0 = runtime := by
  rw [ByteArray.sliceD_eq, creationCode, ByteArray.toList_eq_toList_data, List.toList_toArray]
  have hp : constructorPrefix.length = 488 := by decide +kernel
  rw [← hp, ← runtime_length]
  exact Bytes.sliceD_append_middle constructorPrefix runtime constructorSuffix

end Blanc.Lift.Curve3Pool.Creation
