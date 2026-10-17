import Blanc.BytesWrite
import Blanc.Lift.UniswapV2Factory.Cert

/-! The certified factory bytes are `factoryCode`, and its `CODECOPY` window `[2171, 2171 + 11636)`
is the registered Pair creation code, by list reasoning alone: no byte of the embedded creation
code is evaluated. -/

namespace Blanc.Lift.UniswapV2Factory

open Jaune

/-- The bytes the factory certificate checks are `factoryCode`
(`logic ++ UniswapV2Pair.Creation.code ++ metadata`). -/
theorem code_eq_factoryCode : code = factoryCode := rfl

theorem logic_length : logic.length = 2171 := by decide +kernel

/-- The registered Pair creation code's length; a length count, not a byte comparison. -/
theorem pairCreation_length : UniswapV2Pair.Creation.code.data.toList.length = 11636 := by
  decide +kernel

/-- **The `CREATE2` init-code window is the Pair creation code**: `code[2171, 2171 + 11636)` is
`UniswapV2Pair.Creation.code`. -/
theorem pairCreation_window :
    code.sliceD 2171 11636 0 = UniswapV2Pair.Creation.code.toList := by
  rw [ByteArray.sliceD_eq, code_eq_factoryCode, factoryCode, ByteArray.toList_eq_toList_data,
    List.toList_toArray, ByteArray.toList_eq_toList_data, ← logic_length, ← pairCreation_length]
  exact Bytes.sliceD_append_middle logic _ metadata

end Blanc.Lift.UniswapV2Factory
