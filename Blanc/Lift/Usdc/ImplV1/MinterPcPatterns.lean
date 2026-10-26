import Blanc.BytePattern
import Blanc.Lift.Usdc.ImplV1.Cert

/-! Exact V1 minter store-tail byte patterns, including immediate-byte offsets. -/

namespace Blanc.Lift.Usdc.ImplV1

open Jaune

def minter160bPattern : List UInt8 := [0x55, 0x50, 0x60, 0x00]
def minter1650Pattern : List UInt8 := [0x55, 0x50, 0x81, 0x73]
def minter20b2Pattern : List UInt8 := [0x55, 0x50, 0x81, 0x60, 0x0d]
def minter20f6Pattern : List UInt8 := [0x55, 0x50, 0x82, 0x73]

theorem minter160bPattern_ne_nil : minter160bPattern ≠ [] := by decide +kernel
theorem minter1650Pattern_ne_nil : minter1650Pattern ≠ [] := by decide +kernel
theorem minter20b2Pattern_ne_nil : minter20b2Pattern ≠ [] := by decide +kernel
theorem minter20f6Pattern_ne_nil : minter20f6Pattern ≠ [] := by decide +kernel

/-- The complete registered V1 bytecode has exactly this store-tail occurrence. -/
theorem minter160bPattern_occurrences :
    Blanc.BytePattern.occurrences minter160bPattern code.toList = [0x160b] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The complete registered V1 bytecode has exactly this store-tail occurrence. -/
theorem minter1650Pattern_occurrences :
    Blanc.BytePattern.occurrences minter1650Pattern code.toList = [0x1650] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The complete registered V1 bytecode has exactly this store-tail occurrence. -/
theorem minter20b2Pattern_occurrences :
    Blanc.BytePattern.occurrences minter20b2Pattern code.toList = [0x20b2] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The complete registered V1 bytecode has exactly this store-tail occurrence. -/
theorem minter20f6Pattern_occurrences :
    Blanc.BytePattern.occurrences minter20f6Pattern code.toList = [0x20f6] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

end Blanc.Lift.Usdc.ImplV1
