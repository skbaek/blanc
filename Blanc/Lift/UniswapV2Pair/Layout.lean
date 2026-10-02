import Blanc.Lift.UniswapV2Pair.Execution

/-! The selected packed slot observed by the checked getReserves path. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def reserveMask112 : B256 := 0xffffffffffffffffffffffffffff
def reserveMask32 : B256 := 0xffffffff
def reserveDiv112 : B256 := 0x10000000000000000000000000000
def reserveDiv224 : B256 := 0x100000000000000000000000000000000000000000000000000000000

def reserve0Read (word : B256) : B256 := word &&& reserveMask112
def reserve1Read (word : B256) : B256 := (word / reserveDiv112) &&& reserveMask112
def reserveTimestampRead (word : B256) : B256 := (word / reserveDiv224) &&& reserveMask32

/-- The uint112/uint112/uint32 source fields equal their actual selected-slot
extractions. Their bounds are carried by State's Fin and UInt32 fields. -/
def ReserveSlotMatches (st : State) (sevm : Sevm) (b : Devm) : Prop :=
  reserve0Read (b.getStorVal sevm.currentTarget 8) = Nat.toB256 st.reserve0.val ∧
  reserve1Read (b.getStorVal sevm.currentTarget 8) = Nat.toB256 st.reserve1.val ∧
  reserveTimestampRead (b.getStorVal sevm.currentTarget 8) = st.blockTimestampLast.toB256

theorem reserveSource_result {st : State} {sevm : Sevm} {b : Devm}
    (slots : ReserveSlotMatches st sevm b) :
    getterResult st .getReserves = some (encodeWords
      [reserve0Read (b.getStorVal sevm.currentTarget 8),
       reserve1Read (b.getStorVal sevm.currentTarget 8),
       reserveTimestampRead (b.getStorVal sevm.currentTarget 8)]) := by
  rcases slots with ⟨h0, h1, ht⟩
  simp only [getterResult, h0, h1, ht]

end Blanc.Lift.UniswapV2Pair
