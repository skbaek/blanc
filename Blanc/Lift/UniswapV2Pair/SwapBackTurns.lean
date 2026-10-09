import Blanc.Lift.UniswapV2Pair.SwapBack
import Blanc.Lift.UniswapV2Pair.StaticViewTurns
import Blanc.AddressSlotProofs

/-! The swap back half's typed consumption: from the suspended frame whose next
request is `balanceOf(pair)` to `token0`, the two authentic static-view turn
queues, both source resumes and the finished frame, with exact Pair storage,
logs and empty output. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A masked address word is the address itself. -/
theorem swapTokenWord_adr (a : Adr) : swapTokenWord a.toB256 = a.toB256 := by
  unfold swapTokenWord
  rw [B256.and_comm, show (0xffffffffffffffffffffffffffffffffffffffff : B256) = ~~~ addressMask
    from by decide]
  change addressSlotReadWord a.toB256 = _
  rw [addressSlotReadWord_eq_toAdr_toB256, toAdr_toB256]

/-- The raw Sync log of the shared update. -/
def swapSyncLog (pair : Adr) (bal0 bal1 : B256) : Jaune.Log :=
  ⟨pair, [updateSyncTopic], encodeWords [bal0, bal1]⟩

end Blanc.Lift.UniswapV2Pair
