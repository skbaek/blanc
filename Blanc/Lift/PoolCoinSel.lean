import Blanc.CommonProofs.Walk

/-!
# The selectors a stable pool sends a coin

`PoolCoinSel`: `transfer`, `transferFrom`, `balanceOf`, and how a call's calldata shows it. Nothing here
mentions a coin.
-/

namespace Blanc.Lift.CurveCoins

open Jaune Blanc

/-- The selectors the pool sends a coin: `transfer`, `transferFrom`, `balanceOf`. -/
def PoolCoinSel (s : B256) : Prop := s = 0xa9059cbb ∨ s = 0x23b872dd ∨ s = 0x70a08231

theorem poolCoinSel_transfer {e : Sevm} {tail : Bytes} (h : e.data = [0xa9, 0x05, 0x9c, 0xbb] ++ tail) :
    PoolCoinSel (Sevm.selector e) :=
  .inl (selector_eq_of_data_eq_abiSelectorBytes_append (by decide) h)

theorem poolCoinSel_transferFrom {e : Sevm} {tail : Bytes}
    (h : e.data = [0x23, 0xb8, 0x72, 0xdd] ++ tail) : PoolCoinSel (Sevm.selector e) :=
  .inr (.inl (selector_eq_of_data_eq_abiSelectorBytes_append (by decide) h))

theorem poolCoinSel_balanceOf {e : Sevm} {tail : Bytes}
    (h : e.data = [0x70, 0xa0, 0x82, 0x31] ++ tail) : PoolCoinSel (Sevm.selector e) :=
  .inr (.inr (selector_eq_of_data_eq_abiSelectorBytes_append (by decide) h))

end Blanc.Lift.CurveCoins
