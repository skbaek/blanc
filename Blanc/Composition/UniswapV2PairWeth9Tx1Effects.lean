import Blanc.Composition.UniswapV2PairWeth9Tx1

/-!
# The closed instance's first transaction: its settled world, account by account

What `tx1SettledState` is at each account, for the second transaction's world agreement: every
account other than the trader, `X` and the coinbase `0` is untouched (the pair and WETH9 among
them); `X` keeps its nonce, balance and code and has exactly the two balance writes; the trader's
nonce is bumped and its ether is `10^7 − 63514`.
-/

namespace Blanc.Composition.UniswapV2PairWeth9Instance

open Jaune Blanc Blanc.Lift
open Blanc.Lift.VyperNonreentrantDeployed.Token20 (balSlot)

theorem trader_ne_zero : trader ≠ 0 := by decide +kernel
theorem tokenX_ne_zero : tokenX ≠ 0 := by decide +kernel

/-- The token frame's writes, at `X`: two storage writes, nothing else of the account. -/
theorem tx1FrameWrites_get_self (st : Jaune.State) (xT xP : B256) :
    (tx1FrameWrites st xT xP).get tokenX =
      { st.get tokenX with
        stor := ((st.get tokenX).stor.set (balSlot trader) (xT - amountIn)).set (balSlot pair)
          (amountIn + xP) } := by
  unfold tx1FrameWrites State.setStorVal
  rw [State.get_set_self, State.get_set_self]

/-- The token frame's writes leave every other account alone. -/
theorem tx1FrameWrites_get_ne (st : Jaune.State) (xT xP : B256) {a : Adr} (h : tokenX ≠ a) :
    (tx1FrameWrites st xT xP).get a = st.get a := by
  unfold tx1FrameWrites State.setStorVal
  rw [State.get_set_ne _ h, State.get_set_ne _ h]

/-- **Every account other than the trader, `X` and the coinbase `0` is untouched by `tx1`.** -/
theorem tx1_settled_get_other (st : Jaune.State) (xT xP : B256) {a : Adr}
    (ht : trader ≠ a) (hx : tokenX ≠ a) (h0 : (0 : Adr) ≠ a) :
    (tx1SettledState st xT xP).get a = st.get a := by
  unfold tx1SettledState tx1FrameState
  rw [addBal_get_ne _ h0, addBal_get_ne _ ht, tx1FrameWrites_get_ne _ _ _ hx, tx1DebitState,
    debit_get_ne ht]

/-- **`X` after `tx1`**: its nonce, balance and code kept, its storage with exactly the two writes
(`balanceOf[trader] := xT − amountIn`, then `balanceOf[pair] := amountIn + xP`). -/
theorem tx1_settled_get_tokenX (st : Jaune.State) (xT xP : B256) :
    (tx1SettledState st xT xP).get tokenX =
      { st.get tokenX with
        stor := ((st.get tokenX).stor.set (balSlot trader) (xT - amountIn)).set (balSlot pair)
          (amountIn + xP) } := by
  unfold tx1SettledState tx1FrameState
  rw [addBal_get_ne _ tokenX_ne_zero.symm, addBal_get_ne _ trader_ne_tokenX,
    tx1FrameWrites_get_self, tx1DebitState, debit_get_ne trader_ne_tokenX]

/-- **The trader after `tx1`**: nonce bumped, ether `9900000 + 36486 = 9936486` (the up-front
`100000` less the refund of the unused `18243 × 2`), storage and code kept. -/
theorem tx1_settled_get_trader (st : Jaune.State) (xT xP : B256)
    (hnonce : (st.get trader).nonce ≠ UInt64.max) :
    (tx1SettledState st xT xP).get trader =
      { st.get trader with nonce := (st.get trader).nonce + 1, bal := 9936486 } := by
  unfold tx1SettledState tx1FrameState
  rw [addBal_get_ne _ trader_ne_zero.symm, addBal_get_self,
    tx1FrameWrites_get_ne _ _ _ trader_ne_tokenX.symm, tx1DebitState, debit_get_self hnonce]
  have hsum : (9900000 : B256) + 36486 = 9936486 := by decide +kernel
  have hbal : ((st.incrNonce trader).setBal trader 9900000).bal trader = 9900000 := by
    change (((st.incrNonce trader).setBal trader 9900000).get trader).bal = 9900000
    rw [debit_get_self hnonce]
  rw [tx1FrameWrites, State.setStorVal, State.setStorVal, State.bal,
    State.get_set_ne _ trader_ne_tokenX.symm, State.get_set_ne _ trader_ne_tokenX.symm]
  change (({ st.get trader with nonce := (st.get trader).nonce + 1, bal := 9900000 } : Acct).withBal
    (((st.incrNonce trader).setBal trader 9900000).bal trader + 36486)).clearIfEmpty = _
  rw [hbal, hsum, Acct.clearIfEmpty_of_not_empty]
  · rfl
  · rintro ⟨-, -, hz⟩
    have ne : (9936486 : B256) ≠ 0 := by decide +kernel
    exact ne hz

end Blanc.Composition.UniswapV2PairWeth9Instance
