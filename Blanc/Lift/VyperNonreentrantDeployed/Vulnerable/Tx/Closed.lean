import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Frame1

/-!
# V- as an admitted transaction: the closed message-level theorem

The transaction's real message (`TxTop.msg0tx`: `prepareMessage` over the pre-state `worldTx` under
EIP-2929 pre-warming, the EOA `E` calling the dispatcher attacker `A'`, type-2, zero fees, zero
value, 30,000,000 gas) is processed by Jaune's `processMessage` to a settled machine whose
storage shows the pool's ledger corrupted: `totalSupply = 1800 < 1906 = balanceOf[A']`.  Nothing
about the outcome is assumed: the deep reentrancy chain (`A' -> P.remove_liquidity -> impl ->
A' (callback) -> P.add_liquidity -> impl`, five frames and the token's) is discharged frame by
frame by `Tx.frame1_child` and plugged into `Tx.tx_message_of_child`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-- **V- at the transaction's message level (Prague): the closed theorem.**  The message
`prepareMessage` builds for the transaction succeeds under `processMessage`, with no error and
the EELS gas and empty output, and its settled machine's storage has
`totalSupply = 1800 < 1906 = balanceOf[A']` in the pool `P`: the reentrant `add_liquidity` inside
`remove_liquidity` broke the LP ledger. -/
theorem vminus_tx_message :
    prepareMessage benv0 tenv0 tx0 = .ok msg0tx ∧ msg0tx.caller = eAddress ∧
      msg0tx.currentTarget = a2Address ∧ msg0tx.benv.stat.fork = .prague ∧
      ∃ post : Devm, Nonempty (Exec e0tx.pc e0tx.sta e0tx.dyna (.ok post)) ∧
        processMessage msg0tx = .ok post ∧ post.error = none ∧ post.gasLeft = gas0out ∧
        post.output = [] ∧ post.refundCounter = refund0 ∧
        post.accountsToDelete = .emptyWithCapacity ∧
        (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
        (storOf post.state proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
        (storOf post.state proxyAddress (26 : Nat).toB256).toNat <
          (storOf post.state proxyAddress balanceOfA2Slot.toB256).toNat := by
  obtain ⟨d1, ck, ca, cs, cc, hg, ho, he, hok, ha, h26, hA, hr, hd⟩ := frame1_child
  obtain ⟨post, hx, hpm, herr, hgas, hout, hrf, hatd, hst⟩ :=
    tx_message_of_child d1 ck ca cs cc hg ho he hr hd hok ha
  have hf := msg0tx_facts
  simp only [Prod.mk.injEq] at hf
  obtain ⟨hcaller, htarget, -, -, -, -, hfork⟩ := hf
  have h26' : (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 := by
    rw [hst]; exact h26
  have hA' : (storOf post.state proxyAddress balanceOfA2Slot.toB256).toNat = 1906 := by
    rw [hst]; exact hA
  exact ⟨msg0tx_eq, hcaller, htarget, hfork, post, hx, hpm, herr, hgas, hout, hrf, hatd, h26', hA',
    by rw [h26', hA']; decide⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
