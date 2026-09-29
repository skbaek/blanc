import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame1
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.OuterAt

/-!
# V- as an admitted transaction under every covered fork: the closed message-level theorem

The transaction's real message (`TxTopC.msgC`: `prepareMessage` over the pre-state `worldTx` under
EIP-2929 pre-warming, the EOA `E` calling the dispatcher attacker `A'`, type-2, zero fees, zero
value, an access list naming every precompile and `A'`, 16,043,200 gas: below the EIP-7825 cap of 2^24 = 16,777,216
that Osaka and the BPO forks enforce) is processed by Jaune's `processMessage` under every covered
fork to a settled machine whose storage shows the pool's ledger corrupted: `totalSupply = 1800 <
1906 = balanceOf[A']`.  Nothing about the outcome is assumed: the deep reentrancy chain (`A' ->
P.remove_liquidity -> impl -> A' (callback) -> P.add_liquidity -> impl`, five frames and the
token's) is discharged frame by frame by `TxC.frame1C_child_at` and plugged into
`TxC.txC_message_of_child_at`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx (refund0)

variable {g : Fork}

/-- The prepared message under any covered fork is the Prague message with its fork changed:
the transaction's access list warms every precompile of every covered fork, so the preparation
inserts nothing (`TransactionFork.prepareMessage_withFork`). -/
theorem prepareMessage_at (hg : CoveredFork g) :
    prepareMessage (benv0.withFork g) tenv0C txC = .ok (msgC.withFork g) := by
  have h := TransactionFork.prepareMessage_withFork (benv := benv0) (tenv := tenv0C) (tx := txC)
    (target := a2Address) (g := g) rfl
    (accessListC_contains (by
      show ∀ a ∈ praguePrecompiles ++ [eAddress, a2Address],
        a ∈ eAddress :: accessListC.map Prod.fst
      decide +kernel))
    (accessListC_contains (hg.cases (motive := fun g => ∀ a ∈ (Fork.ruleSet g).precompiles ++
        [eAddress, a2Address], a ∈ eAddress :: accessListC.map Prod.fst)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)))
  rw [h, msgC_eq]; rfl

/-- **V- at the transaction's message level, under every covered fork (Prague, Osaka, BPO1,
BPO2): the closed theorem.**  The message `prepareMessage` builds for the transaction (16,043,200
gas, below EIP-7825's 2^24 cap) succeeds under `processMessage`, with no error and the EELS gas
and empty output, and its settled machine's storage has `totalSupply = 1800 < 1906 =
balanceOf[A']` in the pool `P`: the reentrant `add_liquidity` inside `remove_liquidity` broke the
LP ledger. -/
theorem vminus_txC_message (g : Fork) (hg : CoveredFork g) :
    prepareMessage (benv0.withFork g) tenv0C txC = .ok (msgC.withFork g) ∧
      (msgC.withFork g).caller = eAddress ∧ (msgC.withFork g).currentTarget = a2Address ∧
      (msgC.withFork g).benv.stat.fork = g ∧ txC.gas = 16043200 ∧ txC.gas < 2 ^ 24 ∧
      ∃ post : Devm,
        Nonempty (Exec (e0C.withFork g).pc (e0C.withFork g).sta (e0C.withFork g).dyna
          (.ok post)) ∧
        processMessage (msgC.withFork g) = .ok post ∧ post.error = none ∧
        post.gasLeft = gas0outC ∧ post.output = [] ∧ post.refundCounter = refund0 ∧
        post.accountsToDelete = .emptyWithCapacity ∧
        (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
        (storOf post.state proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
        (storOf post.state proxyAddress (26 : Nat).toB256).toNat <
          (storOf post.state proxyAddress balanceOfA2Slot.toB256).toNat := by
  obtain ⟨d1, ck, ca, cs, cc, hgas, ho, he, hok, ha, h26, hA, hr, hd⟩ := frame1C_child_at hg
  obtain ⟨post, hx, hpm, herr, hgasP, hout, hrf, hatd, hst⟩ :=
    txC_message_of_child_at hg d1 ck ca cs cc hgas ho he hr hd hok ha
  have hf := msgC_facts
  simp only [Prod.mk.injEq] at hf
  obtain ⟨hcaller, htarget, -, -, -, -, -, -⟩ := hf
  have h26' : (storOf post.state proxyAddress (26 : Nat).toB256).toNat = 1800 := by
    rw [hst]; exact h26
  have hA' : (storOf post.state proxyAddress balanceOfA2Slot.toB256).toNat = 1906 := by
    rw [hst]; exact hA
  exact ⟨prepareMessage_at hg, hcaller, htarget, rfl, rfl, by decide, post, hx, hpm, herr, hgasP,
    hout, hrf, hatd, h26', hA', by rw [h26', hA']; decide⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
