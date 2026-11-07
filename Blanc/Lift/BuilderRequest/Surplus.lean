import Blanc.Lift.BuilderRequest.Transaction
import Blanc.Lift.BalSilent
import Blanc.Lift.BuilderRequest.Delivery

/-!
# Value goes in and stays in, and the excess in naturals

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

A direct submission raises the contract's balance by its whole value (`Submissions.transaction_balance`). Nothing a frame at the code can do moves ether: its certificate has no call-family or
`CREATE` node and no `SELFDESTRUCT` terminal (`BalSilentSet`), so a successful frame changes no balance, whatever the caller, depth or fork (`frame_keeps_balances`). A failed frame is rolled back.
So surplus stays with the contract, and no path of these bytes pays it out. What a frame's caller does around it is the caller's: this does not say the balance can never change, since `SELFDESTRUCT`
elsewhere and withdrawals can only add to it.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune ExecutionTrace
open RequestSystem

/-- **No successful frame at certified code with no ether-moving node changes a balance**, for any caller, depth and fork: the certificate's jump closure `S` holds only
balance-silent trees. The lift holds on any fork, since no node is call-family. -/
theorem frame_keeps_balances {code : ByteArray} {c : Cert} {S : List Nat} (hc : Cert.check code c = true)
    (hno : ProgNoExec c.prog) (closed : BalSilentSet c.prog S = true) (root : 0 ∈ S) {sevm : Sevm} {pre post : Devm}
    (hcode : sevm.code = code) (exec : Exec 0 sevm pre (.ok post)) : post.getBal = pre.getBal := by
  obtain ⟨f, hf, run⟩ := lift_sound_noExec hc hcode hno exec
  have hat := List.all_eq_true.mp closed 0 root
  rw [hf] at hat
  simp only [Bool.and_eq_true] at hat
  exact SFunc.RunP.getBal_of_balSilent (fun h => h) closed hat.1 hat.2 run

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr} {chainId : UInt64} {prio maxFee i f : Nat}

/-- The message a direct transaction prepares. -/
local notation "TM" => txMsg benv tx index E t (twoPrice benv.stat.baseFeePerGas prio maxFee) i

/-- **A direct submission raises the contract's balance by its whole value.** The premises of `transaction_ok`, and the coinbase is not the contract. After `processTransaction` the balance is up by exactly
`tx.value`, surplus included, and the storage is the submission's. The value is not read by `c.storage`'s record, which is the contract's own statement. -/
theorem Submissions.transaction_balance (c : Submissions) {n : Nat} {out : B256}
    (d : DirectTx benv bout tx E t chainId prio maxFee i f) (installed : benv.state.getCode t = c.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp t) (hnew : t ∉ benv.createdAccounts) (caller : E ≠ systemAddress)
    (value : tx.value.toB256 ≠ 0) (hlen : tx.data.length = c.len)
    (hgas : i + c.regularBound n + c.stateBound + gCallStipend < tx.gas)
    (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess c.target (benv.state.getStor t)) 17 1 17 0 n out)
    (admit : c.Admit tx.data tx.value.toB256 (out / (17 : B256)))
    (noAlias : ((benv.state.getStor t).get 3).toNat < 2 ^ 253) (hcb : benv.stat.coinbase ≠ t) :
    ∃ (entry : Benv) (st : State) (bout' : BlockOutput),
      processTransaction benv bout tx index = .ok (st, bout') ∧
      (st.get t).bal = (benv.state.get t).bal + tx.value.toB256 ∧
      (st.get t).stor = c.storage (userSevm TM c.code entry) (benv.state.getStor t) := by
  obtain ⟨entry, hentry, hstate, used, -, -, -, bout', hproc, -⟩ :=
    c.transaction_ok (index := index) d installed hprecomp hnew caller value hlen hgas off wordRun admit noAlias
  have hne := c.sender_ne d installed
  generalize hst : txFinal _ E benv.stat.coinbase _ _ = st at hproc
  have hget : st.get t = (c.world (userSevm TM c.code entry) entry.state).get t := by
    rw [← hst, txFinal, State.addBal, State.setBal, State.setAccount_get_ne _ hcb, State.addBal, State.setBal,
      State.setAccount_get_ne _ hne]
  refine ⟨entry, st, bout', hproc, ?_, ?_⟩
  · rw [hget, c.world_bal, hstate, State.addBal]
    have h1 := setBal_bal_self ((TM).benv.state.setBal E ((TM).benv.state.bal E - tx.value.toB256)) t
      (State.bal ((TM).benv.state.setBal E ((TM).benv.state.bal E - tx.value.toB256)) t + tx.value.toB256)
    refine h1.trans ?_
    have h2 : State.bal ((TM).benv.state.setBal E ((TM).benv.state.bal E - tx.value.toB256)) t = (benv.state.get t).bal := by
      show ((((TM).benv.state.setBal E _).get t)).bal = _
      rw [State.setBal, State.setAccount_get_ne _ hne]
      show ((txDebit benv.state E (tx.gas * twoPrice benv.stat.baseFeePerGas prio maxFee)).get t).bal = _
      rw [txDebit_get_ne hne]
    rw [h2]
  · rw [hget]
    have h1 : (c.world (userSevm TM c.code entry) entry.state).getStor t =
        c.storage (userSevm TM c.code entry) (entry.state.getStor t) :=
      c.world_stor (userSevm TM c.code entry) entry.state
    have h2 : entry.state.getStor t = benv.state.getStor t := by
      have hs := entry_stor (M := TM) (code := c.code) (by
        show (((txDebit benv.state E (tx.gas * twoPrice benv.stat.baseFeePerGas prio maxFee)).get t).code) = _
        rw [txDebit_get_ne hne]
        exact installed) c.nonempty hentry
      exact hs.trans (c.msg_stor d installed)
    rw [h2] at h1
    exact h1

/-! ## The excess in naturals -/

/-- **The excess a call stores, in naturals.** Off the inhibitor with no word wrap in `excess + count`, an empty-calldata call stores `max(0, excess + count - target)`, natural subtraction being that `max`. On
the inhibitor it stores 0, whatever the count. -/
theorem drained_excess_cases {Record : Type} (cap : Nat) (target : B256) (st : QueueState Record) :
    (st.excess = 2 ^ 256 - 1 → (drainedState cap target st).excess = 0) ∧
      (st.excess ≠ 2 ^ 256 - 1 → st.excess + st.count < 2 ^ 256 →
        (drainedState cap target st).excess = st.excess + st.count - target.toNat) := by
  refine ⟨fun hmax => ?_, fun hne hsum => Delivery.drained_excess_natural cap target st hsum hne⟩
  rw [Delivery.drainedState_excess, hmax, Delivery.inhibitor_toB256, excessNext_inhibitor]
  rfl

end Blanc.Lift.BuilderRequest
