import Blanc.Lift.BuilderRequest.Surplus
import Blanc.Lift.BuilderRequest.Flood
import Blanc.Lift.BuilderRequest.Deposit.Delivery
import Blanc.Lift.BuilderRequest.Deposit.Transaction

/-!
# Deposit properties: surplus, the excess in naturals, inhibited frames

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`; the bytes and `sys-asm` `83f9801`.

Anything a depositor pays above the credit and the fee stays with the contract: the record carries the declared amount, whatever the value. Nothing here says the design should keep it, or that the consensus layer ignores it.
-/

namespace Blanc.Lift.BuilderRequest.Deposit

open Jaune
open RequestSystem
open Delivery
open Creation (address)

/-! ## Surplus -/

/-- **The certificate has no node that moves ether**: no call-family or `CREATE` instruction and no `SELFDESTRUCT` terminal, over every entry of its program. -/
theorem cert_moves_no_value : BalSilentSet cert.prog (List.range cert.prog.length) = true := by decide +kernel

/-- **No successful frame at the code changes a balance**, for any caller, SYSTEM included, at any depth, on any fork. The value a message carries moves before the frame (`message_ok`, `transaction_ok`). -/
theorem frame_keeps_balances {sevm : Sevm} {pre post : Devm} (hcode : sevm.code = code)
    (exec : Exec 0 sevm pre (.ok post)) : post.getBal = pre.getBal :=
  BuilderRequest.frame_keeps_balances cert_check userPath.noExec cert_moves_no_value (by decide +kernel) hcode exec

/-- **The record does not read the value.** Two frames with the same calldata make the same record, whatever value each carried. -/
theorem recordOf_value_free {s s' : Sevm} (hd : s.data = s'.data) (h : s.data.length = 184) (h' : s'.data.length = 184) :
    recordOf s h = recordOf s' h' := by
  simp only [recordOf, hd]

/-- **A submission's storage does not read the value.** -/
theorem submittedStorage_value_free {s s' : Sevm} (hd : s.data = s'.data) (σ : Stor) :
    submittedStorage s σ = submittedStorage s' σ := by
  simp only [submittedStorage, Sevm.dataWord, hd]

/-- **What is credited is what is declared.** On 184 bytes of calldata, the wei the guards count, `creditOf`, is the record's 8 amount bytes, as gwei, times `10 ^ 9`: a function of the calldata alone. Value above the
credit and the fee is admitted (`Admits` asks only `≤`) and appears nowhere in the record. -/
theorem credit_is_declared (s : Sevm) (h : s.data.length = 184) :
    (amountGwei s).toBytes = List.replicate 24 0 ++ (recordOf s h).amount ∧
      (amountGwei s).toNat * 10 ^ 9 = creditOf s.data :=
  ⟨amountGwei_toBytes s h, rfl⟩

/-- **Surplus is locked.** The premises of `transaction_ok` with any value the guards admit, and the coinbase not the contract: the balance rises by the whole value, the storage is the submission's, and that storage
reads the calldata and not the value (`submittedStorage_value_free`). The code cannot pay it out (`frame_keeps_balances`). -/
theorem surplus_locked {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat} {E t : Adr} {chainId : UInt64}
    {prio maxFee i f n : Nat} {out : B256} (d : DirectTx benv bout tx E t chainId prio maxFee i f)
    (installed : benv.state.getCode t = code) (hprecomp : ¬ amsterdamRules.isPrecomp t) (hnew : t ∉ benv.createdAccounts)
    (caller : E ≠ systemAddress) (value : tx.value.toB256 ≠ 0) (hlen : tx.data.length = 184)
    (hgas : i + submissions.regularBound n + submissions.stateBound + gCallStipend < tx.gas)
    (off : (benv.state.getStor t).get 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storageExcess 8 (benv.state.getStor t)) 17 1 17 0 n out)
    (admit : Admits tx.data tx.value.toB256 (out / (17 : B256)))
    (noAlias : ((benv.state.getStor t).get 3).toNat < 2 ^ 253) (hcb : benv.stat.coinbase ≠ t) :
    ∃ (s : Sevm) (st : State) (bout' : BlockOutput), s.data = tx.data ∧
      processTransaction benv bout tx index = .ok (st, bout') ∧
      (st.get t).bal = (benv.state.get t).bal + tx.value.toB256 ∧
      (st.get t).stor = submittedStorage s (benv.state.getStor t) := by
  obtain ⟨entry, st, bout', hproc, hbal, hstor⟩ := submissions.transaction_balance (index := index) d installed hprecomp hnew
    caller value hlen hgas off wordRun admit noAlias hcb
  exact ⟨_, st, bout', rfl, hproc, hbal, hstor⟩

/-! ## The excess in naturals -/

/-- **The excess a system call stores, in naturals.** On storage representing a queue, the checked empty-calldata call stores in slot 0: on the inhibitor, 0 whatever the count; off it, with no word wrap in `excess + count`,
`max(0, excess + count - 8)`, natural subtraction being that `max`. `system_call_fifo` states the same through `excessNext`, a word function. -/
theorem system_call_excess {benv : Benv} (hfork : benv.stat.fork = .amsterdam)
    (installed : benv.state.getCode address = code) {st : QueueState Record}
    (rep : Represents 6 Record.word (storOf benv.state address) st) :
    ∃ post out, processCheckedSystemTransaction benv address [] = .ok (post, out) ∧
      (st.excess = 2 ^ 256 - 1 → (post.getStor address).get 0 = 0) ∧
      (st.excess ≠ 2 ^ 256 - 1 → st.excess + st.count < 2 ^ 256 →
        ((post.getStor address).get 0).toNat = st.excess + st.count - 8) := by
  obtain ⟨post, out, hcall, -, -, hrep⟩ := system_call_fifo hfork installed rep
  have h0 : (post.getStor address).get 0 = (drainedState 64 8 st).excess.toB256 := hrep.excess
  obtain ⟨h1, h2⟩ := drained_excess_cases 64 8 st
  refine ⟨post, out, hcall, fun hmax => ?_, fun hne hsum => ?_⟩
  · rw [h0, h1 hmax]
    rfl
  · rw [h0, B256.toNat_toB256_of_lt hrep.excess_lt, h2 hne hsum]
    rfl

/-- **The excess over a sequence, in naturals.** `excess_dynamics`' update: from the deployed storage, with fewer than `2 ^ 256` submissions before it, an empty-calldata call after frames `xs` stores 0 on the inhibitor, and
`max(0, excess + count - 8)` off it. -/
theorem excess_natural {xs : List Frame} {f : Frame} (hrange : (Delivery.submissions xs).length < 2 ^ 256) (call : f.event = .system false) :
    (queueAfter deployedQueue (xs ++ [f])).excess =
      if (queueAfter deployedQueue xs).excess = 2 ^ 256 - 1 then 0
      else (queueAfter deployedQueue xs).excess + (queueAfter deployedQueue xs).count - 8 :=
  excess_update (by decide) (by
    show load deployedQueue + _ < _
    rw [show load deployedQueue = 0 from rfl, Nat.zero_add]
    exact hrange) call

/-! ## `noAlias`, from a budget -/

/-- **`transaction_ok`'s `noAlias`, from a budget.** After a chain from the deployed storage paying at most `2 ^ 256` wei, the tail in slot 3 is below `2 ^ 253`: each submission carries at least 1 ETH. -/
theorem tail_lt_of_budget {frames : List Frame} {t : Stor} (chain : Chain Stor.empty frames t) (hb : paid frames ≤ 2 ^ 256) :
    (t.get 3).toNat < 2 ^ 253 := by
  have hd := (delivery_of_budget chain hb).1
  have htl := queueAfter_tail_le deployedQueue frames
  have hn := ether_le_paid frames
  have h3 : t.get 3 = (queueAfter deployedQueue frames).tail.toB256 := hd.tail
  rw [h3, B256.toNat_toB256_of_lt hd.tail_lt]
  have ht0 : deployedQueue.tail = 0 := rfl
  simp only [oneEther] at hn
  omega

/-! ## Inhibited frames -/

variable {sevm : Sevm} {pre post : Devm}

/-- **Deposit rejection.** While slot 0 holds the inhibitor, every execution of the deposit code at a non-system caller from an empty stack ends in failure, under covered forks, for any calldata, value and memory. Under Amsterdam
`frameReverts_inhibited` states the positive `REVERT`. -/
theorem exec_user_inhibited_fails {outcome : Execution} (hcode : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork) (stack : pre.stack = []) (caller : sevm.caller ≠ systemAddress)
    (inhibited : pre.getStorVal sevm.currentTarget 0 = B256.max) (exec : Exec 0 sevm pre outcome) :
    ∃ failure, outcome = .error failure := by
  cases outcome with
  | ok post =>
    exact (UserPath.exec_inhibited_no_ok (k := userPath) (coveredSteps_valid fork) hcode stack caller inhibited exec).elim
  | error failure => exact ⟨failure, rfl⟩

end Blanc.Lift.BuilderRequest.Deposit
