import Blanc.ExecutionKeptValue
import Blanc.Lift.BuilderRequest.Surplus
import Blanc.Lift.BuilderRequest.Balances
import Blanc.Lift.BuilderRequest.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.ChainLink
import Blanc.Lift.BuilderRequest.Exit.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.Properties
import Blanc.Lift.BuilderRequest.Exit.Properties

/-!
# The builder contracts' kept value (O37 sizing draft)

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

**Status.** Sizing draft written without Lean elaboration under the run's
no-elaboration constraint. Every `sorry` carries a `-- DRAFT:` comment giving
the leaf's route and an estimated line count from a comparable existing proof
that was actually read. The master compiles this file and clears them.

**What this is.** The contract-level half of O37, generic over
`Delivery.Contract`: the at-code frame law discharges
`Exec.kept_bal_neverFalls`'s `at_code` premise, and the two history headlines
state O37 over kept histories: the balance never falls, and it covers the
committed values (`ChainLink.History.paid`, the kept frames' carried values in
wei: each submission's value is its deposit plus its fee). Stated as at least,
never equality: `SELFDESTRUCT` elsewhere and withdrawals can only add. The
deposit and exit instances supply only their certificate triple; everything
else is shared.

**Reuse.** `frame_keeps_balances` (Surplus.lean, W18, merged),
`system_calls_keep_balances` (Balances.lean), `KeptHistory` and its `chain`,
`caller_ne`, `entry_in` folds, `ChainLink.history_chain`, `History.paid`,
`History.kept`, `Deposit.contract`, `Exit.contract`, `Deposit.linked`,
`Exit.linked` are reused, not redefined. At the green boundary the generic
section stays in this family module and only genuinely generic leaves hoist to
`Blanc/ExecutionKeptValue.lean`; the two instances are contract-local.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune ExecutionTrace ChainLink
open Delivery

variable {c : Contract}

/-- The at-code frame law O37 needs: a committed frame at the contract's code
keeps every balance. -/
abbrev AtCodeKeeps (c : Contract) : Prop :=
  ∀ {sevm : Sevm} {pre post : Devm}, sevm.code = c.code →
    Exec 0 sevm pre (.ok post) → post.getBal = pre.getBal

/-- **The generic run corollary.** With the at-code law, one kept run of a frame not at the
contract, from a world whose balances sum below `2 ^ 256`, never lowers the contract's balance
and covers its kept values. The foreign leaves live in `Blanc/ExecutionKeptValue.lean`; this is
direct application. -/
theorem kept_run_value {C : ByteArray} {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (committed : Execution.commits out = true) (target : sevm.currentTarget ≠ c.address)
    (code : pre.getCode c.address = C)
    (nonempty : C.toList ≠ []) (nondelegating : ¬ isValidDelegation C)
    (law : AtCodeKeeps c) (hC : C = c.code) (sums : SumNof pre.state.bal) :
    (pre.getBal c.address).toNat ≤
      ((Execution.committedPost out committed).getBal c.address).toNat ∧
    (pre.getBal c.address).toNat + Exec.keptPaid c.address run ≤
      ((Execution.committedPost out committed).getBal c.address).toNat := by
  -- `law` is about `c.code` while the folds' `at_code` is about `C`: `hC`
  -- links them. The folds take `at_code` at `pc = 0` only, matching `law`.
  have at_code : ∀ {s : Sevm} {d e : Devm}, s.currentTarget = c.address →
      s.code = C → Exec 0 s d (.ok e) →
      (e.getBal c.address).toNat = (d.getBal c.address).toNat := by
    intro s d e _ hcode exec
    have hcode' : s.code = c.code := hC ▸ hcode
    have h := law hcode' exec
    exact congrArg B256.toNat (congrFun h c.address)
  exact ⟨Exec.kept_bal_neverFalls run committed target code nonempty
    nondelegating sums at_code,
    Exec.kept_bal_ge_keptPaid run committed target code nonempty
    nondelegating sums at_code⟩

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock}

/-- **Never falls across a kept history.** From installed code, with the
world-sum bound, no sender, authority or creation at the account, and no kept
caller at it, the contract's balance at the end covers its balance at the
start. The start balance is a pinned read, not a universal. -/
theorem history_value_neverFalls (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code)
    (runnable : c.code.toList ≠ [] ∧ ¬ isValidDelegation c.code)
    (law : AtCodeKeeps c)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (senders : History.NoSender c.address blocks)
    (authorities : History.NoAuthority c.address blocks)
    (creates : History.NoCreate c.address blocks)
    (callers : ∀ b ∈ blocks, ∀ f ∈ b.keptAt c.address, f.sevm.caller ≠ c.address) :
    ((start.state.get c.address).bal).toNat ≤
      ((stop.state.get c.address).bal).toNat := by
  -- DRAFT: induction on `h`, mirroring `KeptHistory.chain`
  -- (ExecutionKeptChain.lean:1967, ~15 lines read) and `Mapped.ofHistory`
  -- (ChainLink.lean:599, ~25 lines read). The per-block obligation is
  -- message-level balance mono: gas debits the sender (`senders`), fee credit
  -- and withdrawals only add, system calls keep balances by
  -- `system_calls_keep_balances` (Balances.lean, 27 lines read), user frames
  -- by `law`, nested kept frames by `kept_run_value`. Code across the history
  -- by `(h.chain _ _).2`. Estimated 100-200 lines: the least-known part of
  -- this route (message/transaction layers unread); attack second.
  sorry

/-- **At least the committed deposits plus fees.** As above, and the end
balance additionally covers every kept frame's carried value. Each
submission's carried value is its deposit plus its quoted fee
(`Contract.paid`); fee reads and system calls carry no committed value away.
Stated as at least, never equality. -/
theorem history_value_ge_paid (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code)
    (runnable : c.code.toList ≠ [] ∧ ¬ isValidDelegation c.code)
    (law : AtCodeKeeps c)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (senders : History.NoSender c.address blocks)
    (authorities : History.NoAuthority c.address blocks)
    (creates : History.NoCreate c.address blocks)
    (callers : ∀ b ∈ blocks, ∀ f ∈ b.keptAt c.address, f.sevm.caller ≠ c.address) :
    ((start.state.get c.address).bal).toNat + History.paid c.address blocks ≤
      ((stop.state.get c.address).bal).toNat := by
  -- DRAFT: same induction as `history_value_neverFalls`; the per-block
  -- obligation additionally telescopes the block's kept values via the
  -- entry-credit clause (`Submissions.transaction_balance`,
  -- Surplus.lean:39, ~40 lines read, for direct submissions; the internal-call
  -- entry twin is unwritten). Needs no `Delivery.Chain`: the sum is over kept
  -- frames, and `History.paid` already is that sum. Estimated 60-120 lines on
  -- top of the never-falls induction.
  sorry

/-! ## Instances -/

/-- **The deposit contract keeps every balance at its code.** From its lift
certificate's jump closure holding only balance-silent trees. -/
theorem Deposit.atCodeKeeps : AtCodeKeeps Deposit.contract := by
  intro sevm pre post hcode exec
  exact Deposit.frame_keeps_balances hcode exec

/-- **The exit contract keeps every balance at its code.** From its lift
certificate's jump closure holding only balance-silent trees. -/
theorem Exit.atCodeKeeps : AtCodeKeeps Exit.contract := by
  intro sevm pre post hcode exec
  exact Exit.frame_keeps_balances hcode exec

/-- **O37 at the deposit contract, over a kept history.** The balance never
falls and covers the committed deposits plus fees. -/
theorem Deposit.history_value (h : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode Deposit.contract.address = Deposit.contract.code)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (senders : History.NoSender Deposit.contract.address blocks)
    (authorities : History.NoAuthority Deposit.contract.address blocks)
    (creates : History.NoCreate Deposit.contract.address blocks)
    (callers : ∀ b ∈ blocks, ∀ f ∈ b.keptAt Deposit.contract.address,
      f.sevm.caller ≠ Deposit.contract.address) :
    ((start.state.get Deposit.contract.address).bal).toNat ≤
      ((stop.state.get Deposit.contract.address).bal).toNat ∧
    ((start.state.get Deposit.contract.address).bal).toNat +
        History.paid Deposit.contract.address blocks ≤
      ((stop.state.get Deposit.contract.address).bal).toNat :=
  ⟨history_value_neverFalls h installed Deposit.linked.runnable Deposit.atCodeKeeps
      sums senders authorities creates callers,
    history_value_ge_paid h installed Deposit.linked.runnable Deposit.atCodeKeeps
      sums senders authorities creates callers⟩

/-- **O37 at the exit contract, over a kept history.** The balance never falls
and covers the committed values. -/
theorem Exit.history_value (h : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode Exit.contract.address = Exit.contract.code)
    (sums : ∀ {q : Nat} {s : Sevm} {d : Devm} {o : Execution},
      Exec q s d o → SumNof d.state.bal)
    (senders : History.NoSender Exit.contract.address blocks)
    (authorities : History.NoAuthority Exit.contract.address blocks)
    (creates : History.NoCreate Exit.contract.address blocks)
    (callers : ∀ b ∈ blocks, ∀ f ∈ b.keptAt Exit.contract.address,
      f.sevm.caller ≠ Exit.contract.address) :
    ((start.state.get Exit.contract.address).bal).toNat ≤
      ((stop.state.get Exit.contract.address).bal).toNat ∧
    ((start.state.get Exit.contract.address).bal).toNat +
        History.paid Exit.contract.address blocks ≤
      ((stop.state.get Exit.contract.address).bal).toNat :=
  ⟨history_value_neverFalls h installed Exit.linked.runnable Exit.atCodeKeeps
      sums senders authorities creates callers,
    history_value_ge_paid h installed Exit.linked.runnable Exit.atCodeKeeps
      sums senders authorities creates callers⟩

end Blanc.Lift.BuilderRequest
