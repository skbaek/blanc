import Blanc.ExecutionKeptValue
import Blanc.Lift.BuilderRequest.Surplus
import Blanc.Lift.BuilderRequest.Balances
import Blanc.Lift.BuilderRequest.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.ChainLink
import Blanc.Lift.BuilderRequest.Exit.ChainLink
import Blanc.Lift.BuilderRequest.Deposit.Properties
import Blanc.Lift.BuilderRequest.Exit.Properties

/-!
# The builder contracts' kept value (O37)

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

**What this is.** O37 at the two builder contracts, generic over `Delivery.Contract`. Across a kept
history the contract's balance never falls (`history_value_neverFalls`) and covers its start plus the
committed values (`history_value_ge_paid`: `ChainLink.History.paid`, each submission's carried value,
its deposit plus its fee). Stated as at least, never equality: tips, withdrawals and `SELFDESTRUCT`
elsewhere can only add. Both are corollaries of the shared fold `KeptHistory.bal_covers`
(`Blanc/ExecutionKeptValue.lean`) over kept frames; `kept_run_value` is the same over one run.

**Premises.** `Linked` (the contract's code runs, and no kept fork runs a precompile at its address),
the code installed at the start (a pinned read), the at-code law (`AtCodeKeeps`, discharged per
contract from its lift certificate by `frame_keeps_balances`), no transaction sent from the contract
(`History.NoSender`), and two virtual certainties no pinned read answers today: the world-sum bound
at every root message (`HistoryRootsFit`) and no wrap at a credit to the contract
(`HistoryCreditsFit`: the tips and withdrawal credits).
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

variable {cfg : ChainConfig} {start stop : BlockChain} {blocks : List KeptBlock} {ty : UInt8}

/-- **At least the committed deposits plus fees.** From the contract's code installed at the start,
with the at-code law, no transaction sent from the contract, the world-sum bound per root message,
and no wrap at a credit to the contract: its balance at the end covers its balance at the start plus
every kept frame's carried value (`History.paid`). Each submission's carried value is its deposit plus
its quoted fee; fee reads and system calls carry none. Stated as at least, never equality: tips,
withdrawals and `SELFDESTRUCT` elsewhere can only add. The start balance is a pinned read. -/
theorem history_value_ge_paid (L : Linked c ty) (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code) (law : AtCodeKeeps c)
    (senders : History.NoSender c.address blocks) (fits : HistoryRootsFit blocks)
    (credits : HistoryCreditsFit c.address blocks) :
    ((start.state.get c.address).bal).toNat + History.paid c.address blocks ≤
      ((stop.state.get c.address).bal).toNat := by
  have V : KeptValueAt c.address c.code := ⟨L.runnable.1, L.runnable.2, fun {s d e} _ hcode exec =>
    congrArg B256.toNat (congrFun (law hcode exec) c.address)⟩
  exact KeptHistory.bal_covers h V code L.placed.precompile senders fits credits

/-- **Never falls across a kept history.** Under the premises of `history_value_ge_paid`, the
contract's balance at the end covers its balance at the start. -/
theorem history_value_neverFalls (L : Linked c ty) (h : KeptHistory cfg start blocks stop)
    (code : start.state.getCode c.address = c.code) (law : AtCodeKeeps c)
    (senders : History.NoSender c.address blocks) (fits : HistoryRootsFit blocks)
    (credits : HistoryCreditsFit c.address blocks) :
    ((start.state.get c.address).bal).toNat ≤ ((stop.state.get c.address).bal).toNat :=
  Nat.le_trans (Nat.le_add_right _ _) (history_value_ge_paid L h code law senders fits credits)

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
    (senders : History.NoSender Deposit.contract.address blocks) (fits : HistoryRootsFit blocks)
    (credits : HistoryCreditsFit Deposit.contract.address blocks) :
    ((start.state.get Deposit.contract.address).bal).toNat ≤
      ((stop.state.get Deposit.contract.address).bal).toNat ∧
    ((start.state.get Deposit.contract.address).bal).toNat +
        History.paid Deposit.contract.address blocks ≤
      ((stop.state.get Deposit.contract.address).bal).toNat :=
  ⟨history_value_neverFalls Deposit.linked h installed Deposit.atCodeKeeps senders fits credits,
    history_value_ge_paid Deposit.linked h installed Deposit.atCodeKeeps senders fits credits⟩

/-- **O37 at the exit contract, over a kept history.** The balance never falls
and covers the committed values. -/
theorem Exit.history_value (h : KeptHistory cfg start blocks stop)
    (installed : start.state.getCode Exit.contract.address = Exit.contract.code)
    (senders : History.NoSender Exit.contract.address blocks) (fits : HistoryRootsFit blocks)
    (credits : HistoryCreditsFit Exit.contract.address blocks) :
    ((start.state.get Exit.contract.address).bal).toNat ≤
      ((stop.state.get Exit.contract.address).bal).toNat ∧
    ((start.state.get Exit.contract.address).bal).toNat +
        History.paid Exit.contract.address blocks ≤
      ((stop.state.get Exit.contract.address).bal).toNat :=
  ⟨history_value_neverFalls Exit.linked h installed Exit.atCodeKeeps senders fits credits,
    history_value_ge_paid Exit.linked h installed Exit.atCodeKeeps senders fits credits⟩

end Blanc.Lift.BuilderRequest
