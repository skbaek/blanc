import Blanc.Lift.BeaconDeposit.HistSafe
import Blanc.Lift.BeaconDeposit.Body
import Blanc.Lift.BeaconDeposit.Lift
import Blanc.Lift.BeaconDeposit.SafeViews
import Blanc.Lift.BeaconDeposit.SafeDispatch
import Blanc.Lift.BeaconDeposit.SafeDecoder
import Blanc.Lift.BeaconDeposit.SafeGuards
import Blanc.Lift.BeaconDeposit.SafeEvent
import Blanc.Lift.WalkKitSupport

/-!
# The deployed runtime refines the model (B3, safety): composed from its segments

Every successful frame execution of the deployed runtime either is a `deposit` whose effect is
the model's (`deposit_frame_refines`, first conjunct), or keeps every storage map and the log
list (second conjunct).  It is the covered-fork corollary of its `HistSafe.lean` form
(`CoveredFork` gives `rules.stateGas = none`, `rules.bal = none`, the EIP-2929 access
schedule and net-metered `SSTORE`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## The frame -/

/-- **The deployed runtime refines the model (B3, safety).**  For every successful frame
execution of the deployed bytes from a frame start (empty stack and memory), on a covered fork,
with the precompile premises and the storage abstraction `SolInv` for a history:

* if the selector is `deposit`'s, the calldata is `DepositDecodable`, the model deposit on the
  arguments the deployed decoder reads returns `.ok (s', ev)`, the contract's new storage
  abstracts to `s'` and satisfies `SolInv` for the history extended by the model's node, it
  differs from the old one exactly at the count slot and one branch slot, every other account's
  storage is unchanged, and exactly the model's `DepositEvent` log is appended;
* otherwise every storage map and the log list are unchanged. -/
theorem deposit_frame_refines {sevm : Sevm} {pre post : Devm} {history : List B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hcd : sevm.data.length < 2 ^ 256)
    (hstack : pre.stack = []) (hmem : pre.memory = Mem.empty)
    (hsha : ShaReady sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (exc : Exec 0 sevm pre (.ok post)) :
    (Sevm.selector sevm = BeaconDeposit.depositSelector →
      DepositDecodable sevm ∧ ∃ s' ev,
        BeaconDeposit.deposit Bytes.sha256 (solAcc (Devm.getStor pre sevm.currentTarget))
          (argBytes sevm 0) (argBytes sevm 1) (argBytes sevm 2) (argRoot sevm)
          sevm.value.toNat = .ok (s', ev) ∧
        solAcc (Devm.getStor post sevm.currentTarget) = s' ∧
        SolInv (Devm.getStor post sevm.currentTarget)
          (history ++ [BeaconDeposit.depositDataNode Bytes.sha256 (argBytes sevm 0)
            (argBytes sevm 1) (argBytes sevm 2) ev.amount]) ∧
        (∃ h v, h < 32 ∧ Devm.getStor post sevm.currentTarget =
          ((Devm.getStor pre sevm.currentTarget).set solCountSlot (1 + bodyCount sevm pre)).set
            (solBranchSlot h) v) ∧
        (∀ a, a ≠ sevm.currentTarget → Devm.getStor post a = Devm.getStor pre a) ∧
        post.logs = pre.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev]) ∧
    (Sevm.selector sevm ≠ BeaconDeposit.depositSelector →
      (∀ a, Devm.getStor post a = Devm.getStor pre a) ∧ post.logs = pre.logs) :=
  deposit_frame_refinesH_of_rules hcode hfork.rules_stateGas_none hfork.rules_bal_none hcd hstack hmem
    hsha.toRules hinv exc

end Blanc.Lift.BeaconDeposit
