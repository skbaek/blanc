import Blanc.Lift.BeaconDeposit.HistSafe
import Blanc.Lift.BeaconDeposit.Body
import Blanc.Lift.BeaconDeposit.Lift
import Blanc.Lift.BeaconDeposit.SafeViews
import Blanc.Lift.BeaconDeposit.SafeDispatch
import Blanc.Lift.BeaconDeposit.SafeDecoder
import Blanc.Lift.BeaconDeposit.SafeGuards
import Blanc.Lift.BeaconDeposit.SafeEvent
import Blanc.Lift.BeaconDeposit.SafePubkeyRoot
import Blanc.Lift.BeaconDeposit.SafeSignatureRoot
import Blanc.Lift.BeaconDeposit.SafeNode
import Blanc.Lift.BeaconDeposit.SafeCount
import Blanc.Lift.BeaconDeposit.SafeInsertDead
import Blanc.Lift.BeaconDeposit.SafeInsertLive
import Blanc.Lift.SoundExtra
import Blanc.Lift.QuietExtra

/-!
# The deployed runtime refines the model (B3, safety): composed from its segments

Every successful frame execution of the deployed runtime either is a `deposit` whose effect is
the model's (`deposit_frame_refines`, first conjunct), or keeps every storage map and the log
list (second conjunct).  The route: `lift_sound`; the dispatcher (`safe_dispatch`); the three view
wrappers are quiet (`viewSet_quiet`, `SFunc.Run.world_of_quiet`); the `deposit` wrapper
(`safe_decoder`) and the body's inversion segments (`safe_guards` … `safe_countBump`); the
insertion loop by `SFunc.RunP.loop` over the two pass inversions (`safe_insertDead`,
`safe_insertLive`).  Each theorem here is the covered-fork corollary of its `HistSafe.lean`
form (`CoveredFork` gives `rules.stateGas = none`, `rules.bal = none`, the EIP-2929 access
schedule and net-metered `SSTORE`).
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## The views -/

theorem view_world {sevm : Sevm} (hfork : CoveredFork sevm.benvStat.fork) {k : Nat} {g : SFunc}
    {d : Devm} {o : Outcome} (hk : k ∈ viewSet) (hg : prog[k]? = some g)
    (run : SFunc.Run prog sevm d g o) :
    Devm.getStor (Outcome.devm o) = Devm.getStor d ∧ (Outcome.devm o).logs = d.logs :=
  view_worldH hfork.rules_stateGas_none hk hg run

/-! ## The insertion loop -/

/-- **The insertion loop, inverted**: every successful run from the loop head at height `0`
stores at a height `h` whose size bit is set and below which every bit is clear, and returns. -/
theorem safe_insert_loop {sevm : Sevm} {b₀ : Devm} {x : Nat} {node0 : B256}
    {br : Nat → B256} {stor1 : Stor}
    {x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ y₅ y₆ y₇ d : B256} {rest : List B256}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hsha : ShaReady sevm b₀) (hrest : rest.length ≤ 4) (hx : x < 2 ^ 256)
    (hstor1 : Devm.getStor b₀ sevm.currentTarget = stor1)
    (hbr : ∀ h < 32, stor1.get (solBranchSlot h) = br h)
    {M : Mem} {G : Nat} {o : Outcome}
    (hM : BodyMem M (1024 + 96 * 0) (Nat.toB256 (928 + 96 * 0)) [])
    (run : SFunc.Run prog sevm (St b₀ (Nat.toB256 0 :: Nat.toB256 (x / 2 ^ 0) ::
      insertNode Bytes.sha256 br 0 node0 ::
      x₁ :: x₂ :: x₃ :: x₄ :: y₁ :: y₂ :: y₃ :: y₄ :: y₅ :: y₆ :: y₇ :: d :: rest) M G)
      t_0f6e_c23 o) :
    ∃ h bf Mf Gf, o = .returned (St bf rest Mf Gf) ∧ h < 32 ∧ (∀ j < h, (x / 2 ^ j) % 2 = 0) ∧
      (x / 2 ^ h) % 2 = 1 ∧
      BaseRel (afterSstore sevm b₀ (solBranchSlot h) (insertNode Bytes.sha256 br h node0)) bf := by
  simpa only [afterSstoreH_of_eip2929 hfork.rules_access
    (congrArg SstoreRules.netMetering hfork.rules_sstore)] using
    safe_insert_loopH_of_rules hfork.rules_stateGas_none hfork.rules_bal_none hsha.toRules hrest hx
      hstor1 hbr hM run

/-! ## The `deposit` route -/

/-- The `deposit` wrapper's successful runs, from the dispatcher's hand-off. -/
theorem deposit_route {sevm : Sevm} {pre post : Devm} {history : List B256} {G1 : Nat}
    (hfork : CoveredFork sevm.benvStat.fork) (hcd : sevm.data.length < 2 ^ 256)
    (hsha : ShaReady sevm pre)
    (hinv : SolInv (Devm.getStor pre sevm.currentTarget) history)
    (run : SFunc.Run prog sevm (St pre [Sevm.selector sevm] mem0 G1) t_00a4_c32 (.halted post)) :
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
        post.logs = pre.logs ++ [BeaconDeposit.depositEventLog sevm.currentTarget ev] :=
  deposit_routeH_of_rules hfork.rules_stateGas_none hfork.rules_bal_none hcd hsha.toRules hinv run

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
