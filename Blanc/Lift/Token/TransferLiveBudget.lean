import Blanc.Lift.Token.Core

/-!
# Token interface facet: transfer liveness with a gas budget

`TransferLiveBudget` is `TransferLive` with success conditioned on a budget rather than on the
consumed cost plus the call stipend: a proxy forwards only 63/64 of its gas, so the consumed cost
does not suffice.  Every `TransferLive` is one (`TransferLive.toBudget`).  Contract-neutral.
-/

namespace Blanc.Lift.Token

open Jaune Blanc Blanc.ExecutionTrace

/-- **Facet: frame-level transfer liveness with a gas budget.**  As `TransferLive`, except that
success needs `budget ≤ G` (a proxy forwards only 63/64 of its gas, so the consumed `cost` does not
suffice), with `cost` still exact. -/
structure TransferLiveBudget (T : Adr) (B : Book) where
  WorldOk : State → Prop
  FrameOk : Sevm → State → Prop
  ledgerAt : State → B.Ledger
  cost : Sevm → Devm → Nat
  budget : Sevm → Devm → Nat
  cost_le : ∀ sevm pre, cost sevm pre ≤ budget sevm pre
  live : ∀ {sevm : Sevm} {pre : Devm} {G : Nat} {dst : Adr} {v : Nat},
    sevm.currentTarget = T → sevm.codeAddress = some T → sevm.code = pre.state.getCode T →
    FrameOk sevm pre.state → CoveredFork sevm.benvStat.fork →
    sevm.value = 0 → sevm.isStatic = false → pre.output = [] →
    WorldOk pre.state → B.op sevm = .transfer dst v → v ≤ B.bal (ledgerAt pre.state) sevm.caller →
    budget sevm pre ≤ G →
    ∃ post, Nonempty (Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) ∧ post.gasLeft + cost sevm pre = G ∧
      post.output = (Nat.toB256 1).toBytes ∧ WorldOk post.state ∧
      (dst ≠ sevm.caller → B.bal (ledgerAt post.state) sevm.caller + v =
        B.bal (ledgerAt pre.state) sevm.caller)

/-- Every `TransferLive` is budget-aware with `budget := cost + gCallStipend`. -/
def TransferLive.toBudget {T : Adr} {B : Book} (L : TransferLive T B) : TransferLiveBudget T B where
  WorldOk := L.WorldOk
  FrameOk := L.FrameOk
  ledgerAt := L.ledgerAt
  cost := L.cost
  budget sevm pre := L.cost sevm pre + gCallStipend
  cost_le _ _ := Nat.le_add_right _ _
  live target codeAddr code frame fork value static output world op afford budget :=
    L.live target codeAddr code frame fork value static output world op afford
      (Nat.le_trans (Nat.le_add_right _ _) budget) budget

end Blanc.Lift.Token
