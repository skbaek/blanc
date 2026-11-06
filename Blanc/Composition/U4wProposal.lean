import Blanc.Composition.Curve3PoolPublic
import Blanc.Composition.Curve3PoolPublicBridge
import Blanc.Lift.CurveCoins.PoolFreshAtCreation

/-! Compile check of the lemmas the proposed statement edits rely on. Not for commit. -/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Composition.Curve3PoolBlockAnchor

/-- `poolOld`: every moment is a transaction boundary. -/
theorem Moment.poolOld {d : Deployment} (m : Moment d) : pool ∉ m.benv.createdAccounts :=
  m.block.txSplit_notCreated m.cut pool

/-- `sysAvoidsPool`, as the old field read it. -/
theorem Assumes.sysAvoidsPool {d : Deployment} {future : BlockChain}
    {h : MainnetHistory d.minter.post future} (a : Assumes d h) :
    ∀ r ∈ (d.sinceC3Block h).systemRawFrames, r.sevm.currentTarget ≠ pool :=
  d.system_ne a.system AnchoredDeployment.pool_not_system

/-- The coins' `SystemConfined`. -/
theorem Assumes.sincePool_confined {d : Deployment} {future : BlockChain}
    {h : MainnetHistory d.minter.post future} (a : Assumes d h) : (d.sincePool h).SystemConfined :=
  AnchoredDeployment.sincePool_confined d a.system

/-- `quoted`, at the transaction: the spend converges only if the quote does. -/
theorem swapOut_of_spent {w : State} {data : Bytes} {E : Adr} {t : Nat} {i j : Fin 3} {dx spent : Nat}
    (h : swapSpent w data E t i j dx = some spent) : swapOut w t i j dx = some (quote w t i j dx) := by
  unfold quote
  cases hq : swapOut w t i j dx with
  | some v => rfl
  | none =>
    exfalso
    simp only [swapSpent, hq, Option.bind_eq_bind, Option.bind_none, Option.bind_fun_none,
      reduceCtorEq] at h

/-- `quoted`, at the message: the admin's cut exists only if the quote does. -/
theorem swapOut_of_admin {w : State} {t : Nat} {i j : Fin 3} {dx admin : Nat}
    (h : swapAdmin w t i j dx = some admin) : swapOut w t i j dx = some (quote w t i j dx) := by
  unfold quote swapOut
  unfold swapAdmin at h
  cases hq : swapQuote w t i j dx with
  | some q => rfl
  | none =>
    rw [hq] at h
    cases h

end Blanc.Composition.Curve3PoolPublic
