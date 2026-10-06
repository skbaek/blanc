import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallback

/-!
# V− P2, F2 and F0/F1: the frame statements between the callback and the message

The remaining P2-internal statements of the V4 freeze (§5.3, verbatim): `RemoveFacts` and
`RemoveFrame` (F2, `remove_liquidity`, with F3 by `CallbackFrame` and the token's `transfer`
child) and `RootFrame` (F0 with F1, over every `Checkpoint` world). Stated in their own module
so that `remove_frame : CallbackFrame → RemoveFrame` and `root_frame : RemoveFrame → RootFrame`
are proved against one fixed interface.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-- The `remove_liquidity` frame's own facts from its start configuration `c2` (static machine
`S`), with its callback (the `ViolationAt` sub-block (a) and (c) for F2). -/
def RemoveFacts (S : Sevm) (c2 : Cfg) (post2 : Devm) : Prop :=
  ∃ (c339 : Cfg) (e3 : Evm) (c3 : Cfg),
    wrun fsI S 339 c2 = .cont c339 ∧ Agree c339 ∧
    storOf c339.devm.state proxyAddr 2 = 1 ∧ storOf c339.devm.state proxyAddr 26 = 2000 ∧
    SpawnedBy S c339.devm .call e3 ∧
    e3.sta.currentTarget = attackerAddr ∧ e3.sta.code = AttackerR.code ∧ e3.sta.value = 100 ∧
    c3.devm = e3.dyna ∧ c3.f = AttackerR.t_0000_c0 ∧ c3.K = [] ∧ Agree c3 ∧
    ReentryFacts e3.sta c3 ∧
    storOf post2.state proxyAddr 26 = 1800 ∧ storOf post2.state proxyAddr lpSlotA = 1906 ∧
    storOf post2.state proxyAddr 2 = 0

/-- **P2, F2 (with F3 by `CallbackFrame` and the token's `transfer` child)**: the
`remove_liquidity` frame from its entry boundary `bRm0`. -/
def RemoveFrame : Prop :=
  ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    CoveredFork g → (∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2) →
    Agree (Boundary.cfgOfT bRm0 tS tA m w) →
    ∃ post : Devm,
      Nonempty (Exec 0 ((sRm.withOrig O).withFork g) (Boundary.cfgOfT bRm0 tS tA m w).devm
        (.ok post)) ∧
      post.gasLeft = gasRm ∧ post.output = outRm ∧ post.error = none ∧
      ChildAgree post keysRm adrsRm (storRm ++ tS) (acsRm ++ tA) ∧
      lookupS (Boundary.storOf1 bRm0) proxyAddr 2 = 0 ∧
      RemoveFacts ((sRm.withOrig O).withFork g) (Boundary.cfgOfT bRm0 tS tA m w) post

/-- **P2, F0 with F1 (with F2 by `RemoveFrame`)**: the message from its root entry, over every
`Checkpoint` world, under every covered fork. -/
def RootFrame : Prop :=
  ∀ g : Fork, CoveredFork g → ∀ W : State, Checkpoint W → ∃ post : Devm, ViolationAt g W post

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
