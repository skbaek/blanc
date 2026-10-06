import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolCallbackRun

/-!
# V− P2, F3 (with F4 as its child and F5 by `ReAddFrame`): the callback frame

`callback_frame : ReAddFrame → CallbackFrame`: from the callback entry boundary `bCb0`
(with free tails), the 32-step run to the `CALL`, the forwarder child (whose settled
machine comes from `ReAddFrame` via F5), and the resume to the halt with `gasCb`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

/-! ## P2-internal statements (frozen §5.3, verbatim) -/

/-- The re-entry as seen from the callback frame's start configuration `c3` (static machine
`S`): the callback's `CALL` (step 32), the clone's forwarder, its `DELEGATECALL` into F5, and
F5's facts (the `ViolationAt` sub-block). -/
def ReentryFacts (S : Sevm) (c3 : Cfg) : Prop :=
  ∃ (cA : Cfg) (e4 e4' e5 : Evm) (c5 cB : Cfg) (post5 : Devm),
    wrun fsA S 32 c3 = .cont cA ∧ Agree cA ∧ SpawnedBy S cA.devm .call e4 ∧
    e4.sta.currentTarget = proxyAddr ∧ e4.sta.code = fwdCode ∧ e4.sta.value = 100 ∧
    stepN 11 e4 = some e4' ∧ SpawnedBy e4'.sta e4'.dyna .delegatecall e5 ∧
    e5.sta.currentTarget = proxyAddr ∧ e5.sta.code = Vulnerable.code ∧ e5.sta.data = reAddCall ∧
    storOf e5.dyna.state proxyAddr 2 = 1 ∧ storOf e5.dyna.state proxyAddr 0 = 0 ∧
    Nonempty (Exec e5.pc e5.sta e5.dyna (.ok post5)) ∧ post5.error = none ∧
    c5.devm = e5.dyna ∧ c5.f = Vulnerable.t_0000_c0 ∧ c5.K = [] ∧ Agree c5 ∧
    wrun fsI e5.sta 2625 c5 = .cont cB ∧ Agree cB ∧ cB.f = Vulnerable.t_0370_c63 ∧
    storOf cB.devm.state proxyAddr 0 = 1 ∧ storOf cB.devm.state proxyAddr 2 = 1 ∧
    storOf post5.state proxyAddr 26 = 2106 ∧ storOf post5.state proxyAddr lpSlotA = 2106 ∧
    storOf post5.state proxyAddr 0 = 0 ∧ storOf post5.state proxyAddr 2 = 1

/-- **P2, F3 (with F4 as its child and F5 by `ReAddFrame`)**: the callback frame from its
entry boundary `bCb0`, as the certificate interpreter's run (what `childOk_of_start` takes at
F2's `CALL`): the run to the `CALL` (32 steps) and the resume from F4 as one step `StepOk` to `c1`, then `POP` and `STOP` (`wrun … 2`). -/
def CallbackFrame : Prop :=
  ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    CoveredFork g → (∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2) →
    Agree (Boundary.cfgOfT bCb0 tS tA m w) →
    ∃ (c1 cl : Cfg) (post : Devm),
      StepOk fsA ((sCb.withOrig O).withFork g) (Boundary.cfgOfT bCb0 tS tA m w) c1 ∧
      wrun fsA ((sCb.withOrig O).withFork g) 2 c1 = .done (.halted post) cl ∧
      post.gasLeft = gasCb ∧ post.output = [] ∧ post.error = none ∧
      cl.keys = keysCb ∧ cl.adrs = adrsCb ∧ cl.stor = storCb ++ tS ∧ cl.acs = acsCb ++ tA ∧
      ReentryFacts ((sCb.withOrig O).withFork g) (Boundary.cfgOfT bCb0 tS tA m w)

/-! ## Static facts -/

theorem sCb_fork : sCb.benvStat.fork = .prague ∧ sCb.benvStat.excessBlobGas = 0 := by
  decide +kernel

theorem fsCb_zero : fsA[0]? = some AttackerR.t_0000_c0 := by kernel_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
