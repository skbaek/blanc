import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRoot

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

theorem cpR_adrs_shape : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), (cpR O tS tA m w).adrs = [proxyAddr] := by
  kernel_forall_rfl

theorem c2_cfg : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), Boundary.cfgOfT bRm0 tS tA (c2 O tS tA m w).devm.meta
      (c2 O tS tA m w).devm.world = c2 O tS tA m w := by
  intro O tS tA m w
  exact (Boundary.cfg_of_obsDT (c2_obs O tS tA m w)).symm

theorem obsChildF1_acc : ∀ d : Devm,
    (obsChildF1 d).accessedAddresses = d.accessedAddresses := by
  intro d
  rfl

theorem obsChildF1_keys : ∀ d : Devm,
    (obsChildF1 d).accessedStorageKeys = d.accessedStorageKeys := by
  intro d
  rfl

theorem obsChildF1_state : ∀ d : Devm,
    (obsChildF1 d).state = d.state := by
  intro d
  rfl

theorem e1_sta_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (((e1 O tS tA m w).withFork g).sta) = ((e1 O tS tA m w).sta.withFork g) := by
  kernel_forall_rfl

theorem tailF1_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (post2 : Devm), CoveredFork g →
    stepN 10 (((⟨32, (e1 O tS tA m w).sta,
      d1R O tS tA m w post2⟩ : Evm).withFork g)) =
      some ((e1tail O tS tA m w post2).withFork g) := by
  intro g O tS tA m w post2 hg
  exact stepN_withFork hg (e1_fork O tS tA m w).1 (e1_fork O tS tA m w).2
    (tailF1_eq O tS tA m w post2)

def runV (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Res :=
  match callResume (sR.withOrig O) (cR O tS tA m w)
      (obsChildF1 (postF1 O tS tA m w post2)) ((cR O tS tA m w).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ tS) (acsRm ++ tA) with
  | some c => wrun fsA (sR.withOrig O) 2 c
  | none => .stuck

def obsV : Res → Option (Nat × List Nat × Bool × StorShadow × AcctShadow)
  | .done (.halted d) cl =>
    some (d.gasLeft, d.output.map UInt8.toNat, d.error.isNone &&
      decide (cl.keys = keysV) && decide (cl.adrs = adrsV) &&
      decide (cl.stor.take storV.length = storV),
      cl.stor.drop storV.length, cl.acs.drop acsV.length)
  | _ => none

theorem v_kernel : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    obsV (runV O tS tA m w post2) = some (gasV, [], true, tS, tA) := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
