import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolRoot

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun
open Blanc.Lift.VyperNonreentrantDeployed

theorem c2_cfg : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), Boundary.cfgOfT bRm0 tS tA (c2 O tS tA m w).devm.meta
      (c2 O tS tA m w).devm.world = c2 O tS tA m w := by
  intro O tS tA m w
  exact (Boundary.cfg_of_obsDT (c2_obs O tS tA m w)).symm

theorem c2_stor2 : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World), lookupS (c2 O tS tA m w).stor proxyAddr 2 = 0 := by
  kernel_forall_rfl

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

theorem e1'11_fork_shape : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    (e1'11 O tS tA m w).withFork g =
      ⟨31, (e1'11 O tS tA m w).sta.withFork g, (e1'11 O tS tA m w).dyna⟩ := by
  kernel_forall_rfl

theorem e1'11_fork_code : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World),
    ((e1'11 O tS tA m w).sta.withFork g).code = fwdCode := by
  kernel_forall_rfl

theorem bR0_cfg_f : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (Boundary.cfgOfT bR0 tS tA m w).f = AttackerR.t_0000_c0 := by
  kernel_forall_rfl

theorem bR0_cfg_K : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (Boundary.cfgOfT bR0 tS tA m w).K = [] := by
  kernel_forall_rfl

theorem c2_f : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (c2 O tS tA m w).f = Vulnerable.t_0000_c0 := by
  kernel_forall_rfl

theorem c2_K : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    (c2 O tS tA m w).K = [] := by
  kernel_forall_rfl

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

/-! ## F1 resumed from F2 with F2's own gas (raw observation)

`obsChildF1` observes with `gasFwd` (F1's `RETURN` gas, for F0's `ChildAgree` of
`postF1`). F1's own resume incorporates F2's settled gas (`gasRm`:
`incorporateChildOnSuccess` adds `child.gasLeft`), so the F1-internal resume,
tail and halt are restated here with `gasRm`. -/

/-- F2's settled machine as F1's resume input, with F2's own gas left. -/
abbrev obsChildF1raw (d : Devm) : Devm := childObs gasRm outRm d

theorem obsChildF1raw_acc : ∀ d : Devm,
    (obsChildF1raw d).accessedAddresses = d.accessedAddresses := by
  intro d
  rfl

theorem obsChildF1raw_keys : ∀ d : Devm,
    (obsChildF1raw d).accessedStorageKeys = d.accessedStorageKeys := by
  intro d
  rfl

theorem obsChildF1raw_state : ∀ d : Devm,
    (obsChildF1raw d).state = d.state := by
  intro d
  rfl

/-- The forwarder resumed from a settled F2 `post2`, with F2's own gas. -/
def d1Rraw (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Devm :=
  (resumeCallB (cpF2 O tS tA m w).p (cpF2 O tS tA m w).oi (cpF2 O tS tA m w).os
    (.ok (obsChildF1raw post2))).getD default

theorem resumeF1raw_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    resumeCallB (cpF2 O tS tA m w).p (cpF2 O tS tA m w).oi (cpF2 O tS tA m w).os
      (.ok (obsChildF1raw post2)) = some (d1Rraw O tS tA m w post2) := by
  kernel_forall_rfl

/-- The forwarder ten steps past F2's return, from the raw resume. -/
def e1tailraw (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Evm :=
  (stepN 10 ⟨32, (e1 O tS tA m w).sta, d1Rraw O tS tA m w post2⟩).getD default

theorem tailF1raw_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    stepN 10 ⟨32, (e1 O tS tA m w).sta, d1Rraw O tS tA m w post2⟩ =
      some (e1tailraw O tS tA m w post2) := by
  kernel_forall_rfl

/-- The forwarder's halted machine, from the raw resume. -/
def postF1raw (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Devm :=
  match Evm.step (e1tailraw O tS tA m w post2) with
  | .halt (.ok d') => d'
  | _ => default

theorem returnF1raw_eq : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    Evm.step (e1tailraw O tS tA m w post2) =
      .halt (.ok (postF1raw O tS tA m w post2)) := by
  kernel_forall_rfl

theorem postF1raw_obs : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    ((postF1raw O tS tA m w post2).output.map UInt8.toNat,
      (postF1raw O tS tA m w post2).error.isNone) =
    (outRm.map UInt8.toNat, true) := by
  kernel_forall_rfl

theorem postF1raw_gas : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    (postF1raw O tS tA m w post2).gasLeft = gasFwd := by
  kernel_forall_rfl

theorem postF1raw_keep : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    ((postF1raw O tS tA m w post2).accessedAddresses,
      (postF1raw O tS tA m w post2).accessedStorageKeys,
      (postF1raw O tS tA m w post2).state) =
    ((d1Rraw O tS tA m w post2).accessedAddresses,
      (d1Rraw O tS tA m w post2).accessedStorageKeys,
      (d1Rraw O tS tA m w post2).state) := by
  kernel_forall_rfl

theorem tailF1raw_fork : ∀ (g : Fork) (O : State) (tS : StorShadow) (tA : AcctShadow)
    (m : Meta) (w : World) (post2 : Devm), CoveredFork g →
    stepN 10 (((⟨32, (e1 O tS tA m w).sta,
      d1Rraw O tS tA m w post2⟩ : Evm).withFork g)) =
      some ((e1tailraw O tS tA m w post2).withFork g) := by
  intro g O tS tA m w post2 hg
  exact stepN_withFork hg (e1_fork O tS tA m w).1 (e1_fork O tS tA m w).2
    (tailF1raw_eq O tS tA m w post2)

def runVraw (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (post2 : Devm) : Res :=
  match callResume (sR.withOrig O) (cR O tS tA m w)
      (obsChildF1 (postF1raw O tS tA m w post2)) ((cR O tS tA m w).keys ++ keysRm)
      ([implAddr, proxyAddr] ++ adrsRm) (storRm ++ tS) (acsRm ++ tA) with
  | some c => wrun fsA (sR.withOrig O) 2 c
  | none => .stuck

theorem v_kernel_raw : ∀ (O : State) (tS : StorShadow) (tA : AcctShadow) (m : Meta)
    (w : World) (post2 : Devm),
    obsV (runVraw O tS tA m w post2) = some (gasV, [], true, tS, tA) := by
  kernel_forall_rfl

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
