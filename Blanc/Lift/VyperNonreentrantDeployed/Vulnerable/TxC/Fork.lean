import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.ForkKernel
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Entry
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC.Frame5

/-!
V- as an admitted transaction under every covered fork: the machines each frame enters with.

Every machine of the transaction's run under a covered fork `g` (Prague, Osaka, BPO1, BPO2) is the
Prague machine with only its fork changed (`withFork`): the transaction `txC` warms the same
addresses under every fork (its access list names `0x100`, the precompile Osaka adds), so the
prepared message differs only in its fork.  The kernel facts are not re-evaluated: the certificate
interpreter, the child machinery and Jaune's driver are unchanged by the fork, the run never
executes `CLZ` (an invalid opcode at Prague), reads no blob price (the block has no excess blob
gas), and none of its frames enters `MODEXP` or `P256VERIFY` (`ForkKernel.lean`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.ConcreteRun Blanc.ForkUniform Blanc.Lift.NodeWalk
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx (fs3)

attribute [local irreducible] callCfgC cp0C e1C cp2C e2C cfg339C e3C cc3C aCallC cp4C e4C cp5C e5C

variable {g : Fork}

/-! ### The block environment every frame inherits -/

theorem e0C_stat : e0C.sta.benvStat = benvStatTx := (frameEnterS_stat e0C_eq).trans msgC_stat

theorem e1C_stat : e1C.sta.benvStat = e0C.sta.benvStat :=
  (frameEnterS_stat e1C_eq).trans (callPrep_stat cp0C_eq).2

theorem e2C_stat : e2C.sta.benvStat = e1C.sta.benvStat :=
  (frameEnterS_stat e2C_eq).trans (dcallPrep_stat cp2C_eq).2

theorem e3C_stat : e3C.sta.benvStat = e2C.sta.benvStat := childStart_stat start3C_eq

theorem e4C_stat : e4C.sta.benvStat = e3C.sta.benvStat :=
  (frameEnterS_stat e4C_eq).trans (callPrep_stat cp4C_eq).2

theorem e5C_stat : e5C.sta.benvStat = e4C.sta.benvStat :=
  (frameEnterS_stat e5C_eq).trans (dcallPrep_stat cp5C_eq).2

theorem e0C_block : e0C.sta.benvStat.fork = .prague ∧ e0C.sta.benvStat.excessBlobGas = 0 := by
  rw [e0C_stat]; exact ⟨rfl, rfl⟩

theorem e1C_block : e1C.sta.benvStat.fork = .prague ∧ e1C.sta.benvStat.excessBlobGas = 0 := by
  rw [e1C_stat]; exact e0C_block

theorem e2C_block : e2C.sta.benvStat.fork = .prague ∧ e2C.sta.benvStat.excessBlobGas = 0 := by
  rw [e2C_stat]; exact e1C_block

theorem e3C_block : e3C.sta.benvStat.fork = .prague ∧ e3C.sta.benvStat.excessBlobGas = 0 := by
  rw [e3C_stat]; exact e2C_block

theorem e4C_block : e4C.sta.benvStat.fork = .prague ∧ e4C.sta.benvStat.excessBlobGas = 0 := by
  rw [e4C_stat]; exact e3C_block

theorem e5C_block : e5C.sta.benvStat.fork = .prague ∧ e5C.sta.benvStat.excessBlobGas = 0 := by
  rw [e5C_stat]; exact e4C_block

theorem f0C_neutral : f0C.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.1) spawned_codeAddressesC) (by decide)
    (by decide)

theorem cp0C_neutral : cp0C.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.2.1) spawned_codeAddressesC) (by decide)
    (by decide)

theorem cp2C_neutral : cp2C.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.2.2.1) spawned_codeAddressesC) (by decide)
    (by decide)

theorem cp4C_neutral : cp4C.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.2.2.2.1) spawned_codeAddressesC) (by decide)
    (by decide)

theorem cp5C_neutral : cp5C.f.PrecompNeutral :=
  Frame.precompNeutral_of_codeAddress (congrArg (·.2.2.2.2) spawned_codeAddressesC) (by decide)
    (by decide)

/-! ### The machines each frame enters with, under `g` -/

theorem f0C_enter_at (hg : CoveredFork g) : (f0C.withFork g).enter = .run (e0C.withFork g) := by
  have h := frame_enter_withFork (f := f0C) (g := g)
    (by rw [show f0C.outer.benv.stat = benvStatTx from msgC_stat]; exact CoveredFork.prague)
    (by rw [show f0C.inner.benv.stat = benvStatTx from msgC_stat]; exact CoveredFork.prague) hg
    f0C_neutral
  rw [h, f0C_enter]; rfl

theorem callCfgC_at (hg : CoveredFork g) : wrun fs2 (e0C.withFork g).sta 33 c0C = .cont callCfgC :=
  (wrun_withFork (by rw [e0C_block.1]; exact CoveredFork.prague) hg e0C_block.2 fs2 33 c0C).trans
    callCfgC_eq

theorem cp0C_at (hg : CoveredFork g) :
    callPrep (e0C.withFork g).sta callCfgC = some (cp0C.withFork g) := by
  show callPrep (e0C.sta.withFork g) callCfgC = _
  rw [callPrep_withFork (by rw [e0C_block.1]; exact CoveredFork.prague) hg, cp0C_eq]; rfl

theorem e1C_at (hg : CoveredFork g) :
    frameEnterS (cp0C.withFork g).f callCfgC.acs = .run (e1C.withFork g) := by
  show frameEnterS (cp0C.f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat (by rw [e0C_block.1]; exact CoveredFork.prague) hg
    (callPrep_stat cp0C_eq) cp0C_neutral, e1C_eq]
  rfl

theorem prefix1C_at (hg : CoveredFork g) : stepN 11 (e1C.withFork g) = some (e1C31.withFork g) :=
  stepN_withFork hg e1C_block.1 e1C_block.2 prefix1C

theorem cp2C_at (hg : CoveredFork g) :
    dcallPrep (e1C31.withFork g).sta e1C31.dyna adrs1C acs1C = some (cp2C.withFork g) := by
  have hf : CoveredFork e1C31.sta.benvStat.fork := by
    show CoveredFork e1C.sta.benvStat.fork
    rw [e1C_block.1]; exact CoveredFork.prague
  have h := dcallPrep_withFork hf hg e1C31.dyna adrs1C acs1C
  show dcallPrep (e1C31.sta.withFork g) e1C31.dyna adrs1C acs1C = _
  rw [h, cp2C_eq]; rfl

theorem e2C_at (hg : CoveredFork g) :
    frameEnterS (cp2C.withFork g).f acs1C = .run (e2C.withFork g) := by
  show frameEnterS (cp2C.f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat (s := e1C.sta)
    (by rw [e1C_block.1]; exact CoveredFork.prague) hg (dcallPrep_stat cp2C_eq) cp2C_neutral,
    e2C_eq]
  rfl

theorem start3C_at (hg : CoveredFork g) :
    childStart (e2C.withFork g).sta cfg339C Attacker2.t_0000_c0 = some (e3C.withFork g, cc3C) := by
  show childStart (e2C.sta.withFork g) _ _ = _
  rw [childStart_withFork (by rw [e2C_block.1]; exact CoveredFork.prague) hg, start3C_eq]; rfl

theorem aCallC_at (hg : CoveredFork g) : wrun fs3 (e3C.withFork g).sta 32 cc3C = .cont aCallC :=
  (wrun_withFork (by rw [e3C_block.1]; exact CoveredFork.prague) hg e3C_block.2 fs3 32 cc3C).trans
    aCallC_eq

theorem cp4C_at (hg : CoveredFork g) :
    callPrep (e3C.withFork g).sta aCallC = some (cp4C.withFork g) := by
  show callPrep (e3C.sta.withFork g) aCallC = _
  rw [callPrep_withFork (by rw [e3C_block.1]; exact CoveredFork.prague) hg, cp4C_eq]; rfl

theorem e4C_at (hg : CoveredFork g) :
    frameEnterS (cp4C.withFork g).f aCallC.acs = .run (e4C.withFork g) := by
  show frameEnterS (cp4C.f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat (by rw [e3C_block.1]; exact CoveredFork.prague) hg
    (callPrep_stat cp4C_eq) cp4C_neutral, e4C_eq]
  rfl

theorem prefix4C_at (hg : CoveredFork g) : stepN 11 (e4C.withFork g) = some (e4C31.withFork g) :=
  stepN_withFork hg e4C_block.1 e4C_block.2 prefix4C

theorem cp5C_at (hg : CoveredFork g) :
    dcallPrep (e4C31.withFork g).sta e4C31.dyna adrs4C acs4C = some (cp5C.withFork g) := by
  have hf : CoveredFork e4C31.sta.benvStat.fork := by
    show CoveredFork e4C.sta.benvStat.fork
    rw [e4C_block.1]; exact CoveredFork.prague
  have h := dcallPrep_withFork hf hg e4C31.dyna adrs4C acs4C
  show dcallPrep (e4C31.sta.withFork g) e4C31.dyna adrs4C acs4C = _
  rw [h, cp5C_eq]; rfl

theorem e5C_at (hg : CoveredFork g) :
    frameEnterS (cp5C.withFork g).f acs4C = .run (e5C.withFork g) := by
  show frameEnterS (cp5C.f.withFork g) _ = _
  rw [frameEnterS_withFork_of_stat (s := e4C.sta)
    (by rw [e4C_block.1]; exact CoveredFork.prague) hg (dcallPrep_stat cp5C_eq) cp5C_neutral,
    e5C_eq]
  rfl

theorem r5C_at (hg : CoveredFork g) : wrun fs1 (e5C.withFork g).sta 4505 c5C = r5C :=
  wrun_withFork (by rw [e5C_block.1]; exact CoveredFork.prague) hg e5C_block.2 fs1 4505 c5C

/-! ### The spawns -/

theorem cp0C_spec_at (hg : CoveredFork g) :
    Xinst.step (e0C.withFork g).sta callCfgC.devm .call =
        .spawn (cp0C.withFork g).f (.call cp0C.p cp0C.oi cp0C.os) ∧
      (∀ a, a ∈ cp0C.p.accessedAddresses ↔ a ∈ cp0C.adrs) ∧
      cp0C.p.accessedStorageKeys = callCfgC.devm.accessedStorageKeys ∧
      (cp0C.withFork g).f.isCreate = false ∧
      (cp0C.withFork g).f.inner.accessedAddresses = cp0C.p.accessedAddresses ∧
      (cp0C.withFork g).f.inner.accessedStorageKeys = cp0C.p.accessedStorageKeys ∧
      (cp0C.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cp0C.withFork g).f.inner.benv.state = callCfgC.devm.state :=
  callPrep_spec (cp0C_at hg) callCfgC_agree.2.1 callCfgC_agree.2.2.2

theorem cp2C_spec_at (hg : CoveredFork g) :
    Xinst.step (e1C31.withFork g).sta e1C31.dyna .delegatecall =
        .spawn (cp2C.withFork g).f (.call cp2C.p cp2C.oi cp2C.os) ∧
      (∀ a, a ∈ cp2C.p.accessedAddresses ↔ a ∈ cp2C.adrs) ∧
      cp2C.p.accessedStorageKeys = e1C31.dyna.accessedStorageKeys ∧
      (cp2C.withFork g).f.isCreate = false ∧
      (cp2C.withFork g).f.inner.accessedAddresses = cp2C.p.accessedAddresses ∧
      (cp2C.withFork g).f.inner.accessedStorageKeys = cp2C.p.accessedStorageKeys ∧
      (cp2C.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cp2C.withFork g).f.inner.benv.state = e1C31.dyna.state ∧
      cp2C.p.state = e1C31.dyna.state :=
  dcallPrep_spec (cp2C_at hg) (fun a => by rw [e1C31_acc]; exact e1C_adrs a)
    (by rw [e1C31_state]; exact e1C_world.2)

theorem cp4C_spec_at (hg : CoveredFork g) :
    Xinst.step (e3C.withFork g).sta aCallC.devm .call =
        .spawn (cp4C.withFork g).f (.call cp4C.p cp4C.oi cp4C.os) ∧
      (∀ a, a ∈ cp4C.p.accessedAddresses ↔ a ∈ cp4C.adrs) ∧
      cp4C.p.accessedStorageKeys = aCallC.devm.accessedStorageKeys ∧
      (cp4C.withFork g).f.isCreate = false ∧
      (cp4C.withFork g).f.inner.accessedAddresses = cp4C.p.accessedAddresses ∧
      (cp4C.withFork g).f.inner.accessedStorageKeys = cp4C.p.accessedStorageKeys ∧
      (cp4C.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cp4C.withFork g).f.inner.benv.state = aCallC.devm.state :=
  callPrep_spec (cp4C_at hg) agree_aCallC.2.1 agree_aCallC.2.2.2

theorem cp5C_spec_at (hg : CoveredFork g) :
    Xinst.step (e4C31.withFork g).sta e4C31.dyna .delegatecall =
        .spawn (cp5C.withFork g).f (.call cp5C.p cp5C.oi cp5C.os) ∧
      (∀ a, a ∈ cp5C.p.accessedAddresses ↔ a ∈ cp5C.adrs) ∧
      cp5C.p.accessedStorageKeys = e4C31.dyna.accessedStorageKeys ∧
      (cp5C.withFork g).f.isCreate = false ∧
      (cp5C.withFork g).f.inner.accessedAddresses = cp5C.p.accessedAddresses ∧
      (cp5C.withFork g).f.inner.accessedStorageKeys = cp5C.p.accessedStorageKeys ∧
      (cp5C.withFork g).f.inner.benv.stat.rules.stateGas = none ∧
      (cp5C.withFork g).f.inner.benv.state = e4C31.dyna.state ∧
      cp5C.p.state = e4C31.dyna.state :=
  dcallPrep_spec (cp5C_at hg) (fun a => by rw [e4C31_acc]; exact e4C_adrs a)
    (by rw [e4C31_state]; exact e4C_world.2)

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxC
