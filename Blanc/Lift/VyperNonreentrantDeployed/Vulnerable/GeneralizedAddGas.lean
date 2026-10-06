import Blanc.Lift.GasSuccessEffects
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedGasCut
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReAdd

/-!
# The complete reference reentrant-add frame with additional gas

The eight selected cuts retain free shadow tails, metadata and world. Their
checked endpoints are reused; no alternate-budget concrete run is evaluated.
Heavy kernel certificates are checked only by the owning build. Only dynamic
execution gas varies; the static sRe environment retains its reference fields.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddGas

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.GasSuccess
open Blanc.Lift.VyperNonreentrantDeployed
open Reach Reach.Viol

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_1112 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 1112 (Boundary.cfgOfT bRe0 tS tA m w) = true := by
  kernel_forall_rfl

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_1159 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 47 (Boundary.cfgOfT bRe1112 tS tA m w) = true := by
  kernel_forall_rfl

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_2527 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 1368 (Boundary.cfgOfT bRe1159 tS tA m w) = true := by
  kernel_forall_rfl

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_2625 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 98 (Boundary.cfgOfT bRe2527 tS tA m w) = true := by
  kernel_forall_rfl

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_3088 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 463 (Boundary.cfgOfT bReBody tS tA m w) = true := by
  kernel_forall_rfl

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_4048 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 960 (Boundary.cfgOfT bRe3088 tS tA m w) = true := by
  intro tS tA m w
  exact selected_to_effects (GeneralizedGasCut.selected_reference tS tA m w)

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_4377 : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 329 (Boundary.cfgOfT bRe4048 tS tA m w) = true := by
  kernel_forall_rfl

/-- The actual selected reference cut uses only proved gas-success arms. -/
theorem selected_halt : ∀ (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World),
    selectedEffects Reach.fsI sRe 128 (Boundary.cfgOfT bRe4377 tS tA m w) = true := by
  kernel_forall_rfl

/-- The complete 4,505-step reference certificate, composed through all seven
already checked continuing endpoints and the final RETURN cut. -/
theorem selected_full (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    selectedEffects Reach.fsI sRe 4505 (Boundary.cfgOfT bRe0 tS tA m w) = true := by
  obtain ⟨m1, w1, e1⟩ := Boundary.obsDT_cont (reChunk1112 tS tA m w)
  obtain ⟨m2, w2, e2⟩ := Boundary.obsDT_cont (reChunk1159 tS tA m1 w1)
  obtain ⟨m3, w3, e3⟩ := Boundary.obsDT_cont (reChunk2527 tS tA m2 w2)
  obtain ⟨m4, w4, e4⟩ := Boundary.obsDT_cont (reChunkBody tS tA m3 w3)
  obtain ⟨m5, w5, e5⟩ := Boundary.obsDT_cont (reChunk3088 tS tA m4 w4)
  obtain ⟨m6, w6, e6⟩ := Boundary.obsDT_cont (reChunk4048 tS tA m5 w5)
  obtain ⟨m7, w7, e7⟩ := Boundary.obsDT_cont (reChunk4377 tS tA m6 w6)
  have h7 := selectedEffects_add_cont (selected_4377 tS tA m6 w6) e7 (selected_halt tS tA m7 w7)
  have h6 := selectedEffects_add_cont (selected_4048 tS tA m5 w5) e6 h7
  have h5 := selectedEffects_add_cont (selected_3088 tS tA m4 w4) e5 h6
  have h4 := selectedEffects_add_cont (selected_2625 tS tA m3 w3) e4 h5
  have h3 := selectedEffects_add_cont (selected_2527 tS tA m2 w2) e3 h4
  have h2 := selectedEffects_add_cont (selected_1159 tS tA m1 w1) e2 h3
  have h1 := selectedEffects_add_cont (selected_1112 tS tA m w) e1 h2
  rw [show 1112 + (47 + (1368 + (98 + (463 + (960 + (329 + 128)))))) = 4505 from rfl] at h1
  exact h1

/-- Fund the entire successful reference frame at any larger gas budget.
The exact post machine retains output, refund, deletion set, world, logs and
all other columns; only execution gas changes, by the entry offset. -/
theorem full_transport (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    ∃ d cl, wrun Reach.fsI sRe 4505 (Boundary.cfgOfT bRe0 tS tA m w) = .done (.halted d) cl ∧
      d.gasLeft = gasRe ∧ d.output = outRe ∧ d.error = none ∧ cl.keys = keysRe ∧
      cl.adrs = adrsRe ∧ cl.stor = storRe ++ tS ∧ cl.acs = acsRe ++ tA ∧
      ∀ δ, wrun Reach.fsI sRe 4505 (addCfgGas (Boundary.cfgOfT bRe0 tS tA m w) δ) =
        .done (.halted (addGas d δ)) (addCfgGas cl δ) := by
  obtain ⟨_, d, cl, hr, hg, ho, he, hk, ha, hs, hc⟩ := reRun_kernel tS tA m w
  refine ⟨d, cl, hr, hg, ho, he, hk, ha, hs, hc, ?_⟩
  intro δ
  have ht := @wrun_effect_addGas Reach.fsI sRe 4505 (Boundary.cfgOfT bRe0 tS tA m w)
    (selected_full tS tA m w) δ
  rw [hr] at ht
  exact ht

/-- Retain the exact body-entry cut for later lock and headline composition,
reusing a prefix of the complete certificate without another kernel replay. -/
theorem body_transport (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    ∃ mB wB, wrun Reach.fsI sRe 2625 (Boundary.cfgOfT bRe0 tS tA m w) =
      .cont (Boundary.cfgOfT bReBody tS tA mB wB) ∧
      ∀ δ, wrun Reach.fsI sRe 2625 (addCfgGas (Boundary.cfgOfT bRe0 tS tA m w) δ) =
        .cont (addCfgGas (Boundary.cfgOfT bReBody tS tA mB wB) δ) := by
  obtain ⟨⟨mB, wB, hB⟩, _⟩ := reRun_kernel tS tA m w
  refine ⟨mB, wB, hB, ?_⟩
  intro δ
  have hc := @selectedEffects_prefix Reach.fsI sRe 4505 2625 (Boundary.cfgOfT bRe0 tS tA m w)
    (by decide) (selected_full tS tA m w)
  have ht := @wrun_effect_addGas Reach.fsI sRe 2625 (Boundary.cfgOfT bRe0 tS tA m w) hc δ
  rw [hB] at ht
  exact ht

/-- Actual code execution at every covered fork and agreeing original state,
from the existing shadow agreement. Only dynamic execution gas varies: the
static sRe gas field, depth, addresses and calldata retain their reference
values. This is a local Exec bridge, not preparation of a new message. -/
theorem full_exec (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World)
    (g : Fork) (O : State) (δ : Nat) (hg : CoveredFork g)
    (hO : ∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2)
    (hag : Agree (Boundary.cfgOfT bRe0 tS tA m w)) :
    ∃ d, d.gasLeft = gasRe ∧ d.output = outRe ∧ d.error = none ∧
      Nonempty (Exec 0 ((sRe.withOrig O).withFork g)
        (addGas (Boundary.cfgOfT bRe0 tS tA m w).devm δ) (.ok (addGas d δ))) ∧
      (addGas d δ).gasLeft = gasRe + δ ∧ (addGas d δ).output = outRe ∧
      (addGas d δ).refundCounter = d.refundCounter ∧
      (addGas d δ).accountsToDelete = d.accountsToDelete := by
  obtain ⟨d, cl, _, hgas, hout, herr, hk, _, _, _, ha⟩ := full_transport tS tA m w
  have hHat := reRun_at hg hO (ha δ) (fun h => Res.noConfusion h) (fun x hx =>
    keys_sub_readKeys.1 x (by change x ∈ cl.keys at hx; rw [hk] at hx; exact hx))
  have hagδ := (agree_addCfgGas (Boundary.cfgOfT bRe0 tS tA m w) δ).2 hag
  obtain ⟨run, _, _⟩ := wrun_done hHat hagδ
  have hrun : SProg.RunExact (Cert.prog cert) ((sRe.withOrig O).withFork g)
      (addGas (Boundary.cfgOfT bRe0 tS tA m w).devm δ) (addGas d δ) :=
    ⟨t_0000_c0, fsI_zero, run⟩
  have hx := lift_exactM cert_checkM cert_jumpsOkM
    (sevm := (sRe.withOrig O).withFork g) rfl hg hrun
  refine ⟨d, hgas, hout, herr, hx, ?_, ?_, rfl, rfl⟩
  · change d.gasLeft + δ = gasRe + δ
    rw [hgas]
  · exact hout

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.GeneralizedAddGas
