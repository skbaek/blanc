import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun1
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun2
import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.ViolReRun3
import Blanc.Lift.NodeWalkFork

/-!
# V− V4, package P1: the re-entrant `add_liquidity` frame (F5)

`reAdd_frame : ReAddFrame` (the frozen interface of `ViolBoundary.lean`).  Nothing is
evaluated here: the Prague kernel chunk facts of `ViolReRun1`–`ViolReRun3` (static machine
`sRe`, original state `O0`, free shadow tails) chain through the committed boundaries
(`Boundary.obsDT_cont`, `wrun_add_cont`) to the run's halt after 4,505 steps and to
`add_liquidity`'s body at step 2625.  Each run transports to the actual machine
`(sRe.withOrig O).withFork g`: the fork by `wrun_withFork`, the original state by
`wrun_withOrig_keys`, which needs `O` to agree with `O0` only on the keys the run records
(`origAgreeOn_O0`: the halt's keys `keysRe` and the body's keys are `Checkpoint`'s read keys).
The halting run is a gas-exact run of the certificate's program, hence an `Exec` of the
implementation's bytes (`lift_exactM`); its halting configuration's shadows describe the
settled machine (`childAgree_of_halt`).
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.ConcreteRun Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable (cert t_0000_c0 cert_checkM cert_jumpsOkM)

/-! ### The halt observation, read back -/

theorem reHalt_spec {r : Res} {tS : StorShadow} {tA : AcctShadow} (h : reHaltObs r = true)
    (hr : reHaltRest r = (Boundary.restsOf acsRe, tS, tA)) :
    ∃ d cl, r = .done (.halted d) cl ∧ d.gasLeft = gasRe ∧ d.output = outRe ∧
      d.error = none ∧ cl.keys = keysRe ∧ cl.adrs = adrsRe ∧ cl.stor = storRe ++ tS ∧
      cl.acs = acsRe ++ tA := by
  rcases r with _ | ⟨d | d, cl⟩ | _
  · simp only [reHaltObs, Bool.false_eq_true] at h
  · simp only [reHaltObs, Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨⟨⟨hg, ho⟩, he⟩, hk⟩, ha⟩, hs⟩, hc⟩ := h
    simp only [reHaltRest, Prod.mk.injEq] at hr
    obtain ⟨hcr, hst, hat⟩ := hr
    refine ⟨d, cl, rfl, hg, ho, he, hk, ha, ?_, ?_⟩
    · rw [← List.take_append_drop storRe.length cl.stor, hs, hst]
    · rw [← List.take_append_drop acsRe.length cl.acs, hat,
        Boundary.acs_eq_of_views hc (hcr.trans (Boundary.restsOf_eq acsRe))]
  · simp only [reHaltObs, Bool.false_eq_true] at h
  · simp only [reHaltObs, Bool.false_eq_true] at h

/-! ### Small kernel facts about the literals -/

/-- The body boundary's accessed keys are `Checkpoint`'s read keys. -/
theorem reBody_keys : ∀ (m : Meta) (w : World),
    ((Boundary.cfgOf1 bReBody m w).keys.all fun x => decide (x ∈ readKeys)) = true := by
  kernel_forall_rfl

/-- The locks at the body boundary, read through any storage tail. -/
theorem reBody_locks : ∀ tS : StorShadow,
    lookupS (Boundary.storOf1 bReBody ++ tS) proxyAddr 0 = 1 ∧
      lookupS (Boundary.storOf1 bReBody ++ tS) proxyAddr 2 = 1 := by
  kernel_forall_rfl_and

/-- The kernel's machine is the actual one with its original state changed back to `O0`. -/
theorem sRe_withOrig_O0 (O : State) : (sRe.withOrig O).withOrig O0 = sRe := rfl

/-! ### The kernel's runs, chained through the boundaries -/

/-- **F5 at the kernel's machine**: from the entry `bRe0` with any tails, 2625 steps to the
body boundary, and 4,505 steps to the halt with the literal exits. -/
theorem reRun_kernel (tS : StorShadow) (tA : AcctShadow) (m : Meta) (w : World) :
    (∃ mB wB, wrun fsI sRe 2625 (Boundary.cfgOfT bRe0 tS tA m w) =
      .cont (Boundary.cfgOfT bReBody tS tA mB wB)) ∧
    ∃ d cl, wrun fsI sRe 4505 (Boundary.cfgOfT bRe0 tS tA m w) = .done (.halted d) cl ∧
      d.gasLeft = gasRe ∧ d.output = outRe ∧ d.error = none ∧ cl.keys = keysRe ∧
      cl.adrs = adrsRe ∧ cl.stor = storRe ++ tS ∧ cl.acs = acsRe ++ tA := by
  obtain ⟨m1, w1, e1⟩ := Boundary.obsDT_cont (reChunk1112 tS tA m w)
  obtain ⟨m2, w2, e2⟩ := Boundary.obsDT_cont (reChunk1159 tS tA m1 w1)
  obtain ⟨m3, w3, e3⟩ := Boundary.obsDT_cont (reChunk2527 tS tA m2 w2)
  obtain ⟨m4, w4, e4⟩ := Boundary.obsDT_cont (reChunkBody tS tA m3 w3)
  obtain ⟨m5, w5, e5⟩ := Boundary.obsDT_cont (reChunk3088 tS tA m4 w4)
  obtain ⟨m6, w6, e6⟩ := Boundary.obsDT_cont (reChunk4048 tS tA m5 w5)
  obtain ⟨m7, w7, e7⟩ := Boundary.obsDT_cont (reChunk4377 tS tA m6 w6)
  obtain ⟨d, cl, e8, hg, ho, he, hk, ha, hs, hc⟩ :=
    reHalt_spec (reHalt tS tA m7 w7).1 (reHalt tS tA m7 w7).2
  have hB : wrun fsI sRe (1112 + 47 + 1368 + 98) (Boundary.cfgOfT bRe0 tS tA m w) =
      .cont (Boundary.cfgOfT bReBody tS tA m4 w4) :=
    wrun_add_cont (wrun_add_cont (wrun_add_cont e1 e2) e3) e4
  have hH : wrun fsI sRe (1112 + 47 + 1368 + 98 + 463 + 960 + 329 + 128)
      (Boundary.cfgOfT bRe0 tS tA m w) = .done (.halted d) cl :=
    wrun_add_cont (wrun_add_cont (wrun_add_cont (wrun_add_cont hB e5) e6) e7) e8
  rw [show 1112 + 47 + 1368 + 98 = 2625 from rfl] at hB
  rw [show 1112 + 47 + 1368 + 98 + 463 + 960 + 329 + 128 = 4505 from rfl] at hH
  exact ⟨⟨m4, w4, hB⟩, d, cl, hH, hg, ho, he, hk, ha, hs, hc⟩

/-! ### The transport to the actual machine -/

/-- A kernel run of `sRe` that records only `Checkpoint`'s read keys is the same run at the
actual machine: any covered fork, any original state agreeing on `Checkpoint`'s read set. -/
theorem reRun_at {g : Fork} {O : State} (hg : CoveredFork g)
    (hO : ∀ e ∈ readStor, storOf O e.1.1 e.1.2 = e.2) {n : Nat} {c : Cfg} {r : Res}
    (h : wrun fsI sRe n c = r) (hs : r ≠ .stuck) (hk : ∀ x ∈ resKeys r, x ∈ readKeys) :
    wrun fsI ((sRe.withOrig O).withFork g) n c = r := by
  have e := wrun_withOrig_keys (s := sRe.withOrig O) (O := O0) fsI n c
  rw [sRe_withOrig_O0, h] at e
  rw [wrun_withFork (s := sRe.withOrig O) CoveredFork.prague hg rfl]
  exact e hs (origAgreeOn_O0 hO hk)

/-! ### The frame -/

/-- **P1: the re-entrant `add_liquidity` frame (F5).** -/
theorem reAdd_frame : ReAddFrame := by
  intro g O tS tA m w hg hO hag
  obtain ⟨⟨mB, wB, hB⟩, d, cl, hH, hgas, hout, herr, hk, ha, hs, hc⟩ := reRun_kernel tS tA m w
  have hBat := reRun_at hg hO hB (fun h => Res.noConfusion h) fun x hx =>
    of_decide_eq_true (List.all_eq_true.mp (reBody_keys mB wB) x hx)
  have hHat := reRun_at hg hO hH (fun h => Res.noConfusion h) fun x hx =>
    keys_sub_readKeys.1 x (by rw [← hk]; exact hx)
  obtain ⟨run, -, -⟩ := wrun_done hHat hag
  have hrun : SProg.RunExact (Cert.prog cert) ((sRe.withOrig O).withFork g)
      (Boundary.cfgOfT bRe0 tS tA m w).devm d := ⟨t_0000_c0, fsI_zero, run⟩
  have hx := lift_exactM cert_checkM cert_jumpsOkM (sevm := (sRe.withOrig O).withFork g) rfl hg hrun
  have hca := childAgree_of_halt hHat hag
  rw [hk, ha, hs, hc] at hca
  have hagB := (wrun_cont hBat).1 hag
  refine ⟨d, hx, hgas, hout, herr, hca, ⟨_, hBat, hagB, rfl, ?_, ?_⟩,
    fun f h1 h2 => frame_settle_ok h1 h2 herr⟩
  · rw [hagB.2.2.1, Boundary.cfgOfT_stor]; exact (reBody_locks tS).1
  · rw [hagB.2.2.1, Boundary.cfgOfT_stor]; exact (reBody_locks tS).2

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Reach.Viol
