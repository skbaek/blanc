import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Top

/-! # V+ V5: the reachable exclusion witness, stated for the actual message

`vplus_reach_exit` (see `Top.lean`'s module docstring): the outer `remove_liquidity` from the
checkpoint succeeds, and its execution carries lock acquisition, the attempted guarded reentry,
its exclusion (`vplus_exclusion` instantiated with its premises discharged) and the settlement. -/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2 (okNoRel okNoBody settleOr)
open Jaune.Exec.Deriv (ParentPrefix ParentStep)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed (ActiveRel vplus_exclusion lockBodies lockMutBodies
  lockReleasePcs lockL code_size)

attribute [local irreducible] cTop1 cpTop eB cB1 cB2 cpBal eBal cBal1 dBal dB3 cB4 cpEth eRcv
  cRcv1 cpCb eCb cCb1 cpRe eRe cRe1 cRe2 dRe dCb2 cCb3 dCb dRcv2 cRcv3 dRcv dB5 cB6 cpXf eXf
  cXf1 dXf dB7 cB8 dB dTop2 cTop3 dTop

/-- A configuration's agreement reads its machine's code from the account shadow (stated over a
variable configuration: the kernel never evaluates the closed checkpoint's accounts). -/
theorem getCode_of_pagree {c : PCfg} (h : PAgree c) (a : Adr) :
    c.devm.getCode a = (lookupA c.acs a).code := by
  have := congrArg Acct.code (h.2.2.2 a); exact this

/-- The root frame's start configuration agrees, for a world the shadows describe (stated over
a variable world, so that the kernel never unfolds the closed checkpoint). -/
theorem root_agree {W O : State} {acs : AcctShadow} {stor : StorShadow} {t : Adr} {cd : ByteArray}
    {data : Bytes} {gas : Nat} {v : B256} {e : Evm} (hW : WorldIs W acs stor)
    (he : frameEnterS (Frame.ofCall (kCall W O t cd data gas v)) acs = .run e) :
    PAgree (childCfg e (Frame.ofCall (kCall W O t cd data gas v)) [] [] stor acs) :=
  frameStart_agree .undefined he mem_emptyWithCapacity_keys mem_emptyWithCapacity_adrs hW.2 hW.1

/-- What the world the outer call settles to holds. -/
theorem exit_world_facts {W : State} (h : WorldIs W acsExit storExit) :
    (storOf W proxyAddr 0x16).toNat =
      Blanc.ledgerSumOn {creator} (fun holder => storOf W proxyAddr (lpSlot holder)) ∧
    storOf W proxyAddr 0x16 = 1800 ∧ storOf W proxyAddr (lpSlot creator) = 1800 ∧
    storOf W proxyAddr 0 = 3 ∧
    (W.get proxyAddr).bal = 900 ∧ (W.get receiverAddr).bal = 100 ∧
    storOf W tokenAddr receiverAddr.toB256 = 100 ∧ storOf W tokenAddr proxyAddr.toB256 = 900 ∧
    storOf W tokenAddr creator.toB256 = 999000 := by
  have hs := h.2
  have hsup : storOf W proxyAddr 0x16 = 1800 := by rw [hs]; decide +kernel
  have hlp : storOf W proxyAddr (lpSlot creator) = 1800 := by rw [hs]; decide +kernel
  refine ⟨?_, hsup, hlp, by rw [hs]; decide +kernel, (bal_of_worldIs h proxyAddr).trans rfl,
    (bal_of_worldIs h receiverAddr).trans rfl, by rw [hs]; decide +kernel,
    by rw [hs]; decide +kernel, by rw [hs]; decide +kernel⟩
  rw [Blanc.ledgerSumOn, Finset.sum_singleton, hsup, hlp]

/-- **V+ V5: from the funded checkpoint, a successful outer guarded mutating operation whose
callback's guarded reentry through the proxy is blocked at the lock**, on every covered fork.
See the module docstring.  `vplus_exclusion` is instantiated for the execution `R` with its
premises (fork, the clone's forwarder and the comparator in the pre-state, the root, the
trace-local hash condition) discharged, and its conclusion holds for every frame rooted in the
callback's execution, the witnessed reentry being one instance. -/
theorem vplus_reach_exit (g : Fork) (hg : CoveredFork g) (hW : Checkpoint world8) :
    processMessage (removeMsg g world8) = .ok dTop ∧ dTop.error = none ∧
    dTop.gasLeft = 920078 ∧ dTop.refundCounter = 2800 ∧ WorldIs dTop.state acsExit storExit ∧
    (Frame.ofCall (removeMsg g world8)).enter = .run (eTop.re g world8) ∧
    (∀ out, Exec 0 (reS eTop.sta g) eTop.dyna out → out = .ok dTop) ∧
    ∃ (out : Execution) (R : Exec 0 (reS eTop.sta g) eTop.dyna out)
      (F h c q G : Exec.Deriv),
      -- the premises of `vplus_exclusion`, for this `R`
      CoveredFork (reS eTop.sta g).benvStat.fork ∧
      eTop.dyna.getCode proxyAddr = forwarderCode curvePlainImpl847e ∧
      eTop.dyna.getCode curvePlainImpl847e = code ∧
      ((reS eTop.sta g).currentTarget = proxyAddr →
        (reS eTop.sta g).code = eTop.dyna.getCode proxyAddr) ∧
      lockL.HashAvoidIn proxyAddr R ∧
      -- lock acquisition, and the ETH payment spawning the receiver
      F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddr F h ∧ Spawns h c ∧
      h.pc = 7427 ∧ Ninst.At h.sevm.code h.pc (.exec .call) ∧
      c.sevm.currentTarget = receiverAddr ∧
      c.sevm.code = Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code ∧
      c.sevm.value.toNat = 100 ∧
      -- the attempted guarded entry through the clone, refused at the lock check
      q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = proxyAddr ∧ q.sevm.code = fwd ∧
      G ∈ Exec.rawFrameRoots q.exc ∧ G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame proxyAddr code G ∧
      G.sevm.data = reentryData ∧ G.exn = .error (.revert, dRe) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) ∧
      -- `vplus_exclusion`, instantiated
      (∀ G' ∈ Exec.rawFrameRoots c.exc, ¬ lockL.Enters proxyAddr G') ∧
      -- the outer call commits
      out = .ok dTop := by
  obtain ⟨he, hstT, w1, p1, d1, hp, heB, -, hca, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdB, hr, w3, w4, hdT, hgas, hrc, hcanon, hkeys⟩ := exitFacts
  have hO : OrigAgree world8 O8 := origAgree_origOf hW.2
  obtain ⟨hmsg, hca3⟩ := forwarder_root_re hg hW hO he hstT w1 p1 d1 hp heB hca
    (fun hs hag x hx => let r := frameB hg hs hag x hx; ⟨r.1, r.2.1⟩) hdB hr w3 w4 hdT
  have hag0 : PAgree cTop := root_agree hW he
  have hent : (Frame.ofCall (removeMsg g world8)).enter = .run (eTop.re g world8) :=
    root_enter_re hg hW.1 (by decide) he
  obtain ⟨R⟩ := (exec_iff_exec_eq 0 (reS eTop.sta g) eTop.dyna _).mpr rfl
  obtain ⟨hout, -, F, h, c, q, G, hF, act, sp, hash, hpc, hat, hct, hcc, hcv, hq, hqt, hqc,
    hGq, hGc, cpG, hdG, exG, nb, chk⟩ := exit_run_at hg hO hag0 R
  obtain ⟨hcP, hcI⟩ := topCodes
  have hP : eTop.dyna.getCode proxyAddr = forwarderCode curvePlainImpl847e :=
    (getCode_of_pagree hag0 proxyAddr).trans hcP
  have hI : eTop.dyna.getCode curvePlainImpl847e = code :=
    (getCode_of_pagree hag0 curvePlainImpl847e).trans hcI
  have hTcode : eTop.sta.code = fwd := by
    have h := hstT; simp only [Prod.mk.injEq] at h; exact h.2.2.1
  have hroot : (reS eTop.sta g).currentTarget = proxyAddr →
      (reS eTop.sta g).code = eTop.dyna.getCode proxyAddr := fun _ => by
    rw [hP]; exact hTcode
  have hfork' : CoveredFork (reS eTop.sta g).benvStat.fork := hg
  refine ⟨hmsg, hdT, hgas, hrc, ⟨fun a => ?_, fun a k => ?_⟩, hent,
    fun _ R' => (exit_run_at hg hO hag0 R').1, _, R, F, h, c, q, G, hfork', hP, hI, hroot, hash,
    hF, act, sp, hpc, hat, hct, hcc, hcv, hq, hqt, hqc, hGq, hGc, cpG, hdG, exG, nb, chk,
    fun G' hG' => vplus_exclusion R hfork' (Or.inl hP) hI hroot hash hF act sp hG', hout⟩
  · rw [hca3.2.2.2 a]; exact lookupA_eq_of_map hkeys a
  · rw [hca3.2.2.1 a k]; exact lookupS_eq_of_canonS hcanon a k

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
