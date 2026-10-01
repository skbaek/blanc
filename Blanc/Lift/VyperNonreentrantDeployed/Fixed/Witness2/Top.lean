import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2.Frames

/-!
# V+ nonvacuity, committing: an ETH-paying mutating body, a refused reentry, success

`vplus_witness2` exhibits, for the corrected comparator behind the ETH/stETH forwarder
`curveStethPool847e`, an actual Jaune execution `R` of the top-level message `msgTop` (from the
explicit synthetic Prague pre-state of `Witness2/Setup.lean`) that **succeeds**:

* `S` calls the pool with `remove_liquidity(100, [0, 0], X)`.  The forwarder `DELEGATECALL`s the
  comparator (the pool-owned frame `F` running `code`), which sets the lock, reaches the body
  start `0x1bae`, and makes the ETH `CALL` `h` (pc 7427, 100 wei) to the receiver `X`
  (`Receiver.code`, registered through the certificate producer);
* `X` calls the pool again through the forwarder with `add_liquidity`'s selector (a mutating
  guarded function).  The comparator frame `G` this opens reads the held lock at the check
  (pc 0x53), lands on the revert pad 0x477e and reverts; the forwarder fails with it and `X`
  ignores the failure and stops;
* `F` resumes, transfers coin 1 (a `CALL` of `X`, returning the word 1), releases the lock and
  returns; the forwarder returns; the outcome is `.ok dTop`.

It states the antecedent of `vplus_exclusion_stethPool` for the real nodes — `ActiveRel`,
`Spawns`, `HashAvoidIn` (by the digests the walks decide, `pwalkH (.avoid 0)` and
`hashAvoid_of_hashOK`, not by the absence of hashes) — the `CPFrame` of the owner `G`, and
`vplus_exclusion_stethPool`'s conclusion `¬ lockL.Enters P G`; and the post-state the shadows
show: the pool's balance fell from 1000 to 900 wei, `X`'s rose from 0 to 100, and the lock is
released (3) before and after.

`vplus_witness2_covered` states the same for every covered fork (Prague, Osaka, BPO1, BPO2):
the run never executes `CLZ`, reads no blob price on a block without excess blob gas, and none of
its six spawned frames enters `MODEXP` or `P256VERIFY`, so the Prague kernel facts transport
(`Blanc/Lift/NodeWalkFork.lean`, `Frames.lean`); `vplus_witness2` is its Prague instance.

Every node is a node of `R` itself (`Blanc/Lift/NodeWalk.lean`): no particular derivation is
constructed.  Synthetic: the pool's and `X`'s accounts and the pool's storage (Setup), the
receiver code, the block environment; a message call, not a validated transaction.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Jaune.Exec.Deriv (ParentPrefix ParentStep)

attribute [local irreducible] cTop1 cpTop eB cB1 cB2 cpBal eBal cBal1 dBal dB3 cB4 cpEth eRcv
  cRcv1 cpCb eCb cCb1 cpRe eRe cRe1 cRe2 dRe dCb2 cCb3 dCb dRcv2 cRcv3 dRcv dB5 cB6 cpXf eXf
  cXf1 dXf dB7 cB8 dB dTop2 cTop3 dTop

theorem fwdCode_size : fwdCode.size = 45 := by decide

theorem fwdCode_ne : fwdCode ≠ code := fun h => by
  have := congrArg ByteArray.size h
  rw [fwdCode_size, code_size] at this
  exact absurd this (by decide)

theorem receiver_ne : receiverAddress ≠ proxyAddress := by decide

/-- A machine whose account shadow agrees reads its balance from the shadow. -/
theorem getBal_of_agree {d : Devm} {acs : AcctShadow} (h : AcctAgree d.state acs) (a : Adr) :
    d.getBal a = (lookupA acs a).bal := by
  show (d.state.get a).bal = _
  rw [← h a]; rfl

/-! ### Static facts of the frames' entry machines -/

theorem eTop_static : eTop.pc = 0 ∧ eTop.sta.currentTarget = proxyAddress ∧
    eTop.sta.code = fwdCode ∧ eTop.sta.benvStat.fork = .prague := by
  obtain ⟨h, -⟩ := runFactsD
  exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj (Prod.mk.inj h).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2⟩

theorem eB_static : eB.pc = 0 ∧ eB.sta.code = code ∧ eB.sta.currentTarget = proxyAddress := by
  obtain ⟨-, -, -, -, -, h, -⟩ := runFactsA
  exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1,
    (Prod.mk.inj (Prod.mk.inj h).2).1⟩

theorem eBal_static : eBal.sta.currentTarget = receiverAddress := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := runFactsA
  exact (Prod.mk.inj (Prod.mk.inj h).2).1

theorem eXf_static : eXf.sta.currentTarget = receiverAddress := by
  obtain ⟨-, -, -, -, -, h, -⟩ := runFactsC.2
  exact (Prod.mk.inj (Prod.mk.inj h).2).1

theorem eRcv_static : eRcv.sta.currentTarget = receiverAddress ∧ eRcv.sta.code = Receiver.code ∧
    eRcv.sta.value.toNat = 100 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := runFactsA
  exact ⟨(Prod.mk.inj (Prod.mk.inj h).2).1, (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2).1⟩

theorem eCb_static : eCb.sta.currentTarget = proxyAddress ∧ eCb.sta.code = fwdCode := by
  obtain ⟨-, -, -, -, -, h, -⟩ := runFactsB
  exact ⟨(Prod.mk.inj (Prod.mk.inj h).2).1, (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1⟩

theorem eRe_static : eRe.pc = 0 ∧ eRe.sta.currentTarget = proxyAddress ∧ eRe.sta.code = code ∧
    eRe.sta.data = reentryCall := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := runFactsB
  exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj (Prod.mk.inj h).2).1, (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1,
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).2⟩

theorem eTop_withFork_prague : eTop.sta.withFork .prague = eTop.sta := by
  have h := Sevm.withFork_self eTop.sta
  rw [eTop_static.2.2.2] at h
  exact h

/-- **The run, on every derivation, under any covered fork.**  Whatever derivation `R` of the
forwarder frame's machine is taken, with its fork changed to any covered fork, it succeeds with
`dTop`, and it has the nodes the V+ antecedent names.  The kernel facts of the Prague walks are
transported (`Blanc/Lift/NodeWalkFork.lean`, `Frames.lean`); nothing is re-evaluated. -/
theorem vplus_run2_at {S : Sevm} (hS : ∃ g, CoveredFork g ∧ S = eTop.sta.withFork g)
    {out : Execution} (R : Exec 0 S eTop.dyna out) :
    out = .ok dTop ∧ ChildAgree dTop cTop3.keys cTop3.adrs cTop3.stor cTop3.acs ∧
    ∃ F h c q G : Exec.Deriv,
      F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddress F h ∧ Spawns h c ∧
      lockL.HashAvoidIn proxyAddress R ∧
      h.pc = 7427 ∧ Ninst.At h.sevm.code h.pc (.exec .call) ∧
      c.sevm.currentTarget = receiverAddress ∧ c.sevm.code = Receiver.code ∧
      c.sevm.value.toNat = 100 ∧
      q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = proxyAddress ∧
      q.sevm.code = fwdCode ∧ G ∈ Exec.rawFrameRoots q.exc ∧ G ∈ Exec.rawFrameRoots c.exc ∧
      CPFrame proxyAddress code G ∧ G.sevm.data = reentryCall ∧
      G.exn = .error (.revert, dRe) ∧ (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) := by
  obtain ⟨fk, hfk, rfl⟩ := hS
  obtain ⟨hf, hx⟩ := eTop_ok
  obtain ⟨walkTop1, pTop1, decTop1, -, -, -⟩ := runFactsA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, dBerr, resTop2, walkTop3, walkTop4⟩ := runFactsC
  obtain ⟨hTpc, hTtarget, hTcode, -⟩ := eTop_static
  obtain ⟨sTop, nB⟩ := spawnTop_at hfk
  have hcT : (eTop.sta.withFork fk).code = fwdCode := hTcode
  have w1 := (pwalkH_withFork hf hfk hx .refuse fwdTries okAny 11 cTop).trans walkTop1
  have w3 := (pwalkH_withFork hf hfk hx .refuse fwdTries okAny 10 cTop2).trans walkTop3
  have w4 := (pwalkH_withFork hf hfk hx .refuse fwdTries okAny 1 cTop3).trans walkTop4
  -- the forwarder frame to its `DELEGATECALL`, which spawns the pool body `F`
  have hP0 : NodeAt (eTop.sta.withFork fk) cTop ⟨0, eTop.sta.withFork fk, eTop.dyna, out, R⟩ :=
    ⟨hTpc.symm, rfl, rfl⟩
  obtain ⟨hag1, h1⟩ := pwalkH_cont .refuse fwdTries hcT okAny 11 cTop cTop1 cTop_agree w1
  obtain ⟨x1, hx1, pp01, ex01, ds01, -⟩ := h1 _ hP0
  have hat1 : Ninst.At (eTop.sta.withFork fk).code cTop1.pc (.exec .delegatecall) := by
    rw [hcT, pTop1]; exact decodeT_sound fwdTries decTop1
  obtain ⟨stepT, entB, -, hagB0, hFT⟩ := delegatecall_node hag1 hat1 sTop nB
  obtain ⟨F, x2, sp0, hF, e2, hx2, ex2, hdesc2, hag2⟩ :=
    spawn_resume_ok hx1 hag1 hFT stepT entB dBerr resTop2
      (fun F hF => let r := frameB hfk hagB0 F hF; ⟨r.1, r.2.1⟩)
  obtain ⟨exF, -, b, h, t1, xr, q, g, t2, ppFb, hbpc, ppbh, hhpc, hath, hrel, sph, ht1, hxr, hq,
    hg, ht2, dsF, dsr, dsq, hre, hashF⟩ := frameB hfk hagB0 F hF
  -- the forwarder's tail
  obtain ⟨hag3, h3⟩ := pwalkH_cont .refuse fwdTries hcT okAny 10 cTop2 cTop3 hag2 w3
  obtain ⟨x3, hx3, -, ex3, ds3, -⟩ := h3 x2 hx2
  obtain ⟨ex4, ds4, -⟩ := pwalkH_halt .refuse fwdTries hcT okAny 1 cTop3 _ hag3 w4 x3 hx3
  have hout : out = .ok dTop := by
    show (⟨0, eTop.sta.withFork fk, eTop.dyna, out, R⟩ : Exec.Deriv).exn = _
    rw [← ex01, ← ex2, ← ex3]; exact ex4
  -- the raw frame roots of `R`
  have hdescR : Exec.rawFrameDescendants R = [F, t1, xr, q, g, t2] := by
    show Exec.rawFrameDescendants
      (⟨0, eTop.sta.withFork fk, eTop.dyna, out, R⟩ : Exec.Deriv).exc = _
    rw [← ds01, hdesc2, dsF, ← ds3, ds4]
    rfl
  have hroots : ∀ G', G' ∈ Exec.rawFrameRoots R →
      G' = ⟨0, eTop.sta.withFork fk, eTop.dyna, out, R⟩ ∨ G' = F ∨
      G' = t1 ∨ G' = xr ∨ G' = q ∨ G' = g ∨ G' = t2 := by
    intro G' hG'
    simp only [Exec.rawFrameRoots, hdescR, List.mem_cons, List.not_mem_nil, or_false] at hG'
    exact hG'
  have hcodeF : F.sevm.code = code := by rw [hF.2.1]; exact eB_static.2.1
  have hcodeG : g.sevm.code = code := by
    obtain ⟨-, hg1, -⟩ := hg
    rw [hg1]; exact eRe_static.2.2.1
  have hashG := hre.2.1
  have ownerNe : ∀ (n : Exec.Deriv) (sevm : Sevm), n.sevm = sevm →
      sevm.currentTarget = receiverAddress → n.sevm.currentTarget ≠ proxyAddress := by
    intro n sevm h1 h2 h3
    rw [h1, h2] at h3
    exact receiver_ne h3
  have hqcode : q.sevm.code = fwdCode := by rw [hq.2.1]; exact eCb_static.2
  -- the pool-owned frames avoid the lock slot with their hashes
  have hHash : lockL.HashAvoidIn proxyAddress R := by
    intro G' hG' hcp
    have hc : G'.sevm.code = code := hcp.2.2
    have ht : G'.sevm.currentTarget = proxyAddress := hcp.2.1
    rcases hroots G' hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (hTcode.symm.trans hc) fwdCode_ne
    · exact hashAvoid_of_hashOK hcodeF (fun x hx => hashF x hx)
    · exact absurd ht (ownerNe _ _ ht1.2.1 eBal_static)
    · exact absurd ht (ownerNe _ _ hxr.2.1 eRcv_static.1)
    · exact absurd (hqcode.symm.trans hc) fwdCode_ne
    · exact hashAvoid_of_hashOK hcodeG (fun x hx => (hashG x hx).1)
    · exact absurd ht (ownerNe _ _ ht2.2.1 eXf_static)
  have memD : ∀ (n y : Exec.Deriv), y ∈ Exec.rawFrameDescendants n.exc →
      y ∈ Exec.rawFrameRoots n.exc := fun n y hy => List.mem_cons_of_mem _ hy
  refine ⟨hout, halt1_childAgree fwdTries hag3 w4, F, h, xr, q, g, ?_, ⟨⟨(hF.1.trans eB_static.1),
    (by rw [hF.2.1]; exact eB_static.2.2), hcodeF⟩, ppFb.trans ppbh, b, ppFb, ppbh,
    by rw [hbpc]; decide, hrel⟩, sph, hHash, hhpc, hath,
    (by rw [hxr.2.1]; exact eRcv_static.1), (by rw [hxr.2.1]; exact eRcv_static.2.1),
    (by rw [hxr.2.1]; exact eRcv_static.2.2), memD xr q (by rw [dsr]; simp only [List.mem_cons,
      List.not_mem_nil, or_false, true_or]),
    (by rw [hq.2.1]; exact eCb_static.1), hqcode, memD q g (by rw [dsq]; simp only [List.mem_cons,
      List.not_mem_nil, or_false]),
    memD xr g (by rw [dsr]; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]),
    ⟨(hg.1.trans eRe_static.1), (by rw [hg.2.1]; exact eRe_static.2.1), hcodeG⟩,
    (by rw [hg.2.1]; exact eRe_static.2.2.2), hre.1, fun x hx => (hashG x hx).2, hre.2.2⟩
  exact List.mem_cons_of_mem _ (by rw [hdescR]; simp only [List.mem_cons, List.not_mem_nil,
    or_false, true_or])

/-! ### The closed theorem -/

theorem eTop_getCode_proxy : eTop.dyna.getCode proxyAddress = fwdCode := by
  obtain ⟨-, hc, -⟩ := runFactsD
  have h : acctView (eTop.dyna.state.get proxyAddress) = lookupA cTop.acs proxyAddress :=
    cTop_agree.2.2.2 proxyAddress
  show (eTop.dyna.state.get proxyAddress).code = fwdCode
  rw [← hc, ← h]
  rfl

theorem eTop_getCode_impl : eTop.dyna.getCode curvePlainImpl847e = code := by
  obtain ⟨-, -, hc, -⟩ := runFactsD
  have h : acctView (eTop.dyna.state.get curvePlainImpl847e) =
      lookupA cTop.acs curvePlainImpl847e := cTop_agree.2.2.2 curvePlainImpl847e
  show (eTop.dyna.state.get curvePlainImpl847e).code = code
  rw [← hc, ← h]
  rfl

/-- **V+ nonvacuity, committing, under every covered fork.**  `vplus_witness2` with the block
environment's fork changed to any covered fork `g` (Prague, Osaka, BPO1, BPO2): the top-level
message `msgTop.withFork g` enters with `eTop.withFork g`; every execution of that machine
succeeds with `dTop`, one exists, and it carries the antecedent of `vplus_exclusion_stethPool`,
its premises, the spawn, the reentry refused at the lock check, `¬ lockL.Enters P G`, and the
same post-state as at Prague.  Obtained from the Prague kernel facts by
`Blanc/Lift/NodeWalkFork.lean` and `Frames.lean` (the run executes no `CLZ` and reads no blob
price, the block has no excess blob gas, and none of its six spawned frames enters `MODEXP` or
`P256VERIFY`); nothing is re-evaluated. -/
theorem vplus_witness2_covered (g : Fork) (hg : CoveredFork g) :
    (msgTop.withFork g).benv.stat.fork = g ∧
    (frameTop.withFork g).enter = .run (eTop.withFork g) ∧ (eTop.withFork g).pc = 0 ∧
    (∀ out, Exec 0 (eTop.withFork g).sta (eTop.withFork g).dyna out → out = .ok dTop) ∧
    ∃ (out : Execution) (R : Exec 0 (eTop.withFork g).sta (eTop.withFork g).dyna out)
      (F h c q G : Exec.Deriv),
      -- the premises of `vplus_exclusion_stethPool`, for this `R`
      CoveredFork (eTop.withFork g).sta.benvStat.fork ∧
      (eTop.withFork g).dyna.getCode curveStethPool847e = forwarderCode curvePlainImpl847e ∧
      (eTop.withFork g).dyna.getCode curvePlainImpl847e = code ∧
      ((eTop.withFork g).sta.currentTarget = curveStethPool847e →
        (eTop.withFork g).sta.code = (eTop.withFork g).dyna.getCode curveStethPool847e) ∧
      lockL.HashAvoidIn curveStethPool847e R ∧
      -- its antecedent: the pool body, active, spawns the receiver with the ETH payment
      F ∈ Exec.rawFrameRoots R ∧ ActiveRel curveStethPool847e F h ∧ Spawns h c ∧
      h.pc = 7427 ∧ Ninst.At h.sevm.code h.pc (.exec .call) ∧
      c.sevm.currentTarget = receiverAddress ∧ c.sevm.code = Receiver.code ∧
      c.sevm.value.toNat = 100 ∧
      -- the reentry through the forwarder, refused at the lock check
      q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = curveStethPool847e ∧
      q.sevm.code = forwarderCode curvePlainImpl847e ∧ G ∈ Exec.rawFrameRoots q.exc ∧
      G ∈ Exec.rawFrameRoots c.exc ∧ CPFrame curveStethPool847e code G ∧
      G.sevm.data = reentryCall ∧ G.exn = .error (.revert, dRe) ∧
      (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) ∧
      ¬ lockL.Enters curveStethPool847e G ∧
      -- the transaction commits
      out = .ok dTop ∧
      ((eTop.withFork g).dyna.getBal curveStethPool847e).toNat = 1000 ∧
      (dTop.getBal curveStethPool847e).toNat = 900 ∧
      ((eTop.withFork g).dyna.getBal receiverAddress).toNat = 0 ∧
      (dTop.getBal receiverAddress).toNat = 100 ∧
      lockAt curveStethPool847e 0 (eTop.withFork g).dyna = (3 : Nat).toB256 ∧
      lockAt curveStethPool847e 0 dTop = (3 : Nat).toB256 := by
  obtain ⟨R⟩ := (exec_iff_exec_eq 0 (eTop.withFork g).sta (eTop.withFork g).dyna _).mpr rfl
  have hS : ∃ g', CoveredFork g' ∧ (eTop.withFork g).sta = eTop.sta.withFork g' := ⟨g, hg, rfl⟩
  obtain ⟨hout, hca, F, h, c, q, G, hF, act, sp, hash, hpc, hat, hct, hcc, hcv, hq, hqt, hqc,
    hGq, hGc, cpG, hdG, exG, nb, chk⟩ := vplus_run2_at hS R
  obtain ⟨hTpc, hTtarget, hTcode, -⟩ := eTop_static
  obtain ⟨-, -, -, hpost, hxpost, hlockpost, hpre, hxpre, hlockpre, -⟩ := runFactsD
  have hfork' : CoveredFork (eTop.withFork g).sta.benvStat.fork := hg
  have hroot : (eTop.withFork g).sta.currentTarget = curveStethPool847e →
      (eTop.withFork g).sta.code = (eTop.withFork g).dyna.getCode curveStethPool847e := fun _ => by
    show eTop.sta.code = eTop.dyna.getCode curveStethPool847e
    rw [hTcode, eTop_getCode_proxy]
  have hP : (eTop.withFork g).dyna.getCode curveStethPool847e = forwarderCode curvePlainImpl847e :=
    eTop_getCode_proxy
  have hI : (eTop.withFork g).dyna.getCode curvePlainImpl847e = code := eTop_getCode_impl
  have hpreAcc : AcctAgree eTop.dyna.state cTop.acs := cTop_agree.2.2.2
  have hpreStor : ∀ a k, storOf eTop.dyna.state a k = lookupS cTop.stor a k :=
    cTop_agree.2.2.1
  have hent : (frameTop.withFork g).enter = .run (eTop.withFork g) := by
    have h0 : frameTop.enter = .run eTop := by
      rw [frame_enter_eq_B, frameEnterB_eq_S acctAgreeInit]; exact eTop_eq
    have hp : frameTop.PrecompNeutral :=
      Frame.precompNeutral_of_codeAddress (a := proxyAddress) rfl (by decide) (by decide)
    rw [frame_enter_withFork CoveredFork.prague CoveredFork.prague hg hp, h0]
    rfl
  refine ⟨rfl, hent, hTpc, fun _ R' => (vplus_run2_at hS R').1, _, R, F, h, c, q, G, hfork', hP, hI,
    hroot, hash, hF, act, sp, hpc, hat, hct, hcc, hcv, hq, hqt, hqc, hGq, hGc, cpG, hdG, exG, nb,
    chk, vplus_exclusion_stethPool R hfork' hP hI hroot hash hF act sp hGc, hout, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · show (eTop.dyna.getBal curveStethPool847e).toNat = 1000
    rw [getBal_of_agree hpreAcc]; exact hpre
  · rw [getBal_of_agree hca.2.2.2]; exact hpost
  · show (eTop.dyna.getBal receiverAddress).toNat = 0
    rw [getBal_of_agree hpreAcc]; exact hxpre
  · rw [getBal_of_agree hca.2.2.2]; exact hxpost
  · exact (hpreStor curveStethPool847e 0).trans hlockpre
  · exact (hca.2.2.1 curveStethPool847e 0).trans hlockpost

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2
