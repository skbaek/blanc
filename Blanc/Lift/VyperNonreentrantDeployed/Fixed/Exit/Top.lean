import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit.Frames
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund.Checkpoint
import Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exclusion

/-!
# V+ V5: a successful outer `remove_liquidity` from the funded checkpoint, its callback's
guarded reentry blocked at the lock

`vplus_reach_exit`, on every covered fork, from the checkpoint world `world8` (what the first
`add_liquidity` settles to): the code-free creator's `remove_liquidity(200, [0, 0], R)` through
the clone **succeeds** (920,078 gas left, refund 2,800) and settles to a world in which `R` holds
100 wei and 100 `T`, the clone 900 wei and 900 `T`, the supply and the creator's LP balance are
1800 and the lock is released.  Every execution of the entered machine succeeds, and one exists
whose nodes carry, for the pool frame `F` running the comparator in the clone's storage:

* **lock acquisition**: `F` reaches the guarded body start 0x1bae of `remove_liquidity` (after
  the lock-set `SSTORE` at 0x1bad), and no release `SSTORE` lies between it and the ETH `CALL`
  `h` (pc 7427) — `ActiveRel P F h`;
* **the attempted entry**: `h` spawns the receiver `c` (`R`, with the 100 wei), which calls the
  clone again; the forwarder `q` it reaches `DELEGATECALL`s the comparator, opening the
  pool-owned frame `G` with `add_liquidity([100, 0], 0)` calldata (a guarded mutating entry);
* **its exclusion**: `G` reads the held lock at the check (pc 0x53), lands on the revert pad
  0x477e and reverts, reaching no guarded body start; and `vplus_exclusion` is **instantiated** for
  this execution, its world/root/hash premises discharged (the hash premise from the digests the
  walks decide, trace-local, no hash axiom), giving `¬ lockL.Enters P G`;
* **settlement**: the outer call commits with the nontrivial effect above.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit

open Jaune Blanc.Lift Blanc.Lift.Witness Blanc.Lift.NodeWalk Blanc.LockExclusion Blanc.ForkUniform
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Reach Blanc.Lift.VyperNonreentrantDeployed.Fixed.Init
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Fund
open Blanc.Lift.VyperNonreentrantDeployed.Fixed.Witness2 (okNoRel okNoBody settleOr)
open Jaune.Exec.Deriv (ParentPrefix ParentStep)
open Blanc.Lift.VyperNonreentrantDeployed.Fixed (ActiveRel vplus_exclusion lockBodies lockMutBodies
  lockReleasePcs lockL code_size)

/-- The clone and the comparator, as the start shadows show them. -/
theorem topCodes :
    (lookupA cTop.acs proxyAddr).code = fwd ∧ (lookupA cTop.acs implAddr).code = code := by
  kernel_rfl_and

attribute [local irreducible] cTop1 cpTop eB cB1 cB2 cpBal eBal cBal1 dBal dB3 cB4 cpEth eRcv
  cRcv1 cpCb eCb cCb1 cpRe eRe cRe1 cRe2 dRe dCb2 cCb3 dCb dRcv2 cRcv3 dRcv dB5 cB6 cpXf eXf
  cXf1 dXf dB7 cB8 dB dTop2 cTop3 dTop

theorem re_sta (e : Evm) (g : Fork) (O : State) : (e.re g O).sta = (e.sta.withFork g).withOrig O :=
  rfl

theorem fwd_ne : fwd ≠ code := fun h => by
  have := congrArg ByteArray.size h
  rw [Blanc.Lift.VyperNonreentrantDeployed.Fixed.code_size] at this
  exact absurd this (by decide)

theorem eTop_reOK (hO : OrigAgree world8 O8) : ReOK world8 eTop.sta := by
  obtain ⟨he, hst, -⟩ := exitFacts
  have h := hst
  simp only [Prod.mk.injEq] at h
  exact reOK_root hO he h.2.2.2.2 h.2.2.2.1

/-- **The run, on every derivation**, under any covered fork and the real original state. -/
theorem exit_run_at {g : Fork} (hg : CoveredFork g) (hO : OrigAgree world8 O8)
    (hag0 : PAgree cTop) {out : Execution} (R : Exec 0 (reS eTop.sta g) eTop.dyna out) :
    out = .ok dTop ∧ ChildAgree dTop cTop3.keys cTop3.adrs cTop3.stor cTop3.acs ∧
    ∃ F h c q G : Exec.Deriv,
      F ∈ Exec.rawFrameRoots R ∧ ActiveRel proxyAddr F h ∧ Spawns h c ∧
      lockL.HashAvoidIn proxyAddr R ∧
      h.pc = 7427 ∧ Ninst.At h.sevm.code h.pc (.exec .call) ∧
      c.sevm.currentTarget = receiverAddr ∧
      c.sevm.code = Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code ∧
      c.sevm.value.toNat = 100 ∧
      q ∈ Exec.rawFrameRoots c.exc ∧ q.sevm.currentTarget = proxyAddr ∧
      q.sevm.code = fwd ∧ G ∈ Exec.rawFrameRoots q.exc ∧ G ∈ Exec.rawFrameRoots c.exc ∧
      CPFrame proxyAddr code G ∧ G.sevm.data = reentryData ∧
      G.exn = .error (.revert, dRe) ∧ (∀ x, ParentPrefix G x → x.pc ∉ lockBodies) ∧
      (∃ y y', ParentPrefix G y ∧ y.pc = 0x53 ∧ ParentPrefix y y' ∧ y'.pc = 0x477e) := by
  obtain ⟨-, hstT, walkTop1, pTop1, decTop1, dcallTop, enterB, eBF, caB, -, -, -, -, -, -, -, -, eBalF, -, -, -, -, -, -, -, -, -, -, eRcvF, -, -, -, -, -, -, eCbF, -, -, -, -, -, eReF, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, eXfF, -, -, -, -, -, -, dBerr, resTop2, walkTop3, walkTop4, -⟩ := exitFacts
  have hs := eTop_reOK hO
  obtain ⟨hTpc, -, hTcode, -⟩ : eTop.pc = 0 ∧ eTop.sta.currentTarget = proxyAddr ∧
      eTop.sta.code = fwd ∧ eTop.sta.benvStat.fork = .prague := by
    simp only [Prod.mk.injEq] at hstT; exact ⟨hstT.1, hstT.2.1, hstT.2.2.1, hstT.2.2.2.1⟩
  have hsB : ReOK world8 eB.sta :=
    ReOK.of_stat ((frameEnterS_stat enterB).trans (dcallPrep_stat dcallTop).2) hs
  obtain ⟨sTop, nB⟩ := dcallSpawn_re hs hg dcallTop
    (Frame.precompNeutral_of_codeAddress caB (by decide) (by decide)) enterB
  have hcT : (reS eTop.sta g).code = fwd := hTcode
  have w1 := (walk_re hs hg .refuse fwdTries okAny 11 cTop).trans walkTop1
  have w3 := (walk_re hs hg .refuse fwdTries okAny 10 cTop2).trans walkTop3
  have w4 := (walk_re hs hg .refuse fwdTries okAny 1 cTop3).trans walkTop4
  have hP0 : NodeAt (reS eTop.sta g) cTop ⟨0, (reS eTop.sta g), eTop.dyna, out, R⟩ :=
    ⟨hTpc.symm, rfl, rfl⟩
  obtain ⟨hag1, h1⟩ := pwalkH_cont .refuse fwdTries hcT okAny 11 cTop cTop1 hag0 w1
  obtain ⟨x1, hx1, pp01, ex01, ds01, -⟩ := h1 _ hP0
  have hat1 : Ninst.At (reS eTop.sta g).code cTop1.pc (.exec .delegatecall) := by
    rw [hcT, pTop1]; exact decodeT_sound fwdTries decTop1
  obtain ⟨stepT, entB, -, hagB0, hFT⟩ := delegatecall_node hag1 hat1 sTop nB
  obtain ⟨F, x2, sp0, hF, e2, hx2, ex2, hdesc2, hag2⟩ :=
    spawn_resume_ok hx1 hag1 hFT stepT entB dBerr resTop2
      (fun F hF => let r := frameB hg hsB (pagree_re hagB0) F (nodeAt_re hF); ⟨r.1, r.2.1⟩)
  have hF' := nodeAt_re hF
  have hFs : F.sevm = reS eB.sta g := hF'.2.1.trans (re_sta eB g world8)
  obtain ⟨-, -, b, h, t1, xr, q, G, t2, ppFb, hbpc, ppbh, hhpc, hath, hrel, sph, ht1, hxr, hq,
    hG, ht2, dsF, dsr, dsq, hre, hashF⟩ := frameB hg hsB (pagree_re hagB0) F hF'
  obtain ⟨hag3, h3⟩ := pwalkH_cont .refuse fwdTries hcT okAny 10 cTop2 cTop3 hag2 w3
  obtain ⟨x3, hx3, -, ex3, ds3, -⟩ := h3 x2 hx2
  obtain ⟨ex4, ds4, -⟩ := pwalkH_halt .refuse fwdTries hcT okAny 1 cTop3 _ hag3 w4 x3 hx3
  have hout : out = .ok dTop := by
    show (⟨0, (reS eTop.sta g), eTop.dyna, out, R⟩ : Exec.Deriv).exn = _
    rw [← ex01, ← ex2, ← ex3]; exact ex4
  have hdescR : Exec.rawFrameDescendants R = [F, t1, xr, q, G, t2] := by
    show Exec.rawFrameDescendants
      (⟨0, (reS eTop.sta g), eTop.dyna, out, R⟩ : Exec.Deriv).exc = _
    rw [← ds01, hdesc2, dsF, ← ds3, ds4]
    rfl
  have hroots : ∀ G', G' ∈ Exec.rawFrameRoots R →
      G' = ⟨0, (reS eTop.sta g), eTop.dyna, out, R⟩ ∨ G' = F ∨
      G' = t1 ∨ G' = xr ∨ G' = q ∨ G' = G ∨ G' = t2 := by
    intro G' hG'
    simp only [Exec.rawFrameRoots, hdescR, List.mem_cons, List.not_mem_nil, or_false] at hG'
    exact hG'
  have eB_code : eB.sta.code = code := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eBF).2).2).1
  have eB_pc : eB.pc = 0 := (Prod.mk.inj eBF).1
  have eB_tgt : eB.sta.currentTarget = proxyAddr := (Prod.mk.inj (Prod.mk.inj eBF).2).1
  have eRe_code : eRe.sta.code = code := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eReF).2).2).1
  have eRe_pc : eRe.pc = 0 := (Prod.mk.inj eReF).1
  have eRe_tgt : eRe.sta.currentTarget = proxyAddr := (Prod.mk.inj (Prod.mk.inj eReF).2).1
  have eRe_data : eRe.sta.data = reentryData := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eReF).2).2).2
  have eCb_tgt : eCb.sta.currentTarget = proxyAddr := (Prod.mk.inj (Prod.mk.inj eCbF).2).1
  have eCb_code : eCb.sta.code = fwd := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eCbF).2).2).1
  have eRcv_tgt : eRcv.sta.currentTarget = receiverAddr := (Prod.mk.inj (Prod.mk.inj eRcvF).2).1
  have eRcv_code : eRcv.sta.code = Blanc.Lift.VyperNonreentrantDeployed.Fixed.ReceiverR.code :=
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eRcvF).2).2).1
  have eRcv_val : eRcv.sta.value.toNat = 100 :=
    (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj eRcvF).2).2).2).1
  have eBal_tgt : eBal.sta.currentTarget = tokenAddr := (Prod.mk.inj (Prod.mk.inj eBalF).2).1
  have eXf_tgt : eXf.sta.currentTarget = tokenAddr := (Prod.mk.inj (Prod.mk.inj eXfF).2).1
  have hcodeF : F.sevm.code = code := by rw [hFs]; exact eB_code
  have hcodeG : G.sevm.code = code := by rw [hG.2.1]; exact eRe_code
  have hashG := hre.2.1
  have ownerNe : ∀ (n : Exec.Deriv) (sevm : Sevm) (a : Adr), a ≠ proxyAddr → n.sevm = sevm →
      sevm.currentTarget = a → n.sevm.currentTarget ≠ proxyAddr := by
    intro n sevm a ha h1 h2 h3
    rw [h1, h2] at h3
    exact ha h3
  have hqcode : q.sevm.code = fwd := by rw [hq.2.1]; exact eCb_code
  have hHash : lockL.HashAvoidIn proxyAddr R := by
    intro G' hG' hcp
    have hc : G'.sevm.code = code := hcp.2.2
    have ht : G'.sevm.currentTarget = proxyAddr := hcp.2.1
    rcases hroots G' hG' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd (hTcode.symm.trans hc) fwd_ne
    · exact hashAvoid_of_hashOK hcodeF (fun x hx => hashF x hx)
    · exact absurd ht (ownerNe _ _ tokenAddr (by decide) ht1.2.1 eBal_tgt)
    · exact absurd ht (ownerNe _ _ receiverAddr (by decide) hxr.2.1 eRcv_tgt)
    · exact absurd (hqcode.symm.trans hc) fwd_ne
    · exact hashAvoid_of_hashOK hcodeG (fun x hx => (hashG x hx).1)
    · exact absurd ht (ownerNe _ _ tokenAddr (by decide) ht2.2.1 eXf_tgt)
  have memD : ∀ (n y : Exec.Deriv), y ∈ Exec.rawFrameDescendants n.exc →
      y ∈ Exec.rawFrameRoots n.exc := fun n y hy => List.mem_cons_of_mem _ hy
  refine ⟨hout, halt1_childAgree fwdTries hag3 w4, F, h, xr, q, G, ?_, ⟨⟨(hF'.1.trans eB_pc),
    (by rw [hFs]; exact eB_tgt), hcodeF⟩, ppFb.trans ppbh, b, ppFb, ppbh,
    by rw [hbpc]; decide, hrel⟩, sph, hHash, hhpc, hath,
    (by rw [hxr.2.1]; exact eRcv_tgt), (by rw [hxr.2.1]; exact eRcv_code),
    (by rw [hxr.2.1]; exact eRcv_val), memD xr q (by rw [dsr]; simp only [List.mem_cons,
      List.not_mem_nil, or_false, true_or]),
    (by rw [hq.2.1]; exact eCb_tgt), hqcode, memD q G (by rw [dsq]; simp only [List.mem_cons,
      List.not_mem_nil, or_false]),
    memD xr G (by rw [dsr]; simp only [List.mem_cons, List.not_mem_nil, or_false, or_true]),
    ⟨(hG.1.trans eRe_pc), (by rw [hG.2.1]; exact eRe_tgt), hcodeG⟩,
    (by rw [hG.2.1]; exact eRe_data), hre.1, fun x hx => (hashG x hx).2, hre.2.2⟩
  exact List.mem_cons_of_mem _ (by rw [hdescR]; simp only [List.mem_cons, List.not_mem_nil,
    or_false, true_or])

end Blanc.Lift.VyperNonreentrantDeployed.Fixed.Exit
